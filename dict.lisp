;;;; DICTs, a.k.a. Hash Array-Mapped Tries
;;; HAMTs are introduced by Phil Bagwell in the paper "Ideal Hash Trees," Nov 2001,
;;; https://lampwww.epfl.ch/papers/idealhashtrees.pdf . This implementation makes a few simplifications to
;;; Bagwell's data structure:
;;; - The root table is a node like any other, with a maximum radix of +BRACH-RATE+.
;;; - We never rehash conflicting keys. If two keys hash to the same index, we construct a CONFLICT-NODE, for
;;;   which lookup and insertion do a linear scan.
;;; - We use the low bits of the hash to index into the root table, and progressively higher bits to index
;;;   into later nodes, where Bagwell does the opposite. This simplifies our traversal, and has the convenient
;;;   side effect that we don't need to check if we've run out of bits in the hash; after that point, LDB will
;;;   always return all-zeros or all-ones, depending on sign.
(uiop:define-package :immutable/dict
  (:import-from :alexandria
                #:array-index #:array-length #:define-constant #:when-let #:once-only #:with-gensyms #:if-let)
  (:shadow #:get #:remove)
  (:use :cl :iterate :immutable/%generator :immutable/%simple-vector-utils)
  (:import-from :immutable/hash
                #:==
                #:hash
                #:unsigned-fixnum)
  (:export

   ;; type definition
   #:dict

   ;; number of elements
   #:size

   ;; GETHASH analogue
   #:get

   ;; (SETF GETHASH) analogue, but persistent
   #:insert

   ;; REMHASH analogue, but persistent
   #:remove

   ;; MAKE-HASH-TABLE analogue to construct an empty dict
   #:empty))
(in-package :immutable/dict)

#+immutable-dict-debug
(declaim (optimize (speed 1) (safety 3) (space 1) (debug 3) (compilation-speed 0)))
#-immutable-dict-debug
(declaim (optimize (speed 3) (safety 1) (space 1) (debug 1) (compilation-speed 0)))

;;; Early type definitions and whatnot

(eval-when (:compile-toplevel :load-toplevel)
  (declaim (type array-length +branch-rate+))
  (defconstant +branch-rate+ 32
    "The maximum of child nodes contained in each node of a DICT.")

  (declaim (type (and fixnum unsigned-byte) +node-index-bits+))
  (defconstant +node-index-bits+ (floor (log +branch-rate+ 2))
    "The number of bits used to index into a node of a DICT.")

  (declaim (type (and fixnum unsigned-byte) +max-shift+))
  (defconstant +max-shift+ (1- (floor (log most-positive-fixnum +branch-rate+)))))

(deftype size ()
  "The size of a `dict', in number of entries."
  'unsigned-fixnum)

(deftype hash-function ()
  '(function (t) (values fixnum &optional)))

(deftype test-function ()
  '(function (t t) (values boolean &optional)))

(deftype bitmap ()
  "The bitmap held by a `hash-node' which marks the indices which hold children."
  `(unsigned-byte ,+branch-rate+))

(deftype shift ()
  "A bit offset, in units of +NODE-INDEX-BITS+, into a hash.

When extracting a `hash-node-logical-index' from a `hash', we use the +NODE-INDEX-BITS+ starting at (* SHIFT
+NODE-INDEX-BITS+). The SHIFT is the current node's depth in the trie."
  `(integer 0 ,+max-shift+))

(deftype hash-node-logical-index ()
  "An index into a `hash-node'."
  `(integer 0 ,+branch-rate+))

;;; struct definitions for node variants

;;; HASH-NODE
;;
;; A branching node in a `dict' for elements with distinct hash parts.
;;
;; Each `hash-node' is implicitly associated with a `shift', determined by that node's depth in the trie, which
;; determines which bits of the `hash' are used as its indices.
;;
;; The ENTRIES is a sparse sequence of child nodes, and the BITMAP maps hash-part indices to true-indices into
;; the ENTRIES vector. (length ENTRIES) is always equal to (logcount BITMAP).
;;
;; The terminology for HASH-NODE indices is a little wonky, because there are four different kinds of indices:
;; - Logical indices, which are in the range 0 -- 32, are extracted from hashes. These are sparse, and are
;;   mapped to dense counted indices by the hash-node's bitmap. Each corresponds to a two-element pair, which
;;   may be:
;;   - A key and a value.
;;   - A hash and a `conflict-node'.
;;   - A logical-index-bitmap and a child `hash-node'.
;; - Counted indices, which are in the range 0 -- 32, are dense. Transforming a logical index into a counted
;;   index involves inspecting the hash-node's bitmap and counting the number of one bits below the logical
;;   index. This is done by `hash-node-logical-index-to-counted-index'.
;; - Paired indices are counted indices multiplied by two. The paired index 2n contains the key or sub-bitmap
;;   of the child at conted index n, and the paired index (2n + 1) contains the value or child node.
;; - True indices are paired indices added to some automatically-computed offset to skip the hash-node's
;;   named slots. Paired indices are transformed to true indices by `hash-node-paired-index-to-true-index'.

(define-vector-struct hash-node
    (:max-length #.(* +branch-rate+ 2)
     :length hash-node-paired-count
     :ref hash-node-paired-ref
     :logical-index-to-true-index hash-node-paired-index-to-true-index
     :logical-length-to-true-length hash-node-paired-length-to-true-length
     :constructor %make-hash-node
     :zero-index +hash-node-zero+)
  ;; The CHILD-IS-ENTRY-P and CHILD-IS-CONFLICT-P bitmaps map counted-indices to whether the associated child
  ;; is a key/value pair or a hash/conflict-node pair. These are mutually exclusive. If both bits are 0, the
  ;; associated child is either not present, or is a logical-index-bitmap/hash-node pair.
  (child-is-entry-p :type bitmap
                    :initform (error "Supply :CHILD-IS-ENTRY-P to %MAKE-HASH-NODE"))
  (child-is-conflict-p :type bitmap
                       :initform (error "Supply :CHILD-IS-CONFLICT-P to %MAKE-HASH-NODE")))

(declaim (ftype (function (hash-node) (values array-length &optional))
                hash-node-logical-count)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline hash-node-logical-count))
(defun hash-node-logical-count (hash-node)
  (ash (hash-node-paired-count hash-node) -1))

;;; CONFLICT-NODE
;;
;; A leaf-ish node in a `dict' for distinct elements with the same hash.
;;
;; The ENTRIES will be a vector of key/value pairs, all of which have keys with the same hash, but which are
;; not equal under the TEST-FUNCTION. Lookup in a `conflict-node' is a linear search of its ENTRIES.
;;
;; A `conflict-node' will always contain at least two key/value pairs.
;;
;; CONFLICT-NODE indices are not quite as wonky as those for hash-nodes, but still have three levels:
;; - Logical indices start from 0. Each logical index corresponds to a key/value pair.
;; - Paired indices are logical indices multiplied by two. The paired index 2n contains the key of the entry
;;   at logical index n, and the paired index (2n + 1) contains the value.
;; - True indices are paired indices added to some automatically-computed offset to skip the hash-node's named
;;   slots. Paired indices are transformed to true indices by `conflict-node-paired-index-to-true-index'.
(define-vector-struct conflict-node
    (:length conflict-node-paired-count
     :ref conflict-node-paired-ref
     :logical-index-to-true-index conflict-node-paired-index-to-true-index
     :logical-length-to-true-length conflict-node-paired-length-to-true-length
     :constructor %make-conflict-node
     :zero-index +conflict-node-zero+))

(declaim (ftype (function (conflict-node) (values array-length &optional))
                conflict-node-logical-length)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline conflict-node-logical-length))
(defun conflict-node-logical-length (conflict-node)
  (ash (conflict-node-paired-count conflict-node) -1))

(deftype node ()
  '(or hash-node conflict-node))

(deftype child-type ()
  '(member :hash-node :conflict-node :entry nil))

;;; The actual DEFSTRUCT!

(declaim (inline %make-dict %dict-size %dict-hash-function %dict-test-function %dict-key %dict-value %dict-child-type))

(defstruct (dict
            (:constructor %make-dict)
            (:copier nil)
            (:conc-name %dict-))
  "A persistent hash map, implemented as a hash array-mapped trie."
  (size (error "Supply :SIZE to %MAKE-DICT")
   :type size)
  (hash-function (error "Supply :HASH-FUNCTION to %MAKE-DICT")
   :type hash-function)
  (test-function (error "Supply :TEST-FUNCTION to %MAKE-DICT")
   :type test-function)
  (child-type (error "Supply :CHILD-TYPE to %MAKE-DICT")
   :type child-type)
  (key (error "Supply :KEY to %MAKE-DICT"))
  (value (error "Supply :VALUE to %MAKE-DICT")))

;;; accessors

(declaim (ftype (function (dict) (values size &optional))
                size)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline size))
(defun size (dict)
  (%dict-size dict))

;;; lookup with GET

(declaim (ftype (function (array-index) (values array-index &optional))
                conflict-node-key-true-index
                conflict-node-value-true-index)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline conflict-node-key-true-index
                    conflict-node-value-true-index))
(defun conflict-node-key-true-index (logical-index)
  (conflict-node-paired-index-to-true-index (* logical-index 2)))

(defun conflict-node-value-true-index (logical-index)
  (conflict-node-paired-index-to-true-index (1+ (* logical-index 2))))

(declaim (ftype (function (conflict-node array-index) (values t &optional))
                conflict-node-true-ref)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline conflict-node-true-ref))
(defun conflict-node-true-ref (conflict-node true-index)
  (svref conflict-node true-index))

(declaim (ftype (function (t conflict-node array-index) (values t &optional))
                (setf conflict-node-true-ref))
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline (setf conflict-node-true-ref)))
(defun (setf conflict-node-true-ref) (new-elt conflict-node true-index)
  (setf (svref conflict-node true-index) new-elt))

(declaim (ftype (function (conflict-node array-index) (values t t &optional))
                conflict-node-logical-ref)
         ;; Inlining may allow more efficient multiple-values usage, or for the compiler to eliminate unused
         ;; return values if we only need one of them.
         (inline conflict-node-logical-ref))
(defun conflict-node-logical-ref (conflict-node logical-index)
  (let* ((key-index (conflict-node-key-true-index logical-index)))
    (values (conflict-node-true-ref conflict-node key-index)
            (conflict-node-true-ref conflict-node (1+ key-index)))))

(declaim (ftype (function (conflict-node array-index t t) (values &optional))
                set-conflict-node-logical-entry)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline set-conflict-node-logical-entry))
(defun set-conflict-node-logical-entry (conflict-node logical-index new-key new-value)
  (let* ((key-index (conflict-node-key-true-index logical-index)))
    (setf (conflict-node-true-ref conflict-node key-index)
          new-key)
    (setf (conflict-node-true-ref conflict-node (1+ key-index))
          new-value))
  (values))

(declaim (ftype (function (conflict-node array-index) (values t &optional))
                conflict-node-logical-key-ref
                conflict-node-logical-value-ref)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline conflict-node-logical-key-ref
                 conflict-node-logical-value-ref))
(defun conflict-node-logical-key-ref (conflict-node logical-index)
  (conflict-node-true-ref conflict-node (conflict-node-key-true-index logical-index)))
(defun conflict-node-logical-value-ref (conflict-node logical-index)
  (conflict-node-true-ref conflict-node (conflict-node-value-true-index logical-index)))

(declaim (ftype (function (t conflict-node array-index) (values t &optional))
                (setf conflict-node-logical-key-ref)
                (setf conflict-node-logical-value-ref))
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline (setf conflict-node-logical-key-ref)
                 (setf conflict-node-logical-value-ref)))
(defun (setf conflict-node-logical-key-ref) (new-key conflict-node logical-index)
  (setf (conflict-node-true-ref conflict-node (conflict-node-key-true-index logical-index))
        new-key))
(defun (setf conflict-node-logical-value-ref) (new-value conflict-node logical-index)
  (setf (conflict-node-true-ref conflict-node (conflict-node-value-true-index logical-index))
        new-value))

(declaim (ftype (function (bitmap hash-node-logical-index) (values boolean &optional))
                bitmap-contains-p)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline bitmap-contains-p))
(defun bitmap-contains-p (bitmap logical-index)
  (logbitp logical-index bitmap))

(declaim (ftype (function (hash-node bitmap hash-node-logical-index) (values child-type &optional))
                hash-node-child-type)
         ;; Inlining may allow the compiler to eliminate references to and comparisons with the actual
         ;; keywords in `child-type'.
         (inline hash-node-child-type))
(defun hash-node-child-type (hash-node bitmap logical-index)
  "Does this HASH-NODE contain a child at the index LOGICAL-INDEX?"
  (cond ((not (bitmap-contains-p bitmap logical-index)) nil)
        ((bitmap-contains-p (hash-node-child-is-entry-p hash-node) logical-index) :entry)
        ((bitmap-contains-p (hash-node-child-is-conflict-p hash-node) logical-index) :conflict-node)
        (:else :hash-node)))

(declaim (ftype (function (bitmap hash-node-logical-index) (values array-index &optional))
                bitmap-logical-index-to-counted-index)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline bitmap-logical-index-to-counted-index))
(defun bitmap-logical-index-to-counted-index (bitmap logical-index)
  "Find the true-index into a hash-node's entries vector associated with INDEX.

Precondition: the associated hash-node must contain the INDEX, i.e. the INDEXth bit in BITMAP must be 1."
  (let* ((bits-before (ldb (byte logical-index 0)
                           bitmap)))
    (logcount bits-before)))

(declaim (ftype (function (bitmap hash-node-logical-index) (values array-index &optional))
                hash-node-key-true-index
                hash-node-value-true-index)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline hash-node-key-true-index
                 hash-node-value-true-index))
(defun hash-node-key-true-index (bitmap logical-index)
  "Find the true-index into a hash-node's entries vector associated with INDEX.

Precondition: the HASH-NODE must `hash-node-contains-p' the INDEX."
  (hash-node-paired-index-to-true-index (* (bitmap-logical-index-to-counted-index bitmap logical-index)
                                           2)))

(defun hash-node-value-true-index (bitmap logical-index)
  (hash-node-paired-index-to-true-index (1+ (* (bitmap-logical-index-to-counted-index bitmap logical-index)
                                               2))))

(declaim (ftype (function (hash-node array-index) (values t &optional))
                hash-node-true-ref)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline hash-node-true-ref))
(defun hash-node-true-ref (hash-node true-index)
  "Look up a child of HASH-NODE by its TRUE-INDEX.

Precondition: the TRUE-INDEX must have resulted from a valid call to `bitmap-true-index' or
`hash-node-true-index' using the HASH-NODE or its bitmap."
  (svref hash-node true-index))

(declaim (ftype (function (t hash-node array-index) (values t &optional))
                (setf hash-node-true-ref))
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline (setf hash-node-true-ref)))
(defun (setf hash-node-true-ref) (new-value hash-node true-index)
  (setf (svref hash-node true-index)
        new-value))

(declaim (ftype (function (hash-node bitmap hash-node-logical-index) (values t t &optional))
                hash-node-logical-ref)
         ;; Inlining may allow more efficient multiple-values usage, or for the compiler to eliminate unused
         ;; return values if we only need one of them.
         (inline hash-node-logical-ref))
(defun hash-node-logical-ref (hash-node bitmap logical-index)
  "Look up a child of HASH-NODE by its LOGICAL-INDEX.

Precondition: the HASH-NODE must `hash-node-contains-p' the INDEX."
  (let* ((key-index (hash-node-key-true-index bitmap logical-index)))
    (values (hash-node-true-ref hash-node key-index)
            (hash-node-true-ref hash-node (1+ key-index)))))

(declaim (ftype (function (shift fixnum) (values hash-node-logical-index))
                extract-hash-part-for-shift)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline extract-hash-part-for-shift))
(defun extract-hash-part-for-shift (shift hash)
  "Extract a `hash-node-logical-index' from HASH for a `hash-node' at SHIFT, i.e. a hash-node that is SHIFT steps removed from the trie's root."
  (let ((shift-low-bit (* shift +node-index-bits+)))
    (ldb (byte +node-index-bits+ shift-low-bit)
         hash)))

(declaim (ftype (function (conflict-node t test-function t) (values t boolean &optional))
                conflict-node-lookup))
(defun conflict-node-lookup (conflict-node key test-function not-found)
  (declare (inline child-lookup))
  (iter (declare (declare-variables))
       (for index below (conflict-node-logical-length conflict-node))
       (for (values other-key value) = (conflict-node-logical-ref conflict-node index))
       (when (funcall test-function key other-key)
         (return (values value t)))
       (finally (return (values not-found nil)))))

;; Predeclarations for better type inference in recursive calls by HASH-NODE-LOOKUP
(declaim (ftype (function (child-type t t t fixnum shift test-function t)
                          (values t boolean &optional))
                child-lookup))

(declaim (ftype (function (hash-node bitmap t fixnum shift hash-node-logical-index test-function t)
                          (values t boolean &optional))
                hash-node-lookup))
(defun hash-node-lookup (hash-node bitmap key hash shift logical-index test-function not-found)
  "Get the value associated with KEY in NODE.

HASH is the result of applying the containing `dict' 's HASH-FUNCTION to KEY.

SHIFT is the depth into the trie of NODE. For a `dict' 's BODY, this will be 0.

TEST-FUNCTION is the containing `dict' 's TEST-FUNCTION, which must satisfy the hash-test-function laws with
the HASH-FUNCTION used to generate HASH.

NOT-FOUND is an arbitrary value to be returned as primary value if NODE does not contain a mapping for KEY."
  (declare (notinline hash-node-child-type))
  (if-let ((child-type (hash-node-child-type hash-node bitmap logical-index)))
    (multiple-value-bind (subkey value) (hash-node-logical-ref hash-node bitmap logical-index)
      (child-lookup child-type
                    subkey
                    value
                    key
                    hash
                    (1+ shift)
                    test-function
                    not-found))
    (values not-found nil)))

(defun child-lookup (child-type entry-key entry-value sought-key hash shift test-function not-found)
  (declare (notinline extract-hash-part-for-shift bitmap-contains-p))
  (ecase child-type
    ((nil) (values not-found nil))
    (:entry (if (funcall test-function entry-key sought-key)
                (values entry-value t)
                (values not-found nil)))
    (:conflict-node (if (= (the fixnum entry-key)
                           hash)
                        (conflict-node-lookup entry-value sought-key test-function not-found)
                        (values not-found nil)))
    (:hash-node (let* ((logical-index (extract-hash-part-for-shift shift hash)))
                  (if (bitmap-contains-p (the bitmap entry-key)
                                         logical-index)
                      (hash-node-lookup entry-value
                                        (the bitmap entry-key)
                                        sought-key
                                        hash
                                        shift
                                        logical-index
                                        test-function
                                        not-found)
                      (values not-found nil))))))

(declaim (ftype (function (dict t &optional t) (values t boolean))
                get))
(defun get (dict key &optional not-found)
  "Get the value associated with KEY in DICT, or NOT-FOUND if the KEY is not present.

Like `gethash', returns (values VALUE PRESENTP). If DICT contains a mapping for KEY, returns the associated
value as VALUE, and T as PRESENTP. If DICT does not contain a mapping for KEY, returns (values NOT-FOUND
nil)."
  (with-accessors ((hash-function %dict-hash-function)
                   (test-function %dict-test-function)
                   (child-type %dict-child-type)
                   (body-key %dict-key)
                   (body-value %dict-value))
      dict
    (child-lookup child-type
                  body-key
                  body-value
                  key
                  (funcall hash-function key)
                  0
                  test-function
                  not-found)))

;;; INSERT and helpers

;; all of the INSERT helpers which construct nodes will return (values KEY ENTRY CHILD-TYPE
;; NUM-ADDED-ELEMENTS), where the KEY is a thing that goes in the key-index of its parent, and the VALUE is a
;; thing that goes in the value-index of its parent.

(declaim (ftype (function (hash-node-logical-index)
                          (values bitmap &optional))
                bit-from-index)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline bit-from-index))
(defun bit-from-index (index)
  (ash 1 index))

(declaim (ftype (function (bitmap hash-node-logical-index)
                          (values bitmap &optional))
                set-bit)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline set-bit))
(defun set-bit (bitmap index)
  (logior bitmap (bit-from-index index)))

(declaim (ftype (function (bitmap hash-node-logical-index)
                          (values bitmap &optional))
                unset-bit)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline unset-bit))
(defun unset-bit (bitmap index)
  (logandc2 bitmap (bit-from-index index)))

(declaim (ftype (function (&rest hash-node-logical-index) (values bitmap &optional))
                bitmap-from-indices)
         (inline bitmap-from-indices))
;; TODO: determine if inlines of this function generate good machine code, and if not, optimize with a
;; compiler-macro.
(defun bitmap-from-indices (&rest indices)
  (declare (dynamic-extent indices))
  (reduce #'set-bit
          indices
          :initial-value 0))

(declaim (ftype (function (array-length) (values array-length &optional))
                logical-count-to-paired-length)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline logical-count-to-paired-length))
(defun logical-count-to-paired-length (logical-count)
  (* logical-count 2))

(declaim (ftype (function (t t child-type hash-node-logical-index
                           t t child-type hash-node-logical-index
                           bit)
                          (values bitmap hash-node (eql :hash-node) bit &optional))
                make-two-entry-hash-node))
(defun make-two-entry-hash-node (left-key left-value left-child-type left-idx
                                 right-key right-value right-child-type right-idx
                                 num-added)
  (let* ((child-is-conflict-p 0)
         (child-is-entry-p 0))
    (declare (bitmap child-is-conflict-p child-is-entry-p))
    (flet ((set-child-type-bits (child-type logical-index)
             (case child-type
               (:entry (setf child-is-entry-p
                             (set-bit child-is-entry-p
                                      logical-index)))
               (:conflict-node (setf child-is-conflict-p
                                     (set-bit child-is-conflict-p
                                              logical-index))))))
      (set-child-type-bits left-child-type left-idx)
      (set-child-type-bits right-child-type right-idx))
    (values (bitmap-from-indices left-idx right-idx)

            (let* ((initial-contents (if (< left-idx right-idx)
                                         (vector left-key left-value right-key right-value)
                                         (vector right-key right-value left-key left-value))))
              (declare (dynamic-extent initial-contents))
              (with-vector-generator (gen-initial-contents initial-contents)
                (%make-hash-node :child-is-entry-p child-is-entry-p
                                 :child-is-conflict-p child-is-conflict-p
                                 :length (logical-count-to-paired-length 2)
                                 :initial-contents gen-initial-contents)))

            :hash-node
            num-added)))

(declaim (ftype (function (t t child-type hash-node-logical-index t)
                          (values bitmap hash-node (eql :hash-node) t &optional))
                make-one-entry-hash-node))
(defun make-one-entry-hash-node (key value child-type logical-index additional-return-value
                                 &aux (bitmap (bitmap-from-indices logical-index)))
  (values bitmap

          (let* ((initial-contents (vector key value)))
            (declare (dynamic-extent initial-contents))
            (with-vector-generator (gen-initial-contents initial-contents)
              (%make-hash-node :child-is-entry-p (if (eq child-type :entry)
                                                     bitmap
                                                     0)
                               :child-is-conflict-p (if (eq child-type :conflict-node)
                                                        bitmap
                                                        0)
                               :length (logical-count-to-paired-length 1)
                               :initial-contents gen-initial-contents)))

          :hash-node

          additional-return-value))

(declaim (ftype (function (fixnum array-length bit &rest t)
                          (values fixnum conflict-node (eql :conflict-node) bit &optional))
                make-conflict-node))
(defun make-conflict-node (hash logical-count num-added &rest keys-and-values)
  (declare (dynamic-extent keys-and-values))
  (values
   hash

   (with-list-generator (gen-initial-contents keys-and-values)
     (%make-conflict-node :length (logical-count-to-paired-length logical-count)
                          :initial-contents gen-initial-contents))

   :conflict-node

   num-added))

(declaim (ftype (function (t t fixnum child-type
                           t t fixnum child-type
                           shift
                           bit)
                          (values bitmap hash-node (eql :hash-node) bit &optional))
                promote-node))
(defun promote-node (left-key left-value left-hash left-child-type
                     right-key right-value right-hash right-child-type
                     shift
                     num-added)
  "Combine the LEFT-NODE and RIGHT-NODE into a new `hash-node', which should be SHIFT steps deep into the trie.

LEFT-HASH is the hash of the entries in the LEFT-NODE.

RIGHT-HASH is the hash of the entries in the RIGHT-NODE.

Precondition: (/= LEFT-HASH RIGHT-HASH), or else we would construct a unified `conflict-node' instead of a
              `hash-node'."
  (let* ((left-index (extract-hash-part-for-shift shift left-hash))
         (right-index (extract-hash-part-for-shift shift right-hash)))
    (if (= left-index right-index)
        (multiple-value-bind (sub-bitmap sub-node hash-node num-added)
            (promote-node left-key left-value left-hash left-child-type
                          right-key right-value right-hash right-child-type
                          (1+ shift)
                          num-added)
          (make-one-entry-hash-node sub-bitmap sub-node hash-node
                                    left-index
                                    num-added))
        (make-two-entry-hash-node left-key left-value left-child-type left-index
                                  right-key right-value right-child-type right-index
                                  num-added))))

(declaim (ftype (function (t t t t fixnum shift test-function hash-function)
                          (values t t child-type bit &optional))
                insert-alongside-entry))
(defun insert-alongside-entry (neighbor-key neighbor-value key value hash shift test-function hash-function
                               &aux (neighbor-hash (funcall hash-function neighbor-key)))
  (cond ((and (= neighbor-hash hash)
              (funcall test-function neighbor-key key))
         (values key value :entry 0))

        ((= neighbor-hash hash)
         (make-conflict-node hash 2 1 neighbor-key neighbor-value key value))

        (:else (promote-node neighbor-key neighbor-value neighbor-hash :entry
                             key value hash :entry
                             shift 1))))

(declaim (ftype (function (conflict-node t test-function)
                          (values (or null array-index) &optional))
                conflict-node-logical-index-of))
(defun conflict-node-logical-index-of (conflict-node key test-function)
  "If CONFLICT-NODE contains a mapping for KEY under TEST-FUNCTION, return the index into the CONFLICT-NODE's entries vector for that mapping."
  (iter (declare (declare-variables))
    (for logical-index below (conflict-node-logical-length conflict-node))
    (when (funcall test-function
                   key
                   (conflict-node-logical-key-ref conflict-node logical-index))
      (return logical-index))))

(declaim (ftype (function (conflict-node fixnum t t array-index)
                          (values fixnum conflict-node (eql :conflict-node) (eql 0) &optional))
                conflict-node-replace-at-logical-index))
(defun conflict-node-replace-at-logical-index (conflict-node hash new-key new-value logical-index)
  (let* ((new-node (%make-conflict-node :length (conflict-node-paired-count conflict-node)))
         (replaced-key-true-index (conflict-node-key-true-index logical-index)))
    (sv-initialize new-node (:start-from +conflict-node-zero+)
      (:subrange conflict-node
       :count (- replaced-key-true-index +conflict-node-zero+)
       :start +conflict-node-zero+)
      new-key
      new-value
      (:subrange conflict-node :start (+ 2 replaced-key-true-index)))
    
    (values hash new-node :conflict-node 0)))

(declaim (ftype (function (fixnum conflict-node t t)
                          (values fixnum conflict-node (eql :conflict-node) (eql 1) &optional))
                add-to-conflict-node))
(defun add-to-conflict-node (hash conflict-node new-key new-value)
  "Add NEW-ENTRY into the entries of CONFLICT-NODE.

Precondition: NEW-ENTRY has the same hash as CONFLICT-NODE, and no existing entry in CONFLICT-NODE has the
              same key as NEW-ENTRY."
  (let* ((new-node (%make-conflict-node :length (logical-count-to-paired-length
                                                 (1+ (conflict-node-logical-length conflict-node))))))

    (sv-initialize new-node (:start-from +conflict-node-zero+)
      (:subrange conflict-node :start +conflict-node-zero+)
      new-key
      new-value)

    (values hash
            new-node
            :conflict-node
            1)))

(declaim (ftype (function (fixnum conflict-node t t fixnum shift test-function)
                          (values t t child-type bit &optional))
                insert-into-conflict-node))
(defun insert-into-conflict-node (conflict-hash conflict-node new-key new-value hash shift test-function)
  "Add a new entry (KEY -> VALUE) to or alongside CONFLICT-NODE.

Depending on whether HASH is the same as the hash in CONFLICT-NODE, this may allocate a new `hash-node' to
contain both the existing CONFLICT-NODE and the new entry."
  (let* ((same-hash-p (= conflict-hash hash))
         (logical-index (when same-hash-p
                          (conflict-node-logical-index-of conflict-node new-key test-function))))
    (cond ((and same-hash-p logical-index)
           ;; If CONFLICT-NODE already contains a mapping for KEY, replace it.
           (conflict-node-replace-at-logical-index conflict-node hash new-key new-value logical-index))

          (same-hash-p
           ;; If the new mapping conflicts with CONFLICT-NODE but is not already present, add it.
           (add-to-conflict-node hash conflict-node new-key new-value))

          (:else
           ;; If the new mapping does not conflict, grow a new `hash-node' with the CONFLICT-NODE and the new
           ;; entry as siblings.
           (promote-node conflict-hash conflict-node conflict-hash :conflict-node
                         new-key new-value hash :entry
                         shift
                         1)))))

(declaim (ftype (function (bitmap hash-node
                           hash-node-logical-index
                           t t child-type
                           t)
                          (values bitmap hash-node (eql :hash-node) t &optional))
                hash-node-replace-at))
(defun hash-node-replace-at (bitmap hash-node
                             logical-index
                             new-key new-value new-type
                             additional-return-value)
  (let* ((new-elt-key-true-index (hash-node-key-true-index bitmap logical-index))
         (new-node (%make-hash-node :child-is-entry-p (if (eq new-type :entry)
                                                          (set-bit (hash-node-child-is-entry-p hash-node)
                                                                   logical-index)
                                                          (unset-bit (hash-node-child-is-entry-p hash-node)
                                                                     logical-index))
                                    :child-is-conflict-p (if (eq new-type :conflict-node)
                                                             (set-bit (hash-node-child-is-conflict-p hash-node)
                                                                      logical-index)
                                                             (unset-bit (hash-node-child-is-conflict-p hash-node)
                                                                        logical-index))
                                    :length (hash-node-paired-count hash-node))))

    (sv-initialize new-node (:start-from +hash-node-zero+)
      (:subrange hash-node
       :count (- new-elt-key-true-index +hash-node-zero+)
       :start +hash-node-zero+)
      new-key
      new-value
      (:subrange hash-node
       :start (+ 2 new-elt-key-true-index)))

    (values bitmap

            new-node

            :hash-node

            additional-return-value)))

(declaim (ftype (function (bitmap hash-node
                                  hash-node-logical-index
                                  t t child-type)
                          (values bitmap hash-node (eql :hash-node) (eql 1) &optional))
                hash-node-insert-at))
(defun hash-node-insert-at (bitmap hash-node
                            logical-index
                            child-key child-value child-type)
  (let* ((new-bitmap (set-bit bitmap
                              logical-index))
         (new-paired-length (logical-count-to-paired-length (1+ (hash-node-logical-count hash-node))))
         (new-elt-key-true-index (hash-node-key-true-index new-bitmap logical-index))
         (new-node (%make-hash-node :child-is-entry-p (if (eq child-type :entry)
                                                          (set-bit (hash-node-child-is-entry-p hash-node)
                                                                   logical-index)
                                                          (hash-node-child-is-entry-p hash-node))
                                    :child-is-conflict-p (if (eq child-type :conflict-node)
                                                             (set-bit (hash-node-child-is-conflict-p hash-node)
                                                                      logical-index)
                                                             (hash-node-child-is-conflict-p hash-node))
                                    :length new-paired-length)))

    (sv-initialize new-node (:start-from +hash-node-zero+)
      (:subrange hash-node
       :count (- new-elt-key-true-index +hash-node-zero+)
       :start +hash-node-zero+)
      child-key
      child-value
      (:subrange hash-node
       :start new-elt-key-true-index))

    (values new-bitmap

            new-node

            :hash-node

            1)))

;; predeclaration for type inference on recursive calls by `insert-into-hash-node'
(declaim (ftype (function (child-type t t t t fixnum shift test-function hash-function)
                          (values t t child-type bit &optional))
                node-insert))

(declaim (ftype (function (bitmap hash-node t t fixnum shift test-function hash-function)
                          (values bitmap hash-node (eql :hash-node) bit &optional))
                insert-into-hash-node))
(defun insert-into-hash-node (bitmap
                              hash-node
                              key
                              value
                              hash
                              shift
                              test-function
                              hash-function)
  "Add a new entry (KEY -> VALUE) as a child of HASH-NODE."
  (let* ((logical-index (extract-hash-part-for-shift shift hash)))
    (if-let ((child-type (hash-node-child-type hash-node bitmap logical-index)))

      ;; If the hash node already has a child there, recurse to insert into the child.
      (multiple-value-bind (child-key child-value)
          (hash-node-logical-ref hash-node bitmap logical-index)
        (multiple-value-bind (new-child-key new-child-val new-child-type num-added)
            (node-insert child-type
                         child-key child-value
                         key value hash
                         (1+ shift) test-function hash-function)
          (hash-node-replace-at bitmap hash-node
                                logical-index
                                new-child-key new-child-val new-child-type
                                num-added)))

      ;; If the hash node doesn't have a child there yet, insert one.
      (hash-node-insert-at bitmap hash-node
                           logical-index
                           key value :entry))))

(defun node-insert (body-type body-key body-value key value hash shift test-function hash-function)
  "Make KEY map to VALUE within NODE.

Returns a new node like NODE, but with the mapping (KEY -> VALUE). If KEY is already associated with a value
in NODE, the old value will be overwritten.

HASH is the result of applying the containing `dict' 's HASH-FUNCTION to KEY.

SHIFT is the depth into the trie of NODE. For a `dict' 's BODY, this will be 0.

TEST-FUNCTION is the containing `dict' 's TEST-FUNCTION, which must satisfy the hash-test-function laws with
the HASH-FUNCTION used to generate HASH."
  (ecase body-type
    ((nil) (values key value :entry 1))
    (:entry (insert-alongside-entry body-key body-value key value hash shift test-function hash-function))
    (:conflict-node (insert-into-conflict-node body-key body-value key value hash shift test-function))
    (:hash-node
     (insert-into-hash-node body-key body-value key value hash shift test-function hash-function))))

(declaim (ftype (function (dict t t) (values dict &optional))
                insert))
(defun insert (dict key value)
  "Associate a KEY with a VALUE.

Returns a new `dict' like DICT, with KEY mapping to VALUE. If DICT already contains a mapping for KEY, the old
mapping is replaced."
  (with-accessors ((hash-function %dict-hash-function)
                   (test-function %dict-test-function)
                   (body-key %dict-key)
                   (body-value %dict-value)
                   (body-type %dict-child-type)
                   (size %dict-size))
      dict
    (let* ((hash (funcall hash-function key)))
      (multiple-value-bind (new-body-key new-body-value new-type added-count)
          (node-insert body-type body-key body-value key value hash 0 test-function hash-function)
        (%make-dict :size (+ size added-count)
                    :hash-function hash-function
                    :test-function test-function
                    :key new-body-key
                    :value new-body-value
                    :child-type new-type)))))

;;; TODO: left off converting to new node repr here

;;; REMOVE and helpers

(declaim (ftype (function (fixnum conflict-node array-index)
                          (values fixnum conflict-node (eql :conflict-node) (eql t) &optional))
                conflict-node-remove-at-logical-index))
(defun conflict-node-remove-at-logical-index (conflict-hash conflict-node logical-index
                                              &aux )
  (let* ((key-true-index (conflict-node-key-true-index logical-index))
         (new-node (%make-conflict-node :length (logical-count-to-paired-length
                                                   (1- (conflict-node-logical-length conflict-node))))))
    (sv-initialize new-node (:start-from +conflict-node-zero+)
      (:subrange conflict-node
       :count (- key-true-index +conflict-node-zero+)
       :start +conflict-node-zero+)
      (:subrange conflict-node
       :start (+ 2 key-true-index)))
    
    (values conflict-hash

            new-node

            :conflict-node

            t)))

(declaim (ftype (function (fixnum conflict-node t test-function)
                          (values t t child-type boolean &optional))
                conflict-node-remove))
(defun conflict-node-remove (conflict-hash conflict-node key test-function)
  "Remove the entry for KEY from CONFLICT-NODE, if any.

If CONFLICT-NODE does not contain an entry for KEY, the returned node will be `eq' to CONFLICT-NODE.

Precondition: KEY has the same hash as the CONFLICT-NODE."

  (if-let ((logical-index (conflict-node-logical-index-of conflict-node key test-function)))
    ;; If present, ...
    (if (= 2 (conflict-node-logical-length conflict-node))
        ;; If only one remaining entry, promote it so we don't have a one-entry `conflict-node' sitting
        ;; around.
        (multiple-value-bind (other-key other-value) (conflict-node-logical-ref conflict-node
                                                                                (if (= 0 logical-index)
                                                                                    1
                                                                                    0))
          (values other-key other-value :entry t))

        ;; Otherwise, copy the conflict-node with the offending entry removed.
        (conflict-node-remove-at-logical-index conflict-hash conflict-node logical-index))

    ;; If not present, return the conflict-node unchanged.
    (values conflict-hash conflict-node :conflict-node nil)))

(declaim (ftype (function (bitmap hash-node hash-node-logical-index)
                          (values bitmap hash-node (eql :hash-node) (eql t) &optional))
                hash-node-remove-at-logical-index))
(defun hash-node-remove-at-logical-index (bitmap hash-node logical-index-to-remove)
  "Remove from HASH-NODE the child named by INDEX-TO-REMOVE and TRUE-INDEX-TO-REMOVE.

Precondition: HASH-NODE must `hash-node-contains-p' INDEX-TO-REMOVE, and TRUE-INDEX-TO-REMOVE must be the
              `hash-node-true-index' of INDEX-TO-REMOVE."
  (let* ((removed-bitmap (unset-bit bitmap
                                    logical-index-to-remove))
         (removed-child-is-entry-p (unset-bit (hash-node-child-is-entry-p hash-node)
                                              logical-index-to-remove))
         (removed-child-is-conflict-p (unset-bit (hash-node-child-is-conflict-p hash-node)
                                                 logical-index-to-remove))
         (removed-key-true-index (hash-node-key-true-index bitmap logical-index-to-remove))
         (new-node (%make-hash-node :child-is-entry-p removed-child-is-entry-p
                                    :child-is-conflict-p removed-child-is-conflict-p
                                    :length (logical-count-to-paired-length (1- (hash-node-logical-count hash-node))))))

    (sv-initialize new-node (:start-from +hash-node-zero+)
      (:subrange hash-node
       :count (- removed-key-true-index +hash-node-zero+)
       :start +hash-node-zero+)
      (:subrange hash-node
       :start (+ 2 removed-key-true-index)))

    (values removed-bitmap new-node :hash-node t)))

(declaim (ftype (function (bitmap hash-node-logical-index)
                          (values hash-node-logical-index &optional))
                bitmap-other-logical-index))
(defun bitmap-other-logical-index (bitmap logical-index)
  (1- (integer-length (unset-bit bitmap logical-index))))

(declaim (ftype (function (bitmap hash-node hash-node-logical-index)
                          (values t t child-type (eql t) &optional))
                hash-node-maybe-promote-other-child))
(defun hash-node-maybe-promote-other-child (bitmap hash-node logical-index-to-discard)
  (let* ((logical-index-to-keep (bitmap-other-logical-index bitmap logical-index-to-discard))
         (child-type (hash-node-child-type hash-node bitmap logical-index-to-keep)))
    (multiple-value-bind (child-key child-value) (hash-node-logical-ref hash-node bitmap logical-index-to-keep)
      (if (eq child-type :hash-node)
          ;; Cannot promote, because the child is a hash-node with a greater shift than us.
          (make-one-entry-hash-node child-key child-value child-type logical-index-to-keep t)

          ;; Can promote, because the child is an entry or a conflict-node
          (values child-key child-value child-type t)))))

(declaim (ftype (function (bitmap hash-node
                           t fixnum hash-node-logical-index
                           shift test-function)
                          (values t t child-type boolean &optional))
                hash-node-remove))
(defun hash-node-remove (bitmap hash-node
                         key hash logical-index
                         shift test-function)
  (flet ((return-unchanged ()
           (values bitmap hash-node :hash-node nil)))
    (if-let ((child-type (hash-node-child-type hash-node bitmap logical-index)))
      (multiple-value-bind (child-key child-value) (hash-node-logical-ref hash-node bitmap logical-index)
        (multiple-value-bind (new-child-key new-child-value new-child-type removedp)
            (node-remove child-type child-key child-value
                         key hash
                         (1+ shift) test-function)
          (cond ((not removedp)
                 ;; If we didn't remove anything, return ourselves.
                 (return-unchanged))

                ((and (null new-child-type)
                      (= 1 (hash-node-logical-count hash-node)))
                 ;; If we removed our only child, return nothing.
                 (values nil nil nil t))

                ((and (null new-child-type)
                      (= 2 (hash-node-logical-count hash-node)))
                 ;; If we're removing one of two children, try to reduce nesting.
                 (hash-node-maybe-promote-other-child bitmap hash-node logical-index))

                ((null new-child-type)
                 ;; If we removed an entire child, the resulting hash node will have one fewer entries than
                 ;; HASH-NODE.
                 (hash-node-remove-at-logical-index bitmap hash-node logical-index))

                (:else
                 ;; If we removed from a child that still has other entries, splice the new child back in.
                 (hash-node-replace-at bitmap hash-node
                                       logical-index
                                       new-child-key new-child-value new-child-type
                                       t)))))

      (return-unchanged))))

(declaim (ftype (function (child-type t t t fixnum shift test-function)
                          (values t t child-type boolean &optional))
                node-remove))
(defun node-remove (body-type body-key body-value key hash shift test-function)
  "Make KEY unmapped within the node (BODY-KEY BODY-VALUE).

Returns (values NEW-BODY-KEY NEW-BODY-VALUE NEW-BODY-TYPE REMOVEDP).

If KEY is already unmapped within the body, REMOVEDP will be nil, and NEW-BODY-[key|value|type] will be eq to
BODY-[key|value|type].

HASH is the result of applying the containing `dict' 's HASH-FUNCTION to KEY.

SHIFT is the depth into the trie of the body. For a `dict' 's direct body, this will be 0.

TEST-FUNCTION is the containing `dict' 's TEST-FUNCTION, which must satisfy the hash-test-function laws with
the HASH-FUNCTION used to generate HASH."
  (flet ((not-found ()
           (values body-key body-value body-type nil)))
    (ecase body-type
      ((nil) (not-found))

      (:entry (if (funcall test-function body-key key)
                  (values nil nil nil t)
                  (not-found)))

      (:conflict-node
       (if (= hash (the fixnum body-key))
           (conflict-node-remove body-key body-value key test-function)
           (not-found)))

      (:hash-node (let* ((logical-index (extract-hash-part-for-shift shift hash)))
                    (if (bitmap-contains-p (the bitmap body-key)
                                           logical-index)
                        (hash-node-remove body-key body-value
                                          key hash logical-index
                                          shift test-function)
                        (not-found)))))))

(declaim (ftype (function (dict t) (values dict &optional))
                remove))
(defun remove (dict key)
  "Make KEY unmapped in DICT.

Return a new `dict' like DICT, but where KEY is not associated with any value.

If DICT does not contain a mapping for KEY, the returned `dict' will be `eq' to DICT."
  (with-accessors ((hash-function %dict-hash-function)
                   (test-function %dict-test-function)
                   (body-key %dict-key)
                   (body-value %dict-value)
                   (body-type %dict-child-type)
                   (size %dict-size))
      dict
    (if (null body-type)
        dict
        (let* ((hash (funcall hash-function key)))
          (multiple-value-bind (new-key new-value new-child-type removed-p)
              (node-remove body-type body-key body-value key hash 0 test-function)
            (if removed-p
                (%make-dict :size (1- size)
                            :hash-function hash-function
                            :test-function test-function
                            :key new-key
                            :value new-value
                            :child-type new-child-type)
                dict))))))

;; ;;; finding appropriate hash functions for a given test function

(declaim (dict *test-hash-functions*))
(defparameter *test-hash-functions*
  (%make-dict :size 0
              :key nil
              :value nil
              :child-type nil
              :test-function #'eq
              :hash-function (lambda (fun)
                               (declare (symbol fun))
                               ;; `sxhash' on symbols is like `eq-hash'
                               (sxhash fun)))
  "Maps symbols which name test functions to function objects which are `hash-function's.")

(deftype function-designator ()
  '(or (and symbol (not (or keyword boolean)))
    function))

(declaim (ftype (function (function-designator) (values function &optional))
                coerce-to-function))
(defun coerce-to-function (function-designator)
  (etypecase function-designator
    ((and symbol (not keyword)) (symbol-function function-designator))
    (function function-designator)))

(declaim (ftype (function ((and symbol (not keyword) (not boolean))
                           function-designator)
                          (values &optional))
                register-test-hash-function))
(defun register-test-hash-function (test-function hash-function)
  ;; TODO: Make this an atomic-swap when available? Does anyone compile CL source files in parallel?
  (setf *test-hash-functions*
        (insert *test-hash-functions*
                test-function
                (coerce-to-function hash-function)))
  (values))

(defmacro define-test-hash-function (test-function hash-function)
  (check-type test-function (and function-designator symbol)
              "a symbol which names a test function")
  (check-type hash-function (or (and function-designator symbol)
                                (cons (member lambda function)))
              "a symbol which names a hash function, or a LAMBDA or FUNCTION expression")
  (flet ((maybe-quote (thing)
           (if (symbolp thing)
               `',thing
               thing)))
    `(register-test-hash-function ',test-function ,(maybe-quote hash-function))))

(define-test-hash-function equal sxhash)

(define-test-hash-function == hash)

;; TODO: Figure out if it's possible to extract (EQ|EQL|EQUALP)-HASH from implementations' hash-table impls.
;;       SBCL's `sb-impl::eq-hash' is probably impossible to use, because a moving gc will change objects'
;;       hashes. The SBCL impl of hash tables seem to hack around this by pinning objects. (See
;;       sbcl/src/code/target-hash-table.lisp#L1678, in the definition of DEFINE-HT-SETTER.)

(define-condition no-hash-function-for-test (error)
  ((%test-function :type t
                   :initarg :test-function
                   :reader no-hash-function-for-test-function)
   (%known-test-hash-functions :type dict
                               :initarg :known-test-hash-functions
                               :reader no-hash-function-for-test-known-test-hash-functions))
  (:report (lambda (c s)
             ;; TODO: print the KNOWN-TEST-HASH-FUNCTIONS, once we have a way to print dicts
             (format s "Don't know how to find an appropriate :HASH-FUNCTION for the :TEST-FUNCTION ~s.

IMMUTABLE/DICT can only automatically deduce :HASH-FUNCTIONs when the :TEST-FUNCTION is a symbol, and then only for a small number of known :TEST-FUNCTIONs."
                     (no-hash-function-for-test-function c)))))

(declaim (ftype (function ((and function-designator symbol)) (values hash-function &optional))
                test-hash-function))
(defun test-hash-function (test-function)
  (multiple-value-bind (hash-function presentp)
      (get *test-hash-functions* test-function)
    (unless presentp
      (error 'no-hash-function-for-test
             :test-function test-function
             :known-test-hash-functions *test-hash-functions*))
    hash-function))

;;; EMPTY constructor

(declaim (ftype (function (&key (:test-function (or (and symbol (not keyword) (not boolean))
                                                    test-function))
                                (:hash-function (or null
                                                    (and symbol (not keyword) (not boolean))
                                                    hash-function)))
                          (values dict &optional))
                empty))
(defun empty (&key (test-function '==)
                (hash-function nil))
  (let* ((hash-function (coerce-to-function (cond (hash-function
                                                   (coerce-to-function hash-function))
                                                  ((symbolp test-function)
                                                   (test-hash-function test-function))
                                                  (:else
                                                   (error 'no-hash-function-for-test
                                                          :test-function test-function
                                                          :known-test-hash-functions *test-hash-functions*)))))
         (test-function (coerce-to-function test-function)))
    (%make-dict :size 0
                :key nil
                :value nil
                :child-type nil
                :hash-function hash-function
                :test-function test-function)))
