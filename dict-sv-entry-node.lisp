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
(uiop:define-package :immutable/dict-sv-entry-node
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
(in-package :immutable/dict-sv-entry-node)

#+immutable-dict-debug
(declaim (optimize (speed 1) (safety 3) (space 1) (debug 3) (compilation-speed 0)))
#-immutable-dict-debug
(declaim (optimize (speed 3) (safety 0) (space 1) (debug 1) (compilation-speed 0)))

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
  `(integer 0 (,+branch-rate+)))

;;; struct definitions for node variants

(declaim (inline %make-entry-node entry-node-key entry-node-value))

(defstruct (entry-node
            (:constructor %make-entry-node))
  (key (error "Supply :KEY to %MAKE-ENTRY-NODE"))
  (value (error "Supply :VALUE to %MAKE-ENTRY-NODE")))

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
;; The terminology for HASH-NODE indices is a little wonky, because there are three different kinds of indices:
;; - Logical indices, which are in the range 0 -- 32, are extracted from hashes. These are sparse, and are
;;   mapped to dense counted indices by the hash-node's bitmap. Each corresponds to a subnode, which may be:
;;   - An `entry-node', a leaf containing a key/value mapping.
;;   - A `conflict-node', containing multiple `entry-node's with the same hash.
;;   - A child `hash-node', which will be searched with an increased `shift'.
;; - Counted indices, which are in the range 0 -- 32, are dense. Transforming a logical index into a counted
;;   index involves inspecting the hash-node's bitmap and counting the number of one bits below the logical
;;   index. This is done by `hash-node-logical-index-to-counted-index'.
;; - True indices are counted indices added to some automatically-computed offset to skip the hash-node's
;;   named slots. counted indices are transformed to true indices by `hash-node-counted-index-to-true-index'.

(define-vector-struct hash-node
    (:max-length #.(* +branch-rate+ 2)
     :length hash-node-count
     :ref hash-node-counted-ref
     :logical-index-to-true-index hash-node-counted-index-to-true-index
     :logical-length-to-true-length hash-node-counted-length-to-true-length
     :constructor %make-hash-node
     :named t)
  ;; The CHILD-IS-ENTRY-P and CHILD-IS-CONFLICT-P bitmaps map counted-indices to whether the associated child
  ;; is a key/value pair or a hash/conflict-node pair. These are mutually exclusive. If both bits are 0, the
  ;; associated child is either not present, or is a logical-index-bitmap/hash-node pair.
  (child-present-p :type bitmap
                   :initform (error "Supply :CHILD-PRESENT-P to %MAKE-HASH-NODE")))

;;; CONFLICT-NODE
;;
;; A leaf-ish node in a `dict' for distinct elements with the same hash.
;;
;; The ENTRIES will be a vector of `entry-node's, all of which have keys with the sameq hash, but which are
;; not equal under the TEST-FUNCTION. Lookup in a `conflict-node' is a linear search of its ENTRIES.
;;
;; A `conflict-node' will always contain at least two entries.
;;
;; CONFLICT-NODE indices are not quite as wonky as those for hash-nodes, but still have two levels:
;; - Logical indices start from 0. Each logical index corresponds to an `entry-node'.
;; - True indices are logical indices added to some automatically-computed offset to skip the hash-node's named
;;   slots. Logical indices are transformed to true indices by `conflict-node-logical-index-to-true-index'.
(define-vector-struct conflict-node
    (:length conflict-node-count
     :ref conflict-node-ref
     :logical-index-to-true-index conflict-node-logical-index-to-true-index
     :logical-length-to-true-length conflict-node-logical-length-to-true-length
     :constructor %make-conflict-node
     :named t)
  (conflict-hash :type fixnum
                 :initform (error "Supply :CONFLICT-HASH to %MAKE-CONFLICT-NODE")))

(deftype node ()
  '(or hash-node conflict-node entry-node))

(deftype node-type ()
  '(member hash-node conflict-node entry-node))

(declaim (ftype (function (node) (values node-type &optional))
                node-type)
         (inline node-type))
(defun node-type (node)
  (if (entry-node-p node)
      'entry-node
      (vector-struct-name node)))

;;; The actual DEFSTRUCT!

(declaim (inline %make-dict %dict-size %dict-hash-function %dict-test-function %dict-body))

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
  (body (error "Supply :BODY to %MAKE-DICT")
   :type (or null node)))

;;; accessors

(declaim (ftype (function (dict) (values size &optional))
                size)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline size))
(defun size (dict)
  (%dict-size dict))

;;; lookup with GET

(declaim (ftype (function (conflict-node array-index) (values entry-node &optional))
                conflict-node-true-ref)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline conflict-node-true-ref))
(defun conflict-node-true-ref (conflict-node true-index)
  (svref conflict-node true-index))

(declaim (ftype (function (entry-node conflict-node array-index) (values t &optional))
                (setf conflict-node-true-ref))
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline (setf conflict-node-true-ref)))
(defun (setf conflict-node-true-ref) (new-entry conflict-node true-index)
  (setf (svref conflict-node true-index) new-entry))

(declaim (ftype (function (bitmap hash-node-logical-index) (values boolean &optional))
                bitmap-contains-p)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline bitmap-contains-p))
(defun bitmap-contains-p (bitmap logical-index)
  (logbitp logical-index bitmap))

(declaim (ftype (function (hash-node hash-node-logical-index) (values boolean &optional))
                hash-node-contains-p)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline bitmap-contains-p))
(defun hash-node-contains-p (hash-node logical-index)
  (bitmap-contains-p (hash-node-child-present-p hash-node) logical-index))

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

(declaim (ftype (function (hash-node hash-node-logical-index) (values array-index &optional))
                hash-node-logical-index-to-counted-index)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline bitmap-logical-index-to-counted-index))
(defun hash-node-logical-index-to-counted-index (hash-node logical-index)
  (bitmap-logical-index-to-counted-index (hash-node-child-present-p hash-node) logical-index))

(declaim (ftype (function (hash-node hash-node-logical-index) (values node &optional))
                hash-node-logical-ref)
         ;; Inlining may allow more efficient multiple-values usage, or for the compiler to eliminate unused
         ;; return values if we only need one of them.
         (inline hash-node-logical-ref))
(defun hash-node-logical-ref (hash-node logical-index)
  "Look up a child of HASH-NODE by its LOGICAL-INDEX.
Precondition: the HASH-NODE must `hash-node-contains-p' the INDEX."
  (let* ((counted-index (hash-node-logical-index-to-counted-index hash-node logical-index)))
    (hash-node-counted-ref hash-node counted-index)))

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
  (iter (declare (declare-variables))
    (for index below (conflict-node-count conflict-node))
    (for entry = (conflict-node-ref conflict-node index))
    (when (funcall test-function key (entry-node-key entry))
      (return (values (entry-node-value entry) t)))
    (finally (return (values not-found nil)))))

;; Predeclarations for better type inference in recursive calls by HASH-NODE-LOOKUP
(declaim (ftype (function (node t fixnum shift test-function t)
                          (values t boolean &optional))
                node-lookup))

(declaim (ftype (function (hash-node t fixnum shift test-function t)
                          (values t boolean &optional))
                hash-node-lookup))
(defun hash-node-lookup (hash-node key hash shift test-function not-found)
  "Get the value associated with KEY in NODE.
HASH is the result of applying the containing `dict' 's HASH-FUNCTION to KEY.
SHIFT is the depth into the trie of NODE. For a `dict' 's BODY, this will be 0.
TEST-FUNCTION is the containing `dict' 's TEST-FUNCTION, which must satisfy the hash-test-function laws with
the HASH-FUNCTION used to generate HASH.
NOT-FOUND is an arbitrary value to be returned as primary value if NODE does not contain a mapping for KEY."
  (let* ((logical-index (extract-hash-part-for-shift shift hash)))
    (if (hash-node-contains-p hash-node logical-index)
        (node-lookup (hash-node-logical-ref hash-node logical-index)
                     key
                     hash
                     (1+ shift)
                     test-function
                     not-found)
        (values not-found nil))))

(defun node-lookup (node sought-key hash shift test-function not-found)
  (ecase (node-type node)
    (entry-node (if (funcall test-function (entry-node-key node) sought-key)
                    (values (entry-node-value node) t)
                    (values not-found nil)))
    (conflict-node (if (= (conflict-node-conflict-hash node)
                          hash)
                       (conflict-node-lookup node sought-key test-function not-found)
                       (values not-found nil)))
    ;; FIXME: need a way to do TYPEP dispatch on nodes, because CONFLICT-NODE and HASH-NODE are both aliases
    ;; for SIMPLE-VECTOR.
    (hash-node (hash-node-lookup node sought-key hash shift test-function not-found))))

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
                   (body %dict-body))
      dict
    (if body
        (node-lookup body
                     key
                     (funcall hash-function key)
                     0
                     test-function
                     not-found)
        (values not-found nil))))

;;;; TODO: left off converting here

;;; INSERT and helpers

;; all of the INSERT helpers which construct nodes will return (values NEW-NODE NUM-ADDED-ELEMENTS), where
;; NUM-ADDED-ELEMENTS is a bit; 0 if an entry was replaced, 1 if the new node is larger than the original.

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

(declaim (ftype (function (node hash-node-logical-index
                           node hash-node-logical-index)
                          (values hash-node &optional))
                make-two-entry-hash-node))
(defun make-two-entry-hash-node (left left-idx
                                 right right-idx)
  (let* ((bitmap (bitmap-from-indices left-idx right-idx))
         (initial-contents (if (< left-idx right-idx)
                               (vector left right)
                               (vector right left))))
    (declare (dynamic-extent initial-contents))
    (with-vector-generator (gen-initial-contents initial-contents)
      (%make-hash-node :child-present-p bitmap
                       :length 2
                       :initial-contents gen-initial-contents))))

(declaim (ftype (function (node hash-node-logical-index)
                          (values hash-node &optional))
                make-one-entry-hash-node))
(defun make-one-entry-hash-node (node logical-index)
  (%make-hash-node :child-present-p (bitmap-from-indices logical-index)
                   :length 1
                   :initial-element node))

(declaim (ftype (function (fixnum entry-node entry-node)
                          (values conflict-node &optional))
                make-two-entry-conflict-node))
(defun make-two-entry-conflict-node (hash left right)
  (let* ((initial-contents (vector left right)))
    (declare (dynamic-extent initial-contents))
    (with-vector-generator (gen-initial-contents initial-contents)
      (%make-conflict-node :conflict-hash hash
                           :length 2
                           :initial-contents gen-initial-contents))))

(declaim (ftype (function ((or conflict-node entry-node) fixnum
                           (or conflict-node entry-node) fixnum
                           shift)
                          (values hash-node &optional))
                promote-node))
(defun promote-node (left-node left-hash
                     right-node right-hash
                     shift)
  "Combine the LEFT-NODE and RIGHT-NODE into a new `hash-node', which should be SHIFT steps deep into the trie.
LEFT-HASH is the hash of the entries in the LEFT-NODE.
RIGHT-HASH is the hash of the entries in the RIGHT-NODE.
Precondition: (/= LEFT-HASH RIGHT-HASH), or else we would construct a unified `conflict-node' instead of a
              `hash-node'."
  (let* ((left-index (extract-hash-part-for-shift shift left-hash))
         (right-index (extract-hash-part-for-shift shift right-hash)))
    (if (= left-index right-index)
        (let* ((sub-node (promote-node left-node left-hash
                                       right-node right-hash
                                       (1+ shift))))
          (make-one-entry-hash-node sub-node left-index))
        (make-two-entry-hash-node left-node left-index
                                  right-node right-index))))

(declaim (ftype (function (entry-node entry-node fixnum shift test-function hash-function)
                          (values node bit &optional))
                insert-alongside-entry))
(defun insert-alongside-entry (neighbor new-entry hash shift test-function hash-function
                               &aux (neighbor-key (entry-node-key neighbor))
                                 (neighbor-hash (funcall hash-function neighbor-key))
                                 (same-hash-p (= neighbor-hash hash)))
  (cond ((and same-hash-p
              (funcall test-function neighbor-key (entry-node-key new-entry)))
         (values new-entry
                 0))

        (same-hash-p
         (values (make-two-entry-conflict-node hash neighbor new-entry)
                 1))

        (:else (values (promote-node neighbor neighbor-hash
                                     new-entry hash
                                     shift)
                       1))))

(declaim (ftype (function (conflict-node t test-function)
                          (values (or null array-index) &optional))
                conflict-node-logical-index-of))
(defun conflict-node-logical-index-of (conflict-node key test-function)
  "If CONFLICT-NODE contains a mapping for KEY under TEST-FUNCTION, return the LOGICAL-INDEX into the CONFLICT-NODE for that mapping."
  (iter (declare (declare-variables))
    (for logical-index below (conflict-node-count conflict-node))
    (for entry = (conflict-node-ref conflict-node logical-index))
    (for present-key = (entry-node-key entry))
    (when (funcall test-function
                   key
                   present-key)
      (return logical-index))))

(declaim (ftype (function (conflict-node array-index entry-node)
                          (values conflict-node &optional))
                conflict-node-replace-at-logical-index))
(defun conflict-node-replace-at-logical-index (conflict-node logical-index new-entry)
  (let* ((true-index (conflict-node-logical-index-to-true-index logical-index))
         (zero (conflict-node-logical-index-to-true-index 0))
         (new-node (%make-conflict-node :conflict-hash (conflict-node-conflict-hash conflict-node)
                                        :length (conflict-node-count conflict-node))))
    (sv-copy-subrange new-node conflict-node
                      :count (- true-index zero)
                      :target-start zero
                      :source-start zero)
    (setf (svref new-node true-index)
          new-entry)
    (sv-copy-subrange new-node conflict-node
                      :target-start (1+ true-index)
                      :source-start (1+ true-index))
    new-node))

(declaim (ftype (function (conflict-node entry-node)
                          (values conflict-node &optional))
                add-to-conflict-node))
(defun add-to-conflict-node (conflict-node new-entry)
  "Add NEW-ENTRY into the entries of CONFLICT-NODE.
Precondition: the key of NEW-ENTRY has the same hash as CONFLICT-NODE, and no existing entry in CONFLICT-NODE
              has the same key as NEW-ENTRY."
  (let* ((new-node (%make-conflict-node :conflict-hash (conflict-node-conflict-hash conflict-node)
                                        :length (1+ (conflict-node-count conflict-node))))
         (zero (conflict-node-logical-index-to-true-index 0)))
    (sv-copy-subrange new-node conflict-node
                      :target-start zero
                      :source-start zero)
    (setf (svref new-node (conflict-node-logical-index-to-true-index (conflict-node-count conflict-node)))
          new-entry)
    new-node))

(declaim (ftype (function (conflict-node entry-node fixnum shift test-function)
                          (values node bit &optional))
                insert-into-conflict-node))
(defun insert-into-conflict-node (conflict-node new-entry hash shift test-function)
  "Add the NEW-ENTRY to or alongside CONFLICT-NODE.
Depending on whether HASH is the same as the hash in CONFLICT-NODE, this may allocate a new `hash-node' to
contain both the existing CONFLICT-NODE and the new entry."
  (let* ((same-hash-p (= (conflict-node-conflict-hash conflict-node) hash))
         (logical-index (when same-hash-p
                          (conflict-node-logical-index-of conflict-node (entry-node-key new-entry) test-function))))
    (cond ((and same-hash-p logical-index)
           ;; If CONFLICT-NODE already contains a mapping for KEY, replace it.
           (values (conflict-node-replace-at-logical-index conflict-node logical-index new-entry)
                   0))

          (same-hash-p
           ;; If the new mapping conflicts with CONFLICT-NODE but is not already present, add it.
           (values (add-to-conflict-node conflict-node new-entry)
                   1))

          (:else
           ;; If the new mapping does not conflict, grow a new `hash-node' with the CONFLICT-NODE and the new
           ;; entry as siblings.
           (values (promote-node conflict-node (conflict-node-conflict-hash conflict-node)
                                 new-entry hash
                                 shift)
                   1)))))

(declaim (ftype (function (hash-node
                           array-index
                           node)
                          (values hash-node &optional))
                hash-node-replace-at-counted-index))
(defun hash-node-replace-at-counted-index (hash-node
                                           counted-index
                                           new-child)
  (let* ((new-child-true-index (hash-node-counted-index-to-true-index counted-index))
         (new-node (%make-hash-node :child-present-p (hash-node-child-present-p hash-node)
                                    :length (hash-node-count hash-node)))
         (zero (hash-node-counted-index-to-true-index 0)))
    (sv-copy-subrange new-node hash-node :count (- new-child-true-index 0)
                                         :target-start zero
                                         :source-start zero)
    (setf (svref new-node new-child-true-index)
          new-child)
    (sv-copy-subrange new-node hash-node :target-start (1+ new-child-true-index)
                                         :source-start (1+ new-child-true-index))
    new-node))

(declaim (ftype (function (hash-node
                           hash-node-logical-index
                           entry-node)
                          (values hash-node &optional))
                hash-node-insert-at-logical-index))
(defun hash-node-insert-at-logical-index (hash-node
                                          logical-index
                                          new-child)
  (let* ((old-bitmap (hash-node-child-present-p hash-node))
         (new-bitmap (set-bit old-bitmap
                              logical-index))
         (new-count (1+ (hash-node-count hash-node)))
         (new-elt-counted-index (bitmap-logical-index-to-counted-index new-bitmap logical-index))
         (new-elt-true-index (hash-node-counted-index-to-true-index new-elt-counted-index))
         (zero (hash-node-counted-index-to-true-index 0))
         (new-node (%make-hash-node :child-present-p new-bitmap
                                    :length new-count)))
    (sv-copy-subrange new-node hash-node :count (- new-elt-true-index zero)
                                         :target-start zero
                                         :source-start zero)
    (setf (svref new-node new-elt-true-index) new-child)
    (sv-copy-subrange new-node hash-node :target-start (1+ new-elt-true-index)
                                         :source-start new-elt-true-index)
    new-node))

;; predeclaration for type inference on recursive calls by `insert-into-hash-node'
(declaim (ftype (function (node entry-node fixnum shift test-function hash-function)
                          (values node bit &optional))
                node-insert))

(declaim (ftype (function (hash-node entry-node fixnum shift test-function hash-function)
                          (values hash-node bit &optional))
                insert-into-hash-node))
(defun insert-into-hash-node (hash-node
                              new-entry
                              hash
                              shift
                              test-function
                              hash-function)
  "Add the NEW-ENTRY as a child of HASH-NODE."
  (let* ((logical-index (extract-hash-part-for-shift shift hash)))
    (if (hash-node-contains-p hash-node logical-index)
          ;; If the hash node already has a child there, recurse to insert into the child.
        (let* ((counted-index (hash-node-logical-index-to-counted-index hash-node logical-index))
               (existing-child (hash-node-counted-ref hash-node counted-index)))
          (multiple-value-bind (new-child num-added)
              (node-insert existing-child new-entry hash (1+ shift) test-function hash-function)
            (values (hash-node-replace-at-counted-index hash-node
                                                        counted-index
                                                        new-child)
                    num-added)))

        ;; If the hash node doesn't have a child there yet, insert one.
        (values (hash-node-insert-at-logical-index hash-node logical-index new-entry)
                1))))

(defun node-insert (body new-entry hash shift test-function hash-function)
  "Make KEY map to VALUE within NODE.
Returns a new node like NODE, but with the mapping (KEY -> VALUE). If KEY is already associated with a value
in NODE, the old value will be overwritten.
HASH is the result of applying the containing `dict' 's HASH-FUNCTION to KEY.
SHIFT is the depth into the trie of NODE. For a `dict' 's BODY, this will be 0.
TEST-FUNCTION is the containing `dict' 's TEST-FUNCTION, which must satisfy the hash-test-function laws with
the HASH-FUNCTION used to generate HASH."
  (ecase (node-type body)
    (entry-node (insert-alongside-entry body new-entry hash shift test-function hash-function))
    (conflict-node (insert-into-conflict-node body new-entry hash shift test-function))
    (hash-node
     (insert-into-hash-node body new-entry hash shift test-function hash-function))))

(declaim (ftype (function (dict t t) (values dict &optional))
                insert))
(defun insert (dict key value)
  "Associate a KEY with a VALUE.
Returns a new `dict' like DICT, with KEY mapping to VALUE. If DICT already contains a mapping for KEY, the old
mapping is replaced."
  (with-accessors ((hash-function %dict-hash-function)
                   (test-function %dict-test-function)
                   (body %dict-body)
                   (size %dict-size))
      dict
    (let* ((hash (funcall hash-function key))
           (new-entry (%make-entry-node :key key
                                        :value value)))
      (if body
          (multiple-value-bind (new-body added-count)
              (node-insert body new-entry hash 0 test-function hash-function)
            (%make-dict :size (+ size added-count)
                        :hash-function hash-function
                        :test-function test-function
                        :body new-body))
          (%make-dict :size 1
                      :hash-function hash-function
                      :test-function test-function
                      :body new-entry)))))

;;; REMOVE and helpers

(declaim (ftype (function (entry-node t test-function)
                          (values (or null entry-node) boolean &optional))
                entry-node-remove))
(defun entry-node-remove (entry-node key test-function)
  (if (funcall test-function (entry-node-key entry-node) key)
      (values nil t)
      (values entry-node nil)))

(declaim (ftype (function (conflict-node array-index)
                          (values conflict-node &optional))
                conflict-node-remove-at-logical-index))
(defun conflict-node-remove-at-logical-index (conflict-node logical-index)
  (let* ((new-node (%make-conflict-node :conflict-hash (conflict-node-conflict-hash conflict-node)
                                        :length (1- (conflict-node-count conflict-node))))
         (zero (conflict-node-logical-index-to-true-index 0))
         (true-index (conflict-node-logical-index-to-true-index logical-index)))
    (sv-copy-subrange new-node conflict-node
                      :count (- true-index zero)
                      :target-start zero
                      :source-start zero)
    (sv-copy-subrange new-node conflict-node
                      :target-start true-index
                      :source-start (1+ true-index))

    new-node))

(declaim (ftype (function (conflict-node t fixnum test-function)
                          (values node boolean &optional))
                conflict-node-remove))
(defun conflict-node-remove (conflict-node key hash test-function)
  "Remove the entry for KEY from CONFLICT-NODE, if any.
HASH is the result of applying the enclosing dict's HASH-FUNCTION to KEY.
If CONFLICT-NODE does not contain an entry for KEY, or if HASH is not the same as the CONFLICT-NODE's
conflict-hash, the returned node will be `eq' to CONFLICT-NODE."
  (flet ((return-unchanged ()
           (values conflict-node nil)))
    (if (= (conflict-node-conflict-hash conflict-node) hash)
        ;; If matching hashes, ...
        (if-let ((logical-index (conflict-node-logical-index-of conflict-node key test-function)))
          ;; If present, ...
          (if (= 2 (conflict-node-count conflict-node))
              ;; If only one remaining entry, promote it so we don't have a one-entry `conflict-node' sitting
              ;; around.
              (values (conflict-node-ref conflict-node
                                         (if (= 0 logical-index)
                                             1
                                             0))
                      t)
              ;; Otherwise, copy the conflict-node with the offending entry removed.
              (values (conflict-node-remove-at-logical-index conflict-node logical-index)
                      t))
          ;; If not present, return unchanged
          (return-unchanged))
        ;; If hashes don't match, the key can't be present, so return unchanged.
        (return-unchanged))))

(declaim (ftype (function (hash-node array-index hash-node-logical-index)
                          (values hash-node &optional))
                hash-node-remove-at-counted-index))
(defun hash-node-remove-at-counted-index (hash-node counted-index-to-remove logical-index-to-remove)
  "Remove from HASH-NODE the child named by COUNTED-INDEX-TO-REMOVE and LOGICAL-INDEX-TO-REMOVE.
Precondition: HASH-NODE must `hash-node-contains-p' LOGICAL-INDEX-TO-REMOVE, and COUNTED-INDEX-TO-REMOVE must
              be the counted index of LOGICAL-INDEX-TO-REMOVE in HASH-NODE."
  (let* ((old-bitmap (hash-node-child-present-p hash-node))
         (new-bitmap (unset-bit old-bitmap
                                logical-index-to-remove))
         (removed-true-index (hash-node-counted-index-to-true-index counted-index-to-remove))
         (new-node (%make-hash-node :child-present-p new-bitmap
                                    :length (1- (hash-node-count hash-node))))
         (zero (hash-node-counted-index-to-true-index 0)))
    (sv-copy-subrange new-node hash-node :count (- removed-true-index zero)
                                         :target-start zero
                                         :source-start zero)
    (sv-copy-subrange new-node hash-node :target-start removed-true-index
                                         :source-start (1+ removed-true-index))
    new-node))

(declaim (ftype (function (bitmap hash-node-logical-index)
                          (values hash-node-logical-index &optional))
                bitmap-other-logical-index))
(defun bitmap-other-logical-index (bitmap logical-index)
  (1- (integer-length (unset-bit bitmap logical-index))))

(declaim (ftype (function (hash-node hash-node-logical-index)
                          (values node &optional))
                hash-node-maybe-promote-other-child))
(defun hash-node-maybe-promote-other-child (hash-node logical-index-to-discard)
  (let* ((old-bitmap (hash-node-child-present-p hash-node))
         (logical-index-to-keep (bitmap-other-logical-index old-bitmap logical-index-to-discard))
         (child-to-keep (hash-node-logical-ref hash-node logical-index-to-keep)))
    (if (eq (node-type child-to-keep) 'hash-node)
        ;; Cannot promote, because the child is a hash-node with a greater shift than us.
        (make-one-entry-hash-node child-to-keep logical-index-to-keep)

        ;; Can promote, because the child is an entry or a conflict-node
        child-to-keep)))

;; predeclaration for better type inference in recursive calls by `hash-node-remove'
(declaim (ftype (function (node t fixnum shift test-function)
                          (values (or null node) boolean &optional))
                node-remove))

(declaim (ftype (function (hash-node
                           t
                           fixnum
                           shift
                           test-function)
                          (values (or null node) boolean &optional))
                hash-node-remove))
(defun hash-node-remove (hash-node
                         key
                         hash
                         shift
                         test-function)
  (flet ((return-unchanged ()
           (values hash-node nil)))
    (let* ((logical-index (extract-hash-part-for-shift shift hash)))
      (if (hash-node-contains-p hash-node logical-index)
          (let* ((counted-index (hash-node-logical-index-to-counted-index hash-node logical-index))
                 (existing-child (hash-node-counted-ref hash-node counted-index)))
            (multiple-value-bind (new-child removedp)
                (node-remove existing-child
                             key
                             hash
                             (1+ shift)
                             test-function)
              (cond ((not removedp)
                     ;; If we didn't remove anything, return ourselves.
                     (return-unchanged))

                    ((and (null new-child)
                          (= 1 (hash-node-count hash-node)))
                     ;; If we removed our only child, return nothing.
                     (values nil t))

                    ((and (null new-child)
                          (= 2 (hash-node-count hash-node)))
                     ;; If we're removing one of two children, try to reduce nesting.
                     (values (hash-node-maybe-promote-other-child hash-node logical-index)
                             t))

                    ((null new-child)
                     ;; If we removed an entire child, the resulting hash node will have one fewer entries than
                     ;; HASH-NODE.
                     (values (hash-node-remove-at-counted-index hash-node counted-index logical-index)
                             t))

                    (:else
                     ;; If we removed from a child that still has other entries, splice the new child back in.
                     (values (hash-node-replace-at-counted-index hash-node
                                                                 counted-index
                                                                 new-child)
                             t)))))

          (return-unchanged)))))

(defun node-remove (body key hash shift test-function)
  "Make KEY unmapped within the node (BODY-KEY BODY-VALUE).
Returns (values NEW-BODY REMOVEDP).
If KEY is already unmapped within the body, REMOVEDP will be nil, and NEW-BODY will be eq to
BODY.
HASH is the result of applying the containing `dict' 's HASH-FUNCTION to KEY.
SHIFT is the depth into the trie of the body. For a `dict' 's direct body, this will be 0.
TEST-FUNCTION is the containing `dict' 's TEST-FUNCTION, which must satisfy the hash-test-function laws with
the HASH-FUNCTION used to generate HASH."
  (ecase (node-type body)
    (entry-node (entry-node-remove body key test-function))

    (conflict-node
     (conflict-node-remove body key hash test-function))

    (hash-node
     (hash-node-remove body key hash shift test-function))))

(declaim (ftype (function (dict t) (values dict &optional))
                remove))
(defun remove (dict key)
  "Make KEY unmapped in DICT.
Return a new `dict' like DICT, but where KEY is not associated with any value.
If DICT does not contain a mapping for KEY, the returned `dict' will be `eq' to DICT."
  (with-accessors ((hash-function %dict-hash-function)
                   (test-function %dict-test-function)
                   (body %dict-body)
                   (size %dict-size))
      dict
    (if (null body)
        dict
        (let* ((hash (funcall hash-function key)))
          (multiple-value-bind (new-body removed-p)
              (node-remove body key hash 0 test-function)
            (if removed-p
                (%make-dict :size (1- size)
                            :hash-function hash-function
                            :test-function test-function
                            :body new-body)
                dict))))))

;;; finding appropriate hash functions for a given test function

(declaim (dict *test-hash-functions*))
(defparameter *test-hash-functions*
  (%make-dict :size 0
              :body nil
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
                :body nil
                :hash-function hash-function
                :test-function test-function)))
