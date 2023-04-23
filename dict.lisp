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
  (:import-from #:immutable/%atomic
                #:define-atomic-counter
                #:increment-atomic-counter)
  (:shadow #:get #:remove #:do #:union)
  (:use :cl :iterate :immutable/%generator :immutable/%simple-vector-utils)
  (:import-from :immutable/hash
                #:==
                #:hash
                #:unsigned-fixnum)
  (:export

   ;; Type definitions.
   #:dict
   #:transient

   ;; Converting between dicts and transients.
   #:transient #:persistent!

   ;; Stale transient error, when attempting to mutate a transient that has already been made `persistent!'.
   #:stale-transient
   #:stale-transient-operation
   #:stale-transient-transient

   ;; Unknown hash function error.
   #:no-hash-function-for-test
   #:no-hash-function-for-test-function
   #:no-hash-function-for-test-known-hash-functions

   ;; Invalid hash table test error, for `to-hash-table'.
   #:invalid-hash-table-test
   #:invalid-hash-table-test-test

   ;; Malformed plist and alist errors, for `from-alist', `insert-alist' and plist equivalents.
   #:malformed-plist
   #:malformed-plist-plist
   #:malformed-plist-operator

   #:malformed-alist
   #:malformed-alist-alist
   #:malformed-alist-operator

   ;; Error when converting a collection would cause a collision due to different hash/test functions.
   #:convert-overwrite
   #:convert-overwrite-key
   #:convert-overwrite-old-value
   #:convert-overwrite-new-value
   #:convert-overwrite-operation
   #:convert-overwrite-source

   ;; Error on unexpected conflict during rehashes.
   #:rehash-conflict
   #:rehash-conflict-key
   #:rehash-conflict-value-1
   #:rehash-conflict-value-2
   #:rehash-conflict-source
   #:rehash-conflict-new-test-function
   #:rehash-conflict-new-hash-function

   ;; Reading properties of dicts and transients.
   #:size #:test-function #:hash-function

   ;; Registering new test-function/hash-function pairs.
   #:define-test-hash-function

   ;; GETHASH analogue.
   #:get

   ;; (SETF GETHASH) analogue.
   #:insert #:insert!

   ;; Specifying the behavior of insertion when a dict already contains a mapping for the given key.
   #:merge-function #:new-value #:old-value

   ;; REMHASH analogue.
   #:remove #:remove!

   ;; MAKE-HASH-TABLE analogue to construct an empty dict.
   #:empty #:empty-transient

   ;; Batched insertions and removals.
   #:insert-plist
   #:insert-alist
   #:insert-multiple
   #:remove-multiple

   ;; Iteration over dicts.
   #:for-each
   #:map-values
   #:do

   ;; Combining dicts.
   #:union

   ;; Changing hash and test function of a dict.
   #:rehash

   ;; Converting to/from CL mapping collections.
   #:from-hash-table #:to-hash-table
   #:from-alist #:to-alist
   #:from-plist #:to-plist))
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

(deftype transient-id ()
  '(or null fixnum))

(define-atomic-counter current-transient-id 0
                       "Atomic counter used as a global resource for transient ids.

Nodes and `transient's hold a (nullable) fixnum transient-id. Transient operations are allowed to mutate a
node if and only if the node's id is non-null and matches the enclosing transient's id.

When creating a transient, this counter will be incremented with `increment-atomic-counter', and the new value
will be used as the new transient's id.")

(declaim (ftype (function () (values fixnum &optional))
                get-transient-id))
(defun get-transient-id ()
  (increment-atomic-counter current-transient-id))

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
  (transient-id :type transient-id
                :initform nil)
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
     :zero-index +conflict-node-zero+)
  (transient-id :type transient-id
                :initform nil))

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

(declaim (inline %make-transient %transient-id %transient-size %transient-hash-function %transient-test-function %transient-key %transient-value %transient-child-type))

(eval-when (:compile-toplevel :load-toplevel)
  (defparameter +transient-explanation+
    "`transient's are mutable `dict's. Certain operations, namely `insert' and `remove', have transient analogues
`insert!' and `remove!' which may in some cases reduce consing by mutating otherwise inaccessible subparts. No
mutations to a `transient' will ever be visible to the `dict' from which it was constructed.

Construct a `transient' from a `dict' using the function `transient'.

Convert a `transient' into a `dict' using the function `persistent!'. A `transient' which has been made
`persistent!' is considered \"stale,\" and all future transient operations on it will fail, singaling an error
of class `stale-transient'.

The behavior of concurrently mutating a `transient' from multiple threads is undefined."))

(defstruct (transient
            (:constructor %make-transient)
            (:copier nil)
            (:conc-name %transient-))
  #.(concatenate 'string
     "A temporarily mutable `dict', tracking a unique id to ensure it only mutates otherwise-inaccessible nodes.

"

     +transient-explanation+)
  (id (error "Supply :ID to %MAKE-TRANSIENT")
   :type transient-id)
  (size (error "Supply :SIZE to %MAKE-TRANSIENT")
   :type size)
  (hash-function (error "Supply :HASH-FUNCTION to %MAKE-TRANSIENT")
   :type hash-function)
  (test-function (error "Supply :TEST-FUNCTION to %MAKE-TRANSIENT")
   :type test-function)
  (child-type (error "Supply :CHILD-TYPE to %MAKE-TRANSIENT")
   :type child-type)
  (key (error "Supply :KEY to %MAKE-TRANSIENT"))
  (value (error "Supply :VALUE to %MAKE-TRANSIENT")))

;;; error for using a stale transient, i.e. one which has already been made `persistent!'

(define-condition stale-transient (error)
  ((%transient :type transient
               :initarg :transient
               :accessor stale-transient-transient)
   (%operation :type symbol
               :initarg :operation
               :accessor stale-transient-operation))
  (:report (lambda (c s)
             (format s "Attempt to ~s on a `transient' which has already been made `persistent!': ~s"
                     (stale-transient-operation c)
                     (stale-transient-transient c)))))

;;; converting between transient and persistent dicts

(declaim (ftype (function (dict) (values transient &optional))
                transient))
(defun transient (dict)
  #.(concatenate 'string
                 "Construct a `transient' with the contents of DICT.

This operation runs in constant time, and does not copy any substructure of DICT. Future transient operations
will begin by copying what substructure they need to, and will only mutate newly-constructed nodes which are
uniquely owned by the transient.

"
            +transient-explanation+)
  (%make-transient :id (get-transient-id)
                   :size (%dict-size dict)
                   :hash-function (%dict-hash-function dict)
                   :test-function (%dict-test-function dict)
                   :child-type (%dict-child-type dict)
                   :key (%dict-key dict)
                   :value (%dict-value dict)))

(declaim (ftype (function (transient) (values dict &optional))
                persistent!))
(defun persistent! (transient)
  #.(concatenate 'string "Convert TRANSIENT into a persistent `dict'.

This operation runs in constant time.

After this operation, TRANSIENT is considered \"stale,\" and all future transient operations on it will fail
with an error of class `stale-transient'.

"
                 +transient-explanation+)
  (if (null (%transient-id transient))
      (error 'stale-transient
             :operation 'persistent!
             :transient transient)
      (progn
        (setf (%transient-id transient) nil)
        (%make-dict :size (%transient-size transient)
                    :hash-function (%transient-hash-function transient)
                    :test-function (%transient-test-function transient)
                    :child-type (%transient-child-type transient)
                    :key (%transient-key transient)
                    :value (%transient-value transient)))))

;;; accessors

(declaim (ftype (function ((or dict transient)) (values size &optional))
                size)
         ;; Inlining may allow the compiler to eliminate `etypecase' dispatch.
         (inline size))
(defun size (dict)
  (etypecase dict
    (dict (%dict-size dict))
    (transient (%transient-size dict))))

(declaim (ftype (function ((or dict transient)) (values hash-function &optional))
                hash-function)
         ;; Inlining may allow the compiler to eliminate `etypecase' dispatch.
         (inline hash-function))
(defun hash-function (dict)
  (etypecase dict
    (dict (%dict-hash-function dict))
    (transient (%transient-hash-function dict))))

(declaim (ftype (function ((or dict transient)) (values test-function &optional))
                test-function)
         ;; Inlining may allow the compiler to eliminate `etypecase' dispatch.
         (inline test-function))
(defun test-function (dict)
  (etypecase dict
    (dict (%dict-test-function dict))
    (transient (%transient-test-function dict))))

(declaim (ftype (function ((or dict transient)) (values t &optional))
                %key %value)
         ;; Inlining may allow the compiler to eliminate `etypecase' dispatch.
         (inline %key %value))
(defun %key (dict)
  (etypecase dict
    (dict (%dict-key dict))
    (transient (%transient-key dict))))

(defun %value (dict)
  (etypecase dict
    (dict (%dict-value dict))
    (transient (%transient-value dict))))

(declaim (ftype (function ((or dict transient)) (values child-type &optional))
                %child-type)
         ;; Inlining may allow the compiler to eliminate `etypecase' dispatch.
         (inline %child-type))
(defun %child-type (dict)
  (etypecase dict
    (dict (%dict-child-type dict))
    (transient (%transient-child-type dict))))

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

(declaim (ftype (function (hash-node bitmap hash-node-logical-index) (values child-type &optional))
                hash-node-child-type)
         ;; Inlining may allow the compiler to eliminate references to and comparisons with the actual
         ;; keywords in `child-type'.
         (inline hash-node-child-type))
(defun hash-node-child-type (hash-node bitmap logical-index)
  "Does this HASH-NODE contain a child at the index LOGICAL-INDEX?"
  (when (bitmap-contains-p bitmap logical-index)
    (let* ((counted-index (bitmap-logical-index-to-counted-index bitmap logical-index)))
      (cond ((bitmap-contains-p (hash-node-child-is-entry-p hash-node) counted-index) :entry)
            ((bitmap-contains-p (hash-node-child-is-conflict-p hash-node) counted-index) :conflict-node)
            (:else :hash-node)))))

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

(declaim (ftype (function (bitmap hash-node hash-node-logical-index t t) (values &optional))
                set-hash-node-logical-entry)
         ;; Trivial enough that call overhead is meaningful, so always inline.
         (inline set-hash-node-logical-entry))
(defun set-hash-node-logical-entry (bitmap hash-node logical-index new-key new-value)
  "Write the pair (NEW-KEY => NEW-VALUE) into HASH-NODE at LOGICAL-INDEX.

It is the caller's responsibility to update HASH-NODE's child-is-entry-p and child-is-conflict-p bitmaps to
suit the new entry."
  (let* ((key-index (hash-node-key-true-index bitmap logical-index)))
    (setf (hash-node-true-ref hash-node key-index)
          new-key)
    (setf (hash-node-true-ref hash-node (1+ key-index))
          new-value))
  (values))

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

(declaim (ftype (function ((or dict transient) t &optional t) (values t boolean))
                get))
(defun get (dict key &optional not-found)
  "Get the value associated with KEY in DICT, or NOT-FOUND if the KEY is not present.

Like `gethash', returns (values VALUE PRESENTP). If DICT contains a mapping for KEY, returns the associated
value as VALUE, and T as PRESENTP. If DICT does not contain a mapping for KEY, returns (values NOT-FOUND
nil)."
  (with-accessors ((hash-function hash-function)
                   (test-function test-function)
                   (child-type %child-type)
                   (body-key %key)
                   (body-value %value))
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

(deftype merge-function (&optional (key t) (value t))
  "A function used to compute the resulting value in an `insert' operation when the key is already present.

During (insert DICT KEY NEW-VALUE), if DICT already associates KEY with OLD-VALUE, the `merge-function' will
be called with (KEY OLD-VALUE NEW-VALUE).

The default `merge-function' is `new-value', which ignores the KEY and OLD-VALUE and uses the NEW-VALUE."
  `(function (,key ,value ,value) (values ,value &optional)))

(declaim (ftype merge-function
                new-value
                old-value))
(defun new-value (key old-value new-value)
  "The default `merge-function', which inserts the NEW-VALUE, overwriting the OLD-VALUE."
  (declare (ignore key old-value))
  new-value)
(defun old-value (key old-value new-value)
  "A `merge-function' which leaves the OLD-VALUE, effectively aborting the `insert' operation."
  (declare (ignore key new-value))
  old-value)

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

(declaim (ftype (function (transient-id
                           t t child-type hash-node-logical-index
                           t t child-type hash-node-logical-index
                           t)
                          (values bitmap hash-node (eql :hash-node) t &optional))
                make-two-entry-hash-node))
(defun make-two-entry-hash-node (transient-id
                                 left-key left-value left-child-type left-idx
                                 right-key right-value right-child-type right-idx
                                 additional-return-value)
  (multiple-value-bind (lower-key lower-value lower-type lower-idx
                        higher-key higher-value higher-type higher-idx)
      (if (< left-idx right-idx)
          (values left-key left-value left-child-type left-idx
                  right-key right-value right-child-type right-idx)
          (values right-key right-value right-child-type right-idx
                  left-key left-value left-child-type left-idx))
    (let* ((child-is-conflict-p 0)
           (child-is-entry-p 0))
      (declare (bitmap child-is-conflict-p child-is-entry-p))
      (flet ((set-child-type-bits (child-type counted-index)
               (case child-type
                 (:entry (setf child-is-entry-p
                               (set-bit child-is-entry-p
                                        counted-index)))
                 (:conflict-node (setf child-is-conflict-p
                                       (set-bit child-is-conflict-p
                                                counted-index))))))
        (set-child-type-bits lower-type 0)
        (set-child-type-bits higher-type 1))
      (let* ((new-node (%make-hash-node :transient-id transient-id
                                        :child-is-entry-p child-is-entry-p
                                        :child-is-conflict-p child-is-conflict-p
                                        :length (logical-count-to-paired-length 2))))
        (sv-initialize new-node (:start-from +hash-node-zero+)
          lower-key
          lower-value
          higher-key
          higher-value)

        (values (bitmap-from-indices lower-idx higher-idx)

                new-node

                :hash-node

                additional-return-value)))))

(declaim (ftype (function (transient-id t t child-type hash-node-logical-index t)
                          (values bitmap hash-node (eql :hash-node) t &optional))
                make-one-entry-hash-node))
(defun make-one-entry-hash-node (transient-id key value child-type logical-index additional-return-value
                                 &aux )
  (let* ((bitmap (bitmap-from-indices logical-index))
         (new-node (%make-hash-node :transient-id transient-id
                                    :child-is-entry-p (if (eq child-type :entry)
                                                          1
                                                          0)
                                    :child-is-conflict-p (if (eq child-type :conflict-node)
                                                             1
                                                             0)
                                    :length (logical-count-to-paired-length 1))))
    (sv-initialize new-node (:start-from +hash-node-zero+)
      key value)
    (values bitmap

            new-node

            :hash-node

            additional-return-value)))

(declaim (ftype (function (transient-id fixnum array-length t &rest t)
                          (values fixnum conflict-node (eql :conflict-node) t &optional))
                make-conflict-node))
(defun make-conflict-node (transient-id hash logical-count additional-return-value &rest keys-and-values)
  (declare (dynamic-extent keys-and-values))
  (values
   hash

   (with-list-generator (gen-initial-contents keys-and-values)
     (%make-conflict-node :transient-id transient-id
                          :length (logical-count-to-paired-length logical-count)
                          :initial-contents gen-initial-contents))

   :conflict-node

   additional-return-value))

(declaim (ftype (function (transient-id
                           t t fixnum child-type
                           t t fixnum child-type
                           shift
                           t)
                          (values bitmap hash-node (eql :hash-node) t &optional))
                promote-node))
(defun promote-node (transient-id
                     left-key left-value left-hash left-child-type
                     right-key right-value right-hash right-child-type
                     shift
                     additional-return-value)
  "Combine the LEFT-NODE and RIGHT-NODE into a new `hash-node', which should be SHIFT steps deep into the trie.

LEFT-HASH is the hash of the entries in the LEFT-NODE.

RIGHT-HASH is the hash of the entries in the RIGHT-NODE.

Precondition: (/= LEFT-HASH RIGHT-HASH), or else we would construct a unified `conflict-node' instead of a
              `hash-node'."
  (let* ((left-index (extract-hash-part-for-shift shift left-hash))
         (right-index (extract-hash-part-for-shift shift right-hash)))
    (if (= left-index right-index)
        (multiple-value-bind (sub-bitmap sub-node hash-node additional-return-value)
            (promote-node transient-id
                          left-key left-value left-hash left-child-type
                          right-key right-value right-hash right-child-type
                          (1+ shift)
                          additional-return-value)
          (make-one-entry-hash-node transient-id
                                    sub-bitmap sub-node hash-node
                                    left-index
                                    additional-return-value))
        (make-two-entry-hash-node transient-id
                                  left-key left-value left-child-type left-index
                                  right-key right-value right-child-type right-index
                                  additional-return-value))))

(declaim (ftype (function (transient-id t t t t fixnum shift test-function hash-function merge-function)
                          (values t t child-type bit &optional))
                insert-alongside-entry))
(defun insert-alongside-entry (transient-id
                               neighbor-key neighbor-value
                               key value
                               hash shift
                               test-function hash-function merge-function
                               &aux (neighbor-hash (funcall hash-function neighbor-key)))
  (cond ((and (= neighbor-hash hash)
              (funcall test-function neighbor-key key))
         (values key (funcall merge-function key neighbor-value value) :entry 0))

        ((= neighbor-hash hash)
         (make-conflict-node transient-id hash 2 1 neighbor-key neighbor-value key value))

        (:else (promote-node transient-id
                             neighbor-key neighbor-value neighbor-hash :entry
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

(declaim (ftype (function (transient-id conflict-node fixnum t t array-index t)
                          (values fixnum conflict-node (eql :conflict-node) t &optional))
                conflict-node-copy-replace-at-logical-index))
(defun conflict-node-copy-replace-at-logical-index (transient-id
                                                    conflict-node hash
                                                    new-key new-value
                                                    logical-index
                                                    additional-return-value)
  "Do a functional update of CONFLICT-NODE, replacing the entry at LOGICAL-INDEX with (NEW-KEY => NEW-VALUE).

The resulting node will have the TRANSIENT-ID installed.

Return four values suitable for the insertion operation: (values MY-KEY MY-VALUE MY-TYPE DELTA-SIZE)."
  (let* ((new-node (%make-conflict-node :transient-id transient-id
                                        :length (conflict-node-paired-count conflict-node)))
         (replaced-key-true-index (conflict-node-key-true-index logical-index)))
    (sv-initialize new-node (:start-from +conflict-node-zero+)
      (:subrange conflict-node
       :count (- replaced-key-true-index +conflict-node-zero+)
       :start +conflict-node-zero+)
      new-key
      new-value
      (:subrange conflict-node :start (+ 2 replaced-key-true-index)))

    (values hash new-node :conflict-node additional-return-value)))

(declaim (ftype (function (conflict-node fixnum t t array-index)
                          (values fixnum conflict-node (eql :conflict-node) (eql 0) &optional))
                conflict-node-set-at-logical-index))
(defun conflict-node-set-at-logical-index (conflict-node hash new-key new-value logical-index)
  "Mutate the CONFLICT-NODE, replacing the entry at LOGICAL-INDEX with (NEW-KEY => NEW-VALUE).

Invariant: the enclosing `transient' on which the current `insert!' operation is running must uniquely own the
CONFLICT-NODE, that is, their ids must match.

Return four values suitable for the insertion operation: (values MY-KEY MY-VALUE MY-TYPE DELTA-SIZE)."
  (set-conflict-node-logical-entry conflict-node logical-index new-key new-value)
  (values hash
          conflict-node
          :conflict-node
          0))

(declaim (ftype (function (transient-id transient-id) (values boolean &optional))
                same-transient-id-p)
         ;; Inlining may allow the compiler to avoid reifying the result into a `cl:boolean'.
         (inline same-transient-id-p))
(defun same-transient-id-p (a b)
  (and a b (= a b)))

(declaim (ftype (function (transient-id conflict-node fixnum t t array-index)
                          (values fixnum conflict-node (eql :conflict-node) (eql 0) &optional))
                conflict-node-replace-at-logical-index))
(defun conflict-node-replace-at-logical-index (transient-id conflict-node hash new-key new-value logical-index)
  (if (same-transient-id-p transient-id (conflict-node-transient-id conflict-node))
      ;; If we're a transient and we uniquely own this node, mutate it.
      (conflict-node-set-at-logical-index conflict-node hash new-key new-value logical-index)
      ;; Otherwise, do a functional update.
      (conflict-node-copy-replace-at-logical-index transient-id conflict-node hash new-key new-value logical-index 0)))

(declaim (ftype (function (transient-id fixnum conflict-node t t t)
                          (values fixnum conflict-node (eql :conflict-node) t &optional))
                add-to-conflict-node))
(defun add-to-conflict-node (transient-id hash conflict-node new-key new-value additional-return-value)
  "Add (NEW-KEY => NEW-VALUE) into the entries of CONFLICT-NODE.

Because `conflict-node's are not adjustable, this operation must always copy CONFLICT-NODE. The TRANSIENT-ID
will be installed in the new node, potentially allowing future transient operations to mutate it.)

Precondition: NEW-ENTRY has the same hash as CONFLICT-NODE, and no existing entry in CONFLICT-NODE has the
              same key as NEW-ENTRY."
  (let* ((new-node (%make-conflict-node :transient-id transient-id
                                        :length (logical-count-to-paired-length
                                                 (1+ (conflict-node-logical-length conflict-node))))))

    (sv-initialize new-node (:start-from +conflict-node-zero+)
      (:subrange conflict-node :start +conflict-node-zero+)
      new-key
      new-value)

    (values hash
            new-node
            :conflict-node
            additional-return-value)))

(declaim (ftype (function (transient-id fixnum conflict-node t t fixnum shift test-function merge-function)
                          (values t t child-type bit &optional))
                insert-into-conflict-node))
(defun insert-into-conflict-node (transient-id
                                  conflict-hash conflict-node
                                  new-key new-value
                                  hash shift
                                  test-function merge-function)
  "Add a new entry (KEY -> VALUE) to or alongside CONFLICT-NODE.

Depending on whether HASH is the same as the hash in CONFLICT-NODE, this may allocate a new `hash-node' to
contain both the existing CONFLICT-NODE and the new entry.

If TRANSIENT-ID matches the id of the CONFLICT-NODE, this operation may mutate CONFLICT-NODE and return it
instead of allocating a new node. If a new node is allocated, the TRANSIENT-ID will be installed as its id."
  (let* ((same-hash-p (= conflict-hash hash))
         (logical-index (when same-hash-p
                          (conflict-node-logical-index-of conflict-node new-key test-function))))
    (cond ((and same-hash-p logical-index)
           ;; If CONFLICT-NODE already contains a mapping for KEY, replace it. This is the case where we can
           ;; mutate if the transient ids match.
           (let* ((old-value (conflict-node-logical-value-ref conflict-node logical-index))
                  (merged-value (funcall merge-function new-key old-value new-value)))
             (conflict-node-replace-at-logical-index transient-id conflict-node hash new-key merged-value logical-index)))

          (same-hash-p
           ;; If the new mapping conflicts with CONFLICT-NODE but is not already present, add it. This will
           ;; always allocate a new `conflict-node' regardless of transient-ness, because `conflict-node's are
           ;; not adjustable.
           (add-to-conflict-node transient-id hash conflict-node new-key new-value 1))

          (:else
           ;; If the new mapping does not conflict, grow a new `hash-node' with the CONFLICT-NODE and the new
           ;; entry as siblings. This will (obviously) allocate a new `hash-node', regardless of transient-ness.
           (promote-node transient-id
                         conflict-hash conflict-node conflict-hash :conflict-node
                         new-key new-value hash :entry
                         shift
                         1)))))

(declaim (ftype (function (bitmap child-type child-type hash-node-logical-index) (values bitmap &optional))
                bitmap-set-if-same-type-or-unset))
(defun bitmap-set-if-same-type-or-unset (bitmap a b logical-index)
  (if (eq a b)
      (set-bit bitmap logical-index)
      (unset-bit bitmap logical-index)))

(declaim (ftype (function (transient-id
                           bitmap hash-node
                           hash-node-logical-index
                           t t child-type
                           t)
                          (values bitmap hash-node (eql :hash-node) t &optional))
                hash-node-copy-replace-at))
(defun hash-node-copy-replace-at (transient-id
                                  bitmap hash-node
                                  logical-index
                                  new-key new-value new-type
                                  additional-return-value)
  "Do a functional update of HASH-NODE, replacing the entry at LOGICAL-INDEX with (NEW-KEY => NEW-VALUE).

The resulting node will have TRANSIENT-ID installed.

Return four values suitable for the insertion or removal operation:
(values MY-KEY MY-VALUE MY-TYPE ADDITIONAL-RETURN-VALUE)."
  (let* ((counted-index (bitmap-logical-index-to-counted-index bitmap logical-index))
         (new-elt-key-true-index (hash-node-key-true-index bitmap logical-index))
         (new-node (%make-hash-node :transient-id transient-id
                                    :child-is-entry-p (bitmap-set-if-same-type-or-unset
                                                       (hash-node-child-is-entry-p hash-node)
                                                       new-type :entry
                                                       counted-index)
                                    :child-is-conflict-p (bitmap-set-if-same-type-or-unset
                                                          (hash-node-child-is-conflict-p hash-node)
                                                          new-type :conflict-node
                                                          counted-index)
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
                                  t t child-type
                                  t)
                          (values bitmap hash-node (eql :hash-node) t &optional))
                hash-node-set-at-logical-index))
(defun hash-node-set-at-logical-index (bitmap hash-node
                                       logical-index
                                       new-key new-value new-type
                                       additional-return-value)
  "Mutate HASH-NODE, replacing the entry at LOGICAL-INDEX with (NEW-KEY => NEW-VALUE).

Invariant: the enclosing `transient' on which the current `insert!' or `remove!' operation is running must
uniquely own the HASH-NODE, that is, their ids must match.

Return four values suitable for the insertion or removal operation:
(values MY-KEY MY-VALUE MY-TYPE ADDITIONAL-RETURN-VALUE)."
  (set-hash-node-logical-entry bitmap hash-node
                               logical-index
                               new-key new-value)
  (let* ((counted-index (bitmap-logical-index-to-counted-index bitmap logical-index)))
    (setf (hash-node-child-is-entry-p hash-node)
          (bitmap-set-if-same-type-or-unset (hash-node-child-is-entry-p hash-node)
                                            new-type :entry
                                            counted-index))
    (setf (hash-node-child-is-conflict-p hash-node)
          (bitmap-set-if-same-type-or-unset (hash-node-child-is-conflict-p hash-node)
                                            new-type :conflict-node
                                            counted-index)))
  (values bitmap
          hash-node
          :hash-node
          additional-return-value))

(declaim (ftype (function (transient-id
                           bitmap hash-node
                           hash-node-logical-index
                           t t child-type
                           t)
                          (values bitmap hash-node (eql :hash-node) t &optional))
                hash-node-replace-at))
(defun hash-node-replace-at (transient-id
                             bitmap hash-node
                             logical-index
                             new-key new-value new-type
                             additional-return-value)
  (if (same-transient-id-p transient-id (hash-node-transient-id hash-node))
      (hash-node-set-at-logical-index bitmap hash-node
                                      logical-index
                                      new-key new-value new-type
                                      additional-return-value)
      (hash-node-copy-replace-at transient-id
                                 bitmap hash-node
                                 logical-index
                                 new-key new-value new-type
                                 additional-return-value)))

(declaim (ftype (function (bitmap (mod #.+branch-rate+) bit) (values bitmap &optional))
                bitmap-splice-at)
         (inline bitmap-splice-at))
(defun bitmap-splice-at (bitmap index bit)
  (let* ((low (ldb (byte index 0) bitmap))
         (high (ldb (byte (- +branch-rate+ index) index) bitmap)))
    (dpb high
         (byte (- 31 index) (1+ index))
         (dpb bit
              (byte 1 index)
              low))))

(declaim (ftype (function (transient-id
                           bitmap hash-node
                           hash-node-logical-index
                           t t child-type
                           t)
                          (values bitmap hash-node (eql :hash-node) t &optional))
                hash-node-insert-at))
(defun hash-node-insert-at (transient-id
                            bitmap hash-node
                            logical-index
                            child-key child-value child-type
                            additional-return-value)
  "Add (NEW-KEY => NEW-VALUE) into the entries of HASH-NODE at LOGICAL-INDEX.

Because `hash-node's are not adjustable, this operation must always copy HASH-NODE. The TRANSIENT-ID will be
installed in the new node, potentially allowing future transient operations to mutate it."
  (let* ((new-bitmap (set-bit bitmap
                              logical-index))
         (new-paired-length (logical-count-to-paired-length (1+ (hash-node-logical-count hash-node))))
         (counted-index (bitmap-logical-index-to-counted-index new-bitmap logical-index))
         (new-elt-key-true-index (hash-node-key-true-index new-bitmap logical-index))
         (new-node (%make-hash-node :transient-id transient-id
                                    :child-is-entry-p (bitmap-splice-at (hash-node-child-is-entry-p hash-node)
                                                                        counted-index
                                                                        (if (eq child-type :entry) 1 0))
                                    :child-is-conflict-p (bitmap-splice-at (hash-node-child-is-conflict-p hash-node)
                                                                           counted-index
                                                                           (if (eq child-type :conflict-node) 1 0))
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

            additional-return-value)))

;; predeclaration for type inference on recursive calls by `insert-into-hash-node'
(declaim (ftype (function (transient-id child-type t t t t fixnum shift test-function hash-function merge-function)
                          (values t t child-type bit &optional))
                node-insert))

(declaim (ftype (function (transient-id
                           bitmap hash-node
                           t t fixnum
                           shift
                           test-function hash-function merge-function)
                          (values bitmap hash-node (eql :hash-node) bit &optional))
                insert-into-hash-node))
(defun insert-into-hash-node (transient-id
                              bitmap hash-node
                              key value hash
                              shift
                              test-function
                              hash-function
                              merge-function)
  "Add a new entry (KEY -> VALUE) as a child of HASH-NODE.

If TRANSIENT-ID matches the id of the HASH-NODE, this operation may mutate HASH-NODE and return it rather than
allocating a new node. If a new node is allocated, the TRANSIENT-ID will be installed as its id."
  (let* ((logical-index (extract-hash-part-for-shift shift hash)))
    (if-let ((child-type (hash-node-child-type hash-node bitmap logical-index)))

      ;; If the hash node already has a child there, recurse to insert into the child.
      (multiple-value-bind (child-key child-value)
          (hash-node-logical-ref hash-node bitmap logical-index)
        (multiple-value-bind (new-child-key new-child-val new-child-type num-added)
            (node-insert transient-id
                         child-type
                         child-key child-value
                         key value hash
                         (1+ shift)
                         test-function hash-function merge-function)
          ;; This operation may, depending on transient-ness and ownership, mutate the HASH-NODE rather than
          ;; copying.
          (hash-node-replace-at transient-id
                                bitmap hash-node
                                logical-index
                                new-child-key new-child-val new-child-type
                                num-added)))

      ;; If the hash node doesn't have a child there yet, insert one. This will always copy HASH-NODE, because
      ;; `hash-node's are not adjustable.
      (hash-node-insert-at transient-id
                           bitmap hash-node
                           logical-index
                           key value :entry
                           ;; We added an entry, so return 1 as an additional value.
                           1))))

(defun node-insert (transient-id
                    body-type body-key body-value
                    key value
                    hash
                    shift
                    test-function hash-function merge-function)
  "Make KEY map to VALUE within NODE.

Returns a new node like NODE, but with the mapping (KEY -> VALUE). If KEY is already associated with a value
in NODE, the old value will be overwritten.

HASH is the result of applying the containing `dict' 's HASH-FUNCTION to KEY.

SHIFT is the depth into the trie of NODE. For a `dict' 's BODY, this will be 0.

TEST-FUNCTION is the containing `dict' 's TEST-FUNCTION, which must satisfy the hash-test-function laws with
the HASH-FUNCTION used to generate HASH.

If the BODY-TYPE is `:conflict-node' or `:hash-node', and the TRANSIENT-ID matches the BODY-VALUE's id, this
operation may mutate the BODY-VALUE and return it rather than allocating a new node. Any new nodes allocated
will have the TRANSIENT-ID installed as their id."
  (ecase body-type
    ((nil) (values key value :entry 1))
    (:entry (insert-alongside-entry transient-id
                                    body-key body-value
                                    key value hash
                                    shift
                                    test-function hash-function merge-function))
    (:conflict-node (insert-into-conflict-node transient-id
                                               body-key body-value
                                               key value
                                               hash
                                               shift
                                               test-function merge-function))
    (:hash-node
     (insert-into-hash-node transient-id
                            body-key body-value
                            key value
                            hash
                            shift
                            test-function hash-function merge-function))))

(declaim (ftype (function (dict t t &optional merge-function) (values dict &optional))
                insert))
(defun insert (dict key value &optional (merge-function #'new-value))
  "Associate KEY with VALUE in DICT.

Returns a new `dict' like DICT, with KEY mapping to VALUE.

The MERGE-FUNCTION defines the behavior if DICT already contains a mapping for KEY. It is a function of three
arguments, (KEY OLD-VALUE NEW-VALUE), which returns a MERGED-VALUE. The default is `new-value', which returns
the NEW-VALUE as the MERGED-VALUE, effectively overwriting the OLD-VALUE in the resulting `dict'."
  (with-accessors ((hash-function %dict-hash-function)
                   (test-function %dict-test-function)
                   (body-key %dict-key)
                   (body-value %dict-value)
                   (body-type %dict-child-type)
                   (size %dict-size))
      dict
    (let* ((hash (funcall hash-function key)))
      (multiple-value-bind (new-body-key new-body-value new-type added-count)
          (node-insert nil body-type body-key body-value key value hash 0 test-function hash-function merge-function)
        (%make-dict :size (+ size added-count)
                    :hash-function hash-function
                    :test-function test-function
                    :key new-body-key
                    :value new-body-value
                    :child-type new-type)))))

(declaim (ftype (function (transient t t &optional merge-function) (values transient &optional))
                insert!))
(defun insert! (transient key value &optional (merge-function #'new-value))
  "Associate KEY with VALUE in TRANSIENT.

This operation will avoid consing by mutating uniquely owned substructures of TRANSIENT when possible.

The return value will always be `eq' to TRANSIENT.

The MERGE-FUNCTION defines the behavior if DICT already contains a mapping for KEY. It is a function of three
arguments, (KEY OLD-VALUE NEW-VALUE), which returns a MERGED-VALUE. The default is `new-value', which returns
the NEW-VALUE as the MERGED-VALUE, effectively overwriting the OLD-VALUE in the resulting `dict'."
  (with-accessors ((hash-function %transient-hash-function)
                   (test-function %transient-test-function)
                   (body-key %transient-key)
                   (body-value %transient-value)
                   (body-type %transient-child-type)
                   (size %transient-size)
                   (id %transient-id))
      transient
    (if (null id)
        (error 'stale-transient
               :operation 'insert!
               :transient transient)
        (let* ((hash (funcall hash-function key)))
          (multiple-value-bind (new-body-key new-body-value new-type added-count)
              (node-insert id body-type body-key body-value key value hash 0 test-function hash-function merge-function)
            (setf body-key new-body-key)
            (setf body-value new-body-value)
            (setf body-type new-type)
            (incf size added-count)
            transient)))))

;;; REMOVE and helpers

;; All the REMOVE helper functions will return four values:
;; - NEW-KEY, the key part of the resulting node.
;; - NEW-VALUE, the value part of the resulting node.
;; - NEW-TYPE, the `child-type' of the resulting node.
;; - REMOVED-P, a boolean which is true if the size of the resulting node has changed by removing a child, or
;;   nil if no entry was removed.

(declaim (ftype (function (transient-id fixnum conflict-node array-index)
                          (values fixnum conflict-node (eql :conflict-node) (eql t) &optional))
                conflict-node-remove-at-logical-index))
(defun conflict-node-remove-at-logical-index (transient-id conflict-hash conflict-node logical-index)
  "Remove the mapping in CONFLICT-NODE at LOGICAL-INDEX.

Because `conflict-node's are not adjustable, this operation must always copy CONFLICT-NODE. The TRANSIENT-ID
will be installed in the new node, potentially allowing future transient operations to mutate it."
  (let* ((key-true-index (conflict-node-key-true-index logical-index))
         (new-node (%make-conflict-node :transient-id transient-id
                                        :length (logical-count-to-paired-length
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

(declaim (ftype (function (transient-id fixnum conflict-node t test-function)
                          (values t t child-type boolean &optional))
                conflict-node-remove))
(defun conflict-node-remove (transient-id conflict-hash conflict-node key test-function)
  "Remove the entry for KEY from CONFLICT-NODE, if any.

If CONFLICT-NODE does not contain an entry for KEY, the returned node will be `eq' to CONFLICT-NODE.

Because `conflict-node's are not adjustable, this operation must copy CONFLICT-NODE if the KEY is present. The
TRANSIENT-ID will be installed in the new node, potentially allowing future transient operations to mutate it.

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
        (conflict-node-remove-at-logical-index transient-id conflict-hash conflict-node logical-index))

    ;; If not present, return the conflict-node unchanged.
    (values conflict-hash conflict-node :conflict-node nil)))

(declaim (ftype (function (bitmap (mod #.+branch-rate+)) (values bitmap &optional))
                bitmap-remove-at)
         (inline bitmap-remove-at))
(defun bitmap-remove-at (bitmap index)
  (let* ((low (ldb (byte index 0) bitmap))
         (high (ldb (byte (- +branch-rate+ index 1)
                          (1+ index))
                    bitmap)))
    (dpb high
         (byte (- +branch-rate+ index)
               index)
         low)))

(declaim (ftype (function (transient-id bitmap hash-node hash-node-logical-index)
                          (values bitmap hash-node (eql :hash-node) (eql t) &optional))
                hash-node-remove-at-logical-index))
(defun hash-node-remove-at-logical-index (transient-id bitmap hash-node logical-index-to-remove)
  "Remove from HASH-NODE the child named by INDEX-TO-REMOVE and TRUE-INDEX-TO-REMOVE.

Because `hash-node's are not adjustable, this operation must copy HASH-NODE. The TRANSIENT-ID will be
installed in the new node, potentially allowing future transient operations to mutate it.

Precondition: HASH-NODE must `hash-node-contains-p' INDEX-TO-REMOVE, and TRUE-INDEX-TO-REMOVE must be the
              `hash-node-true-index' of INDEX-TO-REMOVE."
  (let* ((removed-bitmap (unset-bit bitmap
                                    logical-index-to-remove))
         (counted-index-to-remove (bitmap-logical-index-to-counted-index bitmap logical-index-to-remove))
         (removed-child-is-entry-p (bitmap-remove-at (hash-node-child-is-entry-p hash-node)
                                                     counted-index-to-remove))
         (removed-child-is-conflict-p (bitmap-remove-at (hash-node-child-is-conflict-p hash-node)
                                                        counted-index-to-remove))
         (removed-key-true-index (hash-node-key-true-index bitmap logical-index-to-remove))
         (new-node (%make-hash-node :transient-id transient-id
                                    :child-is-entry-p removed-child-is-entry-p
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

(declaim (ftype (function (transient-id bitmap hash-node hash-node-logical-index)
                          (values t t child-type (eql t) &optional))
                hash-node-maybe-promote-other-child))
(defun hash-node-maybe-promote-other-child (transient-id bitmap hash-node logical-index-to-discard)
  (let* ((logical-index-to-keep (bitmap-other-logical-index bitmap logical-index-to-discard))
         (child-type (hash-node-child-type hash-node bitmap logical-index-to-keep)))
    (multiple-value-bind (child-key child-value) (hash-node-logical-ref hash-node bitmap logical-index-to-keep)
      (if (eq child-type :hash-node)
          ;; Cannot promote, because the child is a hash-node with a greater shift than us. Build a new
          ;; one-entry hash-node to house the lonely child.
          (make-one-entry-hash-node transient-id child-key child-value child-type logical-index-to-keep t)

          ;; Can promote, because the child is an entry or a conflict-node
          (values child-key child-value child-type t)))))

;; Predeclaration for better type inference in recursive calls by `hash-node-remove'.
(declaim (ftype (function (transient-id child-type t t t fixnum shift test-function)
                          (values t t child-type boolean &optional))
                node-remove))

(declaim (ftype (function (transient-id bitmap hash-node
                           t fixnum hash-node-logical-index
                           shift test-function)
                          (values t t child-type boolean &optional))
                hash-node-remove))
(defun hash-node-remove (transient-id
                         bitmap hash-node
                         key hash logical-index
                         shift test-function)
  (flet ((return-unchanged ()
           (values bitmap hash-node :hash-node nil)))
    (if-let ((child-type (hash-node-child-type hash-node bitmap logical-index)))
      (multiple-value-bind (child-key child-value) (hash-node-logical-ref hash-node bitmap logical-index)
        (multiple-value-bind (new-child-key new-child-value new-child-type removedp)
            (node-remove transient-id
                         child-type child-key child-value
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
                 (hash-node-maybe-promote-other-child transient-id bitmap hash-node logical-index))

                ((null new-child-type)
                 ;; If we removed an entire child, the resulting hash node will have one fewer entries than
                 ;; HASH-NODE.
                 (hash-node-remove-at-logical-index transient-id bitmap hash-node logical-index))

                (:else
                 ;; If we removed from a child that still has other entries, splice the new child back
                 ;; in. This is the only branch that will potentially mutate HASH-NODE when it is an owned
                 ;; transient.
                 (hash-node-replace-at transient-id
                                       bitmap hash-node
                                       logical-index
                                       new-child-key new-child-value new-child-type
                                       t)))))

      (return-unchanged))))

(defun node-remove (transient-id body-type body-key body-value key hash shift test-function)
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
           (conflict-node-remove transient-id body-key body-value key test-function)
           (not-found)))

      (:hash-node (let* ((logical-index (extract-hash-part-for-shift shift hash)))
                    (if (bitmap-contains-p (the bitmap body-key)
                                           logical-index)
                        (hash-node-remove transient-id
                                          body-key body-value
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
              (node-remove nil
                           body-type body-key body-value
                           key hash
                           0
                           test-function)
            (if removed-p
                (%make-dict :size (1- size)
                            :hash-function hash-function
                            :test-function test-function
                            :key new-key
                            :value new-value
                            :child-type new-child-type)
                dict))))))

(declaim (ftype (function (transient t) (values transient &optional))
                remove!))
(defun remove! (transient key)
  "Make KEY unmapped in TRANSIENT.

This operation will avoid consing by mutating uniquely owned substructures of TRANSIENT when possible.

The return value will always be `eq' to TRANSIENT."
  (with-accessors ((hash-function %transient-hash-function)
                   (test-function %transient-test-function)
                   (body-key %transient-key)
                   (body-value %transient-value)
                   (body-type %transient-child-type)
                   (size %transient-size)
                   (id %transient-id))
      transient
    (if (null id)
        (error 'stale-transient
               :operation 'remove!
               :transient transient)
        (let* ((hash (funcall hash-function key)))
          (multiple-value-bind (new-key new-value new-child-type removed-p)
              (node-remove id
                           body-type body-key body-value
                           key hash
                           0
                           test-function)
            (when removed-p
              (setf body-key new-key)
              (setf body-value new-value)
              (setf body-type new-child-type)
              (decf size))
            transient)))))

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

(deftype test-function-designator ()
  '(or null
    (and symbol (not keyword) (not boolean))
    test-function))

(deftype hash-function-designator ()
  '(or null
    (and symbol (not keyword) (not boolean))
    hash-function))

(declaim (ftype (function (test-function-designator
                           hash-function-designator)
                          (values test-function hash-function &optional))
                normalize-test-and-hash-functions))
(defun normalize-test-and-hash-functions (test hash)
  (let* ((defaulted-test (or test '==))
         (hash-function (coerce-to-function (cond (hash
                                                   (coerce-to-function hash))
                                                  ((symbolp defaulted-test)
                                                   (test-hash-function defaulted-test))
                                                  (:else
                                                   (error 'no-hash-function-for-test
                                                          :test-function defaulted-test
                                                          :known-test-hash-functions *test-hash-functions*)))))
         (test-function (coerce-to-function defaulted-test)))
    (values test-function hash-function)))

;;; EMPTY constructor

(eval-when (:compile-toplevel :load-toplevel)
  (defparameter *hash-and-test-docstring*
    "If only TEST-FUNCTION is supplied, it must be a symbol. A suitable HASH-FUNCTION will be selected. See
`define-test-hash-function' for defining new pairs of test and hash functions.

If both TEST-FUNCTION and HASH-FUNCTION are supplied, they may be either symbols or function objects.

Symbols will be coerced into functions by `symbol-function', which will use the global function binding,
ignoring any local binding.

If not supplied, TEST-FUNCTION defaults to `immutable/hash:==', and HASH-FUNCTION to `immutable/hash:hash'."

    ;; TODO: add to docstring: laws for test and hash functions.
    ;; TODO: add to docstring: automatically generated listing of *TEST-HASH-FUNCTIONS*.
    ))

(declaim (ftype (function (&key (:test-function test-function-designator)
                                (:hash-function hash-function-designator))
                          (values dict &optional))
                empty))
(defun empty (&key test-function
                hash-function)
  #.(format nil "Construct an empty `dict' with the provided TEST-FUNCTION and HASH-FUNCTION.

~a"
            *hash-and-test-docstring*)

  (multiple-value-bind (test-function hash-function)
      (normalize-test-and-hash-functions test-function hash-function)
    (%make-dict :size 0
                :key nil
                :value nil
                :child-type nil
                :hash-function hash-function
                :test-function test-function)))

(declaim (ftype (function (&key (:test-function test-function-designator)
                                (:hash-function hash-function-designator))
                          (values transient &optional))
                empty-transient))
(defun empty-transient (&key test-function hash-function)
  #.(format nil "Construct an empty `transient' with the provided TEST-FUNCTION and HASH-FUNCTION.

~a"
            *hash-and-test-docstring*)
  (multiple-value-bind (test-function hash-function)
      (normalize-test-and-hash-functions test-function hash-function)
    (%make-transient :id (get-transient-id)
                     :size 0
                     :key nil
                     :value nil
                     :child-type nil
                     :test-function test-function
                     :hash-function hash-function)))

;;; Internal iteration facility

(declaim (ftype (function ((and vector (not simple-array)))
                          (values t &optional))
                stack-peek)
         ;; Inlining may allow specialization on element-type
         (inline stack-peek))
(defun stack-peek (stack)
  (aref stack (1- (fill-pointer stack))))

(declaim (ftype (function (t (and vector (not simple-array)))
                          (values t &optional))
                (setf stack-peek))
         ;; Inlining may allow specialization on element-type
         (inline stack-peek))
(defun (setf stack-peek) (new-value stack)
  (setf (aref stack (1- (fill-pointer stack)))
        new-value))

(symbol-macrolet ((body-type (%dict-child-type dict))
                  (body-key (%dict-key dict))
                  (body-value (%dict-value dict)))
  (define-generator dict ((dict dict))
                    "A generator which yields the (KEY VALUE) pairs of DICT as multiple values.

Entries are yielded in an arbitrary order. Internally, entries will be sorted by hash from low to high (well,
actually by the unsigned integer with the same two's complement representation as the signed hash from low to
high), so with a stable hash function the order will be a stable global total order except for hash conflicts,
but users should not rely on this behavior."
      ((node-stack (make-array (1+ +max-shift+)
                               :fill-pointer 0))
       (index-stack (make-array (1+ +max-shift+)
                                :fill-pointer 0
                                :element-type 'array-index))
       (leaf-is-conflict-p nil)
       (startedp nil))

      ()
    (labels ((push-node (node-type value)
               (vector-push value node-stack)
               (ecase node-type
                 (:conflict-node
                  (setf leaf-is-conflict-p t)
                  (vector-push +conflict-node-zero+ index-stack))
                 (:hash-node
                  (setf leaf-is-conflict-p nil)
                  (vector-push +hash-node-zero+ index-stack))))

             (yield-from-stack ()
               (if (zerop (fill-pointer node-stack))
                   (done)
                   (if leaf-is-conflict-p
                       (yield-from-conflict-node)
                       (yield-from-hash-node))))

             (yield-from-conflict-node ()
               (let* ((node (stack-peek node-stack))
                      (index (stack-peek index-stack)))
                 (declare (conflict-node node)
                          (array-index index))
                 (if (>= index (length node))
                     (pop-node)
                     ;; declaring THE ARRAY-INDEX here allows SBCL 2.3.2 darwin-arm64 to elide a branch which
                     ;; would allocate a bignum on overflow - pgoldman 2023-04-11.
                     (progn (incf (the array-index (stack-peek index-stack)) 2)
                            (values (svref node index)
                                    (svref node (1+ index)))))))

             (yield-from-hash-node ()
               (let* ((node (stack-peek node-stack))
                      (index (stack-peek index-stack)))
                 (declare (array-index index)
                          (hash-node node))
                 (if (>= index (length node))
                     (pop-node)
                     (let* ((counted-index (ash (- index +hash-node-zero+) -1)))
                       ;; declaring THE ARRAY-INDEX here allows SBCL 2.3.2 darwin-arm64 to elide a branch which
                       ;; would allocate a bignum on overflow - pgoldman 2023-04-11.
                       (incf (the array-index (stack-peek index-stack)) 2)
                       (cond ((bitmap-contains-p (hash-node-child-is-entry-p node) counted-index)
                              (values (svref node index)
                                      (svref node (1+ index))))

                             ((bitmap-contains-p (hash-node-child-is-conflict-p node) counted-index)
                              (push-node :conflict-node
                                         (svref node (1+ index)))
                              (yield-from-stack))

                             (:else
                              (push-node :hash-node
                                         (svref node (1+ index)))
                              (yield-from-stack)))))))

             (pop-node ()
               (if (<= (fill-pointer node-stack) 1)
                   (done)
                   (progn
                     (vector-pop node-stack)
                     (vector-pop index-stack)
                     (yield-from-stack)))))
      (cond ((null body-type)
             (done))

            ((eq body-type :entry)
             (if startedp
                 (done)
                 (progn
                   (setf startedp t)
                   (values body-key body-value))))

            ((not startedp)
             (setf startedp t)
             (push-node body-type body-value)
             (yield-from-stack))

            (:else (yield-from-stack))))))

;;; printing dicts

(defmethod print-object ((dict dict) stream)
  #+immutable-dict-debug
  (return-from print-object (call-next-method))

  (when (and *print-readably* (not *read-eval*))
    (error "Unable to readably print a DICT when *READ-EVAL* is nil."))
  ;; FIXME: handle readably printing DICTs with non-default hash and test functions
  (when *print-readably*
    (write-string "#." stream))
  ;; FIXME: haven't actually defined this ctor yet
  (write-string "(dict" stream)
  (with-dict-generator (generator dict)
    (iter (declare (declare-variables))
      (repeat (size dict))
      (for (values key value) = (advance generator))
      (write-char #\space stream)
      (write key :stream stream)
      (write-char #\space stream)
      (write value :stream stream)))
  (write-char #\) stream))

;;; batched insert operations

(define-condition malformed-plist (error)
  ((%operation :initarg :operation
               :accessor malformed-plist-operation)
   (%plist :initarg :plist
           :accessor malformed-plist-plist))
  (:report (lambda (c s)
             (format s "Malformed plist in ~s:~%  ~s"
                     (malformed-plist-operation c)
                     (malformed-plist-plist c)))))

(define-condition malformed-alist (error)
  ((%operation :initarg :operation
               :accessor malformed-alist-operation)
   (%alist :initarg :alist
           :accessor malformed-alist-alist))
  (:report (lambda (c s)
             (format s "Malformed alist in ~s:~%  ~s"
                     (malformed-alist-operation c)
                     (malformed-alist-alist c)))))

(declaim (ftype (function (dict list &optional merge-function) (values dict &optional))
                insert-alist
                insert-plist))
(defun insert-plist (dict plist &optional (merge-function #'new-value))
  "Return a new `dict' like DICT, but containing all the mappings from PLIST.

PLIST must be a proper list with an even-numbered length. Its entries will be treated as alternating keys and
values.

The MERGE-FUNCTION defines the behavior if DICT already contains a mapping for KEY. It is a function of three
arguments, (KEY OLD-VALUE NEW-VALUE), which returns a MERGED-VALUE. If the PLIST contains multiple entries for
the same key, the MERGE-FUNCTION will be invoked repeatedly, in a manner similar to `reduce', with the
previous MERGED-VALUE becoming the next OLD-VALUE. The default is `new-value', which returns the NEW-VALUE as
the MERGED-VALUE, effectively overwriting the OLD-VALUE in the resulting `dict'."
  (if (null plist)
      dict
      (let* ((transient (transient dict)))
        (labels ((insert-pair (list)
                   (if (not (and (consp list)
                                 (consp (rest list))))
                       (error 'malformed-plist
                              :plist plist
                              :operation 'insert-plist)
                       (destructuring-bind (key value &rest tail) list
                         (insert! transient key value merge-function)
                         (when tail (insert-pair tail))))))
          (insert-pair plist))
        (persistent! transient))))

(defun insert-alist (dict alist &optional (merge-function #'new-value))
  "Return a new `dict' like DICT, but containing all the mappings from ALIST.

ALIST must be a proper list whose elements are all conses. Each cons will be destructured as (KEY . VALUE).

The MERGE-FUNCTION defines the behavior if DICT already contains a mapping for KEY. It is a function of three
arguments, (KEY OLD-VALUE NEW-VALUE), which returns a MERGED-VALUE. If the ALIST contains multiple entries for
the same key, the MERGE-FUNCTION will be invoked repeatedly, in a manner similar to `reduce', with the
previous MERGED-VALUE becoming the next OLD-VALUE. The default is `new-value', which returns the NEW-VALUE as
the MERGED-VALUE, effectively overwriting the OLD-VALUE in the resulting `dict'."
  (if (null alist)
      dict
      (let* ((transient (transient dict)))
        (labels ((insert-pair (list)
                   (destructuring-bind (entry &rest tail) list
                     (if (not (and (consp entry)
                                   (listp tail)))
                         (error 'malformed-alist
                                :alist alist
                                :operation 'insert-alist)
                         (progn
                           (insert! transient (car entry) (cdr entry) merge-function)
                           (when tail (insert-pair tail)))))))
          (insert-pair alist))
        (persistent! transient))))

(declaim (ftype (function (dict &rest t) (values dict &optional))
                insert-multiple))
(defun insert-multiple (dict &rest keys-and-values)
  "Return a new `dict' like DICT, but containing all the mappings specified by KEYS-AND-VALUES.

There must be an even number of KEYS-AND-VALUES. They will be treated as alternating keys and values.

Entries from the KEYS-AND-VALUES will overwrite entries in DICT, and later entries in KEYS-AND-VALUES will
overwrite earlier entries.

`insert-multiple' does not support supplying a `merge-function'. If you want to supply a `merge-function',
construct a `transient' and repeatedly call `insert!'."
  (declare (dynamic-extent keys-and-values))
  (insert-plist dict keys-and-values))

(declaim (ftype (function (dict &rest t) (values dict &optional))
                remove-multiple))
(defun remove-multiple (dict &rest keys)
  "Return a new `dict' like DICT, but with the entries corresponding to each of the KEYS removed.

Any of the KEYS which are not present in DICT will be silently ignored."
  (declare (dynamic-extent keys))
  (if (null keys)
      dict
      (let* ((transient (transient dict)))
        (labels ((remove-one (list)
                   (destructuring-bind (key &rest tail) list
                     (remove! transient key)
                     (when tail
                       (remove-one tail)))))
          (remove-one keys))
        (persistent! transient))))

;;; convenient constructor

(declaim (ftype (function (&rest t) (values dict &optional))
                dict))
(defun dict (&rest keys-and-values)
  "Construct a `dict' containing all the mappings specified by KEYS-AND-VALUES.

There must be an even number of KEYS-AND-VALUES. They will be treated as alternating keys and values.

If the same key appears multiple times in KEYS-AND-VALUES, later values will overwrite earlier values."
  (declare (dynamic-extent keys-and-values))
  (insert-plist (empty) keys-and-values))

;;; user-facing iteration

(declaim (ftype (function (dict (function (t t) (values &rest t))) (values &optional))
                for-each))
(defun for-each (dict func)
  "Apply FUNC to each (KEY VALUE) entry in DICT, discarding the results.

FUNC should be a function of two arguments, the KEY and VALUE.

Entries in DICT are traversed in an undefined order. You can count on FUNC being invoked exactly (size DICT)
times, once for each entry in DICT, but that's where the guarantees end."
  (with-dict-generator (generator dict)
    (iter (declare (declare-variables))
      (repeat (size dict))
      (multiple-value-call func (advance generator))))
  (values))

(declaim (ftype (function (dict (function (t) (values t &rest t)))
                          (values dict &optional))
                map-values))
(defun map-values (dict func)
  "Apply FUNC to each VALUE in DICT, and collect the result into a new `dict' which, for each (KEY VALUE) entry in DICT, maps KEY to (func VALUE).

FUNC should be a function of one argument, a VALUE. The associated KEYs are not passed to FUNC.

For users with strongly-typed backgrounds, this is the operation which implements `Functor' for (Dict :KEY).

This operation runs in O(N log_{+branch_rate+}N) in the size of DICT (assuming FUNC runs in constant time),
and does not allocate except to construct the nodes that will be in the resulting `dict'. This is a notable
contrast to implementing the same interface in terms of `for-each', `empty' and `insert', which would
unnecessarily allocate temporary nodes during insertion."
  (labels ((map-entry (value)
             (funcall func value))
           (map-conflict-node (conflict-node)
             (let* ((new-node (%make-conflict-node :length (conflict-node-paired-count conflict-node))))
               (iter (declare (declare-variables))
                 (for logical-index below (conflict-node-logical-length conflict-node))
                 (for (values key value) = (conflict-node-logical-ref conflict-node logical-index))
                 (for new-value = (map-entry value))
                 (set-conflict-node-logical-entry new-node logical-index key new-value))
                new-node))
           (map-hash-node (hash-node)
             (let* ((new-node (%make-hash-node :child-is-entry-p (hash-node-child-is-entry-p hash-node)
                                               :child-is-conflict-p (hash-node-child-is-conflict-p hash-node)
                                               :length (hash-node-paired-count hash-node))))
               (iter (declare (declare-variables))
                 (for counted-index below (hash-node-logical-count hash-node))
                 (for true-index = (hash-node-paired-index-to-true-index (ash counted-index 1)))
                 (for key = (hash-node-true-ref hash-node true-index))
                 (for value = (hash-node-true-ref hash-node (1+ true-index)))
                 (for new-value = (cond ((bitmap-contains-p (hash-node-child-is-entry-p hash-node) counted-index)
                                         (map-entry value))

                                        ((bitmap-contains-p (hash-node-child-is-conflict-p hash-node) counted-index)
                                         (map-conflict-node value))

                                        (:else
                                         (map-hash-node value))))
                 (setf (hash-node-true-ref new-node true-index)
                       key)
                 (setf (hash-node-true-ref new-node (1+ true-index))
                       new-value))
               new-node)))
    (%make-dict :size (size dict)
                :hash-function (hash-function dict)
                :test-function (test-function dict)
                :child-type (%dict-child-type dict)
                :key (%dict-key dict)
                :value (ecase (%dict-child-type dict)
                         ((null) nil)
                         (:entry (map-entry (%dict-value dict)))
                         (:conflict-node (map-conflict-node (%dict-value dict)))
                         (:hash-node (map-hash-node (%dict-value dict)))))))

(defmacro do ((key-binding value-binding dict) &body body)
  "Evaluate the BODY for each entry of DICT with KEY-BINDING and VALUE-BINDING bound to the KEY and VALUE of the entry, respectively.

Returns no values.

This is a convenience macro which expands to a `for-each' call. All notes on `for-each' apply."
  `(flet ((do-function (,key-binding ,value-binding)
            ,@body))
     (declare (dynamic-extent #'do-function))
     (for-each ,dict #'do-function)))

;;; UNION to combine `dict's

(declaim (ftype (function (dict dict merge-function) (values dict &optional))
                union-different-test-or-hash))
(defun union-different-test-or-hash (left right merge-function)
  "Merge two `dict's which have different HASH-FUNCTION and TEST-FUNCTION.

The resulting `dict' will have the HASH-FUNCTION and TEST-FUNCTION from LEFT.

Because two `dict's with distinct hash and test functions will have different structures, i.e. will store
equivalent entries in different locations, this operation can do no better than iterating over RIGHT and
inserting all of its entries into LEFT."
  (let* ((transient (transient left)))
    (do (key value right)
        (insert! transient key value merge-function))
    (persistent! transient)))

;; The MERGE-FUNCTION interface on `union' specifies that the order of its LEFT- and RIGHT-VALUE arguments is
;; the same as the order of the `dict' arguments to `union'; this allows `old-value' and `new-value' to
;; implement left- and right-bias, respectively. As a result, anywhere in `merge-nodes' (or functions that
;; call it) where we reverse the order of the two node arguments, we also have to reverse the argument order
;; of the MERGE-FUNCTION.
(defmacro with-inverted-merge-function ((inverted-name merge-function-name) &body body)
  `(flet ((,inverted-name (key left-value right-value)
            (funcall ,merge-function-name key right-value left-value)))
     (declare (dynamic-extent #',inverted-name))
     ,@body))

(declaim (ftype (function (t t
                           t t
                           shift
                           hash-function test-function merge-function)
                          (values t t child-type size &optional))
                merge-entries))
(defun merge-entries (left-key left-value
                      right-key right-value
                      shift
                      hash-function test-function merge-function
                      &aux (left-hash (funcall hash-function left-key))
                        (right-hash (funcall hash-function right-key)))
  (cond ((not (= left-hash right-hash))
         ;; If the hashes are different, make a `hash-node' to contain both entries.
         (promote-node nil
                       left-key left-value left-hash :entry
                       right-key right-value right-hash :entry
                       shift
                       ;; No entries were merged, so return 0 as a fourth value.
                       0))

        ((funcall test-function left-key right-key)
         ;; If the entries are the same, use the MERGE-FUNCTION to get a new entry
         (values left-key

                 (funcall merge-function left-key left-value right-value)

                 :entry

                 ;; We merged one entry.
                 1))

        (:else
         ;; If the entries are a hash conflict, make a `conflict-node'
         (make-conflict-node nil
                             left-hash
                             2

                             ;; No entries were merged, so return 0 as a fourth value.
                             0

                             left-key left-value
                             right-key right-value))))

(declaim (ftype (function (hash conflict-node
                           t t
                           shift
                           hash-function test-function merge-function)
                          (values t t child-type size &optional))
                merge-entry-into-conflict-node))
(defun merge-entry-into-conflict-node (conflict-hash conflict-node
                                       key value
                                       shift
                                       hash-function test-function merge-function
                                       &aux (new-hash (funcall hash-function key)))
  (if (= conflict-hash new-hash)
      ;; If we have the same hash, either we need to merge, or we're adding to the conflict node.
      (if-let ((logical-index (conflict-node-logical-index-of conflict-node key test-function)))
        (let* ((old-value (conflict-node-logical-value-ref conflict-node logical-index))
               (merged-value (funcall merge-function key old-value value)))
          (conflict-node-copy-replace-at-logical-index nil
                                                       conflict-node conflict-hash
                                                       key merged-value
                                                       logical-index
                                                       ;; We merged one entry.
                                                       1))

        (add-to-conflict-node nil
                              conflict-hash conflict-node
                              key value
                              ;; No entries were merged.
                              0))

      ;; If we don't have the same hash, promote to a `hash-node'
      (promote-node nil
                    conflict-hash conflict-node conflict-hash :conflict-node
                    key value new-hash :entry
                    shift

                    ;; No entries were merged
                    0)))

(declaim (ftype (function (conflict-node) (values list &optional))
                conflict-node-alist))
(defun conflict-node-alist (conflict-node)
  (iter (declare (declare-variables))
    (for logical-index below (conflict-node-logical-length conflict-node))
    (for (values key value) = (conflict-node-logical-ref conflict-node logical-index))
    ;; AT BEGINNING saves an `nreverse'
    (collect (cons key value) at beginning)))

(declaim (ftype (function (list list test-function merge-function) (values list size &optional))
                alist-merge))
(defun alist-merge (left right test-function merge-function)
  (labels ((loop-for-entry-in-left (left right acc num-merged)
             (declare (size num-merged))
             (cond ((and (not left) (not right)) (values acc num-merged))

                   ((not left) (values (append right acc) num-merged))

                   ((not right) (values (append left acc) num-merged))

                   (:else (destructuring-bind ((key . value) &rest left) left
                            (loop-find-match-in-right key value left right nil acc num-merged)))))

           (loop-find-match-in-right (left-key left-value left right-to-search right-already-searched acc num-merged)
             (declare (size num-merged))
             (if (null right-to-search)
                 (loop-for-entry-in-left left right-already-searched (acons left-key left-value acc) num-merged)
                 (destructuring-bind ((right-key . right-value) &rest right-to-search) right-to-search
                   (if (funcall test-function left-key right-key)

                       (loop-for-entry-in-left left
                                               (append right-to-search right-already-searched)
                                               (acons left-key (funcall merge-function left-key left-value right-value) acc)
                                               (1+ num-merged))

                       (loop-find-match-in-right left-key left-value left
                                                 right-to-search
                                                 (acons right-key right-value right-already-searched)
                                                 acc
                                                 num-merged))))))
    (loop-for-entry-in-left left right nil 0)))

(declaim (ftype (function (hash conflict-node
                           hash conflict-node
                           shift
                           test-function merge-function)
                          (values t t child-type size &optional))
                merge-conflict-nodes))
(defun merge-conflict-nodes (left-hash left-node
                             right-hash right-node
                             shift
                             test-function merge-function)
  (if (/= left-hash right-hash)
      ;; If we have different hashes, promote to a `hash-node'
      (promote-node nil
                    left-hash left-node left-hash :conflict-node
                    right-hash right-node right-hash :conflict-node
                    shift
                    ;; No entries were merged
                    0)

      ;; If we have the same hash, the nasty case: we have to do a setwise union on the two arrays.
      (let* ((unmatched-left (conflict-node-alist left-node))
             (unmatched-right (conflict-node-alist right-node)))
        (multiple-value-bind (merged-alist num-merged)
            (alist-merge unmatched-left unmatched-right test-function merge-function)
          (let* ((new-length (- (+ (conflict-node-logical-length left-node)
                                   (conflict-node-logical-length right-node))
                                num-merged))
                 (new-node (%make-conflict-node :length (logical-count-to-paired-length new-length))))
            (iter (declare (declare-variables))
              (for logical-index below new-length)
              (for (key . value) in merged-alist)
              (set-conflict-node-logical-entry new-node logical-index key value))
            (values left-hash new-node :conflict-node num-merged))))))

(declaim (ftype (function (child-type t t
                           child-type t t
                           shift
                           hash-function test-function merge-function)
                          (values t t child-type size &optional))
                merge-nodes))

(declaim (ftype (function (bitmap hash-node
                           (member :conflict-node :entry) t t
                           shift
                           hash-function test-function merge-function)
                          (values bitmap hash-node (eql :hash-node) size &optional))
                merge-child))
(defun merge-child (bitmap hash-node
                    new-type new-key new-value
                    shift
                    hash-function test-function merge-function)
  (let* ((new-hash (ecase new-type
                     (:conflict-node new-key)
                     (:entry (funcall hash-function new-key))))
         (new-idx (extract-hash-part-for-shift shift new-hash)))
    (if (bitmap-contains-p bitmap new-idx)
        ;; If we already have a child there, merge the two.
        (let* ((old-type (hash-node-child-type hash-node bitmap new-idx)))
          (multiple-value-bind (old-key old-value)
              (hash-node-logical-ref hash-node bitmap new-idx)
            (multiple-value-bind (merged-key merged-value merged-type num-merged)
                (merge-nodes old-type old-key old-value
                             new-type new-key new-value
                             (1+ shift)
                             hash-function test-function merge-function)
              (hash-node-copy-replace-at nil
                                         bitmap hash-node
                                         new-idx
                                         merged-key merged-value merged-type
                                         num-merged))))

        ;; If we don't have a child there, insert.
        (hash-node-insert-at nil
                             bitmap hash-node
                             new-idx
                             new-key new-value new-type
                             ;; We didn't merge any entries.
                             0))))

(declaim (ftype (function (bitmap hash-node
                           bitmap hash-node
                           shift
                           hash-function test-function merge-function)
                          (values bitmap hash-node (eql :hash-node) size))
                merge-hash-nodes))
(defun merge-hash-nodes (left-bitmap left-node
                         right-bitmap right-node
                         shift
                         hash-function test-function merge-function)
  (let* ((merged-bitmap (logior left-bitmap right-bitmap))
         (merged-size (logcount merged-bitmap))
         (new-node (%make-hash-node :child-is-entry-p 0
                                    :child-is-conflict-p 0
                                    :length (logical-count-to-paired-length merged-size)))
         (num-merged 0))
    (declare (size num-merged))
    (iter (declare (declare-variables))
      (for logical-index below +branch-rate+)
      (for left-type = (hash-node-child-type left-node left-bitmap logical-index))
      (for right-type = (hash-node-child-type right-node right-bitmap logical-index))
      (cond ((and left-type right-type)

             (multiple-value-bind (left-key left-value)
                 (hash-node-logical-ref left-node left-bitmap logical-index)
               (multiple-value-bind (right-key right-value)
                   (hash-node-logical-ref right-node right-bitmap logical-index)
                 (multiple-value-bind (child-key child-value child-type child-num-merged)
                     (merge-nodes left-type left-key left-value
                                  right-type right-key right-value
                                  (1+ shift)
                                  hash-function test-function merge-function)
                   (incf num-merged child-num-merged)
                   (hash-node-set-at-logical-index merged-bitmap new-node logical-index
                                                   child-key child-value child-type
                                                   nil)))))

            (left-type
             (multiple-value-bind (left-key left-value)
                 (hash-node-logical-ref left-node left-bitmap logical-index)
               (hash-node-set-at-logical-index merged-bitmap new-node logical-index
                                               left-key left-value left-type
                                               nil)))

            (right-type
             (multiple-value-bind (right-key right-value)
                 (hash-node-logical-ref right-node right-bitmap logical-index)
               (hash-node-set-at-logical-index merged-bitmap new-node logical-index
                                               right-key right-value right-type
                                               nil)))

            (:else nil)))

    (values merged-bitmap new-node :hash-node num-merged)))

(defun merge-nodes (left-type left-key left-value
                    right-type right-key right-value
                    shift
                    hash-function test-function merge-function)
  (cond ((null left-type) (values right-key right-value right-type 0))
        ((null right-type) (values left-key left-value left-type 0))

        ;; past here, neither side is null

        ((and (eq left-type :hash-node) (eq right-type :hash-node))
         (merge-hash-nodes left-key left-value
                           right-key right-value
                           shift
                           hash-function test-function merge-function))

        ((eq left-type :hash-node)
         (merge-child left-key left-value
                      right-type right-key right-value
                      shift
                      hash-function test-function merge-function))

        ((eq right-type :hash-node)
         (with-inverted-merge-function (inverted-merge-function merge-function)
           (merge-child right-key right-value
                        left-type left-key left-value
                        shift
                        hash-function test-function #'inverted-merge-function)))

        ;; past here, neither side is a `:hash-node'

        ((and (eq left-type :conflict-node) (eq right-type :conflict-node))
         (merge-conflict-nodes left-key left-value
                               right-key right-value
                               shift
                               test-function merge-function))

        ((eq left-type :conflict-node)
         (merge-entry-into-conflict-node left-key left-value
                                         right-key right-value
                                         shift
                                         hash-function test-function merge-function))

        ((eq right-type :conflict-node)
         (with-inverted-merge-function (inverted-merge-function merge-function)
           (merge-entry-into-conflict-node right-key right-value
                                           left-key left-value
                                           shift
                                           hash-function test-function #'inverted-merge-function)))

        ;; past here, neither side is a `:conflict-node'

        (:else
         (merge-entries left-key left-value
                        right-key right-value
                        shift
                        hash-function test-function merge-function))))

(declaim (ftype (function (dict dict merge-function) (values dict &optional))
                union-same-test-and-hash))
(defun union-same-test-and-hash (left right merge-function
                                 &aux (hash-function (hash-function left))
                                   (test-function (test-function left)))
  (multiple-value-bind (new-key new-value new-type num-merged)
      (merge-nodes (%dict-child-type left) (%dict-key left) (%dict-value left)
                   (%dict-child-type right) (%dict-key right) (%dict-value right)
                   0
                   hash-function test-function merge-function)
    (%make-dict :size (- (+ (size left) (size right)) num-merged)
                :hash-function hash-function
                :test-function test-function
                :child-type new-type
                :key new-key
                :value new-value)))

(declaim (ftype (function (dict dict &optional merge-function) (values dict &optional))
                union))
(defun union (left right &optional (merge-function #'new-value))
  "Construct a new `dict' containing all the entries from both LEFT and RIGHT.

The MERGE-FUNCTION defines the behavior when a KEY is present in both LEFT and RIGHT. In that case, it is
invoked with (KEY LEFT-VALUE RIGHT-VALUE), and should return a MERGED-VALUE. The resulting `dict' will map KEY
to MERGED-VALUE. The default is `new-value', which selects the RIGHT-VALUE.

If LEFT and RIGHT have different HASH-FUNCTIONs and/or TEST-FUNCTIONs, the resulting `dict' will use the
HASH-FUNCTION and TEST-FUNCTION from LEFT. In that case, this operation is relatively inefficient; it iterates
over RIGHT as if by `for-each' and uses `insert!' to add each entry to a `transient' derived from LEFT. This
may allocate intermediate nodes not necessary to represent the result.

If LEFT and RIGHT have the same HASH-FUNCTION and TEST-FUNCTION (by `eq'), a more efficient implementation
will walk the structure of LEFT and RIGHT in parallel, allocating only enough structure to represent the
resulting `dict'."
  (if (and (eq (test-function left) (test-function right))
           (eq (hash-function left) (hash-function right)))
      (union-same-test-and-hash left right merge-function)
      (union-different-test-or-hash left right merge-function)))

;;; REHASH to change the hash and test function of a dict

(define-condition rehash-conflict (error)
  ((%key :initarg :key
         :accessor rehash-conflict-key)
   (%value-1 :initarg :value-1
             :accessor rehash-conflict-value-1)
   (%value-2 :initarg :value-2
             :accessor rehash-conflict-value-2)
   (%source :initarg :source
            :accessor rehash-conflict-source)
   (%new-test-function :initarg :new-test-function
                       :accessor rehash-conflict-new-test-function)
   (%new-hash-function :initarg :new-hash-function
                       :accessor rehash-conflict-new-hash-function))
  (:report (lambda (c s)
             (format s "Rehash introduces conflict on key ~s with values ~s and ~s

Rehashing the dict:
  ~s
from
  :TEST-FUNCTION ~s
  :HASH-FUNCTION ~s
to
  :TEST-FUNCTION ~s
  :HASH-FUNCTION ~s
causes a conflict between two entries with keys equivalent to
  ~s
with values
  ~s
  ~s"
                     (rehash-conflict-key c)
                     (rehash-conflict-value-1 c)
                     (rehash-conflict-value-2 c)
                     (rehash-conflict-source c)
                     (test-function (rehash-conflict-source c))
                     (hash-function (rehash-conflict-source c))
                     (rehash-conflict-new-test-function c)
                     (rehash-conflict-new-hash-function c)
                     (rehash-conflict-key c)
                     (rehash-conflict-value-1 c)
                     (rehash-conflict-value-2 c)))))

(declaim (ftype (function (dict test-function hash-function t t t) nil)
                error-rehash-conflict))
(defun error-rehash-conflict (source new-test-function new-hash-function key value-1 value-2)
  ;; TODO: Bind restarts.
  (error 'rehash-conflict
         :key key
         :value-1 value-1
         :value-2 value-2
         :source source
         :new-test-function new-test-function
         :new-hash-function new-hash-function))

(declaim (ftype (function (dict &key (:test-function test-function-designator)
                                (:hash-function hash-function-designator)
                                (:merge-function merge-function))
                          (values dict &optional))
                rehash))
(defun rehash (dict &key test-function
                      hash-function
                      merge-function)
  #.(format nil "Create a new `dict' containing all the mappings from DICT, but with new a new TEST-FUNCTION and HASH-FUNCTION.

If the new TEST-FUNCTION and HASH-FUNCTION treat multiple keys from DICT as equivalent which are not
equivalent under the original test-function and hash-function of DICT, the MERGE-FUNCTION will be called to
combine the values of the conflicting entries. If more than two entries conflict, the MERGE-FUNCTION will be
called multiple times, in a manner similar to `cl:reduce'. The order in which conflicting entries are passed
to the MERGE-FUNCTION is neither random nor deterministic, so users should not depend on it. As a result,
MERGE-FUNCTIONs should be associative.

The default MERGE-FUNCTION signals an error of class `rehash-conflict'.

The TEST-FUNCTION and HASH-FUNCTION will be used for the resulting `dict'. They are treated the same way as
the corresponding arguments to `empty' and `empty-transient'.

~s"
            *hash-and-test-docstring*)
  (let* ((transient (empty-transient :test-function test-function
                                     :hash-function hash-function))

         ;; Read the test- and hash-functions back out of the TRANSIENT for error reporting now that they've
         ;; been normalized.
         (test (test-function transient))
         (hash (hash-function transient))
         (merge-function (or merge-function
                             (lambda (k o n)
                               (error-rehash-conflict dict test hash k o n)))))
    (declare (dynamic-extent merge-function))
    (do (key value dict)
        (insert! transient key value merge-function))
    (persistent! transient)))

;;; Conversions to/from CL mappings

(define-condition convert-overwrite (error)
  ((%key :initarg :key
         :accessor convert-overwrite-key)
   (%old-value :initarg :old-value
               :accessor convert-overwrite-old-value)
   (%new-value :initarg :new-value
               :accessor convert-overwrite-new-value)
   (%operation :initarg :operation
               :accessor convert-overwrite-operation)
   (%source :initarg :source
            :accessor convert-overwrite-source))
  (:report (lambda (c s)
             (format s "Attempt to overwrite in ~s with :ERROR-ON-OVERWRITE T:

Found duplicate mappings for key ~s: ~s and ~s
in source collection ~s"
                     (convert-overwrite-operation c)
                     (convert-overwrite-key c)
                     (convert-overwrite-old-value c)
                     (convert-overwrite-new-value c)
                     (convert-overwrite-source c)))))

(declaim (ftype (function (hash-table
                           &key (:test-function test-function-designator)
                           (:hash-function hash-function-designator)
                           (:error-on-overwrite boolean))
                          (values dict &optional))
                from-hash-table))
(defun from-hash-table (hash-table &key test-function hash-function (error-on-overwrite t))
  #.(format nil "Construct a `dict' containing all the mappings in HASH-TABLE.

If TEST-FUNCTION is unsupplied, the hash-table-test of HASH-TABLE will be used for the resulting `dict', and a
compatible hash-function will be chosen by the same method as `empty'. Currently, this only works for `equal'
hash tables, and selects `sxhash' as the hash-function. If TEST-FUNCTION is unsupplied and HASH-TABLE has a
test other than `equal', an error of class `no-hash-function-for-test' will be signaled.

If supplied, TEST-FUNCTION and HASH-FUNCTION will be used as the resulting `dict's test- and
hash-functions. If these are different from the hash-table-test of HASH-TABLE, multiple entries from the
HASH-TABLE may be considered equivalent. In that case:

- Unless :ERROR-ON-OVERWRITE is supplied and nil, if the HASH-TABLE contains multiple keys considered
  equivalent by the TEST-FUNCTION and HASH-FUNCTION, an error of class `convert-overwrite' will be signaled.
- If :ERROR-ON-OVERWRITE nil is supplied, one of the entries with equivalent keys will be chosen
  arbitrarily. The choice is neither random nor deterministic, so users should not depend on its behavior.

~s"
            *hash-and-test-docstring*)
  (let* ((transient (empty-transient :test-function (or test-function (hash-table-test hash-table))
                                     :hash-function hash-function))
         (merge-function (if error-on-overwrite
                             (lambda (k o n)
                               ;; TODO: Bind restarts:
                               ;; - Use old value.
                               ;; - Use new value.
                               ;; - Provide value.
                               (error 'convert-overwrite
                                      :key k
                                      :old-value o
                                      :new-value n
                                      :operation 'from-hash-table
                                      :source hash-table))
                             #'new-value)))
    (declare (dynamic-extent merge-function))
    (iter (declare (declare-variables))
      (for (key value) in-hashtable hash-table)
      (insert! transient
               key value
               merge-function))
    (persistent! transient)))

(deftype hash-table-test-name ()
  '(member eq eql equal equalp))

(define-condition invalid-hash-table-test (error)
  ((%test :initarg :test
          :accessor invalid-hash-table-test-test))
  (:report (lambda (c s)
             (format s "Cannot construct a HASH-TABLE with :TEST ~s"
                     (invalid-hash-table-test-test c)))))

(declaim (ftype (function (dict
                           &key (:test (or null hash-table-test-name function))
                           (:error-on-overwrite boolean))
                          (values hash-table &optional))
                to-hash-table))
(defun to-hash-table (dict &key test (error-on-overwrite t))
  "Construct a `hash-table' containing all the mappings in DICT.

If TEST is unsupplied, the resulting `hash-table' will use the test-function of DICT as its test. Currently,
this only works for `equal' dicts. If TEST is unsupplied and DICT has a test-function other than `equal', an
error of class `invalid-hash-table-test' will be signaled.

If TEST is supplied, it must be one of the four standard hash-table tests: `eq', `eql', `equal' or
`equalp'. Symbols or function objects are both acceptable. If a TEST is supplied which is not a standard
hash-table test, an error of class `invalid-hash-table-test' will be signaled.

If the supplied TEST is different from the test-function of DICT, multiple entries from the DICT may be
considered equivalent. In that case:

- Unless :ERROR-ON-OVERWRITE is supplied and nil, if the HASH-TABLE contains multiple keys considered
  equivalent by the TEST-FUNCTION and HASH-FUNCTION, an error of class `convert-overwrite' will be signaled.
- If :ERROR-ON-OVERWRITE nil is supplied, one of the entries with equivalent keys will be chosen
  arbitrarily. The choice is neither random nor deterministic, so users should not depend on its behavior."
  (let* ((test (or test (test-function dict))))
    (unless (member test (list 'eq 'eql 'equal 'equalp
                               #'eq #'eql #'equal #'equalp))
      (error 'invalid-hash-table-test
             :test test))
    (let* ((hash-table (make-hash-table :test test
                                        ;; Aim for a density of 2/3, for no particular reason other than that
                                        ;; it seems sensible.
                                        ;; TODO: Choose a target density in a more principled way?
                                        :size (the (and fixnum unsigned-byte)
                                                   (ceiling (* (size dict) 1.5))))))
      (do (key value dict)
          (when error-on-overwrite
            (multiple-value-bind (old-value presentp)
                (gethash key hash-table)
              ;; TODO: Bind restarts:
              ;; - Use old value.
              ;; - Use new value.
              ;; - Provide value.
              (when presentp
                (error 'convert-overwrite
                       :key key
                       :old-value old-value
                       :new-value value
                       :operation 'to-hash-table
                       :source dict))))
        (setf (gethash key hash-table) value))
      hash-table)))

(declaim (ftype (function (list
                           &key (:test-function test-function-designator)
                           (:hash-function hash-function-designator)
                           ;; TODO: Consider accepting a :MERGE-FUNCTION instead of an :ERROR-ON-OVERWRITE
                           ;;       flag.
                           (:error-on-overwrite boolean))
                          (values dict &optional))
                from-alist
                from-plist))
(defun from-alist (alist &key test-function hash-function (error-on-overwrite t))
  #.(format nil "Construct a `dict' containing all the mappings in ALIST.

Because alists are not uniqued collections, ALIST may contain multiple mappings for keys which are equivalent
under the chosen TEST-FUNCTION and HASH-FUNCTION. In that case:

- Unless :ERROR-ON-OVERWRITE is supplied and nil, an error of class `convert-overwrite' will be signaled.
- If :ERROR-ON-OVERWRITE nil is supplied, the earliest entry for each key will be selected. This allows
  `acons' or `push' to \"overwrite\" entries in the ALIST. Note that this behavior differs from
  `insert-alist', which by default will select the latest entry for each key.

The TEST-FUNCTION and HASH-FUNCTION will be used for the resulting `dict'. They are treated the same way as
the corresponding arguments to `empty' and `empty-transient'.

~s"
            *hash-and-test-docstring*)
  (if (null alist)
      (empty :test-function test-function
             :hash-function hash-function)

      (let* ((transient (empty-transient :test-function test-function :hash-function hash-function))
             (merge-function (if error-on-overwrite
                                 (lambda (k o n)
                                   ;; TODO: Bind restarts:
                                   ;; - Use old value (named continue as the default?).
                                   ;; - Use new value.
                                   ;; - Provide value.
                                   (error 'convert-overwrite
                                          :key k
                                          :old-value o
                                          :new-value n
                                          :operation 'from-alist
                                          :source alist))

                                 ;; Prefer earlier entries in the ALIST, so that `acons' and `push' overwrite
                                 ;; entries.
                                 #'old-value)))
        (labels ((insert-pair (list)
                   (destructuring-bind (entry &rest tail) list
                     (if (not (and (consp entry)
                                   (listp tail)))
                         (error 'malformed-alist
                                :alist alist
                                :operation 'from-alist)
                         (progn
                           (insert! transient (car entry) (cdr entry) merge-function)
                           (when tail (insert-pair tail)))))))
          (insert-pair alist))
        (persistent! transient))))

(defun from-plist (plist &key test-function hash-function (error-on-overwrite t))
  #.(format nil "Construct a `dict' containing all the mappings in PLIST.

Because plists are not uniqued collections, PLIST may contain multiple mappings for keys which are equivalent
under the chosen TEST-FUNCTION and HASH-FUNCTION. In that case:

- Unless :ERROR-ON-OVERWRITE is supplied and nil, an error of class `convert-overwrite' will be signaled.
- If :ERROR-ON-OVERWRITE nil is supplied, the earliest entry for each key will be selected. This allows
  `list*' or `push' to \"overwrite\" entries in the PLIST. Note that this behavior differs from
  `insert-plist', which by default will select the latest entry for each key.

The TEST-FUNCTION and HASH-FUNCTION will be used for the resulting `dict'. They are treated the same way as
the corresponding arguments to `empty' and `empty-transient'.

~s"
            *hash-and-test-docstring*)
  (if (null plist)
      (empty :test-function test-function
             :hash-function hash-function)

      (let* ((transient (empty-transient :test-function test-function :hash-function hash-function))
             (merge-function (if error-on-overwrite
                                 (lambda (k o n)
                                   ;; TODO: Bind restarts:
                                   ;; - Use old value (named continue as the default?).
                                   ;; - Use new value.
                                   ;; - Provide value.
                                   (error 'convert-on-overwrite
                                          :key k
                                          :old-value o
                                          :new-value n
                                          :operation 'from-plist
                                          :source plist))

                                 ;; Prefer earlier entries in the PLIST, so that `list*' and `push' overwrite
                                 ;; entries.
                                 #'old-value)))
        (labels ((insert-pair (list)
                   (if (not (and (consp list)
                                 (consp (rest list))))
                       (error 'malformed-plist
                              :plist plist
                              :operation 'from-plist)
                       (destructuring-bind (key value &rest tail) list
                         (insert! transient key value merge-function)
                         (when tail (insert-pair tail))))))
          (insert-pair plist))
        (persistent! transient))))

(declaim (ftype (function (dict) (values list &optional))
                to-alist
                to-plist))
(defun to-alist (dict)
  "Construct an alist containing each of the mappings in DICT.

The entries from DICT will appear in the resulting alist in an arbitrary order."
  (let* ((alist nil))
    (do (key value dict)
        (push (cons key value) alist))
    alist))

(defun to-plist (dict)
  "Construct a plist containing each of the mappings in DICT.

The entries from DICT will appear in the resulting plist in an arbitrary order."
  (let* ((plist nil))
    (do (key value dict)
        (setf plist (list* key value plist)))
    plist))
