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

When extracting a `hash-node-index' from a `hash', we use the +NODE-INDEX-BITS+ starting at (* SHIFT
+NODE-INDEX-BITS+). The SHIFT is the current node's depth in the trie."
  `(integer 0 ,+max-shift+))

(deftype hash-node-index ()
  "An index into a `hash-node'.

This may denote either a TRUE-INDEX into the backing array, or an untrue index which must be compared against
the BITMAP to determine membership and to compute a TRUE-INDEX."
  `(integer 0 ,+branch-rate+))

;;; struct definitions for node variants

(declaim (inline %make-hash-node %hash-node-bitmap %hash-node-entries))

;; OPTIMIZE: flatten HASH-NODE and CONFLICT-NODE to store their values inline

(defstruct (hash-node
            (:constructor %make-hash-node)
            (:copier nil)
            (:conc-name %hash-node-)
            :named)
  "A branching node in a `dict' for elements with distinct hash parts.

Each `hash-node' is implicitly associated with a `shift', determined by that node's depth in the trie, which
determines which bits of the `hash' are used as its indices.

The ENTRIES is a sparse sequence of child nodes, and the BITMAP maps hash-part indices to true-indices into
the ENTRIES vector. (length ENTRIES) is always equal to (logcount BITMAP)."
  (bitmap (error "Supply :BITMAP to %MAKE-HASH-NODE")
   :type bitmap)
  (entries (error "Supply :ENTRIES to %MAKE-HASH-NODE")
   :type simple-vector ;; of (or HASH-NODE CONFLICT-NODE VALUE-NODE)
   ))

(declaim (inline %make-conflict-node %conflict-node-entries))

(defstruct (conflict-node
            (:constructor %make-conflict-node)
            (:copier nil)
            (:conc-name %conflict-node-))
  "A leaf-ish node in a `dict' for distinct elements with the same hash.

The ENTRIES will be a vector of `value-node's, all of which have keys with the same hash, but which are not
equal under the TEST-FUNCTION. Lookup in a `conflict-node' is a linear search of its ENTRIES.

A `conflict-node' will always contain at least two `value-node's."
  (hash (error "Supply :HASH to %MAKE-CONFLICT-NODE")
   :type fixnum)
  (entries (error "Supply :ENTRIES to %MAKE-CONFLICT-NODE")
   :type simple-vector ;; of VALUE-NODEs
   ))

(declaim (inline %make-value-node %value-node-hash %value-node-key %value-node-value))

(defstruct (value-node
            (:constructor %make-value-node)
            (:copier nil)
            (:conc-name %value-node-))
  "A leaf node in a `dict' which associates a KEY with a VALUE."
  (hash (error "Supply :HASH to %MAKE-VALUE-NODE")
   :type fixnum)
  (key (error "Supply :KEY to %MAKE-VALUE-NODE"))
  (value (error "Supply :VALUE to %MAKE-VALUE-NODE")))

(deftype node ()
  '(or hash-node conflict-node value-node))

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
         (inline size))
(defun size (dict)
  (%dict-size dict))

;;; lookup with GET

(declaim (ftype (function (value-node t test-function) (values boolean &optional))
                value-node-match-p)
         (inline value-node-match-p))
(defun value-node-match-p (value-node key test)
  "Is this VALUE-NODE's key equal to KEY under TEST?"
  (funcall test
           key
           (%value-node-key value-node)))

(declaim (ftype (function (hash-node hash-node-index) (values boolean &optional))
                hash-node-contains-p))
(defun hash-node-contains-p (hash-node index)
  "Does this HASH-NODE contain a child at the index INDEX?"
  (logbitp index (%hash-node-bitmap hash-node)))

(declaim (ftype (function (bitmap hash-node-index) (values hash-node-index &optional))
                bitmap-true-index))
(defun bitmap-true-index (bitmap index)
  "Find the true-index into a hash-node's entries vector associated with INDEX.

Precondition: the associated hash-node must contain the INDEX, i.e. the INDEXth bit in BITMAP must be 1."
  (let* ((bits-before (ldb (byte index 0)
                           bitmap)))
    (logcount bits-before)))

(declaim (ftype (function (hash-node hash-node-index) (values hash-node-index &optional))
                hash-node-true-index))
(defun hash-node-true-index (hash-node index)
  "Find the true-index into a hash-node's entries vector associated with INDEX.

Precondition: the HASH-NODE must `hash-node-contains-p' the INDEX."
  (bitmap-true-index (%hash-node-bitmap hash-node) index))

(declaim (ftype (function (hash-node hash-node-index) (values node &optional))
                hash-node-true-ref))
(defun hash-node-true-ref (hash-node true-index)
  "Look up a child of HASH-NODE by its TRUE-INDEX.

Precondition: the TRUE-INDEX must have resulted from a valid call to `bitmap-true-index' or
`hash-node-true-index' using the HASH-NODE or its bitmap."
  (svref (%hash-node-entries hash-node) true-index))

(declaim (ftype (function (hash-node hash-node-index) (values node &optional))
                hash-node-ref))
(defun hash-node-ref (hash-node index)
  "Look up a child of HASH-NODE by its (untrue) INDEX.

Precondition: the HASH-NODE must `hash-node-contains-p' the INDEX."
  (hash-node-true-ref hash-node (hash-node-true-index hash-node index)))

(declaim (ftype (function (shift fixnum) (values hash-node-index))
                extract-hash-part-for-shift))
(defun extract-hash-part-for-shift (shift hash)
  "Extract a `hash-node-index' from HASH for a `hash-node' at SHIFT, i.e. a hash-node that is SHIFT steps removed from the trie's root."
  (let ((shift-low-bit (* shift +node-index-bits+)))
    (ldb (byte +node-index-bits+ shift-low-bit)
         hash)))

(declaim (ftype (function (node t fixnum shift test-function t) (values t boolean &optional))
                node-lookup))
(defun node-lookup (node key hash shift test-function not-found)
  "Get the value associated with KEY in NODE.

HASH is the result of applying the containing `dict' 's HASH-FUNCTION to KEY.

SHIFT is the depth into the trie of NODE. For a `dict' 's BODY, this will be 0.

TEST-FUNCTION is the containing `dict' 's TEST-FUNCTION, which must satisfy the hash-test-function laws with
the HASH-FUNCTION used to generate HASH.

NOT-FOUND is an arbitrary value to be returned as primary value if NODE does not contain a mapping for KEY."
  (etypecase node
    (value-node
     (if (value-node-match-p node key test-function)
         (values (%value-node-value node) t)
         (values not-found nil)))

    (conflict-node
     (iter (declare (declare-variables))
       (for value-node in-vector (%conflict-node-entries node))
       (when (value-node-match-p value-node key test-function)
         (return (values (%value-node-value value-node) t)))
       (finally (return (values not-found nil)))))

    (hash-node
     (let* ((index (extract-hash-part-for-shift shift hash)))
       (if (hash-node-contains-p node index)
           (node-lookup (hash-node-ref node index)
                        key
                        hash
                        (1+ shift)
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
                   (body %dict-body)
                   (size %dict-size))
      dict
    (if (null body)
        (values not-found nil)
        (node-lookup body key (funcall hash-function key) 0 test-function not-found))))

;;; INSERT and helpers

(declaim (ftype (function (&rest hash-node-index) (values bitmap &optional))
                bitmap-from-indices)
         (inline bitmap-from-indices))
;; TODO: determine if inlines of this function generate good machine code, and if not, optimize with a
;; compiler-macro.
(defun bitmap-from-indices (&rest indices)
  (declare (dynamic-extent indices))
  (reduce #'logior
          indices
          :initial-value 0
          :key (lambda (index)
                 (declare (hash-node-index index))
                 (ash 1 index))))

(declaim (ftype (function (node hash-node-index node hash-node-index)
                          (values hash-node &optional))
                make-two-entry-hash-node))
(defun make-two-entry-hash-node (left left-idx right right-idx)
  (%make-hash-node :bitmap (bitmap-from-indices left-idx right-idx)
                   :entries (if (< left-idx right-idx)
                                (vector left right)
                                (vector right left))))

(declaim (ftype (function (node hash-node-index)
                          (values hash-node &optional))
                make-one-entry-hash-node))
(defun make-one-entry-hash-node (entry index)
  (%make-hash-node :bitmap (bitmap-from-indices index)
                   :entries (vector entry)))

(declaim (ftype (function (fixnum &rest value-node) (values conflict-node &optional))
                make-conflict-node))
(defun make-conflict-node (hash &rest entries)
  (declare (dynamic-extent entries))
  (%make-conflict-node :hash hash
                       :entries (coerce entries 'simple-vector)))

(declaim (ftype (function ((or value-node conflict-node)
                           fixnum
                           (or value-node conflict-node)
                           fixnum
                           shift)
                          (values hash-node &optional))
                promote-node))
(defun promote-node (left-node left-hash right-node right-hash shift)
  "Combine the LEFT-NODE and RIGHT-NODE into a new `hash-node', which should be SHIFT steps deep into the trie.

LEFT-HASH is the hash of the entries in the LEFT-NODE.

RIGHT-HASH is the hash of the entries in the RIGHT-NODE.

Precondition: (/= LEFT-HASH RIGHT-HASH), or else we would construct a unified `conflict-node' instead of a
              `hash-node'."
  (let* ((left-index (extract-hash-part-for-shift shift left-hash))
         (right-index (extract-hash-part-for-shift shift right-hash)))
    (if (= left-index right-index)
        (make-one-entry-hash-node (promote-node left-node
                                                left-hash
                                                right-node
                                                right-hash
                                                (1+ shift))
                                  left-index)
        (make-two-entry-hash-node left-node left-index right-node right-index))))

(declaim (ftype (function (value-node t t fixnum shift test-function)
                          (values node &optional))
                insert-into-value-node))
(defun insert-into-value-node (neighbor-node key value hash shift test-function)
  (if (value-node-match-p neighbor-node key test-function)
      (%make-value-node :hash hash
                        :key key
                        :value value)
      (let* ((neighbor-hash (%value-node-hash neighbor-node))
             (my-value-node (%make-value-node :hash hash
                                              :key key
                                              :value value)))
        (if (= hash neighbor-hash)
            (make-conflict-node hash neighbor-node my-value-node)
            (promote-node neighbor-node neighbor-hash my-value-node hash shift)))))

(declaim (ftype (function (conflict-node t test-function)
                          (values (or null array-index) &optional))
                conflict-node-index-of))
(defun conflict-node-index-of (conflict-node key test-function)
  "If CONFLICT-NODE contains a mapping for KEY under TEST-FUNCTION, return the index into the CONFLICT-NODE's entries vector for that mapping."
  (position-if (lambda (other-key) (funcall test-function key other-key))
               (%conflict-node-entries conflict-node)
               :key #'%value-node-key))

(declaim (ftype (function (conflict-node value-node array-index) (values conflict-node &optional))
                conflict-node-replace-at))
(defun conflict-node-replace-at (conflict-node new-entry index)
  (%make-conflict-node :hash (%conflict-node-hash conflict-node)
                       :entries (sv-replace-at (%conflict-node-entries conflict-node) index new-entry)))

(declaim (ftype (function (conflict-node value-node) (values conflict-node &optional))
                add-to-conflict-node))
(defun add-to-conflict-node (conflict-node new-entry)
  "Add NEW-ENTRY into the entries of CONFLICT-NODE.

Precondition: NEW-ENTRY has the same hash as CONFLICT-NODE, and no existing entry in CONFLICT-NODE has the
              same key as NEW-ENTRY."
  (%make-conflict-node :hash (%conflict-node-hash conflict-node)
                       :entries (sv-push-back (%conflict-node-entries conflict-node) new-entry)))

(declaim (ftype (function (conflict-node t t fixnum shift test-function)
                          (values node &optional))
                insert-into-conflict-node))
(defun insert-into-conflict-node (conflict-node key value hash shift test-function)
  "Add a new entry (KEY -> VALUE) to or alongside CONFLICT-NODE.

Depending on whether HASH is the same as the hash in CONFLICT-NODE, this may allocate a new `hash-node' to
contain both the existing CONFLICT-NODE and the new entry."
  (let* ((conflict-hash (%conflict-node-hash conflict-node))
         (new-value-node (%make-value-node :hash hash
                                           :key key
                                           :value value))
         (same-hash-p (= conflict-hash hash))
         (index (when same-hash-p
                  (conflict-node-index-of conflict-node key test-function))))
    (cond ((and same-hash-p index)
           ;; If CONFLICT-NODE already contains a mapping for KEY, replace it.
           (conflict-node-replace-at conflict-node new-value-node index))

          (same-hash-p
           ;; If the new mapping conflicts with CONFLICT-NODE but is not already present, add it.
           (add-to-conflict-node conflict-node new-value-node))

          (:else
           ;; If the new mapping does not conflict, grow a new `hash-node' with the CONFLICT-NODE and the new
           ;; entry as siblings.
           (promote-node conflict-node conflict-hash
                         new-value-node hash
                         shift)))))

(declaim (ftype (function (hash-node hash-node-index node) (values hash-node &optional))
                hash-node-replace-at-true-index))
(defun hash-node-replace-at-true-index (hash-node true-index new-child)
  (%make-hash-node :bitmap (%hash-node-bitmap hash-node)
                   :entries (sv-replace-at (%hash-node-entries hash-node)
                                           true-index
                                           new-child)))

(declaim (ftype (function (hash-node hash-node-index node) (values hash-node &optional))
                hash-node-replace-at))
(defun hash-node-replace-at (hash-node index new-child)
  (hash-node-replace-at-true-index hash-node
                                   (hash-node-true-index hash-node index)
                                   new-child))

(declaim (ftype (function (hash-node node hash-node-index) (values hash-node &optional))
                add-to-hash-node))
(defun add-to-hash-node (hash-node child index)
  (let* ((new-bitmap (logior (%hash-node-bitmap hash-node)
                             (bitmap-from-indices index)))
         (true-index (bitmap-true-index new-bitmap index)))
    (%make-hash-node :bitmap new-bitmap
                     :entries (sv-insert-at (%hash-node-entries hash-node)
                                            true-index
                                            child))))

(declaim (ftype (function (hash-node t t fixnum shift test-function)
                          (values node &optional))
                insert-into-hash-node))
(defun insert-into-hash-node (hash-node key value hash shift test-function)
  "Add a new entry (KEY -> VALUE) as a child of HASH-NODE."
  (let* ((index (extract-hash-part-for-shift shift hash)))
    (if (hash-node-contains-p hash-node index)
        ;; If the hash node already has a child there, recurse to insert into the child.
        (let* ((existing-child (hash-node-ref hash-node index))
               (inserted-child (node-insert existing-child
                                            key
                                            value
                                            hash
                                            (1+ shift)
                                            test-function)))
          (hash-node-replace-at hash-node index inserted-child))

        ;; If the hash node doesn't have a child there yet, insert one.
        (add-to-hash-node hash-node
                          (%make-value-node :hash hash
                                            :key key
                                            :value value)
                          index))))

(declaim (ftype (function (node t t fixnum shift test-function) (values node &optional))
                node-insert))
(defun node-insert (node key value hash shift test-function)
  "Make KEY map to VALUE within NODE.

Returns a new node like NODE, but with the mapping (KEY -> VALUE). If KEY is already associated with a value
in NODE, the old value will be overwritten.

HASH is the result of applying the containing `dict' 's HASH-FUNCTION to KEY.

SHIFT is the depth into the trie of NODE. For a `dict' 's BODY, this will be 0.

TEST-FUNCTION is the containing `dict' 's TEST-FUNCTION, which must satisfy the hash-test-function laws with
the HASH-FUNCTION used to generate HASH."
  (etypecase node
    (value-node
     (insert-into-value-node node key value hash shift test-function))
    (conflict-node
     (insert-into-conflict-node node key value hash shift test-function))
    (hash-node
     (insert-into-hash-node node key value hash shift test-function))))

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
    (let* ((hash (funcall hash-function key)))
      (if (null body)
          (%make-dict :size 1
                      :hash-function hash-function
                      :test-function test-function
                      :body (%make-value-node :hash hash
                                              :key key
                                              :value value))
          (let* ((new-body (node-insert body key value hash 0 test-function)))
            (%make-dict :size (1+ size)
                        :test-function test-function
                        :hash-function hash-function
                        :body new-body))))))

;;; REMOVE and helpers

(declaim (ftype (function (conflict-node t test-function) (values (or conflict-node value-node) &optional))
                remove-from-conflict-node))
(defun remove-from-conflict-node (conflict-node key test-function)
  "Remove the entry for KEY from CONFLICT-NODE, if any.

If CONFLICT-NODE does not contain an entry for KEY, the returned node will be `eq' to CONFLICT-NODE.

Precondition: KEY has the same hash as the CONFLICT-NODE."

  (if-let ((index (conflict-node-index-of conflict-node key test-function)))
    (if (= 2 (length (%conflict-node-entries conflict-node)))
        (sv-2-other-index (%conflict-node-entries conflict-node) index)
        (%make-conflict-node :hash (%conflict-node-hash conflict-node)
                             :entries (sv-remove-at (%conflict-node-entries conflict-node) index)))
    conflict-node))

(declaim (ftype (function (hash-node hash-node-index hash-node-index) (values hash-node &optional))
                hash-node-remove-at))
(defun hash-node-remove-at (hash-node index-to-remove true-index-to-remove)
  "Remove from HASH-NODE the child named by INDEX-TO-REMOVE and TRUE-INDEX-TO-REMOVE.

Precondition: HASH-NODE must `hash-node-contains-p' INDEX-TO-REMOVE, and TRUE-INDEX-TO-REMOVE must be the
              `hash-node-true-index' of INDEX-TO-REMOVE."
  (let* ((removed-bitmap (logxor (%hash-node-bitmap hash-node)
                                 (bitmap-from-indices index-to-remove)))
         (removed-entries (sv-remove-at (%hash-node-entries hash-node)
                                        true-index-to-remove)))
    (%make-hash-node :bitmap removed-bitmap
                     :entries removed-entries)))

(declaim (ftype (function (hash-node hash-node-index hash-node-index) (values node &optional))
                maybe-elevate-hash-node-other-child))
(defun maybe-elevate-hash-node-other-child (hash-node index-to-remove true-index-to-remove)
  "When removing an entry from a two-entry `hash-node', attempt to reduce nesting by elevating the remaining child.

If the other child of HASH-NODE is itself a `hash-node', reducing nesting is not possible, so the result will
be a one-entry `hash-node'."
  (let* ((other-true-index (if (zerop true-index-to-remove) 1 0))
         (other-node (hash-node-true-ref hash-node other-true-index)))
    (etypecase other-node
      ;; if the OTHER-NODE is sensitive to its SHIFT in the trie, i.e. is a HASH-NODE, we cannot elevate
      ;; it. But if it is not sensitive to its SHIFT, i.e. is either a VALUE-NODE or a CONFLICT-NODE, then we
      ;; can return it without a one-element hash node intermediate.

      ((or value-node conflict-node) other-node)

      (hash-node (hash-node-remove-at hash-node
                                      index-to-remove
                                      true-index-to-remove)))))

(declaim (ftype (function (hash-node t fixnum shift test-function)
                          (values (or null node) &optional))
                remove-from-hash-node))
(defun remove-from-hash-node (hash-node key hash shift test-function)
  (let* ((index (extract-hash-part-for-shift shift hash)))
    (if (hash-node-contains-p hash-node index)
        (let* ((true-index (hash-node-true-index hash-node index))
               (old-child (hash-node-true-ref hash-node true-index))
               (new-child (node-remove old-child key hash (1+ shift) test-function)))
          (cond ((eq old-child new-child)
                 ;; If we didn't remove anything, return the HASH-NODE unchanged.
                 hash-node)

                ((and (null new-child) (= 1 (length (%hash-node-entries hash-node))))
                 ;; If we removed our only child, return NIL.
                 nil)

                ((and (null new-child) (= 2 (length (%hash-node-entries hash-node))))
                 ;; If we have two children and we're removing one of them, try to reduce nesting if possible.
                 (maybe-elevate-hash-node-other-child hash-node index true-index))

                ((null new-child)
                 ;; If we removed an entire child, the resulting `hash-node' will have one fewer entries than
                 ;; HASH-NODE.
                 (hash-node-remove-at hash-node index true-index))

                (:else
                 ;; If the removed child had other, non-removed entries in it, the resulting `hash-node' will
                 ;; have the same number of entries as HASH-NODE.
                 (hash-node-replace-at-true-index hash-node true-index new-child))))
        hash-node)))

(declaim (ftype (function (node t fixnum shift test-function) (values (or null node) &optional))
                node-remove))
(defun node-remove (node key hash shift test-function)
  "Make KEY unmapped within NODE.

Returns a new node like NODE, but with any mapping from KEY removed. If KEY is already unmapped within NODE,
the return value will be `eq' to NODE.

HASH is the result of applying the containing `dict' 's HASH-FUNCTION to KEY.

SHIFT is the depth into the trie of NODE. For a `dict' 's BODY, this will be 0.

TEST-FUNCTION is the containing `dict' 's TEST-FUNCTION, which must satisfy the hash-test-function laws with
the HASH-FUNCTION used to generate HASH."
  (etypecase node
    (value-node
     (if (and (= hash (%value-node-hash node))
              (value-node-match-p node key test-function))
         nil
         node))

    (conflict-node
     (if (= hash (%conflict-node-hash node))
         (remove-from-conflict-node node key test-function)
         node))

    (hash-node
     (remove-from-hash-node node key hash shift test-function))))

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
        (let* ((hash (funcall hash-function key))
               (new-body (node-remove body key hash 0 test-function)))
          (if (eq new-body body)
              dict
              (%make-dict :size (1- size)
                          :body new-body
                          :hash-function hash-function
                          :test-function test-function))))))

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
