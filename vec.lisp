;;;; VECs, a.k.a. Persistent Vectors, a.k.a. Bit-partitioned Binary Tries with Tails
;;; See Jean Niklas L'orange's series of blog posts, "Understanding Clojure's Persistent Vectors," for an
;;; explanation of this data structure.
;;; https://hypirion.com/musings/understanding-persistent-vector-pt-1
;;; https://hypirion.com/musings/understanding-persistent-vector-pt-2
;;; https://hypirion.com/musings/understanding-persistent-vector-pt-3
(uiop:define-package :immutable/vec
  (:import-from :alexandria
                #:array-index #:array-length #:define-constant #:when-let #:once-only #:with-gensyms)
  (:use :cl :iterate #:immutable/%generator #:immutable/%simple-vector-utils)
  (:shadow #:length #:equal #:map #:do #:concatenate)
  (:export
   ;; condition classes and accessors
   #:out-of-bounds
   #:out-of-bounds-index
   #:out-of-bounds-length
   #:out-of-bounds-vec
   #:out-of-bounds-operation

   #:pop-back-empty

   #:retract-not-enough-elements
   #:retract-not-enough-elements-vec
   #:retract-not-enough-elements-requested-length
   #:retract-not-enough-elements-actual-length

   ;; type and constructor
   #:vec

   ;; the empty vector
   #:+empty+

   ;; element access
   #:unsafe-ref
   #:ref

   ;; reading length (shadowed over CL:LENGTH)
   #:length

   ;; test if vec is empty
   #:emptyp

   ;; append one to end
   #:push-back

   ;; append multiple to end
   #:extend
   #:extend-from-list #:extend-from-vector

   ;; append vecs
   #:concatenate

   ;; remove one from end
   #:pop-back

   ;; remove multiple from end
   #:retract

   ;; replace individual elements in a vec
   #:update-at
   #:replace-at

   ;; map function across vec
   #:map

   ;; iterate over vec
   #:for-each
   #:do

   ;; test if two vectors are equal
   #:equal

   ;; convert from CL sequences
   #:from-list #:to-list

   ;; convert to CL sequences
   #:from-vector #:to-specialized-vector #:to-vector))
(in-package :immutable/vec)

#+immutable-vec-debug
(declaim (optimize (speed 1) (safety 3) (space 1) (debug 3) (compilation-speed 0)))
#-immutable-vec-debug
(declaim (optimize (speed 3) (safety 1) (space 1) (debug 1) (compilation-speed 0)))

(eval-when (:compile-toplevel :load-toplevel)
  (declaim (type array-length +branch-rate+))
  (defconstant +branch-rate+ 32
    "The number of child nodes or elements contained in each node of a vec.")

  (declaim (type (and fixnum unsigned-byte) +node-index-bits+))
  (defconstant +node-index-bits+ (floor (log +branch-rate+ 2)))

  (declaim (type (and fixnum unsigned-byte) +max-length+))
  (defconstant +max-length+ most-positive-fixnum
    "The maximum number of elements contained in a vec.")

  (declaim (type (and fixnum unsigned-byte) +max-height+))
  (defconstant +max-height+ (1- (floor (log +max-length+ +branch-rate+)))
    "The number of chunks traversed from root to leaf in a vec of length +max-length+."))

(deftype node-length ()
  `(integer 1 ,+branch-rate+))

(deftype tail-length ()
  `(integer 0 ,+branch-rate+))

(deftype height ()
  "The number of nodes to traverse from root to a leaf node.

Height of 0 means that the current node is a leaf node, i.e. its elements are the elements of the enclosing
VEC.

Height of 1 means that the current node's elements have height 0, i.e. are leaf nodes.

Height of N means that the current node's elements have height (1- N)."
  `(integer 0 ,+max-height+))

(deftype length ()
  `(integer 0 ,+max-length+))

(deftype index ()
  `(integer 0 (,+max-length+)))

(deftype transient-id ()
  '(and fixnum unsigned-byte))

(define-vector-struct node
    (:max-length #.+branch-rate+
     :conc-name %node-
     :logical-index-to-true-index node-logical-index-to-true-index
     :logical-length-to-true-length node-logical-length-to-true-length)
  (transient-id :type (or null transient-id)
                :initform nil))

(define-generator node ((node node))
                  "Children of a `node'"
    ((idx 0))
  (declare ((or (eql 0) node-length) idx))
  (if (< idx (node-length node))
      (prog1 (node-ref node idx)
        (incf idx))
      (done)))

(deftype full-node ()
  `(and node (simple-vector
              ;; 1 for the number of named slots in `define-vector-struct'. This is not a call to
              ;; `node-logical-length-to-true-length' because of `eval-when' concerns.
              ,(1+ +branch-rate+))))

;; constructing nodes

(declaim (ftype (function (generator node-length) (values node &optional))
                alloc-node))
(defun alloc-node (contents-iterator length-in-children)
  (make-node :length length-in-children
             :initial-contents contents-iterator))

(deftype node-index ()
  `(integer 0 (,+branch-rate+)))

(deftype tail-buf () '(or null node))

;;; the actual defstruct!

(declaim (inline %make-vec %vec-height %vec-length %vec-body %vec-tail))

(defstruct (vec
            (:constructor %make-vec)
            (:copier nil)
            (:conc-name %vec-))
  "A persistent vector, A.K.A. a bit-partitioned vector trie with a tail buffer.

Persistent vectors implement random-access indexing and updates in O(log_{32}(length)) time while sharing
structure, and push- and pop- at the end in amortized constant time.

As implemented here, vecs are untyped, unlike CL arrays, which allow specialization. CL's type system makes
implementing new specialized collections difficult.

The empty vec is called `+empty+'.

To query the length of a vec, use `length', which this package shadows.

To construct a vec from arbitrary elements, use the function (`vec' &rest ELEMENTS), which is analogous to the
functions `list' and `vector'.

To convert a CL sequence into a vec, use `from-list' or `from-vector' as appropriate.

To convert a vec into a CL sequence, use `to-list' or `to-vector'.

To convert a vec into a vector that is not a simple-vector, use `to-specialized-array', which takes keyword
arguments `:element-type', `:adjustable' and `:fill-pointer' analogous to `make-array'."

  ;; The number of array accesses between the body and the elements.
  ;; A height of 0 means that the body is a simple-vector of elements.
  ;; A height of N > 0 means that the body is a simple-vector of nodes of height N.
  (height (error "Supply :HEIGHT to %MAKE-VEC")
   :type height)
  ;; The total length of this vec, including both its body and its tail.
  (length (error "Supply :LENGTH to %MAKE-VEC")
   :type length)
  ;; The body part of this vec, a bit-partitioned trie. Leaf nodes in this trie (those with height 0) will
  ;; always be full, i.e. contain exactly +BRANCH-RATE+ elements. If the vec's length is not a multiple of
  ;; +BRANCH-RATE+, the remainder will be stored in the tail.
  (body (error "Supply :BODY to %MAKE-VEC")
   :type (or null node))
  ;; The tail part of this vec, a single simple-vector of length at most +BRANCH-RATE+. Storing such a tail
  ;; allows `push-back' and `pop-back' to run in amortized constant time.
  (tail nil
   :type tail-buf))

;;; condition class for out-of-bounds access

(define-condition out-of-bounds (error)
  ((%vec :type vec
         :initarg :vec
         :reader out-of-bounds-vec)
   (%length :type unsigned-byte
            :initarg :length
            :reader out-of-bounds-length)
   (%index :type unsigned-byte
           :initarg :index
           :reader out-of-bounds-index)
   (%operation :type (member 'ref 'replace-at 'update-at)
               :initarg :operation
               :reader out-of-bounds-operation))
  (:report (lambda (c s)
             (format s "Invalid index ~d during ~s for VEC of length ~d: ~a"
                     (out-of-bounds-index c)
                     (out-of-bounds-operation c)
                     (out-of-bounds-length c)
                     (out-of-bounds-vec c)))))

;;; condition class for pop-back from empty

(define-condition pop-back-empty (error)
  ()
  (:report (lambda (c s)
             (declare (ignore c))
             (write-string "Attempt to POP-BACK from empty VEC" s))))

;;; condition class for retract with not enough elements

(define-condition retract-not-enough-elements (error)
  ((%vec :initarg :vec
         :reader retract-not-enough-elements-vec)
   (%requested-length :type length
                      :initarg :requested-length
                      :reader retract-not-enough-elements-requested-length)
   (%actual-length :type length
                   :initarg :actual-length
                   :reader retract-not-enough-elements-actual-length))
  (:report (lambda (c s)
             (format s "Attempt to RETRACT ~d elements from a VEC of length ~d: ~a"
                     (retract-not-enough-elements-requested-length c)
                     (retract-not-enough-elements-actual-length c)
                     (retract-not-enough-elements-vec c)))))

;;; length computations

(declaim (ftype (function (tail-buf) (values tail-length &optional))
                tail-buf-length)
         (inline tail-buf-length))
(defun tail-buf-length (tail-buf)
  (if tail-buf
      (node-length tail-buf)
      0))

(declaim (ftype (function (vec) (values tail-length &optional))
                tail-length)
         (inline tail-length))
(defun tail-length (vec)
  (tail-buf-length (%vec-tail vec)))

(declaim (ftype (function (vec) (values length &optional))
                length body-length)
         (inline length body-length))
(defun length (vec)
  (%vec-length vec))
(defun body-length (vec)
  (- (length vec)
     (tail-length vec)))

(declaim (ftype (function (vec) (values boolean &optional))
                emptyp))
(defun emptyp (vec)
  "Returns T if VEC is empty, or `nil' if it contains at least one element."
  (zerop (length vec)))

(declaim (ftype (function (vec index) (values boolean &optional))
                index-in-tail-p)
         (inline index-in-tail-p))
(defun index-in-tail-p (vec idx)
  "True if IDX is within or beyond the tail part of VEC, nil otherwise.

Does not necessarily imply that IDX is in-bounds for VEC."
  (>= idx (body-length vec)))

(declaim (ftype (function (vec index) (values t &optional))
                tailref)
         (inline tailref))
(defun tailref (vec idx)
  "Read from the tail of VEC. IDX must be in-bounds for VEC, and must be `index-in-tail-p'."
  (node-ref (%vec-tail vec) (- idx (body-length vec))))

(declaim (ftype (function (height index) (values node-index index &optional))
                extract-index-parts-for-height)
         (inline extract-index-parts-for-height))
(defun extract-index-parts-for-height (height idx)
  (let ((height-low-bit (* height +node-index-bits+)))
    (values (ldb (byte +node-index-bits+ height-low-bit)
                 idx)
            (ldb (byte height-low-bit 0)
                 idx))))

(declaim (ftype (function (node height index) (values t &optional))
                trieref))
(defun trieref (body height idx)
  "Index into the body part of a vector BODY at HEIGHT.

IDX must be inbounds for BODY at HEIGHT, meaning it must have no one bits higher than
(* (1+ height) +node-index-bits+) and must not pass into an unallocated node."
  (if (zerop height)
      (node-ref body idx)
      (multiple-value-bind (curr remaining) (extract-index-parts-for-height height idx)
        (trieref (node-ref body curr) (1- height) remaining))))

(declaim (ftype (function (vec index) (values t &optional))
                bodyref)
         (inline bodyref))
(defun bodyref (vec idx)
  "Index into the body part of VEC. IDX must be in-bounds for VEC, and must not be `index-in-tail-p'."
  (trieref (%vec-body vec) (%vec-height vec) idx))

(declaim (ftype (function (vec index) (values t &optional))
                unsafe-ref))
(defun unsafe-ref (vec idx)
  (if (index-in-tail-p vec idx)
      (tailref vec idx)
      (bodyref vec idx)))

(declaim (ftype (function (vec index) (values t &optional))
                ref)
         (inline ref))
(defun ref (vec idx &aux (length (length vec)))
  (if (>= idx length)
      (error 'out-of-bounds
             :vec vec
             :length length
             :index idx
             :operation 'ref)
      (unsafe-ref vec idx)))

;;; computing required size, shape, height of new vecs

(declaim (ftype (function (length) (values length &optional))
                length-without-tail-buf)
         (inline length-without-tail-buf))
(defun length-without-tail-buf (total-length)
  (let* ((tail-length (rem total-length +branch-rate+)))
    (- total-length tail-length)))

(declaim (ftype (function (length) (values height &optional))
                length-required-height)
         (inline length-required-height))
(defun length-required-height (length &aux (length-without-tail (length-without-tail-buf length)))
  (if (<= length-without-tail 1)
      0
      (values (floor (log (1- length-without-tail) +branch-rate+)))))

(declaim (ftype (function (height) (values length &optional))
                elts-per-node-at-height)
         (inline elts-per-node-at-height))
(defun elts-per-node-at-height (height)
  (expt +branch-rate+ (1+ height)))

(declaim (ftype (function (length height) (values length &optional))
                trie-length-in-nodes-at-height)
         (inline trie-length-in-nodes-at-height))
(defun trie-length-in-nodes-at-height (length-in-elts height)
  (values (ceiling length-in-elts (elts-per-node-at-height height))))

(declaim (ftype (function (fixnum fixnum fixnum) (values fixnum &optional))
                bracket)
         (inline bracket))
(defun bracket (min middle max)
  (min max (max middle min)))

;;; constructing the body part of vecs

(declaim (ftype (function (height length generator)
                          (values (or null node) &optional))
                alloc-trie))

(declaim (ftype (function (height length generator)
                          (values (generator node) &optional))
                child-nodes-generator))

(defun alloc-trie (height length-in-elts contents)
  (cond ((zerop length-in-elts) nil)
        ((zerop height) (alloc-node contents length-in-elts))
        (:else (alloc-node (child-nodes-generator (1- height) length-in-elts contents)
                           (trie-length-in-nodes-at-height length-in-elts (1- height))))))

(defun child-nodes-generator (child-height length-in-elts contents)
  (generator ((per-child-length (elts-per-node-at-height child-height))
              (remaining length-in-elts))
    (declare (type length per-child-length)
             (fixnum remaining))
    (let ((this-length (bracket 0 per-child-length remaining)))
      (declare (type length this-length))
      (if (zerop this-length)
          (done)
          (progn (decf remaining this-length)
                 (alloc-trie child-height this-length contents))))))

;;; constructing the tail part of vecs

(declaim (ftype (function (tail-length generator) (values tail-buf &optional))
                make-tail)
         (inline make-tail))
(defun make-tail (tail-length contents)
  (if (zerop tail-length)
      nil
      (alloc-node contents tail-length)))

(declaim (ftype (function (t) (values tail-buf &optional))
                make-one-element-tail))
(defun make-one-element-tail (element)
  (make-node :length 1
             :initial-element element))

;;; constructing vecs

(declaim (type vec +empty+))
(defparameter +empty+ (%make-vec :length 0
                                 :height 0
                                 :body nil
                                 :tail nil))

(declaim (ftype (function (length generator) (values vec &optional))
                generator-vec)
         ;; `generator-vec' is private and will be accessed only by `vec', `from-list' and `from-vector', so
         ;; inlining is not a code size concern, and making the generator a local function may allow some
         ;; optimizations.
         (inline generator-vec))
(defun generator-vec (length contents)
  (if (zerop length)
      +empty+
      (let* ((body-length (length-without-tail-buf length))
             (tail-length (- length body-length))
             (height (length-required-height body-length)))
        (%make-vec :height height
                   :length length
                   :body (alloc-trie height body-length contents)
                   :tail (make-tail tail-length contents)))))

;;; internal functional updates to vecs

(declaim (ftype (function (vec &key (:height height)
                               (:length length)
                               (:body (or null node))
                               (:tail tail-buf))
                          (values vec &optional))
                copy-vec)
         ;; Private function that can be inlined without worrying about code size, and reducing to an
         ;; (also inline) struct constructor may allow some optimizations.
         (inline copy-vec))
(defun copy-vec (vec &key (height (%vec-height vec))
                       (length (%vec-length vec))
                       (body (%vec-body vec))
                       (tail (%vec-tail vec)))
  (%make-vec :height height
             :length length
             :body body
             :tail tail))

;;; adding an element to the end of a vec

(declaim (ftype (function (tail-buf) (values boolean &optional))
                tail-has-room-p)
         ;; Inlining `tail-has-room-p' may allow arithmetic optimizations and improved type inference.
         (inline tail-has-room-p))
(defun tail-has-room-p (tail)
  (if tail
      (< (tail-buf-length tail)
         +branch-rate+)
      t))

(declaim (ftype (function (height) (values length &optional))
                max-body-length-at-height)
         ;; Inlining `max-body-length-at-height' may allow arithmetic optimizations.
         (inline max-body-length-at-height))
(defun max-body-length-at-height (height)
  (expt +branch-rate+ (1+ height)))

(declaim (ftype (function (height node) (values node &optional))
                wrap-in-spine))
(defun wrap-in-spine (height body)
  (if (plusp height)
      (wrap-in-spine (1- height) (alloc-node (generate-these body) 1))
      body))

(declaim (ftype (function ((or null node) node height length)
                          (values node &optional))
                grow-trie))
(defun grow-trie (trie new-node height new-length-in-elts)
  (cond ((zerop height) new-node)
        ((null trie) (wrap-in-spine height new-node))
        (t
         (locally (declare (node trie)) ; for some reason, sbcl doesn't infer this, at least on 2.2.11
           (let* ((length-before-in-elts (- new-length-in-elts (node-length new-node)))
                  (elts-per-node (elts-per-node-at-height (1- height)))
                  (new-length-in-nodes (ceiling new-length-in-elts
                                                elts-per-node))
                  (length-before-in-nodes (floor length-before-in-elts
                                                 elts-per-node))
                  (last-node-length-in-nodes (- new-length-in-nodes length-before-in-nodes)))
             (declare (node-length new-length-in-nodes
                                   length-before-in-nodes
                                   last-node-length-in-nodes))
             (with-node-generator (trie-generator trie)
               (alloc-node (concat (take trie-generator length-before-in-nodes)
                                   (generate-these (if (= length-before-in-nodes (node-length trie))
                                                       ;; new node is the leftmost in its subtree
                                                       (wrap-in-spine (1- height) new-node)
                                                       ;; new node has siblings
                                                       (grow-trie (node-ref trie length-before-in-nodes)
                                                                  new-node
                                                                  (1- height)
                                                                  last-node-length-in-nodes))))
                           new-length-in-nodes)))))))

(declaim (ftype (function (vec t) (values vec &optional))
                push-back))
(defun push-back (vec new-element)
  "Return a new `vec' like VEC, with NEW-ELEMENT added to the end.

Attempts to share as much structure as possible with the original VEC.

# Time complexity

This operation has an amortized runtime of O(1). One out of every `+branch-rate+' `push-back's will run in
O(log_{+brach-rate+}N) time in the length of the input VEC, and the rest will run in constant time."
  (with-accessors ((height %vec-height)
                   (length %vec-length)
                   (tail %vec-tail)
                   (body %vec-body))
      vec
    (cond ((not tail)
           ;; super fast path when you have no tail: grow a tail
           (copy-vec vec
                     :tail (make-one-element-tail new-element)
                     :length (1+ length)))
          ((tail-has-room-p tail)
           ;; fast path when your tail is short: make it longer
           (copy-vec vec
                     :tail (sv-push-back tail new-element)
                     :length (1+ length)))
          ((= (body-length vec) (max-body-length-at-height height))
           ;; fast path when your tail and body are both full: grow an extra layer of height, put your old tail
           ;; in the newly-expanded body, then grow a new tail
           (copy-vec vec
                     :height (1+ height)
                     :length (1+ length)
                     :body (alloc-node (generate-these body
                                                       (wrap-in-spine height tail))
                                       2)
                     :tail (make-one-element-tail new-element)))
          (t
           ;; slow path when tail is full but body is not: move your full tail into your not-full body, then
           ;; grow a new tail.
           (copy-vec vec
                     :height height
                     :length (1+ length)
                     :body (grow-trie body tail height length)
                     :tail (make-one-element-tail new-element))))))

;;; adding multiple elements with EXTEND (and helpers)

(declaim (ftype (function (height full-node generator length) (values node &optional))
                fill-behind-direct-child))
(defun fill-behind-direct-child (direct-child-height leading-direct-child follow-elts length-in-elts)
  "Make a trie that starts with the LEADING-DIRECT-CHILD, then filled from the FOLLOW-ELTS.

Allocate a node with height (1+ DIRECT-CHILD-HEIGHT) whose first child is LEADING-DIRECT-CHILD, and with
subsequent children to hold enough elements taken from the FOLLOW-ELTS that the node's total length is
LENGTH-IN-ELTS.

LENGTH-IN-ELTS must be a multiple of +BRANCH-RATE+, and includes the length of LEADING-DIRECT-CHILD."
  (alloc-node (concat (generate-these leading-direct-child)
                      (child-nodes-generator direct-child-height
                                             (- length-in-elts (elts-per-node-at-height direct-child-height))
                                             follow-elts))
              (trie-length-in-nodes-at-height length-in-elts direct-child-height)))

(declaim (ftype (function (height full-node height generator length) (values node &optional))
                fill-behind-node-to-height))
(defun fill-behind-node-to-height (total-height leading-node leading-node-height follow-elts length-in-elts)
  "Make a trie of TOTAL-HEIGHT that starts with the LEADING-NODE, then filled from the FOLLOW-ELTS.

LENGTH-IN-ELTS must be a multiple of +BRANCH-RATE+, and includes the length of LEADING-NODE."
  (cond ((= total-height leading-node-height) leading-node)

        ((= total-height (1+ leading-node-height))
         (fill-behind-direct-child leading-node-height leading-node follow-elts length-in-elts))

        (t
         (let* ((direct-child-height (1- total-height))
                (direct-leading-child-length (max-body-length-at-height direct-child-height))
                (leading-direct-child (fill-behind-node-to-height direct-child-height
                                                                  leading-node
                                                                  leading-node-height
                                                                  follow-elts
                                                                  direct-leading-child-length)))
           (fill-behind-direct-child direct-child-height
                                     leading-direct-child
                                     follow-elts
                                     length-in-elts)))))

(declaim (ftype (function (height node height full-node generator length) (values node &optional))
                extend-full-body-to-new-height))
(defun extend-full-body-to-new-height (new-height full-body old-height full-tail new-elements new-body-length)
  (if (= new-height (1+ old-height))
      (let* ((node-with-tail-length-in-elts (min (max-body-length-at-height old-height)
                                                 new-body-length))
             (new-nodes-length-in-elts (- new-body-length node-with-tail-length-in-elts)))
        (alloc-node (concat (generate-these full-body
                                            (fill-behind-node-to-height old-height
                                                                        full-tail
                                                                        0
                                                                        new-elements
                                                                        node-with-tail-length-in-elts))
                            (child-nodes-generator old-height
                                                   new-nodes-length-in-elts
                                                   new-elements))
                    new-body-length))

      (let* ((one-more-height (1+ old-height))
             (leading-node-length-in-elts (max-body-length-at-height one-more-height))
             (leading-node (extend-full-body-to-new-height one-more-height
                                                           full-body
                                                           old-height
                                                           full-tail
                                                           new-elements
                                                           leading-node-length-in-elts)))
        (fill-behind-node-to-height new-height leading-node one-more-height new-elements new-body-length))))

(declaim (ftype (function (node height length &optional index) (values generator &optional))
                generate-trie))
(defun generate-trie (trie height length-in-elts &optional (start-at 0))
  (let* ((next-idx start-at))
    (declare (length next-idx))
    (lambda ()
      (if (>= next-idx length-in-elts)
          (done)
          (prog1 (trieref trie height next-idx)
            (incf next-idx))))))

(declaim (ftype (function (node height length generator length) (values node &optional))
                extend-node-at-height))
(defun extend-node-at-height (not-full-node height current-length-in-elts new-elements target-length-in-elts)
  "Extend the trie NOT-FULL-NODE to be longer while maintaining its existing length."
  (let* ((child-height (1- height))
         (elts-per-full-child (elts-per-node-at-height child-height))
         (num-full-leading-children (floor current-length-in-elts elts-per-full-child))
         (partial-child-p (not (= num-full-leading-children (node-length not-full-node))))
         (length-in-children (trie-length-in-nodes-at-height target-length-in-elts
                                                             child-height)))
    (declare (height child-height)
             (length elts-per-full-child)
             ((or (eql 0) node-length) num-full-leading-children)
             (node-length length-in-children))
    (if (not partial-child-p)
        ;; If all our children are full, this operation is easy: construct a new node which has all of the
        ;; existing children, followed by new nodes taken from the NEW-ELEMENTS.
        (with-node-generator (existing-children-generator not-full-node)
          (alloc-node (concat existing-children-generator
                              (child-nodes-generator child-height
                                                     (- target-length-in-elts current-length-in-elts)
                                                     new-elements))
                      length-in-children))

        ;; If we have a partial child, things get a little trickier. The resulting node will have 3 parts, and
        ;; unfortunately, we'll have to do some math to compute each one.

        ;; 1. Any full direct children of NOT-FULL-NODE can be inserted as children of the new node without
        ;; copying.

        ;; 2. The NOT-FULL-NODE has exactly one child which is not full; recurse to extend it as far as
        ;;    possible from the NEW-ELEMENTS.

        ;; 3. If there are more than enough NEW-ELEMENTS to fill 2 entirely, some entirely new nodes taken
        ;;    from the NEW-ELEMENTS.
        (let* ((full-leading-children-length-in-elts (* elts-per-full-child num-full-leading-children))
               (partial-existing-child-length-in-elts (- current-length-in-elts
                                                         full-leading-children-length-in-elts))
               (new-elts-to-fill-partial-existing-child (- elts-per-full-child
                                                           partial-existing-child-length-in-elts))
               (available-new-elts (- target-length-in-elts current-length-in-elts))
               (filled-partial-existing-child-length-in-elts (min elts-per-full-child
                                                                  (+ partial-existing-child-length-in-elts
                                                                     available-new-elts)))
               (new-children-length-in-elts (max 0
                                                 (- available-new-elts
                                                    new-elts-to-fill-partial-existing-child))))
          (declare (length full-leading-children-length-in-elts
                           partial-existing-child-length-in-elts
                           new-elts-to-fill-partial-existing-child
                           available-new-elts
                           filled-partial-existing-child-length-in-elts
                           new-children-length-in-elts))
          (with-node-generator (existing-children-generator not-full-node)
            (alloc-node (concat (take existing-children-generator num-full-leading-children)
                                (generate-these (extend-node-at-height (node-ref not-full-node num-full-leading-children)
                                                                       child-height
                                                                       partial-existing-child-length-in-elts
                                                                       new-elements
                                                                       filled-partial-existing-child-length-in-elts))
                                (child-nodes-generator child-height
                                                       new-children-length-in-elts
                                                       new-elements))
                        length-in-children))))))

(declaim (ftype (function (height node height length generator length)
                          (values node &optional))
                extend-partial-node-to-new-height))
(defun extend-partial-node-to-new-height (new-height
                                          partial-node
                                          current-height
                                          current-length-in-elts
                                          new-elements
                                          target-length-in-elts)
  (let* (;; we know that we will be filling the PARTIAL-NODE all the way, that is, that FULL-NODE-LENGTH is
         ;; less than TARGET-LENGTH-IN-ELTS, because NEW-HEIGHT > CURRENT-HEIGHT.
         (full-node-length (elts-per-node-at-height current-height))
         (full-node (extend-node-at-height partial-node
                                           current-height
                                           current-length-in-elts
                                           new-elements
                                           full-node-length)))
    (fill-behind-node-to-height new-height full-node current-height new-elements target-length-in-elts)))

(declaim (ftype (function (tail-buf) (values generator &optional))
                generate-tail)
         ;; Inlining generator constructors may allow optimizations from treating the generator closure as a
         ;; local.
         (inline generate-tail))
(defun generate-tail (tail-buf)
  (if tail-buf
      (generate-node tail-buf)
      (lambda () (done))))

(declaim (ftype (function (vec generator length) (values vec &optional))
                extend-from-generator)

         ;; `extend-from-generator' is private and will be called only by `extend', `extend-from-list',
         ;; `extend-from-vector' and `extend-from-vec', so inlining a large function is reasonable. Inlining
         ;; may allow optimizations by also inlining the NEW-ELEMENTS generator.
         (inline extend-from-generator))
(defun extend-from-generator (vec new-elements added-length)
  (with-accessors ((height %vec-height)
                   (length %vec-length)
                   (tail %vec-tail)
                   (body %vec-body))
      vec
    (let* ((new-length (+ length added-length))
           (new-height (length-required-height new-length))
           (new-body-length (length-without-tail-buf new-length))
           (new-tail-length (- new-length new-body-length)))
      (declare (length new-length new-body-length)
               (height new-height)
               (tail-length new-tail-length))
      (cond ((and (not tail)
                  (< added-length +branch-rate+))
             ;; no tail and new items fit in tail: grow a tail
             (copy-vec vec
                       :length new-length
                       :tail (make-tail added-length new-elements)))

            ((< (+ added-length (tail-length vec)) +branch-rate+)
             ;; have tail, but new elements will fit in it
             (copy-vec vec
                       :length new-length
                       :tail (make-tail new-tail-length
                                        (concat (generate-tail tail) new-elements))))

            ((and (not body)
                  (= (tail-length vec) +branch-rate+))
             ;; no body, full tail: fold tail buf into body, then grow from new-elements.
             (%make-vec :height new-height
                        :length new-length
                        :body (fill-behind-node-to-height new-height tail 0 new-elements new-body-length)
                        :tail (make-tail new-tail-length new-elements)))

            ((not body)
             ;; no body, tail not full: construct vec from elements of old tail and new elements
             (%make-vec :length new-length
                        :height new-height
                        :body (alloc-trie new-height
                                          new-body-length
                                          (concat (generate-tail tail) new-elements))
                        :tail (make-tail new-tail-length new-elements)))

            ((and (= (body-length vec) (max-body-length-at-height height))
                  (= (tail-buf-length tail) +branch-rate+))
             ;; tail and body are both full: grow one or more extra layers of height, move your old tail buf
             ;; into your newly-expanded body, distribute new-elements between body and new tail.
             (%make-vec :height new-height
                        :length new-length
                        :body (extend-full-body-to-new-height new-height
                                                              body
                                                              height
                                                              tail
                                                              new-elements
                                                              new-body-length)
                        :tail (make-tail new-tail-length new-elements)))

            ((= (body-length vec) (max-body-length-at-height height))
             ;; body is full, tail is not: grow to new height, distribute elements from old tail and
             ;; NEW-ELEMENTS between extended body and new tail
             (%make-vec :height new-height
                        :length new-length
                        :body (fill-behind-node-to-height new-height
                                                          body
                                                          height
                                                          (concat (generate-tail tail)
                                                                  new-elements)
                                                          new-body-length)
                        :tail (make-tail new-tail-length new-elements)))

            ;; TODO: missed case: not full body, full tail. small win possible by sharing structure with
            ;; existing tail buf.

            ((= height new-height)
             ;; body is not full, but do not need to grow additional height: distribute elements from your old
             ;; tail and the NEW-ELEMENTS between body and new tail.
             (%make-vec :height height
                        :length new-length
                        :body (extend-node-at-height body
                                                     height
                                                     (body-length vec)
                                                     (concat (generate-tail tail)
                                                             new-elements)
                                                     new-body-length)
                        :tail (make-tail new-tail-length new-elements)))

            (t
             ;; body is not full; need to grow additional height to fit new elements
             (%make-vec :height new-height
                        :length new-length
                        :body (extend-partial-node-to-new-height new-height
                                                                 body
                                                                 height
                                                                 (body-length vec)
                                                                 (concat (generate-tail tail)
                                                                         new-elements)
                                                                 new-body-length)
                        :tail (make-tail new-tail-length new-elements)))))))

(declaim (ftype (function (vec &rest t) (values vec &optional))
                extend))
(defun extend (vec &rest new-elements)
  "Return a new `vec' with all the contents of VEC followed by the NEW-ELEMENTS.

This operation will attempt to share as much structure as possible with the original VEC.

# Time complexity

Let N be the number of elements in VEC, and M be the number of NEW-ELEMENTS.

For M < +BRANCH-RATE+, this operation's amortized time complexity is O((M * log_{+branch-rate+}N) /
+branch-rate+), because every (+branch-rate+ / M) `extend's will overflow the tail buffer and require
log_{+branch-rate+}N operations to splice it into the body.

For M > +BRANCH-RATE+, this operation's time complexity is O(M * log_{+branch-rate+}(M + N))."
  (declare (dynamic-extent new-elements))
  (with-list-generator (elts-generator new-elements)
    (extend-from-generator vec elts-generator (cl:length new-elements))))

(declaim (ftype (function (vec list) (values vec &optional))
                extend-from-list))
(defun extend-from-list (vec new-elements)
  "Return a new `vec' with all the contents of VEC followed by the NEW-ELEMENTS.

See `extend' for more information."
  (with-list-generator (elts-generator new-elements)
    (extend-from-generator vec elts-generator (cl:length new-elements))))

(declaim (ftype (function (vec vector) (values vec &optional))
                extend-from-vector))
(defun extend-from-vector (vec new-elements)
  "Return a new `vec' with all the contents of VEC followed by the NEW-ELEMENTS.

See `extend' for more information."

  ;; It would be nice to declare `extend-from-vector' as `inline' in order to optimize based on the
  ;; element-type and simple-ness of the NEW-ELEMENTS vector, but that would result in inlining the large
  ;; `extend-from-generator' into each callsite.

  ;; CONSIDER: locally declaring `extend-from-generator' as `notinline'.

  ;; CONSIDER: compiler-macro trickery to specialize.
  #+sbcl (declare (sb-ext:muffle-conditions sb-ext:compiler-note))
  (with-vector-generator (elts-generator new-elements)
    (extend-from-generator vec elts-generator (cl:length new-elements))))

;;; POP-BACK and helpers

(declaim (ftype (function (node height) (values (or null node) full-node height &optional))
                pop-last-node-from-body))
(defun pop-last-node-from-body (body height)
  (cond ((zerop height)
         ;; height is zero: current body becomes tail, resulting body is empty
         (values nil body 0))

        ((= (node-length body) 1)
         ;; only one child: pop from child, decrease height
         (pop-last-node-from-body (node-ref body 0) (1- height)))

        ((= height 1)
         ;; direct children are leaves: do a SV-POP-BACK to extract the last node
         (multiple-value-bind (new-body new-tail)
             (sv-pop-back body)
           (values new-body new-tail height)))

        (:otherwise
         ;; recurse to remove a tail from your last child
         (let* ((child-height (1- height))
                (num-children (node-length body))
                (num-copied-children (1- num-children)))
           (multiple-value-bind (new-last-child new-tail new-last-child-height)
               (pop-last-node-from-body (node-ref body num-copied-children)
                                        child-height)
             (with-node-generator (children-generator body)
               (values (alloc-node (concat (take children-generator num-copied-children)
                                           (generate-these (wrap-in-spine (- child-height new-last-child-height)
                                                                          new-last-child)))
                                   num-children)
                       new-tail
                       height)))))))

(declaim (ftype (function (node) (values tail-buf t &optional))
                tail-pop-back))
(defun tail-pop-back (tail)
  (if (= 1 (node-length tail))
      (values nil (node-ref tail 0))
      (sv-pop-back tail)))

(declaim (ftype (function (vec) (values vec t &optional))
                pop-back))
(defun pop-back (vec)
  "Remove the last element from VEC and return it as the secondary value.

Returns two values: a new `vec' like VEC but without its last element, and the element removed.

Signals an error of class `pop-back-empty' if VEC is empty.

# Time complexity

This operation runs in amortized O(1) time. One out of every `+branch-rate+' `pop-back's will run in
O(log_{+branch-rate+}N) time in the length of the input VEC, and the rest will run in constant time."
  (with-accessors ((tail %vec-tail)
                   (body %vec-body)
                   (length %vec-length)
                   (height %vec-height))
      vec
    (cond ((zerop length) (error 'pop-back-empty))
          (tail (multiple-value-bind (new-tail popped-element)
                    (tail-pop-back tail)
                  (values (copy-vec vec
                                    :length (1- length)
                                    :tail new-tail)
                          popped-element)))
          (:else (multiple-value-bind (new-body full-tail new-height)
                     (pop-last-node-from-body body height)
                   (multiple-value-bind (new-tail popped-element)
                       (sv-pop-back full-tail)
                     (values (%make-vec :height new-height
                                        :length (1- length)
                                        :tail new-tail
                                        :body new-body)
                             popped-element)))))))

;;; removing multiple with RETRACT (and helpers)

(declaim (ftype (function (node (or (eql 0) node-length)) (values (or null node) &optional))
                node-retract)
         (inline node-retract))
(defun node-retract (node new-length)
  (if (zerop new-length)
      nil
      (sv-retract node (node-logical-length-to-true-length new-length))))

(declaim (ftype (function (tail-length node height) (values tail-buf &optional))
                extract-tail-from-leftmost-leaf))
(defun extract-tail-from-leftmost-leaf (new-tail-length node height)
  (if (zerop height)
      (node-retract node new-tail-length)
      (extract-tail-from-leftmost-leaf new-tail-length (node-ref node 0) (1- height))))

(declaim (ftype (function (length tail-length node height) (values (or null node) tail-buf &optional))
                retract-body-at-same-height))
(defun retract-body-at-same-height (new-body-length new-tail-length body height)
  (cond ((and (zerop height)
              (= new-body-length +branch-rate+)
              (zerop new-tail-length))
         ;; height of zero implies current body is full (this is one of our invariants). if we want the whole
         ;; thing, just return it.
         (values body nil))
        ((and (zerop height)
              (zerop new-body-length))
         ;; if we want only part of the body, slice it up into a tail
         (values nil (node-retract body new-tail-length)))
        ((zerop height)
         ;; this is an invalid case; if we were supposed to deconstruct the buffer into a partial tail, we
         ;; would've hit one of the previous cases.
         (error
          "Invalid use of `retract-body-at-same-height': cannot construct a partial leaf node of length ~a"
          new-body-length))

        (:else
         ;; height >= 1: do some recursion
         (let* ((child-height (1- height))
                (elts-per-child (elts-per-node-at-height (1- height)))
                (num-verbatim-children (floor new-body-length elts-per-child))
                ;; bug: you're mis-identifying the presence of a partial child when height = 1
                (partial-child-length (- new-body-length (the length (* num-verbatim-children elts-per-child))))
                (partial-child-p (plusp partial-child-length)))
           (multiple-value-bind (partial-child new-tail)
               (if partial-child-p
                   (retract-body-at-same-height partial-child-length
                                                new-tail-length
                                                (node-ref body num-verbatim-children)
                                                child-height)
                   (values nil (extract-tail-from-leftmost-leaf new-tail-length
                                                                (node-ref body num-verbatim-children)
                                                                child-height)))
             (with-node-generator (generate-children body)
               (values (alloc-node (concat (take generate-children num-verbatim-children)
                                           (if partial-child-p
                                               (generate-these partial-child)
                                               (lambda () (done))))
                                   (+ num-verbatim-children
                                      (if partial-child-p 1 0)))
                       new-tail)))))))

(declaim (ftype (function (height length tail-length node height) (values (or null node) tail-buf &optional))
                retract-body-to-lower-height))
(defun retract-body-to-lower-height (new-height new-body-length new-tail-length body height)
  (cond ((= new-height height)
         ;; if height = new-height, we already have a function to handle this case, so call it
         (retract-body-at-same-height new-body-length new-tail-length body height))

        ((= height (1+ new-height))
         ;; if only one more step of recursion, handle an edge case where we want the whole leftmost child,
         ;; and the tail comes out of the second child.
         (let* ((elts-per-child (elts-per-node-at-height new-height))
                (tail-from-second-child-p (and (plusp new-tail-length) (= new-body-length elts-per-child))))
           (if tail-from-second-child-p
               (values (node-ref body 0)
                       (extract-tail-from-leftmost-leaf new-tail-length (node-ref body 1) new-height))

               ;; if not in that edge case, use `retract-body-at-same-height'
               (retract-body-at-same-height new-body-length new-tail-length (node-ref body 0) new-height))))

        (:else
         ;; otherwise, there's more than one step between height and new-height; recurse to close the difference.
         (retract-body-to-lower-height new-height new-body-length new-tail-length (node-ref body 0) (1- height)))))

(declaim (ftype (function (vec length) (values vec &optional))
                retract))
(defun retract (vec elts-to-remove)
  "Remove the last ELTS-TO-REMOVE elements from VEC.

If VEC contains at least ELTS-TO-REMOVE elements, return a new `vec' which removes the trailing elements. If
VEC does not contain at least ELTS-TO-REMOVE elements, signal an error of class
`retract-not-enough-elements'.

E.g.

(retract (vec 0 1 2 3 4 5) 2)
; => (vec 0 1 2 3)

# Time complexity

FIXME: analyze the time complexity of `retract'. I (pgoldman 2023-03-07) expect it to be similar to `extend',
i.e. amortized O(1) on small ELTS-TO-REMOVE, and O(log_{+branch_rate+}N) on large ELTS-TO-REMOVE."
  (with-accessors ((tail %vec-tail)
                   (body %vec-body)
                   (length %vec-length)
                   (height %vec-height))
      vec

    ;; This is a `symbol-macrolet' instead of a `let*' because we want to defer computing these values until
    ;; they are needed. The efficiency is likely inconsequential (reduced code size might even improve perf if
    ;; this were a `let*' by reducing duplication of the initforms), but it would be unsound to compute
    ;; `new-height' before the `(minusp new-length)' test checks whether `new-length' is of type `length'
    ;; (i.e. a non-negative fixnum).
    (symbol-macrolet ((tail-length (tail-buf-length tail))
                      (new-length (- length elts-to-remove))
                      (new-height (length-required-height (max new-length 0)))
                      (new-body-length (length-without-tail-buf new-length))
                      (new-tail-length (- new-length new-body-length)))

      (cond ((zerop elts-to-remove)
             ;; remove no elements: no-op
             vec)

            ((minusp new-length)
             ;; not enough elements: signal an error
             (error 'retract-not-enough-elements
                    :vec vec
                    :requested-length elts-to-remove
                    :actual-length length))

            ((zerop new-length)
             ;; remove all elements: return the empty vec singleton
             +empty+)

            ;; in all subsequent tests and branches, we know that `new-length' is of type `length'.

            ((and tail (>= tail-length elts-to-remove))
             ;; remove part of tail
             (copy-vec vec
                       :length new-length
                       :tail (node-retract tail new-tail-length)))



            ((= height new-height)
             ;; need to remove from body, but not so much to reduce height: slurp new tail out of existing
             ;; body

             (multiple-value-bind (new-body new-tail)
                 (retract-body-at-same-height (the length new-body-length)
                                              (the tail-length new-tail-length)
                                              body
                                              height)
               (%make-vec :length new-length
                          :height height
                          :body new-body
                          :tail new-tail)))

            (:otherwise
             ;; need to remove from body, which will reduce height; must extract a partial tail from the body
             (multiple-value-bind (new-body new-tail)
                 (retract-body-to-lower-height new-height
                                               (the length new-body-length)
                                               (the tail-length new-tail-length)
                                               body
                                               height)
               (%make-vec :length new-length
                          :height new-height
                          :body new-body
                          :tail new-tail)))))))

;;; altering elements at a given index with REPLACE-AT and UPDATE-AT

(declaim (ftype (function (node node-index (function (t) (values t &rest t)))
                          (values node &optional))
                node-update-at)
         ;; inline advantageous because it may allow inlining the update-element function
         (inline node-update-at))
(defun node-update-at (node index update-element)
  (sv-update-at node (node-logical-index-to-true-index index) update-element))

(declaim (ftype (function (height node index (function (t) (values t &rest t)))
                          (values node &optional))
                trie-update-at)
         ;; inline advantageous because it may allow inlining the update-element function
         (inline trie-update-at))
(defun trie-update-at (height node index update-element)
  ;; for reasons that escape me, SBCL will try to inline self-recursive functions into themselves. make it not
  ;; do that.
  (declare (notinline trie-update-at))
  (if (zerop height)
      (node-update-at node index update-element)
      (multiple-value-bind (curr remaining) (extract-index-parts-for-height height index)
        (flet ((update-in-child (child)
                 (trie-update-at (1- height)
                                 child
                                 remaining
                                 update-element)))
          (declare (dynamic-extent #'update-in-child))
          (node-update-at node curr #'update-in-child)))))

(declaim (ftype (function (vec index (function (t) (values t &rest t))) (values vec &optional))
                update-at)
         ;; save inline info for `replace-at', but we'll declare this NOTINLINE so users don't get code size
         ;; inflation.
         (inline update-at))
(defun update-at (vec index update-element)
  "Replace the element of VEC at INDEX by calling UPDATE-ELEMENT on the old element.

Find the INDEX-th element of VEC, apply UPDATE-ELEMENT to it, and return a new `vec' like VEC but with the
result of the call at INDEX.

If INDEX is out-of-bounds for VEC, signals an error of class `out-of-bounds'.

# Time complexity

This operation runs in O(log_{+branch-rate+}N) time in the length of VEC."
  (cond ((>= index (length vec))
         (error 'out-of-bounds
                :vec vec
                :index index
                :length (length vec)
                :operation 'update-at))

        ((index-in-tail-p vec index)
         (copy-vec vec
                   :tail (node-update-at (%vec-tail vec)
                                         (- index (body-length vec))
                                         update-element)))

        (:else
         (copy-vec vec
                   :body (trie-update-at (%vec-height vec)
                                          (%vec-body vec)
                                          index
                                          update-element)))))
(declaim (notinline update-at))

(declaim (ftype (function (vec index t) (values vec &optional))
                replace-at))
(defun replace-at (vec index new-element)
  "Replace the element of VEC at INDEX with NEW-ELEMENT.

Return a new `vec' like VEC but with NEW-ELEMENT at INDEX.

If INDEX is out-of-bounds for VEC, signals an error of class `out-of-bounds'.

# Time complexity

This operation runs in O(log_{+branch-rate+}N) time in the length of VEC."
  (when (>= index (length vec))
    (error 'out-of-bounds
           'vec vec
           :index index
           :length (length vec)
           :operation 'replace-at))
  (flet ((constantly-new-element (_)
           (declare (ignore _))
           new-element))
    (declare (dynamic-extent #'constantly-new-element)
             (inline update-at))
    (update-at vec index #'constantly-new-element)))

;;; easy constructor

(declaim (ftype (function (&rest t) (values vec &optional))
                vec))
(defun vec (&rest elts)
  (with-list-generator (generator elts)
    (generator-vec (cl:length elts) generator)))

;;; generating vecs (for conversions)

(declaim (ftype (function (vector) (values t &optional))
                stack-peek)
         ;; Inlining functions which access vectors may allow more efficient specialized access when the
         ;; caller knows the array's element type.
         (inline stack-peek))
(defun stack-peek (stack)
  (aref stack (1- (cl:length stack))))

(declaim (ftype (function (t vector) (values t &optional))
                (setf stack-peek))
         ;; Inlining functions which access vectors may allow more efficient specialized access when the
         ;; caller knows the array's element type.
         (inline (setf stack-peek)))
(defun (setf stack-peek) (new-element stack)
  (setf (aref stack (1- (cl:length stack)))
        new-element))

(symbol-macrolet ((height (%vec-height vec))
                  (length (%vec-length vec))
                  (body (%vec-body vec))
                  (tail (%vec-tail vec)))
  (define-generator vec ((vec vec))
                    "A generator which yields the elements of VEC in order. The ADVANCE operation is amortized O(1).

Internally, after checking for a few easy cases (empty vec or tail-only), this allocates two vectors to use as
stacks: one holding the sequence of nodes to reach a leaf, and the other holding the indices into those
nodes. ADVANCE reads from the TOP-OF-INDEX-STACKth element of the TOP-OF-NODE-STACKth node to get the next
element to yield, then increments TOP-OF-INDEX-STACK. If that increment overflows the length of
TOP-OF-NODE-STACK, it pops from each stack, increments the index there to find a new leaf TOP-NODE-OF-STACK,
and pushes it back to the vector. The pop and repush sequence will happen every +BRANCH-RATE+ elements, and
involve at most +MAX-HEIGHT+ pops, increments, and pushes each time."

      (;; are we in the tail, and what is the next tail element to yield?
       (tail-idx (unless (%vec-body vec) 0))
       ;; the path of nodes we walk to reach the current leaf
       (node-stack (let* ((stack (make-array (1+ height)
                                             :fill-pointer 0)))
                     (vector-push body stack)
                     (iter (declare (declare-variables))
                       (repeat height)
                       (vector-push (node-ref (stack-peek stack) 0) stack))
                     stack))
       ;; the path of indices into those nodes we walk to reach the next element. for
       ;; all I < Height, (node-ref (aref NODE-STACK I) (aref INDEX-STACK I)) = (aref
       ;; NODE-STACK (1+ I)), i.e. the INDEX-STACK holds the index of the node we are
       ;; currently traversing. for I = HEIGHT, the INDEX-STACK holds the index of the
       ;; next element to yield.
       (index-stack (let* ((stack (make-array (1+ height)
                                              :fill-pointer 0
                                              :element-type 'node-index)))
                      (iter (declare (declare-variables))
                        (repeat (1+ height))
                        (vector-push 0 stack))
                      stack)))

    (declare ((or null tail-length) tail-idx))
    (labels ((generate-from-tail ()
               ;; This is a manually inlined `generate-vector' with an additional check for if
               ;; there is no tail.
               (if (or (null tail) (>= tail-idx (node-length (the node ; for some reason, SBCL can't infer this
                                                                       ; from the previous `null' test.
                                                                tail))))
                   (done)
                   (prog1 (node-ref tail tail-idx)
                     (incf tail-idx))))

             (generate-from-body ()
               ;; We increment after yielding, not before, so on entry here CURRENT-NODE and
               ;; CURRENT-IDX always refer to a valid next element.
               (let* ((current-node (stack-peek node-stack))
                      (current-idx (stack-peek index-stack)))
                 (prog1 (node-ref current-node current-idx)
                   (advance-index current-node current-idx))))

             (advance-index (current-node current-idx)
               (let* ((next-idx (1+ current-idx)))
                 (if (= next-idx (node-length (the node current-node)))
                     ;; If NEXT-IDX is not a valid index into CURRENT-NODE, we need to
                     ;; re-jigger the stack to find a new leaf node.
                     (advance-to-next-node)
                     ;; Otherwise, just record the NEXT-IDX and you're done.
                     (setf (stack-peek index-stack) next-idx))))

             (advance-to-next-node ()
               ;; On entering here from ADVANCE-INDEX, we know the top of NODE-STACK and
               ;; INDEX-STACK to be invalid, so get rid of them.
               (vector-pop node-stack)
               (vector-pop index-stack)
               (if (= 0 (cl:length node-stack))
                   ;; If you're out of nodes, start generating from the tail instead.
                   (setf tail-idx 0)
                   ;; Otherwise, recursively get a new next-highest node and index.
                   (progn
                     (advance-index (stack-peek node-stack)
                                    (stack-peek index-stack))
                     ;; If the recursive call to ADVANCE-INDEX got all the way to the bottom of
                     ;; the stack and moved into the tail, don't try to continue.
                     (unless tail-idx
                       ;; But otherwise, push the next node onto the stack, and start
                       ;; traversing it at index 0.
                       (vector-push (node-ref (stack-peek node-stack) (stack-peek index-stack))
                                    node-stack)
                       (vector-push 0 index-stack))))))
      (if tail-idx
          (generate-from-tail)
          (generate-from-body)))))
(declaim (notinline generate-vec call-with-vec-generator))

;;; CONCATENATE to append vecs

(declaim (ftype (function (vec &rest vec) (values vec &optional))
                concatenate))
(defun concatenate (vec &rest other-vecs)
  "Concatenate multiple `vec's.

Returns a new VEC which contains all the elements of VEC, followed by all the elements of the OTHER-VECS in
order left to right.

# Time complexity

This operation has the same time complexity as `extend', taking the new-elements from the OTHER-VECS.

Let N be the length of VEC, and M be the sum of the lengths of all the OTHER-VECS.

For M < +BRANCH-RATE+, this operation's amortized time complexity is O((M * log_{+branch-rate+}N) /
+branch-rate+), because every (+branch-rate+ / M) `extend's will overflow the tail buffer and require
log_{+branch-rate+}N operations to splice it into the body.

For M > +BRANCH-RATE+, this operation's time complexity is O(M * log_{+branch-rate+}(M + N))."
  (declare (dynamic-extent other-vecs))
  (let* ((added-length (reduce #'+ other-vecs :key #'length)))
    (extend-from-generator vec
                           ;; TODO: figure out how to dx-allocate the generators here
                           (apply #'concat (mapcar #'generate-vec other-vecs))
                           added-length)))

;; `concatenate' cannot dx-allocate its new-elements generator because it needs to create an unpredictable
;; number of `generate-vec' generators and combine them with `concat'. But, when the number of OTHER-VECS is
;; known, it should be possible to dx-allocate the generators. A compiler macro could conceivably do this for
;; any known length of OTHER-VECS, but to avoid growing the code size, and more importantly, to avoid arcane
;; some amount of macro-ology, we'll only optimize for concatenating exactly two vecs together. A compiler
;; macro on `concatenate' will expand to a call to `concatenate-2' in that case.

(declaim (ftype (function (vec vec) (values vec &optional))
                concatenate-2))
(defun concatenate-2 (one two)
  (with-vec-generator (new-elements two)
    (extend-from-generator one new-elements (length two))))

(define-compiler-macro concatenate (&whole form vec &rest other-vecs)
  "When possible, call the more efficient `concatenate-2' instead of `concatenate'.

Also return VEC unchanged if there are no OTHER-VECS."
  (cond ((null other-vecs) vec)
        ((null (rest other-vecs)) `(concatenate-2 ,vec ,(first other-vecs)))
        (:else form)))

;;; MAP to map a function across a vec

(declaim (ftype (function ((function (t) (values t &rest t)) vec)
                          (values vec &optional))
                map))
(defun map (f vec)
  "Construct a new `vec' by applying F to each element of VEC and collecting the result.

Analogous to `mapcar' or `cl:map', but permitting only one VEC argument.

# Time complexity

This operation is O(N) in the length of VEC."
  (with-vec-generator (generate vec)
    (flet ((generate-mapped ()
             (funcall f (advance generate))))
      (declare (dynamic-extent #'generate-mapped))
      (generator-vec (length vec) #'generate-mapped))))

;;; FOR-EACH to map across a vec without collecting a result

(declaim (ftype (function ((function (t) (values &rest t)) vec)
                          (values &optional))
                for-each))
(defun for-each (f vec)
  "Apply F to each element of VEC, discarding the result.

Analogous to `cl:map' with result-type of `nil', but permitting only one VEC argument.

# Time complexity

This operation is O(N) in the length of VEC."
  (with-vec-generator (generate vec)
    (iter (declare (declare-variables))
      (repeat (the length (length vec)))
      (funcall f (advance generate))))
  (values))

;;; DO, a convenience macro around FOR-EACH

(defmacro do ((element-binding vec) &body body)
  "Evaluate the BODY for each element of VEC with ELEMENT-BINDING bound to the element.

This is a convenience macro which expands to a `for-each' call."
  `(flet ((do-function (,element-binding)
            ,@body))
     (declare (dynamic-extent #'do-function))
     (for-each #'do-function
               ,vec)))

;;; ITERATE integration

(defmacro-driver (for binding in-vec vec &optional with-index (index (gensym "FOR-IN-VEC-INDEX")))
  "Elements of a `vec'.

# Time complexity

This operation is O(N) in the length of the VEC."
  (with-gensyms (generator)
    (let ((kwd (if generate 'generate 'for)))
      ;; Unfortunately, `generate-vec' here will allocate. For all ITERATE's extensible beauty, I don't
      ;; believe there is a way for a clause to enclose the entire expansion in a WITH-FOO form, which is what
      ;; we'd need in order to dx-allocate the generator.
      `(progn (with ,generator = (generate-vec ,vec))
              (with ,index = 0)
              (,kwd ,binding next (if (>= ,index (length ,vec))
                                      (terminate)
                                      (progn (incf ,index)
                                             (advance ,generator))))))))

;;; equality comparison

(declaim (ftype (function (vec vec
                               &optional (or symbol (function (t t) (values t &rest t))))
                          (values boolean &optional))
                equal)
         ;; Inlining `equal' may allow more efficient calls to ELT-EQUAL.
         (inline equal))
(defun equal (left right &optional (elt-equal #'eql))
  (and (= (length left) (length right))
       (with-vec-generator (left-gen left)
         (with-vec-generator (right-gen right)
           (iter (declare (declare-variables))
             (repeat (length left))
             (unless (funcall elt-equal (advance left-gen) (advance right-gen))
               (return nil))
             (finally (return t)))))))

;;; printing vecs

(defmethod print-object ((vec vec) stream)
  (when (and *print-readably* (not *read-eval*))
    (error "Unable to readbly print a VEC when *READ-EVAL* is nil."))
  (when *print-readably*
    (write-string "#." stream))
  (write-string "(vec" stream)
  (with-vec-generator (generator vec)
    (iter (declare (declare-variables))
      (repeat (length vec))
      (write-char #\space stream)
      (write (advance generator) :stream stream)))
  (write-string ")" stream))

;;; converting between cl sequences and vecs

(declaim (ftype (function (vector) (values vec &optional))
                from-vector))
(defun from-vector (vector)
  (with-vector-generator (elements vector)
    (generator-vec (cl:length vector) elements)))

(declaim (ftype (function (list) (values vec &optional))
                from-list))
(defun from-list (list)
  (with-list-generator (elements list)
    (generator-vec (cl:length list) elements)))

(declaim (ftype (function (vec) (values list &optional))
                to-list))
(defun to-list (vec)
  (if (= (length vec) 0)
      nil
      (with-vec-generator (generator vec)
        (collect-to-list generator))))

(declaim (ftype (function (vec &key (:element-type t)
                               (:fill-pointer (or boolean array-length))
                               (:adjustable boolean))
                          (values vector &optional))
                to-specialized-vector)
         ;; Inlining `to-specialized-vector' may allow more efficient array operations when the ELEMENT-TYPE
         ;; is constant.
         (inline to-specialized-vector))
(defun to-specialized-vector (vec &key (element-type t)
                                        fill-pointer
                                        adjustable)
  "Convert VEC into a `vector', accepting `:element-type', `:fill-pointer' and `:adjustable' keyword arguments as to `make-array'.

`:fill-pointer' is extended to accept `t', in addition to its usual values of `nil' or an
`array-index'. Supplying `:fill-pointer t' sets the fill-pointer of the resulting vector to be equal to its
length. `:adjustable t' should likely also be supplied in this case."
  (with-vec-generator (gen vec)
    (iter (declare (declare-variables))
      (with vector = (make-array (length vec)
                                 :element-type element-type
                                 :fill-pointer (etypecase fill-pointer
                                                 (null nil)
                                                 ((eql t) (length vec))
                                                 (array-length fill-pointer))
                                 :adjustable adjustable))
      (for idx below (length vec))
      (for next-elt = (advance gen))
      (assert (typep next-elt element-type) (next-elt)
              'type-error
              :expected-type element-type
              :datum next-elt)
      (setf (aref vector idx) next-elt)
      (finally (return vector)))))

(declaim (ftype (function (vec) (values simple-vector &optional))
                to-vector))
(defun to-vector (vec)
  (to-specialized-vector vec :element-type t
                             :fill-pointer nil
                             :adjustable nil))
