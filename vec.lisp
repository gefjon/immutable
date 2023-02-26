(uiop:define-package :immutable/vec
  (:import-from :alexandria
                #:array-index #:array-length #:define-constant #:when-let)
  (:use :cl :iterate #:immutable/%generator)
  (:shadow #:length #:equal)
  (:export
   #:out-of-bounds
   #:out-of-bounds-index
   #:out-of-bounds-length
   #:out-of-bounds-vec
   #:vec
   #:+empty+
   #:unsafe-ref
   #:ref
   #:length
   #:push-back
   #:extend
   #:pop-back
   #:equal
   #:from-list #:to-list
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

(deftype node ()
  `(or ,@(iter (declare (declare-variables))
           (for (the array-length i) from 1 to +branch-rate+)
           (collect `(simple-vector ,i)))))

(deftype full-node ()
  `(simple-vector ,+branch-rate+))

;; constructing nodes

(declaim (ftype (function (generator node-length) (values node &optional))
                alloc-node))
(defun alloc-node (contents-iterator length-in-children)
  (let* ((arr (make-array length-in-children)))
    (iter (declare (declare-variables))
      (for (the fixnum i) below length-in-children)
      (setf (svref arr (the array-index i)) (advance contents-iterator)))
    arr))

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
  ((%vec :initarg :vec
         :reader out-of-bounds-vec)
   (%length :type unsigned-byte
            :initarg :length
            :reader out-of-bounds-length)
   (%index :type unsigned-byte
           :initarg :index
           :reader out-of-bounds-index))
  (:report (lambda (c s)
             (format s "Invalid index ~d for VEC of length ~d: ~a"
                     (out-of-bounds-index c)
                     (out-of-bounds-length c)
                     (out-of-bounds-vec c)))))

;;; condition class for pop-back from empty

(define-condition pop-back-empty (error)
  ()
  (:report (lambda (c s)
             (declare (ignore c))
             (write-string "Attempt to POP-BACK from empty VEC" s))))

;;; length computations

(declaim (ftype (function (tail-buf) (values tail-length &optional))
                tail-buf-length)
         (inline tail-buf-length))
(defun tail-buf-length (tail-buf)
  (if tail-buf
      (cl:length tail-buf)
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
  (svref (%vec-tail vec) (- idx (body-length vec))))

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
      (svref body idx)
      (multiple-value-bind (curr remaining) (extract-index-parts-for-height height idx)
        (trieref (svref body curr) (1- height) remaining))))

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
             :index idx)
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

;;; constructing vecs

(declaim (type vec +empty+))
(defparameter +empty+ (%make-vec :length 0
                                 :height 0
                                 :body nil
                                 :tail nil))

(declaim (ftype (function (length generator) (values vec &optional))
                generator-vec))
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
         (inline tail-has-room-p))
(defun tail-has-room-p (tail)
  (if tail
      (< (cl:length tail)
         +branch-rate+)
      t))

(declaim (ftype (function (simple-vector t) (values simple-vector &optional))
                sv-push-back))
(defun sv-push-back (vector new-element
                &aux (new-vector (make-array (1+ (cl:length vector)))))
  (iter (declare (declare-variables))
    (for elt in-vector vector with-index idx)
    (setf (svref new-vector idx) elt))
  (setf (svref new-vector (cl:length vector)) new-element)
  new-vector)

(declaim (ftype (function (height) (values length &optional))
                max-body-length-at-height)
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
         (let* ((length-before-in-elts (- new-length-in-elts (cl:length new-node)))
                (elts-per-node (elts-per-node-at-height (1- height)))
                (new-length-in-nodes (ceiling new-length-in-elts
                                              elts-per-node))
                (length-before-in-nodes (floor length-before-in-elts
                                               elts-per-node))
                (last-node-length-in-nodes (- new-length-in-nodes length-before-in-nodes)))
           (declare (node-length new-length-in-nodes
                                 length-before-in-nodes
                                 last-node-length-in-nodes))
           (alloc-node (concat (take (generate-vector trie) length-before-in-nodes)
                               (generate-these (if (= length-before-in-nodes (cl:length trie))
                                                   ;; new node is the leftmost in its subtree
                                                   (wrap-in-spine (1- height) new-node)
                                                   ;; new node has siblings
                                                   (grow-trie (svref trie length-before-in-nodes)
                                                              new-node
                                                              (1- height)
                                                              last-node-length-in-nodes))))
                       new-length-in-nodes)))))

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
                     :tail (vector new-element)
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
                     :tail (vector new-element)))
          (t
           ;; slow path when tail is full but body is not: move your full tail into your not-full body, then
           ;; grow a new tail.
           (copy-vec vec
                     :height height
                     :length (1+ length)
                     :body (grow-trie body tail height length)
                     :tail (vector new-element))))))

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
                                             (- length-in-elts +branch-rate+)
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
  (let* ((child-height (1- height))
         (elts-per-full-child (elts-per-node-at-height child-height))
         (num-full-leading-children (floor current-length-in-elts elts-per-full-child))
         (partial-child-p (not (= num-full-leading-children (cl:length not-full-node))))
         (length-in-children (trie-length-in-nodes-at-height target-length-in-elts
                                                             child-height)))
    (declare (height child-height)
             (length elts-per-full-child)
             (node-length num-full-leading-children
                          length-in-children))
    (if (not partial-child-p)
        ;; If all our children are full, this operation is easy: construct a new node which has all of the
        ;; existing children, followed by new nodes taken from the NEW-ELEMENTS.
        (alloc-node (concat (generate-vector not-full-node)
                            (child-nodes-generator child-height
                                                   (- target-length-in-elts current-length-in-elts)
                                                   new-elements))
                    length-in-children)

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
               (new-children-length-in-elts (- target-length-in-elts
                                               full-leading-children-length-in-elts
                                               new-elts-to-fill-partial-existing-child)))
          (declare (length full-leading-children-length-in-elts
                           partial-existing-child-length-in-elts
                           new-elts-to-fill-partial-existing-child
                           available-new-elts
                           filled-partial-existing-child-length-in-elts
                           new-children-length-in-elts))
          (alloc-node (concat (take (generate-vector not-full-node) num-full-leading-children)
                              (generate-these (extend-node-at-height (svref not-full-node num-full-leading-children)
                                                                     child-height
                                                                     partial-existing-child-length-in-elts
                                                                     new-elements
                                                                     filled-partial-existing-child-length-in-elts))
                              (child-nodes-generator child-height
                                                     new-children-length-in-elts
                                                     new-elements))
                      length-in-children)))))

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
         (inline generate-tail))
(defun generate-tail (tail-buf)
  (if tail-buf
      (generate-vector tail-buf)
      (lambda () (done))))

(declaim (ftype (function (vec generator length) (values vec &optional))
                extend-from-generator))
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
                       :tail (make-tail (the tail-length (+ added-length (tail-length vec)))
                                        (concat (generate-tail tail) new-elements))))

            ((and (not body)
                  (= (tail-length vec) +branch-rate+))
             ;; no body, full tail: fold tail buf into body, then grow from new-elements.
             (%make-vec :height new-height
                        :length new-length
                        :body (fill-behind-node-to-height new-height tail 0 new-elements new-length)
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
                extend)
         (inline extend))
(defun extend (vec &rest new-elements)
  "Return a new `vec' with all the contents of VEC followed by the NEW-ELEMENTS.

This operation will attempt to share as much structure as possible with the original VEC.

# Time complexity

Let N be the number of elements in VEC, and M be the number of NEW-ELEMENTS.

For M < +BRANCH-RATE+, this operation's amortized time complexity is O((M * log_{+branch-rate+}N) /
+branch-rate+), because every (+branch-rate+ / M) `extend's will overflow the tail buffer and require
log_{+branch-rate+}N operations to splice it into the body.

For M > +BRANCH-RATE+, this operation's time complexity is O(M * log_{+branch-rate+}N)."
  (declare (dynamic-extent new-elements))
  (extend-from-generator vec (generate-list new-elements) (cl:length new-elements)))

;;; PUSH-BACK and helpers

(declaim (ftype (function (simple-vector) (values (or null simple-vector) t &optional))
                sv-pop-back))
(defun sv-pop-back (simple-vector &aux (len (cl:length simple-vector)))
  (if (zerop len)
      (error 'pop-back-empty)
      (let* ((new-len (1- len))
             (popped-elt (svref simple-vector new-len)))
        (values (unless (zerop new-len)
                  (let* ((new-vector (make-array new-len)))
                    (iter (for i below new-len)
                      (setf (svref new-vector i) (svref simple-vector i)))
                    new-vector))
                popped-elt))))

(declaim (ftype (function (node height) (values (or null node) full-node height &optional))
                pop-last-node-from-body))
(defun pop-last-node-from-body (body height)
  (cond ((zerop height)
         ;; height is zero: current body becomes tail, resulting body is empty
         (values nil body 0))

        ((= (cl:length body) 1)
         ;; only one child: pop from child, decrease height
         (pop-last-node-from-body (svref body 0) (1- height)))

        ((= height 1)
         ;; direct children are leaves: do a SV-POP-BACK to extract the last node
         (multiple-value-bind (new-body new-tail)
             (sv-pop-back body)
           (values new-body new-tail height)))

        (:otherwise
         ;; recurse to remove a tail from your last child
         (let* ((child-height (1- height))
                (num-children (cl:length body))
                (num-copied-children (1- num-children)))
           (multiple-value-bind (new-last-child new-tail new-last-child-height)
               (pop-last-node-from-body (svref body num-copied-children)
                                        child-height)
             (values (alloc-node (concat (take (generate-vector body) num-copied-children)
                                         (generate-these (wrap-in-spine (- child-height new-last-child-height)
                                                                        new-last-child)))
                                 num-children)
                     new-tail
                     height))))))

(declaim (ftype (function (vec) (values vec t &optional))
                pop-back))
(defun pop-back (vec)
  (with-accessors ((tail %vec-tail)
                   (body %vec-body)
                   (length %vec-length)
                   (height %vec-height))
      vec
    (cond ((zerop length) (error 'pop-back-empty))
          (tail (multiple-value-bind (new-tail popped-element)
                    (sv-pop-back tail)
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

;;; easy constructor

(declaim (ftype (function (&rest t) (values vec &optional))
                vec))
(defun vec (&rest elts)
  (declare (dynamic-extent elts))
  (generator-vec (cl:length elts) (generate-list elts)))

;;; equality comparison

(declaim (ftype (function (vec vec
                               &optional (or symbol (function (t t) (values t &rest t))))
                          (values boolean &optional))
                equal)
         (inline equal))
(defun equal (left right &optional (elt-equal #'eql))
  (and (= (length left) (length right))
       (let* ((left-gen (generate-vec left))
              (right-gen (generate-vec right)))
         (iter (declare (declare-variables))
           (repeat (length left))
           (unless (funcall elt-equal (advance left-gen) (advance right-gen))
             (return-from equal nil))
           (finally (return-from equal t))))))

;;; printing vecs

(defmethod print-object ((vec vec) stream)
  (when (and *print-readably* (not *read-eval*))
    (error "Unable to readbly print a VEC when *READ-EVAL* is nil."))
  (when *print-readably*
    (write-string "#." stream))
  (write-string "(vec" stream)
  (iter (declare (declare-variables))
    (for i below (the length (length vec)))
    (write-char #\space stream)
    (write (ref vec i) :stream stream))
  (write-string ")" stream))

;;; generating vecs (for conversions)

(declaim (ftype (function (vector) (values t &optional))
                stack-peek)
         (inline stack-peek))
(defun stack-peek (stack)
  (aref stack (1- (cl:length stack))))

(declaim (ftype (function (t vector) (values t &optional))
                (setf stack-peek))
         (inline (setf stack-peek)))
(defun (setf stack-peek) (new-element stack)
  (setf (aref stack (1- (cl:length stack)))
        new-element))

(declaim (ftype (function (vec) (values generator &optional))
                generate-vec))
(defun generate-vec (vec)
  "A generator which yields the elements of VEC in order. The ADVANCE operation is amortized O(1).

Internally, after checking for a few easy cases (empty vec or tail-only), this allocates two vectors to use as
stacks: one holding the sequence of nodes to reach a leaf, and the other holding the indices into those
nodes. ADVANCE reads from the TOP-OF-INDEX-STACKth element of the TOP-OF-NODE-STACKth node to get the next
element to yield, then increments TOP-OF-INDEX-STACK. If that increment overflows the length of
TOP-OF-NODE-STACK, it pops from each stack, increments the index there to find a new leaf TOP-NODE-OF-STACK,
and pushes it back to the vector. The pop and repush sequence will happen every +BRANCH-RATE+ elements, and
involve at most +MAX-HEIGHT+ pops, increments, and pushes each time."
  (let* ((height (%vec-height vec))
         (body (%vec-body vec))
         (tail (%vec-tail vec)))
    (cond ((and (null body) (null tail)) (lambda () (done)))
          ((null body) (generate-tail tail))
          (:else (generator (;; are we in the tail, and what is the next tail element to yield?
                             (tail-idx nil)

                             ;; the path of nodes we walk to reach the current leaf
                             (node-stack (let* ((stack (make-array (1+ height)
                                                                   :fill-pointer 0)))
                                           (vector-push body stack)
                                           (iter (declare (declare-variables))
                                             (repeat height)
                                             (vector-push (svref (stack-peek stack) 0) stack))
                                           stack))

                             ;; the path of indices into those nodes we walk to reach the next element. for
                             ;; all I < Height, (svref (aref NODE-STACK I) (aref INDEX-STACK I)) = (aref
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
                              (if (or (null tail) (>= tail-idx (cl:length tail)))
                                  (done)
                                  (prog1 (svref tail tail-idx)
                                    (incf tail-idx))))

                            (generate-from-body ()
                              ;; We increment after yielding, not before, so on entry here CURRENT-NODE and
                              ;; CURRENT-IDX always refer to a valid next element.
                              (let* ((current-node (stack-peek node-stack))
                                     (current-idx (stack-peek index-stack)))
                                (prog1 (svref current-node current-idx)
                                  (advance-index current-node current-idx))))

                            (advance-index (current-node current-idx)
                              (let* ((next-idx (1+ current-idx)))
                                (if (= next-idx (cl:length (the node current-node)))
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
                                      (vector-push (svref (stack-peek node-stack) (stack-peek index-stack))
                                                   node-stack)
                                      (vector-push 0 index-stack))))))
                     (if tail-idx
                         (generate-from-tail)
                         (generate-from-body))))))))

;;; converting between cl sequences and vecs

(declaim (ftype (function (vector) (values vec &optional))
                from-vector))
(defun from-vector (vector)
  (generator-vec (cl:length vector) (generate-vector vector)))

(declaim (ftype (function (list) (values vec &optional))
                from-list))
(defun from-list (list)
  (generator-vec (cl:length list) (generate-list list)))

(declaim (ftype (function (vec) (values list &optional))
                to-list))
(defun to-list (vec)
  (if (= (length vec) 0)
      nil
      (collect-to-list (generate-vec vec))))

(declaim (ftype (function (vec &key (:element-type t)
                               (:fill-pointer (or boolean array-length))
                               (:adjustable boolean))
                          (values vector &optional))
                to-specialized-vector)
         (inline to-specialized-vector))
(defun to-specialized-vector (vec &key (element-type t)
                                        fill-pointer
                                        adjustable)
  (iter (declare (declare-variables))
    (with vector = (make-array (length vec)
                               :element-type element-type
                               :fill-pointer (etypecase fill-pointer
                                               (null nil)
                                               ((eql t) (length vec))
                                               (array-length fill-pointer))
                               :adjustable adjustable))
    (with gen = (generate-vec vec))
    (for idx below (length vec))
    (setf (aref vector idx) (advance gen))
    (finally (return vector))))

(declaim (ftype (function (vec) (values simple-vector &optional))
                to-vector))
(defun to-vector (vec)
  (to-specialized-vector vec :element-type t
                             :fill-pointer nil
                             :adjustable nil))
