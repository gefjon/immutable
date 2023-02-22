(uiop:define-package :immutable/vec
  (:import-from :alexandria
                #:array-index #:array-length #:define-constant #:when-let)
  (:use :cl :iterate #:immutable/%generator)
  (:shadow #:length)
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
   #:conj
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

;;; length computations

(declaim (ftype (function (vec) (values tail-length &optional))
                tail-length)
         (inline tail-length))
(defun tail-length (vec &aux (tail (%vec-tail vec)))
  (if tail
      (cl:length tail)
      0))

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

;;; computing required size, shape, depth of new vecs

(declaim (ftype (function (length) (values depth &optional))
                length-required-depth)
         (inline length-required-depth))
(defun length-required-depth (length)
  (case length
    ((0 1) 0)
    (t (values (floor (log (1- length) +branch-rate+))))))

(declaim (ftype (function (depth) (values length &optional))
                elts-per-node-at-depth)
         (inline elts-per-node-at-depth))
(defun elts-per-node-at-depth (depth)
  (expt +branch-rate+ (1+ depth)))

(declaim (ftype (function (length depth) (values length &optional))
                length-in-nodes-at-depth)
         (inline length-in-nodes-at-depth))
(defun length-in-nodes-at-depth (length-in-elts depth)
  (values (ceiling length-in-elts (elts-per-node-at-depth depth))))

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
        (:otherwise (alloc-node (child-nodes-generator (1- height) length-in-elts contents)
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
  (let* ((body-length (length-without-tail-buf length))
         (tail-length (- length body-length))
         (height (length-required-height body-length)))
    (%make-vec :height height
               :length length
               :body (alloc-trie height body-length contents)
               :tail (make-tail tail-length contents))))

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
                sv-conj))
(defun sv-conj (vector new-element
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
  (if (zerop height)
      body
      (alloc-node (generate-these body) 1)))

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
                conj))
(defun conj (vec new-element)
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
                     :tail (sv-conj tail new-element)
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

;;; easy constructor

(declaim (ftype (function (&rest t) (values vec &optional))
                vec))
(defun vec (&rest elts)
  (declare (dynamic-extent elts))
  (generator-vec (cl:length elts) (generate-list elts)))

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
          ((null body) (generate-vector tail))
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

(declaim (ftype (function (vec) (values vector &optional))
                to-vector))
(defun to-vector (vec)
  (to-specialized-vector vec :element-type t
                             :fill-pointer nil
                             :adjustable nil))
