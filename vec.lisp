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

(declaim (optimize (speed 3) (safety 0) (space 1) (debug 1) (compilation-speed 0)))

(eval-when (:compile-toplevel :load-toplevel)
  (declaim (type array-length +branch-rate+))
  (defconstant +branch-rate+ 32
    "The number of child nodes or elements contained in each node of a vec.")

  (declaim (type (and fixnum unsigned-byte) +node-index-bits+))
  (defconstant +node-index-bits+ (floor (log +branch-rate+ 2)))

  (declaim (type (and fixnum unsigned-byte) +max-length+))
  (defconstant +max-length+ most-positive-fixnum
    "The maximum number of elements contained in a vec.")

  (declaim (type (and fixnum unsigned-byte) +max-depth+))
  (defconstant +max-depth+ (1- (floor (log +max-length+ +branch-rate+)))
    "The number of chunks traversed from root to leaf in a vec of length +max-length+."))

(deftype node-length ()
  `(integer 1 ,+branch-rate+))

(deftype tail-length ()
  `(integer 0 ,+branch-rate+))

(deftype depth ()
  "The number of nodes to traverse from root to a leaf node.

Depth of 0 means that the current node is a leaf node, i.e. its elements are the elements of the enclosing
VEC.

Depth of 1 means that the current node's elements have depth 0, i.e. are leaf nodes.

Depth of N means that the current node's elements have depth (1- N)."
  `(integer 0 ,+max-depth+))

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

(declaim (inline %make-vec %vec-depth %vec-length %vec-body %vec-tail))

(defstruct (vec
            (:constructor %make-vec)
            (:copier nil)
            (:conc-name %vec-))
  (depth (error "Supply :DEPTH to %MAKE-VEC")
   :type depth)
  (length (error "Supply :LENGTH to %MAKE-VEC")
   :type length)
  (body (error "Supply :BODY to %MAKE-VEC")
   :type (or null node))
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

(declaim (ftype (function (depth index) (values node-index index &optional))
                extract-index-parts-for-depth)
         (inline extract-index-parts-for-depth))
(defun extract-index-parts-for-depth (depth idx)
  (let ((depth-low-bit (* depth +node-index-bits+)))
    (values (ldb (byte +node-index-bits+ depth-low-bit)
                 idx)
            (ldb (byte depth-low-bit 0)
                 idx))))

(declaim (ftype (function (node depth index) (values t &optional))
                trieref))
(defun trieref (body depth idx)
  "Index into the body part of a vector BODY at DEPTH.

IDX must be inbounds for BODY at DEPTH, meaning it must have no one bits higher than
(* (1+ depth) +node-index-bits+) and must not pass into an unallocated node."
  (if (zerop depth)
      (svref body idx)
      (multiple-value-bind (curr remaining) (extract-index-parts-for-depth depth idx)
        (trieref (svref body curr) (1- depth) remaining))))

(declaim (ftype (function (vec index) (values t &optional))
                bodyref)
         (inline bodyref))
(defun bodyref (vec idx)
  "Index into the body part of VEC. IDX must be in-bounds for VEC, and must not be `index-in-tail-p'."
  (trieref (%vec-body vec) (%vec-depth vec) idx))

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

(declaim (ftype (function (length) (values length &optional))
                length-without-tail-buf)
         (inline length-without-tail-buf))
(defun length-without-tail-buf (total-length)
  (* +branch-rate+ (floor total-length +branch-rate+)))

;;; constructing the body part of vecs

(declaim (ftype (function (depth length generator)
                          (values (or null node) &optional))
                alloc-trie))

(declaim (ftype (function (depth length generator)
                          (values (generator node) &optional))
                child-nodes-generator))

(defun alloc-trie (depth length contents)
  (cond ((zerop length) nil)
        ((zerop depth) (alloc-node contents length))
        (:otherwise (alloc-node (child-nodes-generator (1- depth) length contents)
                                (length-in-nodes-at-depth length (1- depth))))))

(defun child-nodes-generator (child-depth length-in-elts contents)
  (generator ((per-child-length (elts-per-node-at-depth child-depth))
              (remaining length-in-elts))
    (declare (type length per-child-length)
             (fixnum remaining))
    (let ((this-length (bracket 0 per-child-length remaining)))
      (declare (type length this-length))
      (if (zerop this-length)
          +uninit+
          (progn (decf remaining this-length)
                 (alloc-trie child-depth this-length contents))))))

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
                                 :depth 0
                                 :body nil
                                 :tail nil))

(declaim (ftype (function (length generator) (values vec &optional))
                generator-vec))
(defun generator-vec (length contents)
  (let* ((body-length (length-without-tail-buf length))
         (tail-length (- length body-length))
         (depth (length-required-depth body-length)))
    (%make-vec :depth depth
               :length length
               :body (alloc-trie depth body-length contents)
               :tail (make-tail tail-length contents))))

;;; internal functional updates to vecs

(declaim (ftype (function (vec &key (:depth depth)
                               (:length length)
                               (:body (or node uninit))
                               (:tail tail-buf))
                          (values vec &optional))
                copy-vec)
         (inline copy-vec))
(defun copy-vec (vec &key (depth (%vec-depth vec))
                       (length (%vec-length vec))
                       (body (%vec-body vec))
                       (tail (%vec-tail vec)))
  (%make-vec :depth depth
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

(declaim (ftype (function (depth) (values length &optional))
                max-body-length-at-depth)
         (inline max-body-length-at-depth))
(defun max-body-length-at-depth (depth)
  (expt +branch-rate+ (1+ depth)))

(declaim (ftype (function (depth node) (values node &optional))
                wrap-in-spine))
(defun wrap-in-spine (depth body)
  (if (zerop depth)
      body
      (alloc-node (generate-these body) 1)))

(declaim (ftype (function ((or node uninit) node depth length)
                          (values node &optional))
                grow-trie))
(defun grow-trie (trie new-node depth new-length-in-elts)
  (cond ((zerop depth) new-node)
        ((uninitp trie) (wrap-in-spine depth new-node))
        (t
         (let* ((length-before-in-elts (- new-length-in-elts (cl:length new-node)))
                (elts-per-node (elts-per-node-at-depth (1- depth)))
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
                                                   (wrap-in-spine (1- depth) new-node)
                                                   ;; new node has siblings
                                                   (grow-trie (svref trie length-before-in-nodes)
                                                              new-node
                                                              (1- depth)
                                                              last-node-length-in-nodes))))
                       new-length-in-nodes)))))

(declaim (ftype (function (vec t) (values vec &optional))
                conj))
(defun conj (vec new-element)
  (with-accessors ((depth %vec-depth)
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
          ((= (body-length vec) (max-body-length-at-depth depth))
           ;; fast path when your tail and body are both full: grow an extra layer of depth, put your old tail
           ;; in the newly-expanded body, then grow a new tail
           (copy-vec vec
                     :depth (1+ depth)
                     :length (1+ length)
                     :body (alloc-node (generate-these body
                                                       (wrap-in-spine depth tail))
                                       2)
                     :tail (vector new-element)))
          (t
           ;; slow path when tail is full but body is not: move your full tail into your not-full body, then
           ;; grow a new tail.
           (copy-vec vec
                     :depth depth
                     :length (1+ length)
                     :body (grow-trie body tail depth length)
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

(declaim (ftype (function (vec) (values generator &optional))
                generate-vec))
(defun generate-vec (vec)
  (generator ((i 0))
    (declare (length i))
    (if (>= i (length vec))
        (done)
        (let* ((elt (unsafe-ref vec i)))
          (incf i)
          elt))))

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
