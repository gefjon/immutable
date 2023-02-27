(uiop:define-package #:immutable/%generator
  (:use :cl :iterate)
  (:import-from :alexandria
                #:define-constant
                #:array-index
                #:array-length
                #:with-gensyms)
  (:export #:generator
           #:done
           #:advance
           #:generate-list
           #:with-list-generator
           #:generate-these
           #:generate-vector
           #:with-vector-generator
           #:generate-constantly
           #:do-generator
           #:collect-to-list
           #:collect-to-vector
           #:concat
           #:take))
(in-package #:immutable/%generator)

;;; early defs

(deftype generator (&optional (element-type 't))
  "A generator is a closure which takes no arguments and returns successive elements on each invocation, signaling `done' when no elements remain."
  `(function () (values ,element-type &optional)))

(define-condition done ()
  ())

(declaim (ftype (function () nil) done)
         (inline done))
(defun done ()
  "Signal that a generator has finished"
  (error 'done))

(defmacro generator (vars &body body)
  "Construct a generator which closes over VARS and evaluates BODY on each invocation.

VARS are treated as in `let*'."
  `(let* (,@vars)
     (flet ((generator-closure ()
              ,@body))
       #'generator-closure)))

(declaim (ftype (function (generator) (values t &optional)) advance)
         (inline advance))
(defun advance (generator)
  "Advance GENERATOR, returning its next element, or signaling `done' if none remain."
  (funcall generator))

;;; constructing/producing generators

(declaim (type generator +empty-generator+))
(define-constant +empty-generator+ (generator () (done))
  :test (constantly t) ;; no useful way to compare generators, so just don't incompatibly redefine this lmao
  )

(declaim (ftype (function (list) (values generator &optional))
                generate-list)
         (inline generate-list))
(defun generate-list (list)
  "Generate elements of LIST in order left-to-right."
  (generator ((next list))
    (if next (pop next)
        (done))))

(declaim (ftype (function (list (function (generator) (values &rest t)))
                          (values &rest t))
                call-with-list-generator)
         (inline call-with-list-generator))
(defun call-with-list-generator (list thunk)
  (let* ((next list))
    (flet ((generator ()
             (if next
                 (pop next)
                 (done))))
      (declare (dynamic-extent #'generator))
      (funcall thunk #'generator))))

(defmacro with-list-generator ((generator-binding list) &body body)
  "Invoke BODY with GENERATOR-BINDING bound to a dynamic-extent `generator' which yields the elements from LIST.

This is an interface to provide a similar functionality as `generate-list', but with the generator closure
stack-allocated. The LIST will not be dynamic-extent allocated unless otherwise arranged."
  `(call-with-list-generator ,list (lambda (,generator-binding) ,@body)))

(declaim (ftype (function (&rest t) (values generator &optional))
                generate-these)
         (inline generate-these))
(defun generate-these (&rest elts)
  "Generate the ELTS in order left-to-right."
  (generate-list elts))

(declaim (ftype (function (vector) (values generator &optional))
                generate-vector)
         (inline generate-vector))
(defun generate-vector (vec)
  "Generate elements of VEC left-to-right.

If VEC has a fill pointer, only generate elements before the fill pointer.

The consequences are undefined if VEC is destructively modified during generation. This includes:
- Altering its contents via `setf' of `aref' or any other operator.
- Changing its fill pointer via `setf' of `fill-pointer', `vector-push', `vector-push-extend', or any other
  operator.
- For adjustable vectors, adjusting its dimensions or `displaced-to' array with `adjust-array',
  `vector-push-extend' or any other operator. This includes arrays which are not expressly adjustable, but are
  acutally adjustable per `array-adjustable-p'.

Making any of these actions may cause a generator which had previously signaled `done' to produce
new elements, or do other weird stuff."
  (generator ((i 0))
    (declare (type array-index i))
    (if (< i (length vec)) (prog1 (aref vec i)
                             (incf i))
        (done))))

(declaim (ftype (function (vector (function (generator) (values &rest t)))
                          (values &rest t))
                call-with-vector-generator)
         (inline call-with-vector-generator))
(defun call-with-vector-generator (vector thunk)
  (let* ((next-idx 0))
    (declare (type array-index next-idx))
    (flet ((generator ()
             (if (< next-idx (length vector))
                 (prog1 (aref vector next-idx)
                   (incf next-idx))
                 (done))))
      (declare (dynamic-extent #'generator))
      (funcall thunk #'generator))))

(defmacro with-vector-generator ((generator-binding vector) &body body)
  "Invoke BODY with GENERATOR-BINDING bound to a dynamic-extent `generator' which yields the elements from VECTOR.

This is an interface to provide a similar functionality as `generate-vector', but with the generator closure
stack-allocated. The VECTOR will not be dynamic-extent allocated unless otherwise arranged."
  `(call-with-vector-generator ,vector (lambda (,generator-binding) ,@body)))

(declaim (ftype (function (t) (values generator &optional))
                generate-constantly)
         (inline generate-constantly))
(defun generate-constantly (item)
  "Generate ITEM forever, never terminating."
  (generator ()
    item))

;;; iterating over generators

(declaim (ftype (function (function generator &optional function) (values &rest t))
                call-with-generator-elements)
         (inline call-with-generator-elements))
(defun call-with-generator-elements (thunk generator &optional (end-thunk (constantly nil)))
  "Invoke THUNK on each element of GENERATOR as by `multiple-value-call'.

THUNK should accept as many elements as are produced by GENERATOR.

If END-THUNK is provided, call it with no arguments last and return its values."
  (handler-case (loop (multiple-value-call thunk (advance generator)))
    (done () (funcall end-thunk))))

(defmacro do-generator ((vars generator &optional result) &body body)
  "Analogous to `dotimes'. Evaluate BODY for the  element VARS in GENERATOR, then return RESULT.

VARS should be either a lambda list or a symbol. Bare symbols will be bound to the primary value of each
element; lambda lists will be applied to all the values of each element."
  (let* ((thunk (etypecase vars
                  (list `(lambda ,vars
                           ,@body))
                  (symbol (with-gensyms (ignore)
                            `(lambda (,vars &rest ,ignore)
                               (declare (ignore ,ignore))
                               ,@body))))))
    `(call-with-generator-elements ,thunk ,generator (lambda () ,result))))

;;; collecting into strict CL sequences

(declaim (ftype (function (generator) (values list &optional))
                collect-to-list)
         (inline collect-to-list))
(defun collect-to-list (generator)
  (let* ((list nil))
    (do-generator (elt generator (nreverse list))
      (push elt list))))

(declaim (ftype (function (generator
                           &key (:element-type t)
                            (:length-hint array-length))
                          (values vector &optional))
                collect-to-vector)
         (inline collect-to-vector))
(defun collect-to-vector (generator &key (element-type t) (length-hint 0))
  (let* ((vec (make-array length-hint
                          :fill-pointer 0
                          :element-type element-type
                          :adjustable t)))
    (do-generator (elt generator vec)
      (vector-push-extend elt vec))))

;;; combining gnerators

(declaim (ftype (function (&rest generator) (values generator &optional))
                concat))
(defun concat (&rest generators &aux (stack generators))
  "A generator which yields all of the elements of the GENERATORS, in order from right to left."
  (labels ((concat-generator ()
             (if (null stack)
                 (done)
                 (handler-case (advance (first stack))
                   (done ()
                     (pop stack)
                     (concat-generator))))))
    #'concat-generator))

(declaim (ftype (function (generator (and unsigned-byte fixnum)) (values generator &optional))
                take))
(defun take (generator count)
  "A generator which yields at most COUNT elements of GENERATOR."
  (generator ((remaining count))
    (declare (type (and unsigned-byte fixnum) remaining))
    (if (not (plusp remaining))
        (done)
        (progn
          (decf remaining)
          (advance generator)))))
