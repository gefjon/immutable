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
           #:define-generator
           #:generate-list
           #:with-list-generator
           #:generate-these
           #:generate-vector
           #:with-vector-generator
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

(eval-when (:compile-toplevel :load-toplevel)
  (defun typed-arg-type (typed-arg)
    (etypecase typed-arg
      (symbol t)
      (cons (second typed-arg))))
  (defun typed-arg-name (typed-arg)
    (etypecase typed-arg
      (symbol typed-arg)
      (cons (first typed-arg)))))

(defmacro define-indefinite-extent-generator (make-generator (&rest typed-args) docstring (&rest bindings) &body generator-body)
  "Define a function named MAKE-GENERATOR which produces a generator.

- MAKE-GENERATOR should be a symbol which will be defined as a new function.
- TYPED-ARGS should each be either a two-element list (NAME TYPE), or a symbol NAME with implicit type
  `t'. These will be the arguments to the MAKE-GENERATOR function, and will be visible within the BINDINGS'
  initforms and the GENERATOR-BODY.
- DOCSTRING should be a string to be attached to the MAKE-GENERATOR function as documentation.
- BINDINGS should each be a (NAME INITFORM) pair, which will be bound by `let*' around the GENERATOR-BODY. The
  INITFORMs may refer to previous BINDINGS, and to the TYPED-ARGS. These bindings will persist between
  multiple invocations of a generator, and can be used to store mutable state.
- GENERATOR-BODY should be expressions which will be evaluated on each invocation of the resulting
  generator. They should either return the next value to be yielded by the generator, or call `done' to signal
  the end of the generator."
  `(progn
     (declaim (ftype (function (,@(mapcar #'typed-arg-type typed-args)) (values generator &optional))
                     ,make-generator)
              (inline ,make-generator))
     (defun ,make-generator (,@(mapcar #'typed-arg-name typed-args))
       ,docstring
       (let* (,@bindings)
         (lambda () ,@generator-body)))))

(defmacro define-dynamic-extent-generator (with-generator call-with-generator (&rest typed-args) docstring (&rest bindings) &body generator-body)
  "Define a macro named WITH-GENERATOR which evaluates its body in a dynamic context with access to a generator.

- WITH-GENERATOR should be a symbol which will be defined as a new macro.
- CALL-WITH-GENERATOR should be a symbol which will be defined as a function which will implement the
  semantics of the WITH-GENERATOR macro.
- TYPED-ARGS should each be either a two-element list (NAME TYPE), or a symbol NAME with implicit type
  `t'. These will be additional arguments to the WITH-GENERATOR macro, and will be visible within the
  BINDINGS' initforms and the GENERATOR-BODY.
- DOCSTRING should be a string to be attached to the WITH-GENERATOR macro as documentation.
- BINDINGS should each be a (NAME INITFORM) pair, which will be bound by `let*' around the GENERATOR-BODY. The
  INITFORMs may refer to previous BINDINGS, and to the TYPED-ARGS. These bindings will persist between
  multiple invocations of a generator, and can be used to store mutable state.
- GENERATOR-BODY should be expressions which will be evaluated on each invocation of the resulting
  generator. They should either return the next value to be yielded by the generator, or call `done' to signal
  the end of the generator.

The produced WITH-GENERATOR macro will have the syntax:

(WITH-GENERATOR (GENERATOR-BINDING ...ARGS)
  ...BODY)

Where
- WITH-GENERATOR is the symbol passed to `define-dynamic-extent-generator' as WITH-GENERATOR,
- GENERATOR-BINDING is a symbol to be locally bound within the BODY as a `generator', which will be declared
  `dynamic-extent',
- ARGS are expressions which evaluate to values of types appropriate for the TYPED-ARGS,
- BODY are expressions to be evaluated in a dynamic context with GENERATOR-BINDING bound to a `dynamic-extent'
  generator."
  (with-gensyms (generator-binding with-generator-body with-generator-body-function)
    `(progn
       (declaim (ftype (function (,@(mapcar #'typed-arg-type typed-args)
                                  (function (generator) (values &rest t)))
                                 (values &rest t))
                       ,call-with-generator)
                (inline ,call-with-generator))
       (defun ,call-with-generator (,@(mapcar #'typed-arg-name typed-args) thunk)
         (let* (,@bindings)
           (flet ((generator ()
                    ,@generator-body))
             (declare (dynamic-extent #'generator))
             (funcall thunk #'generator))))

       (defmacro ,with-generator ((,generator-binding ,@(mapcar #'typed-arg-name typed-args)) &body ,with-generator-body)
         ,docstring
         (list 'flet (list (list* ',with-generator-body-function (list ,generator-binding) ,with-generator-body))
               (list 'declare (list 'dynamic-extent (list 'function ',with-generator-body-function)))
               (list ',call-with-generator
                     ,@(mapcar #'typed-arg-name typed-args)
                     (list 'function ',with-generator-body-function)))))))

(defmacro define-generator (name (&rest typed-args) docstring (&rest bindings) &body generator-body)
  "Define a function NAME-generator and a macro with-NAME-generator for indefinite-extent and dynamic-extent generators, respectively.

- NAME should be a symbol which will be combined with the parts \"GENERATE-~a\" and \"WITH-~a-GENERATOR\" to
  produce the names of the resulting function and macro respectively.
- TYPED-ARGS should each be either a two-element list (NAME TYPE), or a symbol NAME with implicit type
  `t'. These will be arguments to the defined function or macro, and will be visibile within the BINDINGS'
  initforms and the GENERATOR-BODY.
- BINDINGS should each be a (NAME INITFORM) pair, which will be bound by `let*' around the GENERATOR-BODY. The
  INITFORMs may refer to previous BINDINGS, and to the TYPED-ARGS. These bindings will persist between
  multiple invocations of a generator, and can be used to store mutable state.
- GENERATOR-BODY should be expressions which will be evaluated on each invocation of the resulting
  generator. They should either return the next value to be yielded by the generator, or call `done' to signal
  the end of the generator."
  `(progn
     (define-indefinite-extent-generator ,(intern (format nil "GENERATE-~a" name) *package*)
         ,typed-args
         ,docstring
         ,bindings
       ,@generator-body)
     (define-dynamic-extent-generator ,(intern (format nil "WITH-~a-GENERATOR" name) *package*)
         ,(intern (format nil "CALL-WITH-~a-GENERATOR" name) *package*)
         ,typed-args
         ,docstring
         ,bindings
         ,@generator-body)))

(define-generator list ((list list))
                  "Generate elements of LIST in order left-to-right."
    ((next list))
  (if next
      (pop next)
      (done)))

(declaim (ftype (function (&rest t) (values generator &optional))
                generate-these)
         (inline generate-these))
(defun generate-these (&rest elts)
  "Generate the ELTS in order left-to-right."
  (generate-list elts))

(define-generator vector ((vector vector))
                  "Generate elements of VECTOR left-to-right.

If VECTOR has a fill pointer, only generate elements before the fill pointer.

The consequences are undefined if VECTOR is destructively modified during generation. This includes:
- Altering its contents via `setf' of `aref' or any other operator.
- Changing its fill pointer via `setf' of `fill-pointer', `vector-push', `vector-push-extend', or any other
  operator.
- For adjustable vectors, adjusting its dimensions or `displaced-to' array with `adjust-array',
  `vector-push-extend' or any other operator. This includes arrays which are not expressly adjustable, but are
  acutally adjustable per `array-adjustable-p'.

Making any of these actions may cause a generator which had previously signaled `done' to produce
new elements, or do other weird stuff."
    ((i 0))
  (declare (type array-index i))
  (if (< i (length vector)) (prog1 (aref vector i)
                              (incf i))
      (done)))

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
