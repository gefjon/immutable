(uiop:define-package #:immutable/%simple-vector-utils
  (:use :cl :iterate #:immutable/%generator)
  (:import-from :alexandria
                #:array-length #:array-index
                #:with-gensyms
                #:symbolicate)
  (:export
   #:sv-push-back
   #:sv-pop-back
   #:sv-retract
   #:sv-update-at
   #:sv-replace-at
   #:sv-insert-at
   #:sv-remove-at
   #:sv-2-other-index
   #:sv-copy-subrange

   #:vector-struct-name

   #:define-vector-struct))
(in-package #:immutable/%simple-vector-utils)

(declaim (ftype (function (simple-vector t) (values simple-vector &optional))
                sv-push-back))
(defun sv-push-back (vector new-element
                &aux (new-vector (make-array (1+ (cl:length vector)))))
  (iter (declare (declare-variables))
    (for elt in-vector vector with-index idx)
    (setf (svref new-vector idx) elt))
  (setf (svref new-vector (cl:length vector)) new-element)
  new-vector)

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

(declaim (ftype (function (simple-vector array-length) (values (or null simple-vector) &optional))
                sv-retract)
         (inline sv-retract))
(defun sv-retract (simple-vector new-length)
  (unless (zerop new-length)
    (let* ((new-sv (make-array new-length)))
      (iter (declare (declare-variables))
        (for i below new-length)
        (setf (svref new-sv i) (svref simple-vector i)))
      new-sv)))

(declaim (ftype (function (simple-vector array-index (function (t) (values t &rest t)))
                          (values simple-vector &optional))
                sv-update-at)
         ;; inline advantageous because it may allow inlining the update-element function
         (inline sv-update-at))
(defun sv-update-at (simple-vector index update-element)
  (let* ((copy (copy-seq simple-vector)))
    (setf (svref copy index) (funcall update-element (svref copy index)))
    copy))

(declaim (ftype (function (simple-vector array-index t) (values simple-vector &optional))
                sv-replace-at))
(defun sv-replace-at (simple-vector index new-element)
  (sv-update-at simple-vector index (constantly new-element)))

(declaim (ftype (function (simple-vector array-index t)
                          (values simple-vector &optional))
                sv-insert-at))
(defun sv-insert-at (simple-vector index new-element)
  (let* ((new-vector (make-array (1+ (length simple-vector))))
         (fill-index -1))
    (declare ((or (eql -1) array-index) fill-index))
    (flet ((insert (value)
             (setf (svref new-vector (incf fill-index))
                   value)))
      (iter (declare (declare-variables))
        (for element in-vector simple-vector with-index source-index)
        (when (= source-index index)
          (insert new-element))
        (insert element)
        (finally (when (= source-index index)
                   (insert new-element)))))
    new-vector))

(declaim (ftype (function (simple-vector array-index)
                          (values simple-vector &optional))
                sv-remove-at))
(defun sv-remove-at (simple-vector index)
  (let* ((new-vector (make-array (1- (length simple-vector))))
         (fill-index -1))
    (declare ((or (eql -1) array-index) fill-index))
    (flet ((insert (value)
             (setf (svref new-vector (incf fill-index))
                   value)))
      (iter (declare (declare-variables))
        (for element in-vector simple-vector with-index source-index)
        (unless (= source-index index)
          (insert element))))
    new-vector))

(declaim (ftype (function ((simple-vector 2) bit) (values t &optional))
                sv-2-other-index))
(defun sv-2-other-index (simple-vector index)
  (svref simple-vector
         (if (zerop index) 1 0)))

(declaim (ftype (function (simple-vector simple-vector
                                         &key (:count (or null array-length))
                                         (:target-start array-index) (:source-start array-index))
                          (values &optional))
                sv-copy-subrange)
         ;; inlining may allow the compiler to specialize on whether key args are or aren't passed.
         (inline sv-copy-subrange))
(defun sv-copy-subrange (target source &key
                                         (target-start 0) (source-start 0)
                                         count
                         &aux (really-count (min (or count most-positive-fixnum)
                                                 (- (length target) target-start)
                                                 (- (length source) source-start))))
  (declare (array-length really-count))
  (iter (declare (declare-variables))
    (for (the fixnum i) below really-count)
    (setf (svref target (+ i target-start))
          (svref source (+ i source-start))))
  (values))

(declaim (ftype (function (simple-vector) (values symbol &optional))
                vector-struct-name)
         (inline vector-struct-name))
(defun vector-struct-name (vector-struct)
  "Return the NAME of VECTOR-STRUCT, which must be an instance of a `define-vector-struct' defined with `:name t'."
  (svref vector-struct 0))

(defmacro define-vector-struct (name
                                (&key max-length
                                   (ref nil ref-supplied-p)
                                   (constructor nil ctor-supplied-p)
                                   (conc-name (format nil "~a-" name))
                                   ((:length length-name) nil length-supplied-p)
                                   (logical-index-to-true-index nil)
                                   (logical-length-to-true-length nil)
                                   named)
                                &body slot-descriptors)
  "Define a structured vector type with named slots followed by indexed elements.

Each of the SLOT-DESCRIPTORS may be either:
- A symbol SLOT-NAME.
- A list of the form (SLOT-NAME &key TYPE INITFORM).
If unsupplied, slots' types default to T, and their initforms to nil.

If NAMED is true, a slot will be added before the SLOT-DESCRIPTORS which always holds the symbol NAME. It can
be accessed using `vector-struct-name'. The behavior of applying `vector-struct-name' to any object except a
vector-struct with `:named' supplied is undefined.

A accessor for each of the SLOT-DESCRIPTORS will be defined, named by concatenating CONC-NAME with the
SLOT-NAME, as per `defstruct'. `:read-only' slots are not supported; if you don't want to mutate the slots,
just don't mutate them.

NAME will be defined by `deftype' as an alias for `simple-vector'.

If MAX-LENGTH is supplied, it must be a literal integer. Instances will be restricted to containing at most
MAX-LENGTH indexed elements.

If REF is not nil, it will be defined as a function which accepts an instance and a zero-based index, and
returns the associated indexed element from the index. REF defaults to NAME-ref.

If LENGTH is not nil, it will be defined as a function which accepts an instance, and returns the number of
indexed elements. LENGTH defaults to NAME-length.

If CONSTRUCTOR is not nil, it will be defined as a function which accepts a keyword argument for each slot,
plus `:length', `:initial-element' and `:initial-contents'. `:length' is mandatory, and is the number of
indexed elements in the new instance. `:initial-element' and `:initial-contents' are mutually exclusive, but
neither is mandatory. `:initial-element', if supplied, is used to pre-populate each of the indexed
elements. `:initial-contents', if supplied, should be a `generator' which will yield at least `:length'
elements, which will be stored into the indexed elements.

If LOGICAL-INDEX-TO-TRUE-INDEX is supplied, it should be a symbol. It will be defined as a function which
transforms \"logical\" indices of the indexed elements, starting from zero, into \"true\" indices appropriate
for `svref' into the underlying vector.

LOGICAL-LENGTH-TO-TRUE-LENGTH is like LOGICAL-INDEX-TO-TRUE-INDEX, but with an inclusive rather than exclusive
upper bound. This is analogous to the difference between `alexandria:array-length' and
`alexandria:array-index'.

The constructor, length-function, ref-function, logical-index-to-true-index-function, and slot-accessors will
all be declared globally `inline'."
  (flet ((make-name (&rest stuff)
           (apply #'symbolicate conc-name stuff)))
    (let* ((num-slots (+ (length slot-descriptors)
                         (if named 1 0)))
           (logical-length-type (make-name "LENGTH"))
           (logical-index-type (make-name "INDEX"))
           (max-logical-length (or max-length
                                   (- array-dimension-limit num-slots)))
           (max-logical-index (1- max-logical-length))
           (max-true-length (+ max-logical-length num-slots))
           (max-true-index (+ max-logical-index num-slots))

           (ctor-name (if ctor-supplied-p
                          constructor
                          (symbolicate "MAKE-" name)))

           (ref-name (if ref-supplied-p
                         ref
                         (symbolicate name "-REF")))

           (length-name (if length-supplied-p
                            length-name
                            (symbolicate name "-LENGTH")))
           (logical-index-to-true-index (or logical-index-to-true-index
                                            (gensym "LOGICAL-INDEX-TO-TRUE-INDEX-")))
           (logical-length-to-true-length (or logical-length-to-true-length
                                              (gensym "LOGICAL-LENGTH-TO-TRUE-LENGTH-"))))

      (with-gensyms (true-length-type
                     true-index-type
                     true-length-to-logical-length)
        (labels ((slot-name (slot-descriptor)
                   (etypecase slot-descriptor
                     (symbol slot-descriptor)
                     (cons (first slot-descriptor))))

                 (slot-initarg (slot-descriptor)
                   (intern (string (slot-name slot-descriptor)) "KEYWORD"))

                 (slot-type (slot-descriptor)
                   (etypecase slot-descriptor
                     (symbol t)
                     (cons (getf (rest slot-descriptor) :type t))))

                 (slot-initform (slot-descriptor)
                   (etypecase slot-descriptor
                     (symbol nil)
                     (cons (getf (rest slot-descriptor) :initform))))

                 (slot-accessor-name (slot-descriptor)
                   (make-name (slot-name slot-descriptor)))

                 (slot-position (slot-descriptor)
                   (+ (position slot-descriptor slot-descriptors :test #'eq)
                      (if named 1 0)))

                 (define-accessor (slot-descriptor &aux (accessor-name (slot-accessor-name slot-descriptor)))
                   `(progn
                      (declaim (ftype (function (,name) (values ,(slot-type slot-descriptor) &optional))
                                      ,accessor-name)
                               (inline ,accessor-name))
                      (defun ,accessor-name (instance)
                        (svref instance ,(slot-position slot-descriptor)))

                      (declaim (ftype (function (,(slot-type slot-descriptor) ,name)
                                                (values ,(slot-type slot-descriptor) &optional))
                                      (setf ,accessor-name))
                               (inline (setf ,accessor-name)))
                      (defun (setf ,accessor-name) (new-value instance)
                        (setf (svref instance ,(slot-position slot-descriptor))
                              new-value))))

                 (slot-kwarg-type (slot-descriptor)
                   `(,(slot-initarg slot-descriptor)
                     ,(slot-type slot-descriptor)))

                 (slot-kw-arg (slot-descriptor)
                   `(,(slot-name slot-descriptor)
                     ,(slot-initform slot-descriptor)))

                 (initialize-slot-form (slot-descriptor)
                   `(setf (,(slot-accessor-name slot-descriptor)
                           instance)
                          ,(slot-name slot-descriptor))))
          `(progn
             (deftype ,name ()
               'simple-vector)

             (deftype ,logical-index-type ()
               '(integer 0 ,max-logical-index))
             (deftype ,logical-length-type ()
               '(integer 0 ,max-logical-length))
             (deftype ,true-index-type ()
               '(integer ,num-slots ,max-true-index))
             (deftype ,true-length-type ()
               '(integer ,num-slots ,max-true-length))

             (declaim (ftype (function (,logical-index-type) (values ,true-index-type &optional))
                             ,logical-index-to-true-index)
                      (inline ,logical-index-to-true-index))
             (defun ,logical-index-to-true-index (logical-index)
               (+ logical-index ,num-slots))

             (declaim (ftype (function (,logical-length-type) (values ,true-length-type &optional))
                             ,logical-length-to-true-length)
                      (inline ,logical-length-to-true-length))
             (defun ,logical-length-to-true-length (logical-length)
               (+ logical-length ,num-slots))

             (declaim (ftype (function (,true-length-type) (values ,logical-length-type &optional))
                             ,true-length-to-logical-length)
                      (inline ,true-length-to-logical-length))
             (defun ,true-length-to-logical-length (true-length)
               (- true-length ,num-slots))

             (declaim (ftype (function (,name) (values ,logical-length-type &optional))
                             ,length-name)
                      (inline ,length-name))
             (defun ,length-name (instance)
               (,true-length-to-logical-length (length instance)))

             ,@(mapcar #'define-accessor slot-descriptors)

             ,@(when ctor-name
                 `((declaim (ftype (function (&key ,@(mapcar #'slot-kwarg-type slot-descriptors)
                                                   (:length ,logical-length-type)
                                                   (:initial-element t)
                                                   (:initial-contents (or null generator)))
                                             (values ,name &optional))
                                   ,ctor-name)
                            (inline ,ctor-name))
                   (defun ,ctor-name (&key ,@(mapcar #'slot-kw-arg slot-descriptors)
                                        (length (error ,(format nil "Must supply :LENGTH to ~a" ctor-name)))
                                        (initial-element nil initial-element-p)
                                        initial-contents)
                     (let* ((true-length (,logical-length-to-true-length length))
                            (instance (make-array true-length)))
                       ,@(when named
                           `((setf (svref instance 0) ',name)))
                       ,@(mapcar #'initialize-slot-form slot-descriptors)
                       (cond ((and initial-element-p initial-contents)
                              (error ,(format nil ":INITIAL-ELEMENT and :INITIAL-CONTENTS are mutually exclusive in ~a" ctor-name)))

                             (initial-element-p
                              (iter (declare (declare-variables))
                                (for (the fixnum idx) from ,num-slots below true-length)
                                (setf (svref instance idx) initial-element)))

                             (initial-contents
                              (iter (declare (declare-variables))
                                (for (the fixnum idx) from ,num-slots below true-length)
                                (setf (svref instance idx) (advance initial-contents)))))
                       instance))))

             ,@(when ref-name
                 `((declaim (ftype (function (,name ,logical-index-type) (values t &optional))
                                   ,ref-name)
                            (inline ,ref-name))
                   (defun ,ref-name (instance idx)
                     (svref instance (,logical-index-to-true-index idx)))

                   (declaim (ftype (function (t ,name ,logical-index-type) (values t &optional))
                                   (setf ,ref-name))
                            (inline (setf ,ref-name)))
                   (defun (setf ,ref-name) (new-value instance idx)
                     (setf (svref instance (,logical-index-to-true-index idx)) new-value))))))))))
