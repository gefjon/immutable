(uiop:define-package :immutable/test/utils
  (:use :cl :fiveam :iterate)
  (:import-from :alexandria
                #:array-length)
  (:export
   #:quietly
   #:sync-test-dribble

   #:gen-element

   #:*gen-short-length*

   #:*gen-fixnum*
   #:*gen-bignum*
   #:*gen-short-float*
   #:*gen-single-float*
   #:*gen-long-float*
   #:*gen-double-float*
   #:*gen-long-float*
   #:*gen-float*

   #:gen-ratio
   #:*gen-small-ratio*
   #:*gen-large-ratio*

   #:*gen-real*

   #:gen-complex
   #:*gen-complex*

   #:gen-specialized-vector
   #:gen-simple-vector
   #:gen-adjustable-vector

   #:gen-simple-base-string
   #:gen-base-string
   #:gen-simple-string
   #:gen-general-string
   #:gen-simple-bit-vector
   #:gen-bit-vector

   #:gen-array

   #:signals-with))
(in-package :immutable/test/utils)

(defun dribble-dot ()
  (write-char #\. *test-dribble*))

(defun sync-test-dribble ()
  (force-output *test-dribble*))

(defun call-quietly (thunk)
  "Call THUNK in a context where FiveAM produces no text output for checks. Then print a single dot at the end.

Useful for comparing each element of a VEC against the corresponding element of its source data, to avoid
printing a large number of dots to *TEST-DRIBBLE*."
  (prog1 (let* ((*test-dribble* (make-broadcast-stream)))
           (unwind-protect (funcall thunk)
             (close *test-dribble*)))
    (dribble-dot)
    (sync-test-dribble)))

(defmacro quietly (&body body)
  "Evaluate BODY in a context where FiveAM produces no text output for checks.

Useful for comparing each element of a VEC against the corresponding element of its source data, to avoid
printing a large number of dots to *TEST-DRIBBLE*."
  `(call-quietly (lambda () ,@body)))

(defun gen-element (&rest generators)
  "Generate a value of essentially arbitrary type, to be compared with EQL."
  (let* ((get-generator (apply #'gen-one-element generators)))
    (lambda ()
      (funcall (funcall get-generator)))))

(defparameter *gen-fixnum* (gen-integer :min most-negative-fixnum
                                        :max most-positive-fixnum))

(defparameter *gen-bignum* (gen-integer :min (* #x1000000 most-negative-fixnum)
                                        :max (* #x1000000 most-positive-fixnum)))

(defparameter *gen-short-float* (gen-float :type 'short-float))
(defparameter *gen-single-float* (gen-float :type 'single-float))
(defparameter *gen-double-float* (gen-float :type 'double-float))
(defparameter *gen-long-float* (gen-float :type 'long-float))

(defparameter *gen-float* (gen-element *gen-short-float*
                                       *gen-single-float*
                                       *gen-double-float*
                                       *gen-long-float*))

(defun gen-ratio (gen-part)
  (lambda ()
    (/ (funcall gen-part)
       (funcall gen-part))))

(defparameter *gen-small-ratio*
  (gen-ratio *gen-fixnum*))

(defparameter *gen-large-ratio*
  (gen-ratio *gen-bignum*))

(defparameter *gen-real* (gen-element *gen-bignum*
                                      *gen-float*
                                      *gen-large-ratio*))

(defun gen-complex (gen-part)
  (lambda ()
    (complex (funcall gen-part)
             (funcall gen-part))))

(defparameter *gen-complex* (gen-complex *gen-real*))

(defparameter *gen-short-length* (gen-integer :min 16 :max 128))

(defun gen-specialized-vector (&key (length *gen-short-length*)
                                 (elements *gen-fixnum*)
                                 extra-capacity
                                 adjustable
                                 fill-pointer
                                 (element-type t)
                                 (initial-element nil initial-element-p))
  (lambda ()
    (let* ((this-length (etypecase length
                          (array-length length)
                          (function (funcall length))))
           (this-capacity (+ this-length
                             (etypecase extra-capacity
                               (array-length extra-capacity)
                               (function (funcall extra-capacity))
                               (null 0))))
           (this (apply #'make-array
                        this-capacity
                        :fill-pointer (etypecase fill-pointer
                                        (null nil)
                                        ((eql t) this-length)
                                        (array-length fill-pointer))
                        :adjustable adjustable
                        :element-type element-type
                        (when initial-element-p (list :initial-element initial-element)))))
      (iter (declare (declare-variables))
        (for idx below (the (and fixnum unsigned-byte) this-length))
        (setf (aref this idx) (funcall elements)))
      this)))

(defun gen-simple-vector (&key (length *gen-short-length*)
                            (elements *gen-fixnum*))
  "Generate a SIMPLE-VECTOR, with length chosen from the LENGTH generator, and elements chosen from the ELEMENTS generator."
  (gen-specialized-vector :length length
                          :elements elements))

(defun gen-adjustable-vector (&key (length *gen-short-length*)
                                (extra-capacity *gen-short-length*)
                                (elements *gen-fixnum*)
                                (element-type t))
  (gen-specialized-vector
   :adjustable t
   :fill-pointer t
   :length length
   :extra-capacity extra-capacity
   :elements elements
   :element-type element-type))

(defconstant +max-standard-char-code+
  (iter (for char in-string "
 abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890!$\"'(),_-./:;?+<=>#%&*@[\\]{|}`^~")
    (maximizing (char-code char))))

(defparameter *gen-base-char*
  (gen-character :code-limit (1+ +max-standard-char-code+)))

(defun gen-simple-base-string (&key (length *gen-short-length*))
  (gen-specialized-vector :length length
                          :elements *gen-base-char*
                          :element-type 'base-char))

(defun gen-base-string (&key (length *gen-short-length*)
                          (extra-capacity *gen-short-length*))
  (gen-adjustable-vector :length length
                         :extra-capacity extra-capacity
                         :elements *gen-base-char*
                         :element-type 'base-char))

(defun gen-simple-string (&key (length *gen-short-length*))
  (gen-specialized-vector :length length
                          :elements (gen-character)
                          :element-type 'character))

(defun gen-general-string (&key (length *gen-short-length*)
                             (extra-capacity *gen-short-length*))
  (gen-adjustable-vector :length length
                         :extra-capacity extra-capacity
                         :elements (gen-character)
                         :element-type 'character))

(defun gen-simple-bit-vector (&key (length *gen-short-length*))
  (gen-specialized-vector :length length
                          :elements (gen-integer :min 0 :max 1)
                          :element-type 'bit))

(defun gen-bit-vector (&key (length *gen-short-length*)
                         (extra-capacity *gen-short-length*))
  (gen-adjustable-vector :length length
                         :extra-capacity extra-capacity
                         :elements (gen-integer :min 0 :max 1)
                         :element-type 'bit))

(defun gen-array (&key (rank (gen-integer :min 2 :max 4))
                    (dimensions (gen-integer :min 4 :max 16))
                    (elements *gen-fixnum*)
                    (element-type t))
  (lambda ()
    (let* ((this-rank (etypecase rank
                        (function (funcall rank))
                        (array-rank rank)))
           (this-dimensions (iter (declare (declare-variables))
                              (repeat (the array-rank this-rank))
                              (collect (etypecase dimensions
                                         (array-length dimensions)
                                         (function (funcall dimensions))))))
           (this (make-array this-dimensions
                             :element-type element-type)))
      (iter (for i below (array-total-size this))
        (setf (row-major-aref this i)
              (funcall elements)))
      this)))

(defmacro signals-with ((condition-class &rest readers-and-expected-values) &body body)
  (flet ((assert-slot-matches (reader-and-expected-value)
           (destructuring-bind (test expected-value reader) reader-and-expected-value
             `(is (,test ,expected-value (,reader c))))))
    `(handler-case (progn ,@body)
       (,condition-class (c)
         ,@(mapcar #'assert-slot-matches readers-and-expected-values))
       (condition (c)
         (fail "SIGNALS-WITH: Expected a condition of class ~s, but found ~s.

Executing ~s was expected to signal an error of class ~s, but instead it signaled ~s."
               ',condition-class c '(progn ,@body) c))
       (:no-error (&rest c)
         (fail "SIGNALS-WITH: Expected a condition of class ~s.

Executing ~s was expected to signal an error of class ~s, but instead it returned normally. Return values were: ~s"

               ',condition-class '(progn ,@body) c)))))
