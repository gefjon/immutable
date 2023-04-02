(uiop:define-package #:immutable/%atomic
  (:use :cl)
  (:shadowing-import-from :org.shirakumo.atomics
                          #:atomic-incf
                          #-sbcl #:defstruct)
  (:shadow #:count)
  (:export
   #:define-atomic-counter
   #:increment-atomic-counter))
(in-package #:immutable/%atomic)

#-sbcl
(defstruct atomic-counter
  (count 0 :type fixnum))

(defmacro define-atomic-counter (name &optional (initial-value 0) documentation)
  (check-type name symbol)
  (check-type initial-value fixnum)
  (check-type documentation (or null string))
  #+sbcl
  `(progn
     (declaim (fixnum ,name))
     (sb-ext:defglobal ,name ,initial-value ,@(when documentation (list documentation))))
  #-sbcl
  (progn
    (declaim (atomic-counter ,name))
    (defparameter ,name (make-atomic-counter :count ,initial-value)
      ,@(when documentation (list documentation)))))

(defmacro increment-atomic-counter (name &optional (delta 1))
  (check-type name symbol)
  `(atomic-incf #+sbcl ,name
                #-sbcl (atomic-counter-count ,name)
                ,delta))
