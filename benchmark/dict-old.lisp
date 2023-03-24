(uiop:define-package :immutable/benchmark/dict-old
  (:use :cl :iterate :immutable/benchmark/utils)
  (:import-from :alexandria
                #:symbolicate)
  (:local-nicknames (#:hash :immutable/hash)
                    (#:dict :immutable/dict-old))
  (:export #:immutable-dict-old-suite))
(in-package :immutable/benchmark/dict-old)

(declaim (optimize (speed 3) (safety 1) (debug 1) (space 1) (compilation-speed 0)))

(def-suite immutable-dict-old-suite
    (asdf:system-relative-pathname "immutable" "benchmark-data/dict-old/"))

(declaim (ftype (function (fixnum symbol &optional boolean) (values dict:dict &optional))
                make-integer-to-string-dict)
         (inline make-integer-to-string-dict))
(defun make-integer-to-string-dict (total-size test-function &optional insert-with-op)
  (iter (declare (declare-variables))
    (with (the dict:dict dict) = (dict:empty :test-function test-function))
    (for (the fixnum key) below total-size)
    (for value = (prin1-to-string key))
    (for inserted = (if insert-with-op
                        (with-op (dict:insert dict key value))
                        (dict:insert dict key value)))
    (setf dict inserted)
    (finally (return dict))))

(declaim (ftype (function (fixnum symbol &optional boolean) (values dict:dict &optional))
                make-string-to-integer-dict)
         (inline make-string-to-integer-dict))
(defun make-string-to-integer-dict (total-size test-function &optional insert-with-op)
  (iter (declare (declare-variables))
                 (with (the dict:dict dict) = (dict:empty :test-function test-function))
    (for (the fixnum value) below total-size)
    (for key = (prin1-to-string value))
    (for inserted = (if insert-with-op
                        (with-op (dict:insert dict key value))
                        (dict:insert dict key value)))
    (setf dict inserted)
    (finally (return dict))))

(defmacro define-experiment-for-test-functions (base-name (test-function-binding total-size-binding) &body body)
  (cons 'progn
        (iter (for test-function in '(hash:== equal))
          (collect
              `(define-growing-experiment ,(symbolicate base-name '- test-function) (:suite immutable-dict-old-suite)
                   (,total-size-binding)
                 (symbol-macrolet ((,test-function-binding ',test-function))
                   ,@body))))))

(define-experiment-for-test-functions insert-no-conflicts-integer-to-string
    (test-function total-size)
  (let* ((dict (make-integer-to-string-dict total-size test-function t)))
    (assert (= (dict:size dict) total-size))))

(define-experiment-for-test-functions insert-no-conflicts-string-to-integer
    (test-function total-size)
  (let* ((dict (make-string-to-integer-dict total-size test-function t)))
    (assert (= (dict:size dict) total-size))))

(define-experiment-for-test-functions replace-integer-to-string
    (test-function total-size)
  (let* ((dict (make-integer-to-string-dict total-size test-function)))
    (assert (= (dict:size dict) total-size))
    (iter (declare (declare-variables))
      (with (the dict:dict new) = dict)
      (for (the fixnum key) below total-size)
      (for value = (prin1-to-string (1+ key)))
      (for replaced = (with-op (dict:insert new key value)))
      (setf dict replaced)
      (finally (assert (= (dict:size new) total-size))))))

(define-experiment-for-test-functions replace-string-to-integer
    (test-function total-size)
  (let* ((dict (make-string-to-integer-dict total-size test-function)))
    (assert (= (dict:size dict) total-size))
    (iter (declare (declare-variables))
      (with (the dict:dict new) = dict)
      (for (the fixnum key-int) below total-size)
      (for (the fixnum value) = (1+ key-int))
      (for key = (prin1-to-string key-int))
      (for replaced = (with-op (dict:insert new key (1+ value))))
      (setf dict replaced)
      (finally (assert (= (dict:size new) total-size))))))

(define-experiment-for-test-functions lookup-in-order-integer-to-string-present
  (test-function total-size)
  (let* ((dict (make-integer-to-string-dict total-size test-function)))
    (assert (= (dict:size dict) total-size))
    (iter (declare (declare-variables))
      (for (the fixnum key) below total-size)
      (for val = (with-op (dict:get dict key)))
      (assert (and (stringp val) (string= val (prin1-to-string key)))))))

(define-experiment-for-test-functions lookup-in-order-string-to-integer-present
    (test-function total-size)
  (let* ((dict (make-string-to-integer-dict total-size test-function)))
    (assert (= (dict:size dict) total-size))
    (iter (declare (declare-variables))
      (for (the fixnum value) below total-size)
      (for (the string key) = (prin1-to-string value))
      (for val = (with-op (dict:get dict key)))
      (assert (and (typep val 'fixnum) (= val value))))))

(define-experiment-for-test-functions lookup-integer-to-string-not-present
    (test-function total-size)
  (let* ((dict (make-integer-to-string-dict total-size test-function)))
    (assert (= (dict:size dict) total-size))
    (iter (declare (declare-variables))
      (with not-found = '#:not-found)
      (for (the fixnum present-key) below total-size)
      (for key = (1- (- present-key)))
      (for val = (with-op (dict:get dict key not-found)))
      (assert (eq val not-found)))))

(define-experiment-for-test-functions lookup-string-to-integer-not-present
    (test-function total-size)
  (let* ((dict (make-string-to-integer-dict total-size test-function)))
    (assert (= (dict:size dict) total-size))
    (iter (declare (declare-variables))
      (with not-found = '#:not-found)
      (for (the fixnum present-val) below total-size)
      (for key = (prin1-to-string (1- (- present-val))))
      (for val = (with-op (dict:get dict key not-found)))
      (assert (eq val not-found)))))

(define-experiment-for-test-functions lookup-integer-to-string-random-present
    (test-function total-size)
  (let* ((dict (make-integer-to-string-dict total-size test-function)))
    (assert (= (dict:size dict) total-size))
    (iter (declare (declare-variables))
      (repeat total-size)
      (for (the fixnum key) = (random total-size))
      (for val = (with-op (dict:get dict key)))
      (assert (and (stringp val) (string= val (prin1-to-string key)))))))

(define-experiment-for-test-functions lookup-string-to-integer-random-present
    (test-function total-size)
  (let* ((dict (make-string-to-integer-dict total-size test-function)))
    (assert (= (dict:size dict) total-size))
    (iter (declare (declare-variables))
      (repeat total-size)
      (for (the fixnum value) = (random total-size))
      (for (the string key) = (prin1-to-string value))
      (for val = (with-op (dict:get dict key)))
      (assert (and (typep val 'fixnum) (= val value))))))

(define-experiment-for-test-functions remove-integer-to-string-in-order-deconstruct
    (test-function total-size)
  (let* ((dict (make-integer-to-string-dict total-size test-function)))
    (assert (= (dict:size dict) total-size))
    (iter (declare (declare-variables))
      (with partial = dict)
      (for (the fixnum key) below total-size)
      (for removed = (with-op (dict:remove partial key)))
      (assert (not (eq partial removed)))
      (assert (= (dict:size removed) (1- (dict:size partial))))
      (setf partial removed))))

(define-experiment-for-test-functions remove-string-to-integer-in-order-deconstruct
    (test-function total-size)
  (let* ((dict (make-string-to-integer-dict total-size test-function)))
    (assert (= (dict:size dict) total-size))
    (iter (declare (declare-variables))
      (with partial = dict)
      (for (the fixnum value) below total-size)
      (for key = (prin1-to-string value))
      (for removed = (with-op (dict:remove partial key)))
      (assert (not (eq partial removed)))
      (assert (= (dict:size removed) (1- (dict:size partial))))
      (setf partial removed))))

(define-experiment-for-test-functions remove-integer-to-string-in-order-persist
    (test-function total-size)
  (let* ((dict (make-integer-to-string-dict total-size test-function)))
    (assert (= (dict:size dict) total-size))
    (iter (declare (declare-variables))
      (for (the fixnum key) below total-size)
      (for removed = (with-op (dict:remove dict key)))
      (assert (not (eq dict removed)))
      (assert (= (dict:size removed) (1- total-size))))))

(define-experiment-for-test-functions remove-string-to-integer-in-order-persist
    (test-function total-size)
  (let* ((dict (make-string-to-integer-dict total-size test-function)))
    (assert (= (dict:size dict) total-size))
    (iter (declare (declare-variables))
      (for (the fixnum value) below total-size)
      (for key = (prin1-to-string value))
      (for removed = (with-op (dict:remove dict key)))
      (assert (not (eq dict removed)))
      (assert (= (dict:size removed) (1- total-size))))))

(define-experiment-for-test-functions remove-integer-to-string-not-present
    (test-function total-size)
  (let* ((dict (make-integer-to-string-dict total-size test-function)))
    (assert (= (dict:size dict) total-size))
    (iter (declare (declare-variables))
      (for (the fixnum present-key) below total-size)
      (for key = (1- (- present-key)))
      (for removed = (with-op (dict:remove dict key)))
      (assert (eq dict removed)))))

(define-experiment-for-test-functions remove-string-to-integer-not-present
    (test-function total-size)
  (let* ((dict (make-string-to-integer-dict total-size test-function)))
    (assert (= (dict:size dict) total-size))
    (iter (declare (declare-variables))
      (for (the fixnum present-value) below total-size)
      (for key = (prin1-to-string (1- (- present-value))))
      (for removed = (with-op (dict:remove dict key)))
      (assert (eq dict removed)))))
