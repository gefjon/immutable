(uiop:define-package :immutable/test/dict
  (:use :cl :fiveam :iterate :immutable/test/utils)
  (:local-nicknames (#:dict :immutable/dict)
                    (#:hash :immutable/hash)))
(in-package :immutable/test/dict)

(def-suite immutable-dict-suite)

(declaim (ftype (function (dict::shift fixnum) (values fixnum &optional))
                bits-below-shift))
(defun bits-below-shift (shift hash)
  (ldb (byte (* shift dict::+node-index-bits+) 0)
       hash))

(declaim (ftype (function (fixnum dict::hash-node-index dict::shift)
                          (values fixnum &optional))
                add-to-hash-path))
(defun add-to-hash-path (path index shift)
  (dpb index
       (byte dict::+node-index-bits+
             (* dict::+node-index-bits+ shift))
       path))

(declaim (ftype (function (fixnum dict::shift fixnum) (values &optional))
                is-path-correct))
(defun is-path-correct (path shift hash)
  (is (= path
         (bits-below-shift shift
                           hash))
      "Path to current node is #x~x, but its hash is #x~x, with an extracted part #x~x"
      path
      hash
      (bits-below-shift shift
                        hash))
  (values))

(declaim (ftype (function ((or null dict::node) dict::shift fixnum dict::hash-function)
                          (values dict::size &optional))
                is-body-sane-and-size-in-elts))
(defun is-body-sane-and-size-in-elts (body shift hash-path hash-function)
  (etypecase body
    (null 0)

    (dict::value-node
     (is-path-correct hash-path shift (dict::%value-node-hash body))
     (is (= (dict::%value-node-hash body)
            (funcall hash-function (dict::%value-node-key body))))
     1)

    (dict::conflict-node
     (is-path-correct hash-path shift (dict::%conflict-node-hash body))
     (iter (for val in-vector (dict::%conflict-node-entries body))
       (is (typep val 'dict::value-node))
       (is (= (dict::%conflict-node-hash body)
              (dict::%value-node-hash val)))
       (is (= (dict::%conflict-node-hash body)
              (funcall hash-function (dict::%value-node-key val)))))
     (length (dict::%conflict-node-entries body)))

    (dict::hash-node
     (is (plusp (length (dict::%hash-node-entries body))))
     (is (= (length (dict::%hash-node-entries body))
            (logcount (dict::%hash-node-bitmap body))))
     (iter (declare (declare-variables))
       (for i below dict::+branch-rate+)
       (when (logbitp i (dict::%hash-node-bitmap body))
         (summing (is-body-sane-and-size-in-elts (dict::hash-node-ref body i)
                                                 (1+ shift)
                                                 (add-to-hash-path hash-path i shift)
                                                 hash-function)))))))

(declaim (ftype (function (dict:dict) (values &optional))
                is-dict-valid))
(defun is-dict-valid (dict)
  (let* ((body (dict::%dict-body dict))
         (size (dict::%dict-size dict))
         (hash-function (dict::%dict-hash-function dict)))
    (is (= size
           (is-body-sane-and-size-in-elts body 0 0 hash-function)))))

(defmacro make-dict-by-reduce ((&key test-function hash-function) &body pairs)
  `(reduce (lambda (dict pair)
             (destructuring-bind (key value) pair
               (dict:insert dict key value)))
           (list ,@pairs)
           :initial-value (dict:empty ,@(when test-function `((:test-function ,test-function)))
                                      ,@(when hash-function `((:hash-function ,hash-function))))))

(def-test small-integer-to-string (:suite immutable-dict-suite)
  (flet ((is-behavior-sane (test-function)
           (let* ((dict (iter (with partial-dict = (dict:empty :test-function test-function))
                          (for i below 128)
                          (for inserted = (dict:insert partial-dict
                                                       i
                                                       (princ-to-string i)))
                          (is (= (1+ i) (dict:size inserted)))
                          (is (not (eq partial-dict inserted)))
                          (setf partial-dict inserted)
                          (finally (return partial-dict)))))
             (is-dict-valid dict)
             (iter (for i below 128)
               (is (string= (princ-to-string i)
                            (dict:get dict i ""))
                   "Expected dict[~a] to be ~s but found ~s in ~s"
                   i
                   (princ-to-string i)
                   (dict:get dict i "")
                   dict))
             (iter (with partial-dict = dict)
               (for i below 128)
               (for removed = (dict:remove partial-dict i))
               (is (not (eq partial-dict removed)))
               (is (= (- 128 i 1) (dict:size removed))
                   "After removing ~d, expected the dict's size to be ~d, but found ~d"
                   i
                   (- 128 i 1)
                   (dict:size removed))
               (setf partial-dict removed)))))
    (is-behavior-sane 'hash:==)
    (is-behavior-sane 'equal)))
