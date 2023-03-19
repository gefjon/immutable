(uiop:define-package :immutable/test/dict
  (:use :cl :fiveam :iterate :immutable/test/utils)
  (:import-from :alexandria
                #:set-equal
                #:shuffle)
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
  (quietly
    (let* ((body (dict::%dict-body dict))
           (size (dict::%dict-size dict))
           (hash-function (dict::%dict-hash-function dict)))
      (is (= size
             (is-body-sane-and-size-in-elts body 0 0 hash-function))))))

(defun make-dict-by-reduce (pairs &rest empty-args &key test-function hash-function)
  (declare (ignore test-function hash-function))
  (reduce (lambda (dict pair)
            (destructuring-bind (key value) pair
              (dict:insert dict key value)))
          pairs
          :initial-value (apply #'dict:empty empty-args)))

(defun value-node-equal-p (a b test-function &optional (same-value test-function))
  (and (= (dict::%value-node-hash a)
          (dict::%value-node-hash b))
       (funcall test-function
                (dict::%value-node-key a)
                (dict::%value-node-key b))
       (if same-value
           (funcall same-value
                    (dict::%value-node-value a)
                    (dict::%value-node-value b))
           t)))

(defun are-bodies-same (a b test-function &optional (same-value test-function))
  (hash::typecase-both (a b)
                       (fail "Type of bodies do not match: ~a and ~a"
                             a b)
    (null ())
    (dict::value-node (is (value-node-equal-p a b test-function same-value)))

    (dict::conflict-node (is (= (dict::%conflict-node-hash a)
                                (dict::%conflict-node-hash b)))
                         (is (= (length (dict::%conflict-node-entries a))
                                (length (dict::%conflict-node-entries b))))
                         (is (set-equal (coerce (dict::%conflict-node-entries a) 'list)
                                        (coerce (dict::%conflict-node-entries b) 'list)
                                        :test #'value-node-equal-p)))

    (dict::hash-node (is (= (dict::%hash-node-bitmap a)
                            (dict::%hash-node-bitmap b)))
                     (is (= (length (dict::%hash-node-entries a))
                            (length (dict::%hash-node-entries b))))
                     (iter (for a-entry in-vector (dict::%hash-node-entries a))
                       (for b-entry in-vector (dict::%hash-node-entries b))
                       (are-bodies-same a-entry b-entry test-function same-value))))
  (values))

(defun are-structures-same (a b &optional (same-value (dict::%dict-test-function a)))
  (quietly
    (is (eq (dict::%dict-hash-function a)
            (dict::%dict-hash-function b)))
    (is (eq (dict::%dict-test-function a)
            (dict::%dict-test-function b)))
    (is (= (dict::%dict-size a)
           (dict::%dict-size b)))
    (are-bodies-same (dict::%dict-body a)
                     (dict::%dict-body b)
                     (dict::%dict-test-function a)
                     same-value)))

(def-test small-integer-to-string (:suite immutable-dict-suite)
  (flet ((is-behavior-sane (test-function)
           (let* ((dict (quietly (iter (with partial-dict = (dict:empty :test-function test-function))
                                   (for i below 128)
                                   (for inserted = (dict:insert partial-dict
                                                                i
                                                                (princ-to-string i)))
                                   (is (= (1+ i) (dict:size inserted)))
                                   (is (not (eq partial-dict inserted)))
                                   (setf partial-dict inserted)
                                   (finally (return partial-dict))))))
             (is-dict-valid dict)
             (quietly
               (iter (for i below 128)
                 (is (string= (princ-to-string i)
                              (dict:get dict i ""))
                     "Expected dict[~a] to be ~s but found ~s in ~s"
                     i
                     (princ-to-string i)
                     (dict:get dict i "")
                     dict)))
             (quietly
               (iter (with partial-dict = dict)
                 (for i below 128)
                 (for removed = (dict:remove partial-dict i))
                 (is (not (eq partial-dict removed)))
                 (is (= (- 128 i 1) (dict:size removed))
                     "After removing ~d, expected the dict's size to be ~d, but found ~d"
                     i
                     (- 128 i 1)
                     (dict:size removed))
                 (setf partial-dict removed))))))
    (is-behavior-sane 'hash:==)
    (is-behavior-sane 'equal)))

(def-test small-integer-to-string-random-order-same-structure (:suite immutable-dict-suite)
  (flet ((is-behavior-sane (test-function)
           (let* ((entries (iter (for i below 128)
                             (collect (list i (princ-to-string i)))))
                  (entries-dict (make-dict-by-reduce entries :test-function test-function)))
             (is-dict-valid entries-dict)
             (flet ((gen-shuffle ()
                      (shuffle (copy-seq entries))))
               (for-all ((shuffled #'gen-shuffle))
                 (let* ((shuffled-dict (make-dict-by-reduce shuffled :test-function test-function)))
                   (is-dict-valid shuffled-dict)
                   (quietly
                     (iter (for i below 128)
                       (for (values entry presentp) = (dict:get entries-dict i))
                       (for (values shuffled-entry shuffled-presentp) = (dict:get shuffled-dict i))
                       (is-true presentp)
                       (is-true shuffled-presentp)
                       (is (string= entry shuffled-entry))))))))))
    (is-behavior-sane 'hash:==)
    (is-behavior-sane 'equal)))
