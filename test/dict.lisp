(uiop:define-package :immutable/test/dict
  (:use :cl :fiveam :iterate :immutable/test/utils)
  (:import-from :alexandria
                #:set-equal
                #:shuffle
                #:with-gensyms)
  (:local-nicknames (#:dict :immutable/dict)
                    (#:hash :immutable/hash))
  (:export #:immutable-dict-suite))
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

(declaim (ftype (function (dict::child-type t t dict::shift fixnum dict::hash-function)
                          (values dict::size &optional))
                is-body-sane-and-size-in-elts))
(defun is-body-sane-and-size-in-elts (body-type body-key body-value
                                      shift
                                      hash-path
                                      hash-function)
  (ecase body-type
    ((nil) 0)

    (:entry
     (is-path-correct hash-path shift (funcall hash-function body-key))
     1)

    (:conflict-node
     (let* ((conflict-hash body-key)
            (conflict-node body-value))
       (declare (fixnum conflict-hash)
                (dict::conflict-node conflict-node))
       (is-path-correct hash-path shift conflict-hash)
       (is (<= 2 (dict::conflict-node-logical-length conflict-node)))
       (iter (for logical-index below (dict::conflict-node-logical-length conflict-node))
         (for (values entry-key entry-value) = (dict::conflict-node-logical-ref conflict-node logical-index))
         (for entry-hash = (funcall hash-function entry-key))
         (is (= conflict-hash
                entry-hash)
             "Expected each entry in conflict-node to have the same hash as the conflict-hash #x~x, but found entry hash #x~x for entry:~%  (~s ~s)"
             conflict-hash
             entry-hash
             entry-key entry-value))
       (dict::conflict-node-logical-length conflict-node)))

    (:hash-node
     (let* ((bitmap body-key)
            (hash-node body-value)
            (count (dict::hash-node-logical-count body-value)))
       (declare (dict::bitmap bitmap)
                (dict::hash-node hash-node))
       (is (<= 1 count))
       (is (= count
              (logcount bitmap)))
       (is (zerop (logand (dict::hash-node-child-is-entry-p hash-node)
                          (dict::hash-node-child-is-conflict-p hash-node))))
       (is (zerop (logandc2 (dict::hash-node-child-is-entry-p hash-node)
                            bitmap)))
       (is (zerop (logandc2 (dict::hash-node-child-is-conflict-p hash-node)
                            bitmap)))
       (iter (for logical-index below dict::+branch-rate+)
         (for child-type = (dict::hash-node-child-type hash-node bitmap logical-index))
         (unless child-type (next-iteration))
         (for (values child-key child-value) = (dict::hash-node-logical-ref hash-node bitmap logical-index))
         (summing (is-body-sane-and-size-in-elts child-type child-key child-value
                                                 (1+ shift)
                                                 (add-to-hash-path hash-path logical-index shift)
                                                 hash-function)))))))

(declaim (ftype (function (dict:dict) (values &optional))
                is-dict-valid))
(defun is-dict-valid (dict)
  (quietly
    (let* ((body-key (dict::%dict-key dict))
           (body-value (dict::%dict-value dict))
           (body-type (dict::%dict-child-type dict))
           (size (dict::%dict-size dict))
           (hash-function (dict::%dict-hash-function dict)))
      (is (= size
             (is-body-sane-and-size-in-elts body-type body-key body-value 0 0 hash-function))))))

(defun make-dict-by-reduce (pairs &rest empty-args &key test-function hash-function)
  (declare (ignore test-function hash-function))
  (reduce (lambda (dict pair)
            (destructuring-bind (key value) pair
              (dict:insert dict key value)))
          pairs
          :initial-value (apply #'dict:empty empty-args)))

(defun are-entries-equal (a-key a-value b-key b-value
                        test-function hash-function &optional (same-value test-function))
  (is (= (funcall hash-function a-key)
         (funcall hash-function b-key)))
  (is (funcall test-function
               a-key
               b-key))
  (when same-value
    (is (funcall same-value
                 a-value
                 b-value))))

(defun conflict-node-entry-pairs (conflict-node)
  (iter (for logical-index below (dict::conflict-node-logical-length conflict-node))
    (for (values key value) = (dict::conflict-node-logical-ref conflict-node logical-index))
    (collect (list key value))))

(defun pair-sets-equal-p (pair-set-a pair-set-b keys-equal hash-function &optional (values-equal keys-equal))
  (set-equal pair-set-a pair-set-b
             :test (lambda (pair-a pair-b)
                     (destructuring-bind (a-key a-value) pair-a
                       (destructuring-bind (b-key b-value) pair-b
                         (and (= (funcall hash-function a-key)
                                 (funcall hash-function b-key))
                              (funcall keys-equal a-key b-key)
                              (if values-equal
                                  (funcall values-equal a-value b-value)
                                  t)))))))

(defun are-conflict-nodes-equal (a-hash a-conflict-node
                                 b-hash b-conflict-node
                                 test-function hash-function &optional (same-value test-function))
  (is (= a-hash b-hash))
  (is (= (dict::conflict-node-logical-length a-conflict-node)
         (dict::conflict-node-logical-length b-conflict-node)))
  (is (pair-sets-equal-p (conflict-node-entry-pairs a-conflict-node)
                         (conflict-node-entry-pairs b-conflict-node)
                         test-function hash-function same-value)))

(defun are-hash-nodes-equal (a-bitmap a-hash-node
                             b-bitmap b-hash-node
                             test-function hash-function &optional (same-value test-function))
  (is (= a-bitmap b-bitmap))
  (is (= (dict::hash-node-child-is-entry-p a-hash-node)
         (dict::hash-node-child-is-entry-p b-hash-node)))
  (is (= (dict::hash-node-child-is-conflict-p a-hash-node)
         (dict::hash-node-child-is-conflict-p b-hash-node)))
  (iter (for logical-index below dict::+branch-rate+)
    ;; We know this is the entry type for both nodes, because we've already asserted their various bitmaps are
    ;; equal.
    (for entry-type = (dict::hash-node-child-type a-hash-node a-bitmap logical-index))
    (unless entry-type (next-iteration))
    (for (values a-key a-value) = (dict::hash-node-logical-ref a-hash-node a-bitmap logical-index))
    (for (values b-key b-value) = (dict::hash-node-logical-ref b-hash-node b-bitmap logical-index))
    (are-bodies-same entry-type a-key a-value
                     entry-type b-key b-value
                     test-function hash-function same-value)))

(defun are-bodies-same (a-type a-key a-value
                        b-type b-key b-value
                        test-function hash-function &optional (same-value test-function))
  (unless (eq a-type b-type)
    (fail "Type of bodies do not match: ~a and ~a"
          a-type b-type))
  (ecase a-type
    ((nil) nil)

    (:entry (are-entries-equal a-key a-value
                               b-key b-value
                               test-function hash-function same-value))

    (:conflict-node (are-conflict-nodes-equal a-key a-value
                                              b-key b-value
                                              test-function hash-function same-value))

    (:hash-node (are-hash-nodes-equal a-key a-value
                                      b-key b-value
                                      test-function hash-function same-value)))
  (values))

(defun are-structures-same (a b &optional (same-value (dict::%dict-test-function a)))
  (quietly
    (is (eq (dict::%dict-hash-function a)
            (dict::%dict-hash-function b)))
    (is (eq (dict::%dict-test-function a)
            (dict::%dict-test-function b)))
    (is (= (dict::%dict-size a)
           (dict::%dict-size b)))
    (are-bodies-same (dict::%dict-child-type a) (dict::%dict-key a) (dict::%dict-value a)
                     (dict::%dict-child-type b) (dict::%dict-key b) (dict::%dict-value b)
                     (dict::%dict-test-function a) (dict::%dict-hash-function a)
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
                       (is (string= entry shuffled-entry))))
                   (are-structures-same entries-dict shuffled-dict)))))))
    (is-behavior-sane 'hash:==)
    (is-behavior-sane 'equal)))

(def-test replace-size-consistent (:suite immutable-dict-suite)
  (flet ((is-size-consistent-after-replace (test-function)
           (let* ((entries (iter (for i below 128)
                             (collect (list i i))))
                  (id-dict (make-dict-by-reduce entries :test-function test-function)))
             (is-dict-valid id-dict)
             (is (= 128 (dict:size id-dict)))
             (iter (for i below 128)
               (for new-value = (1+ i))
               (for replaced-dict = (dict:insert id-dict i new-value))
               (is (= new-value
                      (dict:get replaced-dict i)))
               (is (= (dict:size id-dict)
                      (dict:size replaced-dict)))
               (is (= i
                      (dict:get id-dict i)))))))
    (is-size-consistent-after-replace 'hash:==)
    (is-size-consistent-after-replace 'equal)))

(def-test insert-lookup-replace-remove-artificial-conflict (:suite immutable-dict-suite)
  (let* ((id-dict (iter (with partial = (dict:empty :test-function #'eql
                            :hash-function (constantly 0)))
                    (for i below 128)
                    (setf partial (dict:insert partial i i))
                    (finally (return partial)))))
    (is-dict-valid id-dict)
    (is (= 128 (dict:size id-dict)))
    (quietly
      (iter (for i below 128)
        (for (values val presentp) = (dict:get id-dict i))
        (is-true presentp)
        (is (eql i val))))
    (let* ((replaced (iter (with partial = id-dict)
                       (for i below 128)
                       (setf partial (dict:insert partial i (1+ i)))
                       (finally (return partial)))))
      (is-dict-valid replaced)
      (is (= 128 (dict:size replaced)))
      (quietly
        (iter (for i below 128)
          (for (values val presentp) = (dict:get replaced i))
          (is-true presentp)
          (is (eql (1+ i) val))))
      (let* ((removed (iter (with partial = replaced)
                        (for i below 128)
                        (setf partial (dict:remove partial i))
                        (finally (return partial)))))
        (is-dict-valid removed)
        (is (= 0 (dict:size removed)))))))

(def-test detect-stale-transient (:suite immutable-dict-suite)
  (let* ((transient (dict:transient (dict:empty)))
         (persistent (dict:persistent! transient)))
    ;; operations that are disallowed on stale transients
    (signals-with (dict:stale-transient (eq transient dict:stale-transient-transient)
                                        (eq 'dict:insert! dict:stale-transient-operation))
      (dict:insert! transient 0 0))
    (signals-with (dict:stale-transient (eq transient dict:stale-transient-transient)
                                        (eq 'dict:remove! dict:stale-transient-operation))
      (dict:remove! transient 0))
    ;; operations that are allowed on stale transients
    (is (null (dict:get transient 0)))
    (is (zerop (dict:size transient)))))

(def-test transient-not-observable (:suite immutable-dict-suite)
  (let* ((dict (iter (with partial = (dict:empty))
                 (for i below 128)
                 (setf partial (dict:insert partial i i))
                 (finally (return partial))))
         (transient (iter (with partial = (dict:transient dict))
                      (for i below 128)
                      (setf partial (dict:insert! partial i (1+ i)))
                      (finally (return partial))))
         (persistent (dict:persistent! transient)))
    (is-dict-valid dict)
    (is-dict-valid persistent)
    (iter (for i below 128)
      (quietly
        (is (eql i (dict:get dict i)))
        (is (eql (1+ i) (dict:get persistent i)))
        (is (eql (1+ i) (dict:get transient i)))))))
