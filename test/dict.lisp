(uiop:define-package :immutable/test/dict
  (:use :cl :fiveam :iterate :immutable/test/utils)
  (:import-from :alexandria
                #:set-equal
                #:shuffle)
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

(declaim (ftype (function ((or null dict::node) dict::shift fixnum dict::hash-function)
                          (values dict::size &optional))
                is-body-sane-and-size-in-elts))
(defun is-body-sane-and-size-in-elts (body
                                      shift
                                      hash-path
                                      hash-function)
  (if (null body)
      0
      (ecase (dict::node-type body)
        (dict::entry-node
         (is-path-correct hash-path shift (funcall hash-function (dict::entry-node-key body)))
         1)

        (dict::conflict-node
         (let* ((conflict-node body)
                (conflict-hash (dict::conflict-node-conflict-hash conflict-node)))
           (is-path-correct hash-path shift conflict-hash)
           (is (<= 2 (dict::conflict-node-count conflict-node)))
           (iter (for logical-index below (dict::conflict-node-count conflict-node))
             (for entry = (dict::conflict-node-ref conflict-node logical-index))
             (for entry-key = (dict::entry-node-key entry))
             (for entry-hash = (funcall hash-function entry-key))
             (is (= conflict-hash
                    entry-hash)
                 "Expected each entry in conflict-node to have the same hash as the conflict-hash #x~x, but found entry hash #x~x for entry:~% ~s"
                 conflict-hash
                 entry-hash
                 entry))
           (dict::conflict-node-count conflict-node)))

        (dict::hash-node
         (let* ((hash-node body)
                (bitmap (dict::hash-node-child-present-p hash-node))
                (count (dict::hash-node-count hash-node)))
           (is (<= 1 count)
               "Found empty hash node at hash-path #x~x:~% ~s"
               hash-path hash-node)
           (is (= count
                  (logcount bitmap)))
           (iter (for logical-index below dict::+branch-rate+)
             (unless (dict::hash-node-contains-p hash-node logical-index)
               (next-iteration))
             (for child = (dict::hash-node-logical-ref hash-node logical-index))
             (summing (is-body-sane-and-size-in-elts child
                                                     (1+ shift)
                                                     (add-to-hash-path hash-path logical-index shift)
                                                     hash-function))))))))

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

(defun are-entries-equal (a b
                          test-function hash-function &optional (same-value test-function)
                          &aux (a-key (dict::entry-node-key a))
                            (a-value (dict::entry-node-value a))
                            (a-hash (funcall hash-function a-key))
                            (b-key (dict::entry-node-key b))
                            (b-value (dict::entry-node-value b))
                            (b-hash (funcall hash-function b-key)))
  (is (= a-hash b-hash)
      "Entries have different hashes under hash-function ~s:~% ~s => #x~x~% ~s => #x~x"
      a a-hash
      b b-hash)
  (is (funcall test-function
               a-key
               b-key)
      "Entries have keys which are not ~s:~% ~s~% ~s"
      test-function
      a b)
  (when same-value
    (is (funcall same-value
                 a-value
                 b-value)
        "Entries have values which are not ~s:~% ~s~% ~s"
        same-value
        a b)))

(defun conflict-node-entries (conflict-node)
  (iter (for logical-index below (dict::conflict-node-count conflict-node))
    (collect (dict::conflict-node-ref conflict-node logical-index))))

(defun entry-sets-equal-p (a b test-function hash-function &optional (same-value test-function))
  (set-equal a b
             :test (lambda (a-entry b-entry
                            &aux (a-key (dict::entry-node-key a-entry))
                            (a-value (dict::entry-node-value a-entry))
                            (a-hash (funcall hash-function a-key))
                            (b-key (dict::entry-node-key b-entry))
                            (b-value (dict::entry-node-value b-entry))
                            (b-hash (funcall hash-function b-key)))
                     (and (= a-hash b-hash)
                          (funcall test-function a-key b-key)
                          (if same-value
                              (funcall same-value a-value b-value)
                              t)))))

(defun are-conflict-nodes-equal (a b
                                 test-function hash-function &optional (same-value test-function)
                                 &aux (a-hash (dict::conflict-node-conflict-hash a))
                                   (b-hash (dict::conflict-node-conflict-hash b)))
  (is (= a-hash b-hash)
      "Conflict nodes have different hashes:~% #x~x from ~s~% #x~x from ~s"
      a-hash a
      b-hash b)
  (is (= (dict::conflict-node-count a)
         (dict::conflict-node-count b))
      "Conflict nodes have different lengths:~% ~d from ~s~% ~d from ~s"
      (dict::conflict-node-count a) a
      (dict::conflict-node-count b) b)
  (is (entry-sets-equal-p (conflict-node-entries a)
                          (conflict-node-entries b)
                          test-function hash-function same-value)
      "Conflict nodes' entries are not setwise equal"))

(defun are-hash-nodes-equal (a b
                             test-function hash-function &optional (same-value test-function)
                             &aux (a-bitmap (dict::hash-node-child-present-p a))
                               (b-bitmap (dict::hash-node-child-present-p b)))
  (is (= a-bitmap b-bitmap))
  (iter (for logical-index below dict::+branch-rate+)
    ;; We know this contains-p applies to both nodes, because we asserted their bitmaps were equal.
    (unless (dict::hash-node-contains-p a logical-index)
      (next-iteration))
    (for a-child = (dict::hash-node-logical-ref a logical-index))
    (for b-child = (dict::hash-node-logical-ref b logical-index))
    (are-bodies-same a-child b-child
                     test-function hash-function same-value)))

(defun are-bodies-same (a b
                        test-function hash-function &optional (same-value test-function)
                        &aux (a-type (dict::node-type a))
                          (b-type (dict::node-type b)))
  (is (eq a-type b-type)
      "Node types do not match:~% ~s for ~s~% ~s for ~s"
      a-type a
      b-type b)
  (ecase a-type
    (dict::entry-node (are-entries-equal a b
                                         test-function hash-function same-value))

    (dict::conflict-node (are-conflict-nodes-equal a b
                                                   test-function hash-function same-value))

    (dict::hash-node (are-hash-nodes-equal a b
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
    (are-bodies-same (dict::%dict-body a)
                     (dict::%dict-body b)
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
                       (is (string= entry shuffled-entry))))))))))
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
