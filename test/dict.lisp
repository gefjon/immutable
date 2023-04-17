(uiop:define-package :immutable/test/dict
  (:use :cl :fiveam :iterate :immutable/test/utils)
  (:import-from :alexandria
                #:set-equal
                #:shuffle
                #:with-gensyms
                #:symbolicate)
  (:local-nicknames (#:dict :immutable/dict)
                    (#:hash :immutable/hash))
  (:export #:immutable-dict-suite))
(in-package :immutable/test/dict)

(declaim (optimize (debug 3) (speed 2) (safety 3) (space 1) (compilation-speed 0)))

(def-suite immutable-dict-suite)

(eval-when (:compile-toplevel :load-toplevel)
  (defun hash-always-conflict (thing)
    (declare (ignore thing))
    0)
  (defparameter *test-and-hash-functions*
    (list (cons 'hash:== 'hash:hash)
          (cons 'equal 'sxhash)
          (cons 'hash:== 'hash-always-conflict)
          (cons 'equal 'hash-always-conflict))))

(defmacro define-test (name (test-function hash-function) &body body)
  (let* ((func-name (gensym (symbol-name name))))
    (flet ((test-name (test-function hash-function)
             (symbolicate name '- test-function '- hash-function)))
      `(progn
         (defun ,func-name (,test-function ,hash-function)
           ,@body)
         ,@(iter (for (test . hash) in *test-and-hash-functions*)
             (collect `(def-test ,(test-name test hash) (:suite immutable-dict-suite)
                         (,func-name ',test ',hash))))))))

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
       (is (<= (logcount (dict::hash-node-child-is-entry-p hash-node))
               (logcount bitmap)))
       (is (<= (logcount (dict::hash-node-child-is-conflict-p hash-node))
               (logcount bitmap)))

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

(define-test small-integer-to-string (test-function hash-function)
  (let* ((dict (quietly (iter (with partial-dict = (dict:empty :test-function test-function
                                                               :hash-function hash-function))
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
        (setf partial-dict removed)))))

(define-test small-integer-to-string-random-order-same-structure (test-function hash-function)
  (let* ((entries (iter (for i below 128)
                    (collect (list i (princ-to-string i)))))
         (entries-dict (make-dict-by-reduce entries :test-function test-function
                                                    :hash-function hash-function)))
    (is-dict-valid entries-dict)
    (flet ((gen-shuffle ()
             (shuffle (copy-seq entries))))
      (for-all ((shuffled #'gen-shuffle))
        (let* ((shuffled-dict (make-dict-by-reduce shuffled :test-function test-function
                                                            :hash-function hash-function)))
          (is-dict-valid shuffled-dict)
          (quietly
            (iter (for i below 128)
              (for (values entry presentp) = (dict:get entries-dict i))
              (for (values shuffled-entry shuffled-presentp) = (dict:get shuffled-dict i))
              (is-true presentp)
              (is-true shuffled-presentp)
              (is (string= entry shuffled-entry))))
          (are-structures-same entries-dict shuffled-dict))))))

(define-test replace-size-consistent (test-function hash-function)
  (let* ((entries (iter (for i below 128)
                    (collect (list i i))))
         (id-dict (make-dict-by-reduce entries :test-function test-function
                                               :hash-function hash-function)))
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
             (dict:get id-dict i))))))

(define-test detect-stale-transient (test-function hash-function)
  (let* ((transient (dict:transient (dict:empty :test-function test-function
                                                :hash-function hash-function)))
         (persistent (dict:persistent! transient)))
    (is-dict-valid persistent)
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

(define-test transient-not-observable (test-function hash-function)
  (let* ((dict (iter (with partial = (dict:empty :test-function test-function
                                                 :hash-function hash-function))
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

(def-test simple-constructor (:suite immutable-dict-suite)
  (let* ((dict (dict:dict :zero 0 :one 1 :two 2 :three 3)))
    (is-dict-valid dict)
    (is (eql 0 (dict:get dict :zero)))
    (is (eql 1 (dict:get dict :one)))
    (is (eql 2 (dict:get dict :two)))
    (is (eql 3 (dict:get dict :three)))

    (is-false (dict:get dict :four))

    (is-false (dict:get dict 0))
    (is-false (dict:get dict 1))
    (is-false (dict:get dict 2))
    (is-false (dict:get dict 3))

    (is-false (dict:get dict "zero"))
    (is-false (dict:get dict "one"))
    (is-false (dict:get dict "two"))
    (is-false (dict:get dict "three"))

    (is-false (dict:get dict :|zero|))
    (is-false (dict:get dict :|one|))
    (is-false (dict:get dict :|two|))
    (is-false (dict:get dict :|three|))

    (is-false (dict:get dict "ZERO"))
    (is-false (dict:get dict "ONE"))
    (is-false (dict:get dict "TWO"))
    (is-false (dict:get dict "THREE"))))

(define-test for-each-sum (test-function hash-function)
  (let* ((dict (iter (with partial = (dict:empty :test-function test-function
                                                 :hash-function hash-function))
                 (for i below 128)
                 (setf partial (dict:insert partial i i))
                 (finally (return partial))))
         (expected-sum (/ (* 127 (1+ 127)) 2))
         (sum-for-each 0)
         (sum-do 0))
    (is-dict-valid dict)
    (quietly
      (dict:for-each dict
                     (lambda (k v)
                       (is (= k v))
                       (incf sum-for-each v)))
      (dict:do (k v dict)
        (is (= k v))
        (incf sum-do v)))
    (is (= expected-sum sum-for-each))
    (is (= expected-sum sum-do))))

(define-test map-values-1+ (test-function hash-function)
  (let* ((dict (iter (with partial = (dict:empty :test-function test-function
                                                 :hash-function hash-function))
                 (for i below 128)
                 (setf partial (dict:insert partial i i))
                 (finally (return partial))))
         (mapped (dict:map-values dict #'1+)))
    (is-dict-valid dict)
    (is-dict-valid mapped)
    (is (eq (dict:test-function dict) (dict:test-function mapped)))
    (is (eq (dict:hash-function dict) (dict:hash-function mapped)))
    (are-structures-same dict mapped
                         nil)
    (iter (for i below 128)
      (is (eql i (dict:get dict i)))
      (is (eql (1+ i) (dict:get mapped i))))))

(defun merge-function-fail (k o n)
  (fail "Unexpectedly called MERGE-FUNCTION.

Called with:
  KEY       = ~a
  OLD-VALUE = ~a
  NEW-VALUE = ~a"
        k o n))

(define-test merge-function-old-value (test-function hash-function)
  (let* ((old '#:old)
         (new '#:new)
         (dict (quietly (iter (with partial-dict = (dict:empty :test-function test-function
                                                               :hash-function hash-function))
                          (for i below 128)
                          (for inserted = (dict:insert partial-dict
                                                       i
                                                       old
                                                       #'merge-function-fail))
                          (is (= (1+ i) (dict:size inserted)))
                          (is (not (eq partial-dict inserted)))
                          (setf partial-dict inserted)
                          (finally (return partial-dict)))))
         (by-transient (iter (with transient = (dict:transient (dict:empty :test-function test-function
                                                                           :hash-function hash-function)))
                         (for i below 128)
                         (dict:insert! transient i old #'merge-function-fail)
                         (finally (return (dict:persistent! transient))))))
    (is-dict-valid dict)
    (is-dict-valid by-transient)
    (are-structures-same dict by-transient)
    (quietly
      (iter (for i below 128)
        (is (eq old (dict:get dict i '#:wrong)))
        (is (eq old (dict:get dict i '#:wrong)))))
    (let* ((replaced (quietly
                       (iter (with partial-dict = dict)
                         (for i below 128)
                         (for replaced = (dict:insert partial-dict i new #'dict:old-value))
                         (is (not (eq partial-dict replaced)))
                         (setf partial-dict replaced)
                         (finally (return replaced)))))
           (replaced-transient (iter (with transient = (dict:transient dict))
                                 (for i below 128)
                                 (dict:insert! transient i new #'dict:old-value)
                                 (finally (return (dict:persistent! transient))))))
      (is-dict-valid replaced)
      (is-dict-valid replaced-transient)
      (are-structures-same replaced replaced-transient)
      (are-structures-same dict replaced)
      (quietly
        (iter (declare (declare-variables))
          (for i below 128)
          (is (eq old
                  (dict:get replaced i)))
          (is (eq old
                  (dict:get replaced-transient i))))))))

(define-test merge-function-+ (test-function hash-function)
  (labels ((merge-+ (key old-value new-value)
             (declare (ignore key))
             (+ old-value new-value)))
    (let* ((dict (quietly (iter (with partial = (dict:empty :test-function test-function
                                                            :hash-function hash-function))
                            (for i below 128)
                            (for inserted = (dict:insert partial
                                                         i
                                                         i
                                                         #'merge-function-fail))
                            (is (= (1+ i) (dict:size inserted)))
                            (is (not (eq partial inserted)))
                            (setf partial inserted)
                            (finally (return partial))))))
      (is-dict-valid dict)
      (quietly
        (iter (for i below 128)
          (is (eql i (dict:get dict i)))))
      (let* ((doubled (iter (with partial = dict)
                        (for i below 128)
                        (setf partial (dict:insert partial i i #'merge-+))
                        (finally (return partial)))))
        (is-dict-valid doubled)
        (are-structures-same dict doubled
                             nil)
        (quietly
          (iter (for i below 128)
            (is (eql (dict:get doubled i)
                     (* i 2)))))))))

(define-test insert-multiple-like-insert (test-function hash-function)
  (labels ((insert-range (dict min max method)
             (ecase method
               (:insert (iter (with partial = dict)
                          (for i from min below max)
                          (setf partial (dict:insert partial i i))
                          (finally (return partial))))
               (:insert! (iter (with partial = (dict:transient dict))
                           (for i from min below max)
                           (dict:insert! partial i i)
                           (finally (return (dict:persistent! partial)))))
               (:insert-multiple (apply #'dict:insert-multiple
                                        dict
                                        (iter (for i from min below max)
                                          (collect i)
                                          (collect i))))
               (:insert-plist (dict:insert-plist dict
                                                 (iter (for i from min below max)
                                                   (collect i)
                                                   (collect i))))
               (:insert-alist (dict:insert-alist dict
                                                 (iter (for i from min below max)
                                                   (collect (cons i i)))))))
           (insert-range-each-method-and-compare (dict min step max)
             (if (>= min max)
                 dict
                 (let* ((dicts (iter (for method in '(:insert :insert! :insert-multiple :insert-plist :insert-alist))
                                 (collect (insert-range dict min (+ min step) method)))))
                   (iter (for dict in dicts)
                     (is-dict-valid dict))
                   (iter (for (a b . rest) on dicts)
                     (are-structures-same a b)
                     (while rest))
                   (insert-range-each-method-and-compare (first dicts)
                                                         (+ min step) step max)))))
    (let* ((empty (dict:empty :test-function test-function
                              :hash-function hash-function))
           (dict (insert-range-each-method-and-compare empty 0 16 128)))
      (is (= 128 (dict:size dict)))
      (iter (for i below 128)
        (is (eql i (dict:get dict i)))))))

(define-test union-right-or-left-bias (test-function hash-function)
  (let* ((even '#:even)
         (odd '#:odd)
         (all (iter (with partial = (dict:transient (dict:empty :test-function test-function
                                                                :hash-function hash-function)))
                (for i below 128)
                (dict:insert! partial i even)
                (finally (return (dict:persistent! partial)))))
         (odds (iter (with partial = (dict:transient (dict:empty :test-function test-function
                                                                 :hash-function hash-function)))
                 (for i below 128)
                 (unless (oddp i)
                   (next-iteration))
                 (dict:insert! partial i odd)
                 (finally (return (dict:persistent! partial)))))
         (merged-left (dict:union all odds))
         (merged-right (dict:union odds all #'dict:old-value)))
    (is-dict-valid all)
    (is (= 128 (dict:size all)))
    (is-dict-valid odds)
    (is (= 64 (dict:size odds)))
    (is-dict-valid merged-left)
    (is (= 128 (dict:size merged-left)))
    (is-dict-valid merged-right)
    (is (= 128 (dict:size merged-right)))
    (are-structures-same merged-left merged-right)
    (iter (for i below 128)
      (if (oddp i)
          (progn (is (eql odd (dict:get merged-left i)))
                 (is (eql odd (dict:get merged-right i))))
          (progn (is (eql even (dict:get merged-left i)))
                 (is (eql even (dict:get merged-right i))))))))

(define-test union-merge-function-+ (test-function hash-function)
  (let* ((all (iter (with partial = (dict:transient (dict:empty :test-function test-function
                                                                :hash-function hash-function)))
                (for i below 128)
                (dict:insert! partial i i)
                (finally (return (dict:persistent! partial)))))
         (evens (iter (with partial = (dict:transient (dict:empty :test-function test-function
                                                                  :hash-function hash-function)))
                  (for i below 128 by 2)
                  (dict:insert! partial i i)
                  (finally (return (dict:persistent! partial)))))
         (merged-left (dict:union all evens (lambda (k o n)
                                              (is (evenp k)
                                                  "Merge function unexpectedly called for odd number ~d" k)
                                              (is (= k o))
                                              (is (= k n))
                                              (+ o n))))
         (merged-right (dict:union evens all (lambda (k o n)
                                               (is (evenp k)
                                                   "Merge function unexpectedly called for odd number ~d" k)
                                               (is (= k o))
                                               (is (= k n))
                                               (+ o n)))))
    (is-dict-valid all)
    (is (= 128 (dict:size all)))
    (is-dict-valid evens)
    (is (= 64 (dict:size evens)))
    (is-dict-valid merged-left)
    (is (= 128 (dict:size merged-left)))
    (is-dict-valid merged-right)
    (is (= 128 (dict:size merged-right)))
    (are-structures-same merged-left merged-right)
    (iter (for i below 128)
      (if (evenp i)
          (progn (is (eql (* i 2) (dict:get merged-left i)))
                 (is (eql (* i 2) (dict:get merged-right i))))
          (progn (is (eql i (dict:get merged-left i)))
                 (is (eql i (dict:get merged-right i))))))))

(define-test to-alist-from-alist-setwise-identity (test-function hash-function)
  (for-all ((alist (gen-alist)))
    (let* ((dict (dict:from-alist alist :test-function test-function
                                        :hash-function hash-function))
           (dict-by-insert-alist (dict:insert-alist (dict:empty :test-function test-function
                                                                :hash-function hash-function)
                                                    alist
                                                    #'merge-function-fail)))
      (is-dict-valid dict)
      (is-dict-valid dict-by-insert-alist)
      (are-structures-same dict dict-by-insert-alist)
      (is (= (length alist) (dict:size dict)))
      (let* ((reconstructed-alist (dict:to-alist dict)))
        (is (set-equal alist reconstructed-alist :test #'equal))))))

(define-test to-ht-from-ht-identity (test-function hash-function)
  (let* ((ht (make-hash-table :test #'eq)))
    (iter (for i below 128)
      (for key = (gensym))
      (setf (gethash key ht)
            (symbol-name key)))
    (signals-with (dict:no-hash-function-for-test (eq 'eq dict:no-hash-function-for-test-function))
      (dict:from-hash-table ht))
    (let* ((dict (dict:from-hash-table ht :test-function test-function
                                          :hash-function hash-function)))
      (is-dict-valid dict)
      (is (= (hash-table-count ht)
             (dict:size dict)))
      (dict:do (key value dict)
        (is (eql value (gethash key ht))))
      (unless (eq #'equal (dict:test-function dict))
        (signals-with (dict:invalid-hash-table-test (eq #'hash:== dict:invalid-hash-table-test-test))
          (dict:to-hash-table dict)))
      (let* ((reconstructed-ht (dict:to-hash-table dict :test #'eq)))
        (is (= (hash-table-count ht)
               (hash-table-count reconstructed-ht)))
        (iter (for (key value) in-hashtable reconstructed-ht)
          (is (eql value (gethash key ht))))))))
