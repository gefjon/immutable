(uiop:define-package :immutable/test/vec
  (:use :cl :fiveam :iterate :immutable/test/utils)
  (:import-from :alexandria
                #:once-only #:with-gensyms)
  (:local-nicknames (#:vec :immutable/vec)
                    (#:gen :immutable/%generator)))
(in-package :immutable/test/vec)

;; don't care about micro-optimizations in the tests
#+sbcl (declaim (sb-ext:muffle-conditions sb-ext:compiler-note))

(def-suite immutable-vec-suite)

;;; helpers

(defun gen-vec (&key (length (gen-integer :min 16 :max 128))
                  (elements *gen-fixnum*))
  "Generate a random vec with length taken from the LENGTH generator and elements taken from the ELEMENTS generator."
  (lambda ()
    (vec::generator-vec (funcall length) elements)))

(defmacro is-each-element (vec in sequence pred)
  "Assert that each element in VEC is PRED to the corresponding element of SEQUENCE.

IN is an iterate keyword for iterating over SEQUENCE; IN for lists, IN-VECTOR for vectors."
  (with-gensyms (idx elt)
    (once-only (vec sequence)
      `(quietly (iter (for ,idx upfrom 0)
                  (for ,elt ,in ,sequence)
                  (is (,pred ,elt (vec:ref ,vec ,idx))))))))

(defun is-body-balanced-and-length-in-elts (body height)
  (if (zerop height)
      (progn (is (typep body `(simple-vector ,vec::+branch-rate+))
                 "Expected node of height zero to be a ~a but found ~a"
                 `(simple-vector ,vec::+branch-rate+)
                 body)
             vec::+branch-rate+)
      (progn
        (is (typep body 'simple-vector))
        (is (>= vec::+branch-rate+ (length body)))
        (is (< 0 (length body)))
        (iter (for child in-vector body)
          (summing (is-body-balanced-and-length-in-elts child (1- height)))))))

(defun is-vec-valid (vec)
  (quietly
    (let* ((height (vec::%vec-height vec))
           (body (vec::%vec-body vec))
           (tail (vec::%vec-tail vec))
           (length (vec::%vec-length vec))
           (found-body-length (if body
                                  (is-body-balanced-and-length-in-elts body height)
                                  0)))
      (when tail
        (is (typep tail 'simple-vector))
        (is (>= vec::+branch-rate+ (length tail)))
        (is (< 0 (length tail))))
      (is (= length (+ found-body-length (length tail))))))
  vec)

;;; testing round-trips between CL data structures and vecs

(def-test round-trip-small-lists (:suite immutable-vec-suite)
  (for-all ((list (gen-list :length (gen-integer :min 16 :max 128)
                            :elements *gen-fixnum*)))
    (let* ((vec (vec:from-list list)))
      (is-vec-valid vec)
      (is-each-element vec in list eql)
      (is (equal list (vec:to-list vec)))
      (sync-test-dribble))))

(def-test round-trip-small-vectors (:suite immutable-vec-suite)
  (for-all ((vector (gen-simple-vector)))
    (let* ((vec (vec:from-vector vector)))
      (is-vec-valid vec)
      (is-each-element vec in-vector vector eql)
      (is (equalp vector (vec:to-vector vec)))
      (sync-test-dribble))))

(defun max-length-at-height (height)
  (+ (vec::max-body-length-at-height height)
     vec::+branch-rate+)) ; the max tail length

(defun gen-length-of-height (height)
  (gen-integer :min (if (zerop height)
                        0
                        (1+ (max-length-at-height (1- height))))
               :max (max-length-at-height height)))

(defparameter *gen-length-of-height-2-or-3*
  (gen-integer :min (1+ (max-length-at-height 1))
               :max (max-length-at-height 3)))

(def-test round-trip-large-integer-lists (:suite immutable-vec-suite)
  (for-all ((list (gen-list :length *gen-length-of-height-2-or-3*)))
    (let* ((vec (vec:from-list list)))
      (is-vec-valid vec)
      (is-each-element vec in list =)
      (is (equal list (vec:to-list vec)))
      (sync-test-dribble))))

(def-test round-trip-large-integer-vectors (:suite immutable-vec-suite)
  (for-all ((vector (gen-simple-vector :length *gen-length-of-height-2-or-3*
                                       :elements (gen-integer :min -10 :max 10))))
    (let* ((vec (vec:from-vector vector)))
      (is-vec-valid vec)
      (is-each-element vec in-vector vector =)
      (is (equalp vector (vec:to-vector vec)))
      (sync-test-dribble))))

;;; testing the PUSH-BACK operator

(def-test reduce-push-back-like-from-vector-small (:suite immutable-vec-suite)
  (for-all ((vector (gen-simple-vector)))
    (let* ((by-reduce (reduce #'vec:push-back vector :initial-value vec:+empty+)))
      (is-vec-valid by-reduce)
      (is-each-element by-reduce in-vector vector eql)
      (is (equalp vector (vec:to-vector by-reduce)))
      (sync-test-dribble))))

;;; testing error on out-of-bounds access

(def-test ref-out-of-bounds-error (:suite immutable-vec-suite)
  (for-all ((vec (gen-vec)))
    (is-vec-valid vec)
    (signals vec:out-of-bounds
      (vec:ref vec (vec:length vec)))
    (sync-test-dribble)))

;;; testing the EXTEND operator and its EXTEND-FROM-FOO friends

(def-test extend-like-append-small-list (:suite immutable-vec-suite)
  (for-all ((start (gen-list :length (gen-integer :min 0 :max 128) :elements *gen-fixnum*))
            (end (gen-list :length (gen-integer :min 0 :max 128) :elements *gen-fixnum*)))
    (let* ((start-vec (vec:from-list start))
           (whole-vec (vec:extend-from-list start-vec end))
           (whole-list (append start end)))
      (is-vec-valid start-vec)
      (is-vec-valid whole-vec)
      (is-each-element whole-vec in whole-list eql)
      (is (equal whole-list (vec:to-list whole-vec)))
      (sync-test-dribble))))

(def-test extend-like-concatenate-small-vector (:suite immutable-vec-suite)
  (for-all ((start (gen-simple-vector :length (gen-integer :min 0 :max 128)))
            (end (gen-simple-vector :length (gen-integer :min 0 :max 128))))
    (let* ((start-vec (vec:from-vector start))
           (whole-vec (vec:extend-from-vector start-vec end))
           (whole-vector (concatenate 'vector start end)))
      (is-vec-valid start-vec)
      (is-vec-valid whole-vec)
      (is-each-element whole-vec in-vector whole-vector eql)
      (is (equalp whole-vector (vec:to-vector whole-vec)))
      (sync-test-dribble))))

(def-test extend-like-append-large-then-short-integer-list (:suite immutable-vec-suite)
  (for-all ((start-list (gen-list :length *gen-length-of-height-2-or-3*
                                  :elements (gen-integer :min 0 :max most-positive-fixnum)))
            (end-list (gen-list :elements (gen-integer :min 0 :max most-positive-fixnum))))
    (let* ((start-vec (vec:from-list start-list))
           (whole-vec (vec:extend-from-list start-vec end-list))
           (whole-list (append start-list end-list)))
      (is-vec-valid start-vec)
      (is-vec-valid whole-vec)
      (is-each-element whole-vec in whole-list eql)
      (is (equal whole-list (vec:to-list whole-vec)))
      (sync-test-dribble))))

(def-test extend-like-append-short-then-large-integer-list (:suite immutable-vec-suite)
  (for-all ((start-list (gen-list :elements (gen-integer :min 0 :max most-positive-fixnum)))
            (end-list (gen-list :length *gen-length-of-height-2-or-3*
                                :elements (gen-integer :min 0 :max most-positive-fixnum))))
    (let* ((start-vec (vec:from-list start-list))
           (whole-vec (vec:extend-from-list start-vec end-list))
           (whole-list (append start-list end-list)))
      (is-vec-valid start-vec)
      (is-vec-valid whole-vec)
      (is-each-element whole-vec in whole-list eql)
      (is (equal whole-list (vec:to-list whole-vec)))
      (sync-test-dribble))))

(def-test extend-like-append-large-then-large-integer-list (:suite immutable-vec-suite)
  (for-all ((start-list (gen-list :length (gen-length-of-height 2)
                                  :elements (gen-integer :min 0 :max most-positive-fixnum)))
            (end-list (gen-list :length (gen-length-of-height 2)
                                :elements (gen-integer :min 0 :max most-positive-fixnum))))
    (let* ((start-vec (vec:from-list start-list))
           (whole-vec (vec:extend-from-list start-vec end-list))
           (whole-list (append start-list end-list)))
      (is-vec-valid start-vec)
      (is-vec-valid whole-vec)
      (is-each-element whole-vec in whole-list eql)
      (is (equal whole-list (vec:to-list whole-vec)))
      (sync-test-dribble))))

(def-test extend-like-concatenate-large-then-short-integer-vector (:suite immutable-vec-suite)
  (for-all ((start-vector (gen-simple-vector :length (gen-length-of-height 2)
                                             :elements (gen-integer :min 0 :max most-positive-fixnum)))
            (end-vector (gen-simple-vector :elements (gen-integer :min 0 :max most-positive-fixnum))))
    (let* ((start-vec (vec:from-vector start-vector))
           (whole-vec (vec:extend-from-vector start-vec end-vector))
           (whole-vector (concatenate 'vector start-vector end-vector)))
      (is-vec-valid start-vec)
      (is-vec-valid whole-vec)
      (is-each-element whole-vec in-vector whole-vector eql)
      (is (equalp whole-vector (vec:to-vector whole-vec)))
      (sync-test-dribble))))

(def-test extend-like-concatenate-short-then-large-integer-vector (:suite immutable-vec-suite)
  (for-all ((start-vector (gen-simple-vector :elements (gen-integer :min 0 :max most-positive-fixnum)))
            (end-vector (gen-simple-vector :length (gen-length-of-height 2)
                                           :elements (gen-integer :min 0 :max most-positive-fixnum))))
    (let* ((start-vec (vec:from-vector start-vector))
           (whole-vec (vec:extend-from-vector start-vec end-vector))
           (whole-vector (concatenate 'vector start-vector end-vector)))
      (is-vec-valid start-vec)
      (is-vec-valid whole-vec)
      (is-each-element whole-vec in-vector whole-vector eql)
      (is (equalp whole-vector (vec:to-vector whole-vec)))
      (sync-test-dribble))))

;;; CONCATENATE, which could be called EXTEND-FROM-VEC

(def-test concatenate-compiler-macro-well-behaved (:suite immutable-vec-suite)
  (flet ((test-many-times (start-length end-length)
           (for-all ((start-vec (gen-vec :length start-length
                                         :elements (gen-integer :min 0 :max most-positive-fixnum)))
                     (end-vec (gen-vec :length end-length
                                       :elements (gen-integer :min 0 :max most-positive-fixnum))))
             (is-vec-valid start-vec)
             (is-vec-valid end-vec)
             (let* ((concat-2 (vec:concatenate start-vec end-vec))
                    (concat-n (locally (declare (notinline vec:concatenate))
                                (vec:concatenate start-vec end-vec))))
               (is-vec-valid concat-2)
               (is-vec-valid concat-n)
               (is (= (+ (vec:length start-vec) (vec:length end-vec))
                      (vec:length concat-n)
                      (vec:length concat-2)))
               (is (vec:equal concat-n concat-2)))
             (sync-test-dribble))))
    (test-many-times (gen-integer :min 16 :max 128)
                     (gen-integer :min 16 :max 128))
    (test-many-times (gen-length-of-height 2)
                     (gen-length-of-height 2))))

;;; testing the POP-BACK operator

(def-test push-back-pop-back-identity (:suite immutable-vec-suite)
  (flet ((is-id (vec elt)
           (is-vec-valid vec)
           (let* ((pushed (vec:push-back vec elt)))
             (is-vec-valid vec)
             (is (eql elt
                      (vec:ref pushed (1- (vec:length pushed)))))
             (multiple-value-bind (popped popped-elt)
                 (vec:pop-back pushed)
               (is-vec-valid popped)
               (is (vec:equal vec popped))
               (is (eql popped-elt elt))))))
    (is-id (vec:vec) 0)
    (is-id (vec:vec 0) 1)
    (for-all ((vec (gen-vec))
              (next-elt *gen-fixnum*))
      (is-id vec next-elt))))

(def-test pop-back-empty-error (:suite immutable-vec-suite)
  (flet ((is-empty (vec)
           (is (zerop (vec:length vec)))
           (signals vec:pop-back-empty
             (vec:pop-back vec))))
    (is-empty vec:+empty+)
    (let* ((vec (vec:vec 0)))
      (is-vec-valid vec)
      (is (= 1 (vec:length vec)))
      (multiple-value-bind (empty-vec zero) (vec:pop-back vec)
        (is-vec-valid empty-vec)
        (is (= 0 zero))
        (is-empty empty-vec)))))

;;; testing the RETRACT operator

(def-test retract-short-integer-vec-expected-length (:suite immutable-vec-suite)
  (for-all ((vec (gen-vec :elements (gen-integer :min 0 :max most-positive-fixnum)))
            (elts-to-remove (gen-integer :min 16 :max 128)))
    (is-vec-valid vec)
    (if (<= elts-to-remove (vec:length vec))
        (let* ((retracted (vec:retract vec elts-to-remove)))
          (is-vec-valid retracted)
          (is (= (- (vec:length vec) elts-to-remove)
                 (vec:length retracted))))
        (signals vec:retract-not-enough-elements
          (vec:retract vec elts-to-remove)))))

(def-test retract-long-integer-vec-expected-length (:suite immutable-vec-suite)
  (for-all ((vec (gen-vec :elements (gen-integer :min 0 :max most-positive-fixnum)
                          :length (gen-length-of-height 3)))
            (elts-to-remove (gen-length-of-height 2)))
    (is-vec-valid vec)
    (let* ((retracted (vec:retract vec elts-to-remove)))
      (is-vec-valid retracted)
      (is (= (- (vec:length vec) elts-to-remove)
             (vec:length retracted))))))

(def-test retract-known-vec-expected-outputs (:suite immutable-vec-suite)
  (flet ((is-expected (vec elts-to-remove expected-contents)
           (is-vec-valid vec)
           (let* ((retracted (vec:retract vec elts-to-remove)))
             (is-vec-valid retracted)
             (is-each-element retracted in expected-contents eql))
           (sync-test-dribble)))
    (is-expected (vec:vec) 0 nil)
    (flet ((list-below (n)
             (iter (for i below n) (collect i))))
      (let* ((vec-128 (vec:from-list (list-below 128))))
        (iter (for i below 128)
          (is-expected vec-128 i (list-below (- 128 i))))))))

;;; testing the UPDATE-AT and REPLACE-AT operators

(def-test update-at-long-integer-vec-1+ (:suite immutable-vec-suite)
  (for-all ((vec (gen-vec :elements (gen-integer :min -128 :max 128)
                          :length *gen-length-of-height-2-or-3*)))
    (let* ((index-to-update (random (vec:length vec)))
           (updated (vec:update-at vec index-to-update #'1+)))
      (quietly
        (is-vec-valid vec)
        (is-vec-valid updated)
        (is (= (vec:length vec)
               (vec:length updated)))
        (iter (for i below (vec:length vec))
          (if (= i index-to-update)
              (is (= (1+ (vec:ref vec i))
                     (vec:ref updated i)))
              (is (= (vec:ref vec i)
                     (vec:ref updated i)))))))))

(def-test replace-at-long-integer-vec (:suite immutable-vec-suite)
  (for-all ((vec (gen-vec :elements (gen-integer :min -128 :max 128)
                          :length *gen-length-of-height-2-or-3*)))
    (let* ((new-element '#:not-an-integer)
           (index-to-replace (random (vec:length vec)))
           (replaced (vec:replace-at vec index-to-replace new-element)))
      (quietly
        (is-vec-valid vec)
        (is-vec-valid replaced)
        (is (= (vec:length vec)
               (vec:length replaced)))
        (iter (for i below (vec:length vec))
          (if (= i index-to-replace)
              (is (eq new-element
                     (vec:ref replaced i)))
              (is (= (vec:ref vec i)
                     (vec:ref replaced i)))))))))

;;; testing MAP

(def-test map-1+-long-integer-vec (:suite immutable-vec-suite)
  (for-all ((vec (gen-vec :elements (gen-integer :min -128 :max 128)
                          :length *gen-length-of-height-2-or-3*)))
    (let* ((mapped (vec:map #'1+ vec)))
      (is-vec-valid vec)
      (is-vec-valid mapped)
      (is (= (vec:length vec)
             (vec:length mapped)))
      (quietly 
        (iter (for i below (vec:length vec))
          (is (= (1+ (vec:ref vec i))
                 (vec:ref mapped i))))))))

;;; testing iteration constructs: FOR-EACH, DO, and the ITER driver

(def-test for-each-slow-count (:suite immutable-vec-suite)
  (flet ((is-count-like-length (vec)
           (is-vec-valid vec)
           (let* ((count 0))
             (vec:for-each (lambda (elt)
                             (declare (ignore elt))
                             (incf count))
                           vec)
             (is (= (vec:length vec) count)))
           (sync-test-dribble)))
    (for-all ((vec (gen-vec)))
      (is-count-like-length vec))
    (for-all ((vec (gen-vec :length *gen-length-of-height-2-or-3*
                            :elements (gen-integer :min 0 :max most-positive-fixnum))))
      (is-count-like-length vec))))

(def-test do-slow-count (:suite immutable-vec-suite)
  (flet ((is-count-like-length (vec)
           (is-vec-valid vec)
           (let* ((count 0))
             (vec:do (elt vec)
                     (declare (ignore elt))
               (incf count))
             (is (= (vec:length vec) count)))
           (sync-test-dribble)))
    (for-all ((vec (gen-vec)))
      (is-count-like-length vec))
    (for-all ((vec (gen-vec :length *gen-length-of-height-2-or-3*
                            :elements (gen-integer :min 0 :max most-positive-fixnum))))
      (is-count-like-length vec))))

(def-test iter-slow-count (:suite immutable-vec-suite)
  (flet ((is-count-like-length (vec)
           (is-vec-valid vec)
           (is (= (vec:length vec)
                  (iter (for elt in-vec vec)
                    (declare (ignorable elt))
                    (counting t))))
           (sync-test-dribble)))
    (for-all ((vec (gen-vec)))
      (is-count-like-length vec))
    (for-all ((vec (gen-vec :length *gen-length-of-height-2-or-3*
                            :elements (gen-integer :min 0 :max most-positive-fixnum))))
      (is-count-like-length vec))))

;;; EMPTYP sanity check

(def-test emptyp (:suite immutable-vec-suite)
  (flet ((is-empty (vec)
           (is-vec-valid vec)
           (is (zerop (vec:length vec)))
           (is (vec:emptyp vec)))
         (is-not-empty (vec)
           (is-vec-valid vec)
           (is (plusp (vec:length vec)))
           (is (not (vec:emptyp vec)))))
    (is-empty vec:+empty+)
    (is-empty (vec:pop-back (vec:vec 0)))
    (for-all ((vec (gen-vec)))
      (is-not-empty vec)
      (is-empty (vec:retract vec (vec:length vec))))))
