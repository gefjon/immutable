(uiop:define-package :immutable/test/vec
  (:use :cl :fiveam :iterate)
  (:import-from :alexandria
                #:once-only #:with-gensyms)
  (:local-nicknames (#:vec :immutable/vec)
                    (#:gen :immutable/%generator)))
(in-package :immutable/test/vec)

(def-suite immutable-vec-suite)

;;; helpers

(defun call-quietly (thunk)
  "Call THUNK in a context where FiveAM produces no text output for checks.

Useful for comparing each element of a VEC against the corresponding element of its source data, to avoid
printing a large number of dots to *TEST-DRIBBLE*."
  (let* ((*test-dribble* (make-broadcast-stream)))
    (unwind-protect (funcall thunk)
      (close *test-dribble*))))

(defmacro quietly (&body body)
  "Evaluate BODY in a context where FiveAM produces no text output for checks.

Useful for comparing each element of a VEC against the corresponding element of its source data, to avoid
printing a large number of dots to *TEST-DRIBBLE*."
  `(call-quietly (lambda () ,@body)))

(defun gen-element (&key (generators (list (gen-string) (gen-list) (gen-tree) (gen-character) (gen-float) (gen-integer))))
  "Generate a value of essentially arbitrary type, to be compared with EQL."
  (let* ((get-generator (apply #'gen-one-element generators)))
    (lambda ()
      (funcall (funcall get-generator)))))

(defun gen-simple-vector (&key (length (gen-integer :min 16 :max 128))
                            (elements (gen-element)))
  "Generate a SIMPLE-VECTOR, with length chosen from the LENGTH generator, and elements chosen from the ELEMENTS generator."
  (lambda ()
    (let* ((this-length (funcall length))
           (arr (make-array this-length)))
      (iter (for i below this-length)
        (setf (svref arr i)
              (funcall elements)))
      arr)))

(defun gen-vec (&key (length (gen-integer :min 16 :max 128))
                  (elements (gen-element)))
  "Generate a random vec with length taken from the LENGTH generator and elements taken from the ELEMENTS generator."
  (lambda ()
    (vec::generator-vec (funcall length) elements)))

(defun sync-test-dribble ()
  (force-output *test-dribble*))

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
        (is (>= vec::+branch-rate+ (length tail))))
      (is (= length (+ found-body-length (length tail))))))
  (write-char #\. *test-dribble*)
  (sync-test-dribble)
  vec)

;;; testing round-trips between CL data structures and vecs

;; the -SMALL- tests use GEN-ELEMENT of (relatively) arbitrary type, which makes generation somewhat slow.

(def-test round-trip-small-lists (:suite immutable-vec-suite)
  (for-all ((list (gen-list :length (gen-integer :min 16 :max 128)
                            :elements (gen-element))))
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

;; the -LARGE- tests use GEN-INTEGER to generate elements, which makes generation relatively fast, to
;; compensate for the much larger data being generated and processed.

(defun max-length-at-height (height)
  (+ (vec::max-body-length-at-height height)
     vec::+branch-rate+)) ; the max tail length

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

;;; testing the EXTEND operator

(def-test extend-like-append-small-list (:suite immutable-vec-suite)
  (for-all ((start (gen-list :length (gen-integer :min 0 :max 128) :elements (gen-element)))
            (end (gen-list :length (gen-integer :min 0 :max 128) :elements (gen-element))))
    (let* ((start-vec (apply #'vec:vec start))
           (whole-vec (apply #'vec:extend start-vec end))
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
           (whole-vec (vec::extend-from-generator start-vec (gen:generate-vector end) (length end)))
           (whole-vector (concatenate 'vector start end)))
      (is-vec-valid start-vec)
      (is-vec-valid whole-vec)
      (is-each-element whole-vec in-vector whole-vector eql)
      (is (equalp whole-vector (vec:to-vector whole-vec)))
      (sync-test-dribble))))

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
              (next-elt (gen-element)))
      (is-id vec next-elt))))
