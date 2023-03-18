(uiop:define-package :immutable/test/hash
  (:use :cl :fiveam :iterate :immutable/test/utils)
  (:import-from :trivial-garbage
                #:gc)
  (:local-nicknames (#:hash :immutable/hash))
  (:export #:immutable-hash-suite))
(in-package :immutable/test/hash)

(def-suite immutable-hash-suite)

;;; helper functions

(declaim (ftype (function (vector) (values &optional))
                are-hashes-stable))
(defun are-hashes-stable (things)
  (quietly
    (let* ((hashes-before-gc (iter (for thing in-vector things)
                               (collect (hash:hash thing) result-type vector))))
      (gc :full t)
      (iter (for thing in-vector things)
        (for hash-before-gc in-vector hashes-before-gc)
        (is (eql hash-before-gc (hash:hash thing)))))
    (write-char #\. *test-dribble*)
    (sync-test-dribble))
  (values))

(defparameter *acceptable-hash-conflict-rate*
  1e-6
  "TODO: come up with a more rigorous value for this than \"I picked a number that seems small\" - pgoldman 2023-03-17")

(defvar *hash-conflicts*)
(defvar *hash-trials*)
(defvar *found-hash-conflicts*)

(defun are-hash-and-==-consistent (gen-element &key id not-id)
  (let* ((random-elements (iter (repeat *num-trials*)
                            (collect (funcall gen-element) result-type vector)))
         (*hash-conflicts* 0)
         (*hash-trials* 0)
         (*found-hash-conflicts* ()))
    (iter (for element in-vector random-elements)
      (is (hash:== element element))
      (is (eql (hash:hash element)
               (hash:hash element)))
      (iter (for wonky-id in id)
        (for same-element = (funcall wonky-id element))
        (is (hash:== element same-element))
        (is (eql (hash:hash element)
                 (hash:hash same-element))))

      (iter (for get-other in not-id)
        (for different-element = (funcall get-other element))
        (is (not (hash:== element different-element)))
        (incf *hash-trials*)
        (when (eql (hash:hash element)
                   (hash:hash different-element))
          (incf *hash-conflicts*)
          (push (cons element different-element)
                *found-hash-conflicts*))))

    (when (plusp *hash-trials*)
      (is (< (/ *hash-conflicts* *hash-trials*)
             *acceptable-hash-conflict-rate*)
          "Rate of observed hash conflicts ~a (~a / ~a) is greater than threshold ~a~%Found the following conflicts: ~a"
          (/ *hash-conflicts* *hash-trials*)
          *hash-conflicts*
          *hash-trials*
          *acceptable-hash-conflict-rate*
          *found-hash-conflicts*))
    
    (sync-test-dribble)

    (are-hashes-stable random-elements)))

;;; testing various numeric types

(def-test hash-fixnums (:suite immutable-hash-suite)
  (are-hash-and-==-consistent *gen-fixnum*
                              :id (list #'+
                                        #'*
                                        (lambda (x) (1- (1+ x)))
                                        (lambda (x) (floor (* x 2) 2)))
                              :not-id (list #'-
                                            #'/
                                            #'1+
                                            #'1-
                                            (lambda (x) (* x 2))
                                            (lambda (x) (/ x 2))
                                            #'float
                                            (lambda (x)
                                              (complex x x)))))

(def-test hash-bignums (:suite immutable-hash-suite)
  (are-hash-and-==-consistent *gen-bignum*
                              :id (list #'+
                                        #'*
                                        (lambda (x) (1- (1+ x)))
                                        (lambda (x) (floor (* x 2) 2)))
                              :not-id (list #'-
                                            #'/
                                            #'1+
                                            #'1-
                                            (lambda (x) (* x 2))
                                            (lambda (x) (/ x 2))
                                            (lambda (x)
                                              (complex x x)))))

(defun without-float-traps (thunk &optional (default 0))
  "Wrap THUNK in code that arranges to return DEFAULT instead of signaling an error on an invalid operation, e.g. float overflow."
  (lambda (&rest stuff)
    (handler-case (apply thunk stuff)
      (arithmetic-error () default))))

(def-test hash-floats (:suite immutable-hash-suite)
  (declare (optimize (debug 3) (space 1) (speed 1) (safety 3)))
  (dolist (float-type (list *gen-short-float* *gen-single-float* *gen-long-float* *gen-double-float*))
    (are-hash-and-==-consistent float-type
                                :id (list #'+
                                          #'*
                                          #'float
                                          (lambda (x) (coerce (coerce x 'long-float) (type-of x)))
                                          (lambda (x) (float (rationalize x) x)))
                                ;; For all of these NOT-ID functions, we don't really care about getting the
                                ;; mathematically correct result out (though we'd prefer it, as detecting
                                ;; collisions with the result of some math is more interesting than detecting
                                ;; collisions with the fixnum 0), so we install a handler using
                                ;; `without-float-traps' instead of worrying about overflow.
                                :not-id (list #'-
                                              #'/
                                              (without-float-traps #'exp)
                                              (without-float-traps #'log)
                                              #'rational
                                              #'rationalize
                                              (without-float-traps
                                                  (lambda (x)
                                                    (etypecase x
                                                      (short-float (coerce x 'long-float))
                                                      (single-float (coerce x 'double-float))
                                                      (double-float (coerce x 'single-float))
                                                      (long-float (coerce x 'short-float)))))))))

(def-test hash-character (:suite immutable-hash-suite)
  (are-hash-and-==-consistent (gen-character)
                              :id (list (lambda (x) (code-char (char-code x))))
                              :not-id (list (lambda (x)
                                              (let* ((code (char-code x)))
                                                (if (< code (1- char-code-limit))
                                                    (code-char (1+ code))
                                                    (code-char (1- code)))))
                                            (lambda (x)
                                              (code-char (floor (char-code x) 2)))
                                            (lambda (x)
                                              (code-char (ceiling (char-code x) 2))))))

(def-test hash-ratio (:suite immutable-hash-suite)
  (let* ((ids (list #'+
                    #'*
                    (lambda (x) (/ (/ x)))
                    (lambda (x) (1- (1+ x)))
                    (lambda (x) (/ (* x 2) 2))))
         (not-ids (list #'/
                        #'-
                        (lambda (x)
                          (complex x x))
                        (lambda (x)
                          (complex x 1)))))
    (are-hash-and-==-consistent *gen-small-ratio*
                                :id ids
                                :not-id not-ids)
    (are-hash-and-==-consistent *gen-large-ratio*
                                :id ids
                                :not-id not-ids)))

(def-test hash-complex (:suite immutable-hash-suite)
  (dolist (gen-part (list *gen-fixnum*
                          *gen-bignum*
                          *gen-short-float*
                          *gen-single-float*
                          *gen-single-float*
                          *gen-double-float*
                          *gen-long-float*
                          *gen-small-ratio*
                          *gen-large-ratio*))
    (are-hash-and-==-consistent (gen-complex gen-part)
                                :id (list (lambda (x) (complex (realpart x)
                                                               (imagpart x))))
                                ;; For all of these NOT-ID functions, we don't really care about getting the
                                ;; mathematically correct result out (though we'd prefer it, as detecting
                                ;; collisions with the result of some math is more interesting than detecting
                                ;; collisions with the fixnum 0), so we install a handler using
                                ;; `without-float-traps' instead of worrying about overflow.
                                :not-id (mapcar #'without-float-traps
                                                (list #'/
                                                      #'-
                                                      (lambda (x)
                                                        (* x 2))
                                                      (lambda (x)
                                                        (* x (complex 0 2)))
                                                      (lambda (x)
                                                        (* x (complex 2 2))))))))

;;; vectors, strings and arrays

(defun extend-vector (vector &key (additional-capacity 1000)
                             (adjustable t)
                             (element-type (array-element-type vector))
                      &aux (copy (make-array (+ (length vector) additional-capacity)
                                             :fill-pointer (length vector)
                                             :adjustable adjustable
                                             :element-type element-type)))
  (iter (for elt in-vector vector with-index idx)
    (setf (aref copy idx) elt))
  copy)

(def-test hash-strings (:suite immutable-hash-suite)
  (let* ((string-generators (list (gen-simple-base-string)
                                  (gen-base-string)
                                  (gen-simple-string)
                                  (gen-general-string))))
    (dolist (gen-str string-generators)
      (are-hash-and-==-consistent gen-str
                                  :id (list #'copy-seq
                                            #'extend-vector
                                            (lambda (x)
                                              (coerce x 'string))
                                            (lambda (x)
                                              (coerce x 'simple-vector)))
                                  :not-id (list (lambda (x)
                                                  (subseq x 1))
                                                (lambda (x)
                                                  (subseq x 0 (1- (length x)))))))))

(def-test hash-bit-vectors (:suite immutable-hash-suite)
  (let* ((bit-vector-generators (list (gen-simple-bit-vector)
                                      (gen-bit-vector))))
    (dolist (gen-bit-vector bit-vector-generators)
      (are-hash-and-==-consistent gen-bit-vector
                                  :id (list #'copy-seq
                                            #'extend-vector
                                            (lambda (x)
                                              (coerce x 'simple-vector)))
                                  :not-id (list (lambda (x)
                                                  (subseq x 1))
                                                (lambda (x)
                                                  (subseq x 0 (1- (length x))))
                                                (lambda (x)
                                                  (bit-not x)))))))

(def-test hash-vectors (:suite immutable-hash-suite)
  (let* ((vector-generators (list (gen-simple-vector)
                                  (gen-adjustable-vector))))
    (dolist (gen-vector vector-generators)
      (are-hash-and-==-consistent gen-vector
                                  :id (list #'copy-seq
                                            #'extend-vector
                                            (lambda (x)
                                              (coerce x 'simple-vector)))
                                  :not-id (list (lambda (x)
                                                  (subseq x 1))
                                                (lambda (x)
                                                  (subseq x 0 (1- (length x)))))))))

(def-test hash-arrays (:suite immutable-hash-suite)
  ;; not a call to `are-hash-and-==-consistent' for memory usage reasons: while the arrays we're consing
  ;; aren't *huge*, consing `*num-trials*' of them at once seems not ideal.
  (for-all ((array (gen-array)))
    (is (hash:== array array))
    (is (hash:==-array array array))
    (let* ((hash-before-gc (hash:hash array)))
      (gc)
      (is (eql hash-before-gc
               (hash:hash array))))))

(def-test hash-cons-trees (:suite immutable-hash-suite)
  (are-hash-and-==-consistent (gen-list :length *gen-short-length*
                                        :elements *gen-fixnum*)
                              :id (list #'copy-seq
                                        (lambda (x)
                                          (reverse (reverse x))))
                              :not-id (list #'cdr
                                            (constantly nil)
                                            (lambda (x)
                                              (coerce x 'vector))))
  (are-hash-and-==-consistent (gen-tree :elements *gen-fixnum*)
                              ;; TODO: come up with some ID-ey and NOT-ID-ey functions on cons trees
                              ))

(def-test hash-symbols (:suite immutable-hash-suite)
  (are-hash-and-==-consistent #'gensym
                              ;; TODO: come up with some ID-ey and NOT-ID-ey functions on symbols. Constraint:
                              ;;       SBCL's `sxhash' on symbol hashes only by `symbol-name', and we defer to
                              ;;       it because it's cached and therefore efficient, so e.g. `intern',
                              ;;       `alexandria:make-gensym', etc. will cause hash-conflicts.
                              ))
