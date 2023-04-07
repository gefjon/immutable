(uiop:define-package :immutable/benchmark/compare-batch-inserts
  (:use :cl :iterate)
  (:local-nicknames (#:dict :immutable/dict))
  (:export #:run-benchmarks))
(in-package :immutable/benchmark/compare-batch-inserts)

(declaim (optimize (speed 3) (safety 1) (debug 1) (space 1) (compilation-speed 0)))

(declaim (pathname *out-dir*))
(defparameter *out-dir*
  (asdf:system-relative-pathname "immutable" "benchmark-data/compare-batch-inserts/"))
#+sbcl (declaim (sb-ext:always-bound *out-dir*))

(declaim (fixnum *min-trials* *min-run-time-s*))
(defparameter *min-trials* 16)
(defparameter *min-run-time-s* 16)
#+sbcl (declaim (sb-ext:always-bound *min-trials* *min-run-time-s*))

(declaim (ftype (function ((and fixnum unsigned-byte)) (values dict:dict &optional))
                make-int-id-dict-of-size-persistent
                make-int-id-dict-of-size-transient))
(defun make-int-id-dict-of-size-persistent (size)
  (iter (declare (declare-variables))
    (with partial = (dict:empty))
    (for (the fixnum i) below size)
    (setf partial (dict:insert partial i i))
    (finally (return partial))))

(defun make-int-id-dict-of-size-transient (size)
  (iter (declare (declare-variables))
    (with trans = (dict:transient (dict:empty)))
    (for (the fixnum i) below size)
    (dict:insert! trans i i)
    (finally (return (dict:persistent! trans)))))

(defstruct time-info
  (num-iterations 0 :type fixnum)
  (total-internal-real-time 0 :type fixnum)
  (total-internal-run-time 0 :type fixnum)
  #+sbcl (total-bytes-consed 0 :type fixnum)
  #+sbcl (total-internal-gc-time 0 :type fixnum))

(declaim (ftype (function ((function () (values &rest t))
                           &key (:min-trials fixnum)
                           (:min-run-time-s fixnum))
                          (values time-info &optional))
                call-with-timing))
(defun call-with-timing (thunk &key (min-trials *min-trials*)
                                 (min-run-time-s *min-run-time-s*)
                         &aux (min-internal-run-time (* min-run-time-s internal-time-units-per-second)))
  (declare (fixnum min-internal-run-time))
  ;; garbage collect before running to avoid noise; reinit the gc statistics so that GET-BYTES-CONSED isn't a
  ;; bignum.
  #+sbcl (progn (sb-ext:gc :full t)
                (sb-kernel:gc-reinit))
  (let* (#+sbcl (bytes-consed-before (sb-ext:get-bytes-consed))
         #+sbcl (gc-time-before sb-ext:*gc-run-time*)
         (real-time-before (get-internal-real-time))
         (run-time-before (get-internal-run-time))
         (trial-count 0))
    (declare (fixnum trial-count #+sbcl bytes-consed-before #+sbcl gc-time-before))
    (iter (declare (declare-variables))
      (funcall thunk)
      (incf trial-count)
      (until (and (>= trial-count min-trials)
                  (>= (- (get-internal-run-time) run-time-before)
                      min-internal-run-time))))
    (let* ((real-time-after (get-internal-real-time))
           (run-time-after (get-internal-run-time))
           #+sbcl (gc-time-after sb-ext:*gc-run-time*)
           #+sbcl (bytes-consed-after (sb-ext:get-bytes-consed)))
      (declare (fixnum #+sbcl gc-time-after #+sbcl bytes-consed-after))
      (make-time-info :num-iterations trial-count
              :total-internal-real-time (- real-time-after real-time-before)
              :total-internal-run-time (- run-time-after run-time-before)
              #+sbcl :total-bytes-consed #+sbcl (- bytes-consed-after bytes-consed-before)
              #+sbcl :total-internal-gc-time #+sbcl (- gc-time-after gc-time-before)))))

(defmacro with-timing ((&key (min-trials '*min-trials*)
                          (min-run-time-s '*min-run-time-s*))
                       &body body)
  `(flet ((with-timing-thunk ()
           ,@body))
    (declare (dynamic-extent #'with-timing-thunk))
    (call-with-timing #'with-timing-thunk
                      :min-trials ,min-trials
                      :min-run-time-s ,min-run-time-s)))

(declaim (ftype (function (fixnum)
                          (values time-info &optional))
                time-constructing-persistent
                time-constructing-transient))
(defun time-constructing-persistent (size)
  (with-timing ()
    (make-int-id-dict-of-size-persistent size)))

(defun time-constructing-transient (size)
  (with-timing ()
    (make-int-id-dict-of-size-transient size)))

(declaim (ftype (function (time-info (function (time-info) (values fixnum &optional)))
                          (values fixnum double-float double-float &optional))
                total-internal-total-seconds-average-seconds))
(defun total-internal-total-seconds-average-seconds (time-info slot-reader)
  (let* ((total-internal (funcall slot-reader time-info))
         (total-seconds (/ total-internal internal-time-units-per-second))
         (average-seconds (/ total-seconds (time-info-num-iterations time-info))))
    (values total-internal
            (coerce total-seconds 'double-float)
            (coerce average-seconds 'double-float))))

(declaim (ftype (function (stream fixnum time-info)
                          (values &optional))
                csv-print-time-info))
(defun csv-print-time-info (stream size time-info)
  (fresh-line stream)
  (format stream
          "~d, ~d"
          size
          (time-info-num-iterations time-info))
  (multiple-value-bind (total-internal-real-time total-s-real-time avg-s-real-time)
      (total-internal-total-seconds-average-seconds time-info #'time-info-total-internal-real-time)
    (format stream
            ", ~d, ~f, ~f"
            total-internal-real-time
            total-s-real-time
            avg-s-real-time))
  (multiple-value-bind (total-internal-run-time total-s-run-time avg-s-run-time)
      (total-internal-total-seconds-average-seconds time-info #'time-info-total-internal-run-time)
    (format stream
            ", ~d, ~f, ~f"
            total-internal-run-time
            total-s-run-time
            avg-s-run-time))
  #+sbcl
  (multiple-value-bind (total-internal-gc-time total-s-gc-time avg-s-gc-time)
      (total-internal-total-seconds-average-seconds time-info #'time-info-total-internal-gc-time)
    (format stream
            ", ~d, ~f, ~f"
            total-internal-gc-time
            total-s-gc-time
            avg-s-gc-time))
  #+sbcl
  (format stream
          ", ~d, ~f"
          (time-info-total-bytes-consed time-info)
          (coerce (/ (time-info-total-bytes-consed time-info)
                     (time-info-num-iterations time-info))
                  'double-float))

  (terpri stream)

  (force-output stream)

  (values))

(defun print-csv-header (stream &optional (size "SIZE"))
  (format stream "# ~a, NUM-ITERATIONS, TOTAL-INTERNAL-REAL-TIME, TOTAL-S-REAL-TIME, AVG-S-REAL-TIME, TOTAL-INTERNAL-RUN-TIME, TOTAL-S-RUN-TIME, AVG-S-RUN-TIME"
          size)
  #+sbcl
  (write-string ", TOTAL-INTERNAL-GC-TIME, TOTAL-S-GC-TIME, AVG-S-GC-TIME, TOTAL-BYTES-CONSED, AVG-BYTES-CONSED"
                stream)
  (terpri stream))

(declaim (ftype (function (pathname
                           (and fixnum unsigned-byte)
                           (and fixnum unsigned-byte)
                           (function (fixnum) (values time-info &optional)))
                          (values &optional))
                time-constructing-to-csv))
(defun time-constructing-to-csv (outpath min-size-2^ max-size-2^ time-function)
  (with-open-file (outfile outpath :direction :output
                                   :if-exists :supersede)
    (print-csv-header outfile)
    (iter (declare (declare-variables))
      (for (the fixnum expt) from min-size-2^ to max-size-2^)
      (for size = (ash 1 expt))
      (format *debug-io* "~&Running experiment ~a with size ~d..."
              time-function size)
      (force-output *debug-io*)
      (for time-info = (funcall time-function size))
      (csv-print-time-info outfile size time-info)
      (format *debug-io* " Done!~%"))
    (values)))

(defun test-time-constructing (&key (min-size-2^ 4) (max-size-2^ 16))
  (ensure-directories-exist *out-dir*)
  (time-constructing-to-csv (make-pathname :name "time-constructing-persistent"
                                           :type "csv"
                                           :defaults *out-dir*)
                            min-size-2^ max-size-2^
                            #'time-constructing-persistent)
  (time-constructing-to-csv (make-pathname :name "time-constructing-transient"
                                           :type "csv"
                                           :defaults *out-dir*)
                            min-size-2^ max-size-2^
                            #'time-constructing-transient))

(declaim (ftype (function ((and fixnum (integer 1)) (and fixnum (integer 1)))
                          (values time-info &optional))
                time-batched-insert-persistent-inorder
                time-batched-insert-transient-inorder
                time-batched-insert-persistent-random
                time-batched-insert-transient-random))
(defun time-batched-insert-persistent-inorder (total-size num-insertions)
  (let* ((dict (make-int-id-dict-of-size-persistent total-size)))
    (with-timing ()
      (iter (declare (declare-variables))
        (with (the dict:dict partial) = dict)
        (for (the fixnum i) below num-insertions)
        (setf partial (dict:insert partial i i))))))

(defun time-batched-insert-transient-inorder (total-size num-insertions)
  (let* ((dict (make-int-id-dict-of-size-persistent total-size)))
    (with-timing ()
      (iter (declare (declare-variables))
        (with (the dict:transient partial) = (dict:transient dict))
        (for (the fixnum i) below num-insertions)
        (setf partial (dict:insert! partial i i))
        (finally (dict:persistent! partial))))))

(defun time-batched-insert-persistent-random (total-size num-insertions)
  (let* ((dict (make-int-id-dict-of-size-persistent total-size)))
    (with-timing ()
      (iter (declare (declare-variables))
        (with (the dict:dict partial) = dict)
        (repeat num-insertions)
        (for i = (random total-size))
        (setf partial (dict:insert partial i i))))))

(defun time-batched-insert-transient-random (total-size num-insertions)
  (let* ((dict (make-int-id-dict-of-size-persistent total-size)))
    (with-timing ()
      (iter (declare (declare-variables))
        (with (the dict:transient partial) = (dict:transient dict))
        (repeat num-insertions)
        (for i = (random total-size))
        (setf partial (dict:insert! partial i i))
        (finally (dict:persistent! partial))))))

(declaim (ftype (function (pathname
                           (and fixnum unsigned-byte)
                           (and fixnum (integer 1))
                           (and fixnum (integer 1))
                           (and fixnum (integer 1))
                           (function (fixnum fixnum) (values time-info &optional)))
                          (values &optional))
                time-inserting-to-csv))
(defun time-inserting-to-csv (out-dir
                              min-size-2^ max-size-2^
                              min-num-insertions-2^ max-num-insertions-2^
                              time-function)
  (ensure-directories-exist out-dir)
  (iter (declare (declare-variables))
    (for i from min-size-2^ to max-size-2^)
    (for size = (ash 1 i))
    (for out-path = (make-pathname :name (format nil "initial-size-~10,'0d" size)
                                   :type "csv"
                                   :defaults out-dir))
    (with-open-file (outfile out-path :direction :output
                                      :if-exists :supersede)
      (print-csv-header outfile "NUM-INSERTIONS")
      (iter (declare (declare-variables))
        (for j from min-num-insertions-2^ to max-num-insertions-2^)
        (for num-insertions = (ash 1 j))
        (format *debug-io* "~&Running experiment ~a with initial-size ~d and num-insertions ~d..."
                time-function
                size
                num-insertions)
        (force-output *debug-io*)
        (for time-info = (funcall time-function size num-insertions))
        (csv-print-time-info outfile num-insertions time-info)
        (write-line " Done!" *debug-io*))))
  (values))

(defun test-time-inserting (&key (min-size-2^ 4) (max-size-2^ 16)
                              (min-num-insertions-2^ 4)
                              (max-num-insertions-2^ 16))
  (time-inserting-to-csv (pathname (concatenate 'string
                                                (namestring *out-dir*)
                                                "inorder-persistent/"))
                         min-size-2^ max-size-2^
                         min-num-insertions-2^ max-num-insertions-2^
                         #'time-batched-insert-persistent-inorder)
  (time-inserting-to-csv (pathname (concatenate 'string
                                                (namestring *out-dir*)
                                                "inorder-transient/"))
                         min-size-2^ max-size-2^
                         min-num-insertions-2^ max-num-insertions-2^
                         #'time-batched-insert-transient-inorder)
  (time-inserting-to-csv (pathname (concatenate 'string
                                                (namestring *out-dir*)
                                                "random-persistent/"))
                         min-size-2^ max-size-2^
                         min-num-insertions-2^ max-num-insertions-2^
                         #'time-batched-insert-persistent-random)
  (time-inserting-to-csv (pathname (concatenate 'string
                                                (namestring *out-dir*)
                                                "random-transient/"))
                         min-size-2^ max-size-2^
                         min-num-insertions-2^ max-num-insertions-2^
                         #'time-batched-insert-transient-random))

(defun run-benchmarks ()
  (ensure-directories-exist *out-dir*)
  (test-time-constructing)
  (test-time-inserting))
