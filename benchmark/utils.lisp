(uiop:define-package :immutable/benchmark/utils
  (:use :cl :iterate)
  (:import-from :alexandria
                #:if-let
                #:symbolicate)
  (:export
   #:*bench-out*
   
   #:with-op
   #:def-suite
   #:def-experiment
   #:run-suite
   #:define-growing-experiment))
(in-package :immutable/benchmark/utils)

(declaim (stream *bench-out*))
(defparameter *bench-out* *standard-output*)

(declaim (type fixnum *run-time* *real-time* *num-ops* #+sbcl *gc-time* #+sbcl *bytes-consed*))
(defparameter *run-time* 0)
(defparameter *real-time* 0)
(defparameter *num-ops* 0)
#+sbcl
(defparameter *gc-time* 0)
#+sbcl
(defparameter *bytes-consed* 0)
#+sbcl (declaim (sb-ext:always-bound *run-time* *real-time* *num-ops* *gc-time* *bytes-consed*))

(declaim (ftype (function ((function () (values &rest t)))
                          (values fixnum ;; total internal-real-time
                                  fixnum ;; total internal-run-time
                                  fixnum ;; total num-ops
                                  #+sbcl fixnum ;; gc time
                                  #+sbcl fixnum ;; bytes consed
                                  ))
                call-with-experiment))
(defun call-with-experiment (thunk)
  (let* ((*run-time* 0)
         (*real-time* 0)
         (*num-ops* 0)
         #+sbcl (*gc-time* 0)
         #+sbcl (*bytes-consed* 0))
    (funcall thunk)
    (values *run-time* *real-time* *num-ops* #+sbcl *gc-time* #+sbcl *bytes-consed*)))

(defmacro with-experiment (&body body)
  `(call-with-experiment (lambda () ,@body)))

(declaim (ftype (function ((function () (values &rest t)))
                          (values t &optional))
                call-with-op))
(defun call-with-op (thunk)
  (let* (#+sbcl (bytes-consed-before (sb-ext:get-bytes-consed))
         #+sbcl (sb-ext:*gc-run-time* 0)
         (run-time-before (get-internal-run-time))
         (real-time-before (get-internal-real-time)))
    (prog1 (funcall thunk)
      (let* ((run-time-after (get-internal-run-time))
             (real-time-after (get-internal-real-time))
             #+sbcl (gc-run-time sb-ext:*gc-run-time*)
             #+sbcl (bytes-consed-after (sb-ext:get-bytes-consed)))
        (incf *num-ops*)
        (incf *run-time* (max 0 (- run-time-after run-time-before)))
        (incf *real-time* (max 0 (- real-time-after real-time-before)))
        #+sbcl (incf *gc-time* gc-run-time)
        #+sbcl (incf *bytes-consed* (the fixnum (- bytes-consed-after bytes-consed-before)))))))

(defmacro with-op (&body body)
  `(call-with-op (lambda () ,@body)))

(declaim (ftype (function (fixnum) (values double-float &optional))
                internal-time-to-seconds))
(defun internal-time-to-seconds (internal-time)
  (coerce (/ internal-time internal-time-units-per-second) 'double-float))

(declaim (ftype (function ((or string pathname) fixnum (function () (values &rest t)))
                          (values &optional))
                call-run-experiment))
(defun call-run-experiment (out-file num-trials experiment-thunk)
  (with-open-file (out-stream out-file :direction :output
                                       :if-exists :supersede)
    (declare (stream out-stream))
    (format out-stream "# Running on ~a ~a, ~a ~a, ~a ~a~%"
            (software-type) (software-version)
            (machine-type) (machine-version)
            (lisp-implementation-type) (lisp-implementation-version))
    (write-string "TRIAL, OPS, INTERNAL-REAL-TIME, INTERNAL-RUN-TIME, REAL-TIME-S, RUN-TIME-S, AVG-REAL-TIME-S, AVG-RUN-TIME-S"
                  out-stream)
    #+sbcl
    (write-string ", INTERNAL-GC-TIME, GC-TIME-S, AVG-GC-TIME-S, BYTES-CONSED, AVG-BYTES-CONSED"
                  out-stream)
    (write-char #\newline out-stream)
    (iter (declare (declare-variables))
      (for (the fixnum trial) below num-trials)
      (for (values run-time real-time num-ops #+sbcl gc-time #+sbcl bytes-consed)
           = (call-with-experiment experiment-thunk))
      (for real-time-s = (internal-time-to-seconds real-time))
      (for avg-real-time-s = (/ real-time-s num-ops))
      (for run-time-s = (internal-time-to-seconds run-time))
      (for avg-run-time-s = (/ run-time-s num-ops))
      #+sbcl
      (for gc-time-s = (internal-time-to-seconds gc-time))
      #+sbcl
      (for avg-gc-time-s = (/ gc-time-s num-ops))
      #+sbcl
      (for avg-bytes-consed = (coerce (/ bytes-consed num-ops) 'double-float))
      (format out-stream
              "~&~d, ~d, ~d, ~d, ~f, ~f, ~f, ~f"
              trial num-ops real-time run-time real-time-s run-time-s avg-real-time-s avg-run-time-s)
      #+sbcl
      (format out-stream
              ", ~d, ~f, ~f, ~d, ~f"
              gc-time gc-time-s avg-gc-time-s bytes-consed avg-bytes-consed)
      (write-char #\newline out-stream)
      (write-char #\. *bench-out*)
      (force-output *bench-out*)))
  (values))

(defstruct suite
  (experiments nil :type list)
  out-dir)

(defmacro def-suite (name out-dir)
  `(defvar ,name (make-suite :out-dir ,out-dir)))

(defun add-experiment (suite name func)
  (if-let ((entry (assoc name (suite-experiments suite) :test #'eq)))
    (setf (cdr entry) func)
    (push (cons name func)
          (suite-experiments suite))))

(defmacro def-experiment (name (&key suite) &body body)
  `(progn
     (defun ,name ()
       ,@body)
     (add-experiment ,suite ',name #',name)))

(defun run-suite (suite &optional (num-trials 16))
  (ensure-directories-exist (suite-out-dir suite))
  (iter (for (name . runner) in (reverse (suite-experiments suite)))
    (for out-file = (format nil "~a/~a.csv"
                            (suite-out-dir suite)
                            name))
    (format *bench-out*
            "~&Running experiment ~s with ~d trials; output to ~s...~%"
            name num-trials out-file)
    (call-run-experiment out-file num-trials runner)
    (format *bench-out* "~&  Experiment ~s done!~%"
            name)))

(defmacro define-growing-experiment (base-name (&key suite) (binding &optional (min-2^ 4) (max-2^ 22)) &body body)
  (declare ((and fixnum unsigned-byte) min-2^ max-2^)
           (symbol base-name suite)
           #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note))
  (let* ((width (length (prin1-to-string (ash 1 max-2^))))
         (format-number-string (concatenate 'string "~" (prin1-to-string width) ",'0d")))
    (labels ((experiment-name (count)
               (symbolicate base-name '- (format nil format-number-string count)))
             (def-one-experiment (i &aux (count (ash 1 i)))
                 `(def-experiment ,(experiment-name count) (:suite ,suite)
                    (symbol-macrolet ((,binding ,count))
                      ,@body))))
      (cons 'progn
            (iter (for i from min-2^ below max-2^)
              (collect (def-one-experiment i)))))))
