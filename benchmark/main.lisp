(uiop:define-package :immutable/benchmark/main
  (:use :cl :iterate
        :immutable/benchmark/utils
        :immutable/benchmark/dict
        :immutable/benchmark/dict-old)
  (:export #:run-benchmarks))
(in-package :immutable/benchmark/main)

(defun run-benchmarks ()
  (run-suite immutable-dict-suite)
  (run-suite immutable-dict-old-suite))
