(uiop:define-package :immutable/benchmark/main
  (:use :cl :iterate
        :immutable/benchmark/utils
        :immutable/benchmark/dict-naive
        :immutable/benchmark/dict-inline
        :immutable/benchmark/dict-sv-entry-node)
  (:export #:run-benchmarks))
(in-package :immutable/benchmark/main)

(defun run-benchmarks ()
  (run-suite immutable-dict-sv-entry-node-suite)
  (run-suite immutable-dict-naive-suite)
  (run-suite immutable-dict-inline-suite))
