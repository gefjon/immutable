(defsystem "immutable"
  :class :package-inferred-system
  :author "Phoebe Goldman <phoebe@goldman-tribe.org>"
  :version "0.0.1"
  :depends-on ("immutable/vec"
               "immutable/hash"
               "immutable/dict-inline"
               "immutable/dict-naive"
               "immutable/dict-sv-entry-node")
  :in-order-to ((test-op (test-op "immutable/test"))))

(defsystem "immutable/test"
  :defsystem-depends-on ((:version "fiveam-asdf" "3.0.1"))
  :class :package-inferred-fiveam-tester-system
  :depends-on ((:version "uiop" "3.3.5") ; for uiop package-local-nicknames support
               "immutable/test/vec"
               "immutable/test/hash"
               "immutable/test/dict")
  :test-names ((#:immutable-vec-suite . #:immutable/test/vec)
               (#:immutable-hash-suite . #:immutable/test/hash)
               (#:immutable-dict-suite . #:immutable/test/dict)))

(defsystem "immutable/benchmark"
  :class :package-inferred-system
  :depends-on ((:version "uiop" "3.3.5")
               "immutable/benchmark/dict-naive"
               "immutable/benchmark/dict-inline"
               "immutable/benchmark/dict-sv-entry-node"
               "immutable/benchmark/main"))
