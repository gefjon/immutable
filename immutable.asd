(defsystem "immutable"
  :class :package-inferred-system
  :author "Phoebe Goldman <phoebe@goldman-tribe.org>"
  :version "0.0.1"
  :depends-on ("immutable/vec"
               "immutable/hash"
               "immutable/dict")
  :in-order-to ((test-op (test-op "immutable/test"))))

(defsystem "immutable/test"
  :defsystem-depends-on ((:version "fiveam-asdf" "3.0.1"))
  :class :package-inferred-fiveam-tester-system
  :depends-on ((:version "uiop" "3.3.5") ; for uiop package-local-nicknames support
               "immutable/test/vec"
               "immutable/test/hash")
  :test-names ((#:immutable-vec-suite . #:immutable/test/vec)
               (#:immutable-hash-stuie . #:immutable/test/hash)))
