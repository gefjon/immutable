(defsystem "immutable"
  :class :package-inferred-system
  :author "Phoebe Goldman <phoebe@goldman-tribe.org>"
  :version "0.0.1"
  :depends-on ("immutable/vec" "immutable/dict")
  :in-order-to ((test-op (test-op "immutable/test"))))

(defsystem "immutable/test"
  :defsystem-depends-on ((:version "fiveam-asdf" "3.0.1"))
  :class :package-inferred-fiveam-tester-system
  :depends-on ((:version "uiop" "3.3.4") ; for sbcl package-local-nicknames
               "immutable/test/vec")
  :test-names ((#:immutable-vec-suite . :immutable/test/vec)))
