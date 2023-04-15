# IMMUTABLE - persistent data structures in Common Lisp
## By Phoebe Goldman

![CI](https://github.com/gefjon/immutable/actions/workflows/CI.yml/badge.svg?branch=main)

This is a (currently WIP) repository of immutable, persistent data structures in Common
Lisp. My dream is that someday it will rival Clojure's standard library collection types.

## Design notes

### Naming and package local nicknames

Modern CL code has access to `:package-local-nicknames` in `defpackage` and
`uiop:define-package`. We can expect the main way of using IMMUTABLE to be by
local-nicknaming `immutable/vec` to `vec`, or `immutable/map` to `map`, and referring to
operators like `vec:length` and `vec:ref`. This means that operator names should be
concise, and need not include their type to disambiguate. IMMUTABLE's packages should
shadow CL symbols liberally to accomplish this.

## TODO

- [ ] `vec` - bit-partitioned tries with tails
  - [x] type definition - `vec`
  - [x] indexing - `ref`
  - [x] examine length - `length`
    - [x] `emptyp`
  - [x] internal iteration facility - `generate-vec`
  - [x] convert from CL sequences - `from-list` and `from-vector`
  - [x] convert to CL sequences - `to-list` and `to-vector`
  - [x] constructor analogous to `list` and `vector` - `vec`
  - [x] append one to end - `push-back`
  - [x] pop one from end - `pop-back`
  - [x] append multiple to end - `extend`
    - [x] `extend-from-vector`
    - [x] `extend-from-list`
  - [x] concatenate vecs - `concatenate`
  - [x] remove multiple from end - `retract`
  - [x] replace element at given index - `replace-at`
  - [x] update element at given index by function - `update-at`
  - [x] convenient iteration constructs
    - [x] `map` - apply function to each element, collect result to new `vec`
    - [x] `for-each` - apply function to each element, discard result
    - [x] `do` - macro analogous to `dolist`
    - [x] `iterate` integration - `FOR elt IN-VEC vec`
    - [ ] sequence keywords
      - [ ] `start`
      - [ ] `end`
      - [ ] `from-end`
  - [x] equality testing - `equal`
  - [ ] hashing?
  - [ ] transients - see [Jean Niklas L'orange's blog post](https://hypirion.com/musings/understanding-clojure-transients)
    - [ ] representation for transient ids
    - [ ] make `vec` transient - `transient!`
    - [ ] make transient persistent - `persistent`
    - [ ] append one to end - `push-back!`
    - [ ] pop one from end
    - [ ] append multiple to end - `extend!`
    - [ ] remove multiple from end
  - [ ] [trivial-extensible-sequences](https://shinmera.github.io/trivial-extensible-sequences/) integration
    - [ ] define `vec` as a `standard-class` subclassing `sequences:sequence`
      - [ ] use `standard-instance-access` when available to optimize slot access
    - [ ] method on `sequences:length` which calls `length`
    - [ ] method on `sequences:elt` which calls `ref`
    - [ ] method on `make-simple-sequence-iterator`
      - [ ] method on `iterator-element`
      - [ ] method on `iterator-step`
      - [ ] method on `iterator-endp`
      - [ ] method on `iterator-element`
      - [ ] method on `iterator-index`
      - [ ] method on `iterator-copy`
    - [ ] method on `concatenate` when RESULT-PROTOTYPE and the first sequence are `vec`s
          to share structure with the first sequence
    - [ ] no-op method on `copy-seq`
    - [ ] method on `emptyp`
    - [ ] method on `map`
- [ ] `hash` - generic hashing and equality for use by `dict`
  - [x] core FxHash algorithm
  - [ ] hashing and equality for builtin types, and tests
    - [x] `fixnum`
    - [x] `integer`
    - [x] `float`
      - [x] `single-float`
      - [x] `double-float`
      - [x] do implementations with `short-float` and `long-float` actually exist?
    - [x] `character`
    - [x] `complex`
    - [x] `ratio`
    - [x] `vector`
      - [x] `string`
        - [x] `simple-base-string`
        - [x] `base-string`
        - [x] `simple-string`
        - [x] generic `string`
      - [x] `bit-vector`
        - [x] `simple-bit-vector`
        - [x] generic `bit-vector`
      - [x] `simple-vector`
      - [x] generic `vector`
    - [x] `array`
    - [x] `cons`
    - [x] `symbol`
    - [ ] generic function for user-defined methods
      - [ ] MOP-ey default method for `standard-object` and `condition`
  - [x] `==` wrapper
  - [x] `hash` wrapper which returns `unsigned-fixnum`
- [ ] `dict` - hash array mapped tries
  - [x] type definition
    - [x] generic over hash and equality functions
  - [x] lookup
    - [x] generic over hash and equality functions
    - [x] tests
  - [x] optimize node definitions to store key/value pairs inline.
    - [ ] convenient internal iterators over the children of a `hash-node` or `conflict-node`?
  - [x] internal iteration facility
  - [ ] convert from CL collections - `from-hash-table`, `from-alist`?
  - [ ] convert to CL collections - `to-hash-table`, `to-alist`?
  - [x] convenient constructor - `dict`
  - [x] insert one pair
    - [x] tests
  - [x] remove one pair
    - [x] tests
  - [x] user-friendly print-object
    - [ ] print-object for transients?
  - [ ] test that same hash and test functions imply same structure after various operations
    - [x] insertion in random order
    - [ ] removal
    - [ ] replacement
  - [x] insert multiple pairs - `insert-multiple`
    - [x] tests
  - [x] remove multiple pairs - `remove-multiple`
    - [x] tests
  - [x] combine two maps - `union`
    - [x] check for compatible hash and equality functions
      - [ ] solve equality testing on arbitrary closures /s
      - [x] fall back to `reduce` of `insert` when the hash and equality functions are not `eq`
      - [x] structural merge when the hash and equality functions are `eq`
    - [x] accept a `merge-entries` function of type `(function (key value value) (values
          value &optional))` to avoid left- or right-bias
  - [ ] convenient iteration constructs
    - [x] `map-values` - apply function to each value, leaving keys untouched, collect to new `dict`
    - [x] `for-each` - apply function to each pair, discard result
    - [x] `do` - macro analogous to `dolist`
    - [ ] `iterate` integration?
  - [ ] equality testing
  - [ ] change hash and test function of `dict` - `rehash`
  - [ ] hashing?
  - [x] transients
    - [x] representation for transient ids
    - [x] make dict transient - `transient!`
    - [x] add one pair
    - [ ] add multiple pairs?
    - [x] remove one pair
    - [ ] remove multiple pairs?
  - [ ] integration with trivial-extensible-sequences?
- [ ] `rope` - ropes of characters as strings
  - [ ] type definition
    - [ ] node for strings
      - [ ] specialize on string subtypes?
    - [ ] node for concatenation
    - [ ] node for substring
  - [ ] short node optimization to avoid unnecessary indirections
    - [ ] experiment with different cutoffs to balance between cost of copying and cost of indirection
  - [ ] lookup
  - [ ] internal iteration facility
  - [ ] convert from CL strings
  - [ ] convert to CL strings
  - [ ] convenient constructor?
      - [ ] output to stream without converting to string
