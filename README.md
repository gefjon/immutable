# IMMUTABLE - persistent data structures in Common Lisp
## By Phoebe Goldman

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
  - [x] internal iteration facility - `generate-vec`
  - [x] convert from CL sequences - `from-list` and `from-vector`
  - [x] convert to CL sequences - `to-list` and `to-vector`
  - [x] constructor analogous to `list` and `vector` - `vec`
  - [x] append one to end - `push-back`
  - [ ] pop one from end
  - [x] append multiple to end - `extend`
  - [ ] remove multiple from end
  - [ ] replace element at given index - `replace-at`
  - [ ] convenient iteration constructs
    - [ ] `map` - apply function to each element, collect result to new `vec`
    - [ ] `for-each` - apply function to each element, discard result
    - [ ] `do` - macro analogous to `dolist`
    - [ ] `iterate` integration?
  - [ ] equality testing
  - [ ] hashing?
  - [ ] transients - see [Jean Niklas L'orange's blog post](https://hypirion.com/musings/understanding-clojure-transients)
    - [ ] representation for transient ids
    - [ ] make `vec` transient - `transient!`
    - [ ] make transient persistent - `persistent`
    - [ ] append one to end - `push-back!`
    - [ ] pop one from end
    - [ ] append multiple to end - `extend!`
    - [ ] remove multiple from end
- [ ] `map` - hash array mapped tries
  - [ ] type definition
    - [ ] generic over hash and equality functions
  - [ ] lookup
    - [ ] generic over hash and equality functions
  - [ ] internal iteration facility
  - [ ] convert from CL collections - `from-hash-table`, `from-alist`?
  - [ ] convert to CL collections - `to-hash-table`, `to-alist`?
  - [ ] convenient constructor macro?
  - [ ] insert one pair
  - [ ] insert multiple pairs?
  - [ ] remove one pair
  - [ ] remove multiple pairs?
  - [ ] convenient iteration constructs
    - [ ] `map-values` - apply function to each value, leaving keys untouched, collect to new `map`
    - [ ] `for-each` - apply function to each pair, discard result
    - [ ] `do` - macro analogous to `dolist`
    - [ ] `iterate` integration?
  - [ ] equality testing
  - [ ] hashing?
  - [ ] transients
    - [ ] representation for transient ids
    - [ ] make map transient - `transient!`
    - [ ] add one pair
    - [ ] add multiple pairs?
    - [ ] remove one pair
    - [ ] remove multiple pairs?
