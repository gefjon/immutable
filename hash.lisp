;;;; A hash function inspired by the FxHash hashing algorithm.
;; FxHash was originally developed by the Firefox web browser. The Firefox implementation can be viewed at
;; https://searchfox.org/mozilla-central/rev/633345116df55e2d37be9be6555aa739656c5a7d/mfbt/HashFunctions.h#109-153
;; It is described by Nicholas Nethercote in a blog post, "A brutally effective hash function in Rust," which
;; can be viewed at https://nnethercote.github.io/2021/12/08/a-brutally-effective-hash-function-in-rust.html

;; Possibly unexpected quirks of this hashing algorithm
;; - Any builtin types which cannot be hashed meaningfully will signal an error.
;;   - This includes `stream', `function', `random-state', `hash-table', `readtable', `package', `condition'
;;     and `restart'.
;;   - These are types for which the only meaningful way to hash is by object identity (`eq'), which is not a
;;     stable property on implementations with a moving garbage collector.
;; - Equality comparisons are only provided for types with meaningful hashing.
;; - Hasing for user-defined classes (`defclass', `defstruct', `define-condition') defers to the generic
;;   function `hash-object'.
;;   - CLOS dispatch is somewhat slow on PCL-based implementations, so users building hash maps keyed by known
;;     user-defined types may want to define their own hash function.
;;   - On MOP-ful implementations, a default method is provided for `condition' and `standard-object' which
;;     uses the MOP to recurse into all slots. This is likely catastrophically slow, so users are encouraged
;;     to define their own methods.
;;   - No default method is provided for `structure-object', so users who want to hash structures must define
;;     their own method on `hash-object'.
;; - Numeric types are treated as if by `eql', not `='. That is, equality takes type into consideration. The
;;   following objects are not `==', and should have different hashes:
;;   - (the fixnum 1)
;;   - (the double-float 1d0)
;;   - (the single-float 1f0)
;; - Arrays are potentially equal regardless of their element-type. Two arrays are equal if their rank and
;;   dimensions are the same and all of their elements are equal.
;;   - `hash-vector', `==-vector', and more specialized comparisons respect the fill-pointer, while
;;     `hash-array' and `==-array' ignore it. This means that two vectors may be `==-vector' but not
;;     `==-array'. The generic `hash', `hash-dispatch' and `==' always prefer the `-vector' operators when
;;     the argument is one-dimensional.
;; - Internally, hashing is done on (unsigned-64), but the entry function `hash' truncates hashes to be an
;;   `unsigned-fixnum'. This allows consumers, like `immutable/dict', to operate on hashes efficiently without
;;   heap-allocating bignums.
(uiop:define-package :immutable/hash
  (:use :cl :iterate :immutable/%generator)
  (:import-from :alexandria
                #:type= #:with-gensyms #:once-only #:array-index)
  (:import-from :float-features
                #:short-float-bits
                #:single-float-bits
                #:double-float-bits
                #:long-float-bits)

  (:import-from :closer-mop
                ;; No actual imports, just tell ASDF we depend on this.
                )

  (:export
   ;; generic entry points
   #:hash
   #:==

   ;; condition class for un-hash-able objects
   #:cannot-hash
   #:cannot-hash-object

   ;; generic functions
   #:==-object
   #:hash-object

   ;; equality on particular types
   #:==-fixnum
   #:==-bignum
   #:==-single-float
   #:==-double-float
   #:==-short-float
   #:==-long-float
   #:==-float
   #:==-ratio
   #:==-complex
   #:==-character
   #:==-simple-bit-vector
   #:==-bit-vector
   #:==-simple-base-string
   #:==-base-string
   #:==-simple-string
   #:==-string
   #:==-simple-vector
   #:==-vector
   #:==-array
   #:==-cons
   #:==-list
   #:==-symbol

   ;; hasher state
   #:lx-hasher
   #:add-to-hash

   ;; hashing particular objects
   #:hash-dispatch
   #:hash-fixnum
   #:hash-bignum
   #:hash-single-float
   #:hash-double-float
   #:hash-short-float
   #:hash-long-float
   #:hash-float
   #:hash-ratio
   #:hash-complex
   #:hash-character
   #:hash-simple-bit-vector
   #:hash-bit-vector
   #:hash-simple-base-string
   #:hash-base-string
   #:hash-simple-string
   #:hash-string
   #:hash-simple-vector
   #:hash-vector
   #:hash-array
   #:hash-cons
   #:hash-list
   #:hash-symbol

   ;; utility type
   #:unsigned-fixnum))
(in-package :immutable/hash)

#+immutable-hash-debug
(declaim (optimize (speed 1) (safety 3) (debug 3) (space 0) (compilation-speed 0)))
#-immutable-hash-debug
(declaim (optimize (speed 3) (safety 1) (debug 1) (space 0) (compilation-speed 0)))

#-(or 64-bit 32-bit)
(eval-when (:compile-toplevel :load-toplevel)
  (error "Unable to detect the word size on your lisp implementation.

Push either :32-BIT or :64-BIT to *FEATURES* before compiling IMMUTABLE/HASH."))

(eval-when (:compile-toplevel :load-toplevel)
  (defconstant +word-bits+
    #+64-bit
    64
    #+32-bit
    32)
  (defconstant +hash-bits+ +word-bits+))

(deftype hash ()
  "A computed hash of an arbitrary object."
  `(unsigned-byte ,+hash-bits+))

(deftype word ()
  "An unsigned machine integer of the same width as a hash."
  `(unsigned-byte ,+word-bits+))

(deftype unsigned-fixnum ()
  '(and unsigned-byte fixnum))

(defconstant +all-ones-hash+
  (1- (ash 1 +hash-bits+)))

(declaim ((and fixnum unsigned-byte) +unsigned-fixnum-bits+))
(defconstant +unsigned-fixnum-bits+
  (floor (log (1+ most-positive-fixnum) 2)))

(declaim (ftype (function (hash) (values fixnum &optional))
                truncate-hash)
         (inline truncate-hash))
(defun truncate-hash (hash)
  (* (ecase (ldb (byte 1 (1- +hash-bits+)) hash)
       (0 1)
       (1 -1))
     (ldb (byte +unsigned-fixnum-bits+ 0)
          hash)))

(declaim (ftype (function (word (integer 0 #.(1- +word-bits+)))
                          (values word &optional))
                rotate-word)
         (inline rotate-word))
;; adapted from https://www.cliki.net/ROTATE-BYTE

;; on SBCL, we could use SB-ROTATE-BYTE, but a comparison showed that they generate the same machine code, at
;; least on my m1 mac. - pgoldman 2023-03-14
(defun rotate-word (word count)
  (logand +all-ones-hash+
          (logior (ash word count)
                  (ash word (- count +hash-bits+)))))

(declaim (hash +magic-constant+))
(defconstant +magic-constant+
  #+64-bit
  #x517cc1b727220a95
  #+32-bit
  #x9e3779b9
  ;; Approximately:
  ;; (floor +all-ones-hash+
  ;;        (rationalize pi))
  ;; but that computes #x517cc1b727220b26 (on SBCL 2.2.11 on my m1 mac - pgoldman 2023-03-17), which is just
  ;; slightly off from the number used by Firefox and rustc. Their version seems to produce better hashes, so
  ;; I just hard-code it.
  )

(declaim (ftype (function (word word) (values hash &optional))
                wrapping-mul)
         (inline wrapping-mul))
(defun wrapping-mul (left right)
  (logand +all-ones-hash+
          (* left right)))

;; We define a struct `fx-hasher' which holds a running hash in an unboxed slot for use in `call-with-hasher',
;; rather than using a closure, because on SBCL it results in fewer heap allocations: if we stored the running
;; hash in a closure variable, we would (potentially, unless it could be dx) allocate its value cell, plus
;; we'd heap-allocate every hash greater than `most-positive-fixnum' as a bignum. With the struct, we
;; heap-allocate a signle `fx-hasher' instance, and then no hash ever gets consed as a bignum; they just get
;; stored into the hasher's unboxed slot.

(declaim (inline make-fx-hasher fx-hasher-hash))

(defstruct fx-hasher
  (hash 0 :type hash))

(declaim (ftype (function (fx-hasher word) (values &optional))
                add-to-hasher)
         (inline add-to-hasher))
(defun add-to-hasher (hasher word)
  (setf (fx-hasher-hash hasher)
        (wrapping-mul (logxor (rotate-word (fx-hasher-hash hasher)
                                           5)
                              word)
                      +magic-constant+))
  (values))

(declaim (ftype (function ((function (fx-hasher) (values &rest t)))
                          (values hash &optional))
                call-with-hasher)
         (inline call-with-hasher))
(defun call-with-hasher (thunk)
  (let* ((hasher (make-fx-hasher)))
    (declare (dynamic-extent hasher))
    (funcall thunk hasher)
    (fx-hasher-hash hasher)))

(defmacro with-hasher ((binding) &body body)
  `(call-with-hasher (lambda (,binding) ,@body)))

;; equality helpers

(declaim (ftype (function (t) (values boolean &optional))
                truthyp)
         (inline truthyp))
(defun truthyp (thing)
  "Coerce THING into a `boolean', i.e. either T or nil."
  (if thing t nil))

(defmacro typecase-both ((left right) default-clause &body clauses)
  (with-gensyms (default-case)
    (once-only (left right)
      (flet ((transform-clause (clause)
               (let* ((type (first clause))
                      (body (rest clause)))
                 `(,type (if (typep ,right',type)
                             (progn ,@body)
                             (,default-case))))))
        `(flet ((,default-case () ,default-clause))
           (typecase ,left
             ,@(mapcar #'transform-clause clauses)
             (t (,default-case))))))))

;; predeclarations for better type inference
(declaim (ftype (function (fx-hasher t) (values &optional))
                hash-dispatch)
         (ftype (function (t t) (values boolean &optional))
                ==)
         ;; this quiets some "unable to inline" warnings
         (notinline hash-dispatch ==))

;;; hashing integers

(declaim (ftype (function ((signed-byte #.+word-bits+)) (values word &optional))
                signed-to-unsigned-word)
         ;; Inlining may allow the compiler to avoid heap-allocating bignum results.
         (inline signed-to-unsigned-word))
(defun signed-to-unsigned-word (signed-word)
  (ldb (byte +word-bits+ 0)
       signed-word))

(declaim (ftype (function (fx-hasher fixnum) (values &optional))
                hash-fixnum))
(defun hash-fixnum (hasher fixnum)
  (add-to-hasher hasher (signed-to-unsigned-word fixnum)))

(declaim (ftype (function (fixnum fixnum) (values boolean &optional))
                ==-fixnum))
(defun ==-fixnum (a b)
  (= a b))

(declaim (ftype (function (fx-hasher integer &optional (and fixnum unsigned-byte)) (values &optional))
                hash-bignum)
         ;; inlining may allow the compiler to specialize on the SIZE-IN-BITS argument
         (inline hash-bignum))
(defun hash-bignum (hasher integer &optional (size-in-bits (integer-length integer)))
  (labels ((repeat (offset)
             (let* ((word (ldb (byte +word-bits+ offset)
                               integer)))
               (add-to-hasher hasher word)
               (if (> offset size-in-bits)
                   (values)
                   (repeat (+ offset +word-bits+))))))
    (repeat 0)))

(declaim (ftype (function (integer integer) (values boolean &optional))
                ==-bignum))
(defun ==-bignum (a b)
  (= a b))

;;; hashing floats and characters

(eval-when (:compile-toplevel :load-toplevel)
  (unless (type= 'single-float 'short-float)
    (pushnew :distinct-short-float *features*))
  (unless (type= 'double-float 'long-float)
    (pushnew :distinct-long-float *features*)))

(macrolet ((define-hash-immediate (fname type-name num-bits get-bits)
             (declare ((and fixnum unsigned-byte) num-bits)
                      (symbol fname type-name get-bits))
             (with-gensyms (salt-constant)
               `(progn
                  (defconstant ,salt-constant (sxhash ',type-name))
                  (declaim (ftype (function (fx-hasher ,type-name) (values &optional))
                                  ,fname)
                           (inline ,fname))
                  (defun ,fname (hasher value)
                    (add-to-hasher hasher ,salt-constant)
                    (let* ((bits (,get-bits value)))
                      ,(if (<= num-bits +word-bits+)
                           `(add-to-hasher hasher bits)
                           `(hash-bignum hasher bits ,num-bits))))
                  (declaim (notinline ,fname))))))
  (define-hash-immediate hash-character character 32 char-code)
  #+distinct-short-float
  (define-hash-immediate hash-short-float short-float 16 short-float-bits)
  (define-hash-immediate hash-single-float single-float 32 single-float-bits)
  (define-hash-immediate hash-double-float double-float 64 double-float-bits)
  #+distinct-long-float
  (define-hash-immediate hash-long-float long-float 128 long-float-bits))

#-distinct-short-float
(declaim (ftype (function (fx-hasher short-float) (values &optional))
                hash-short-float))
(defun hash-short-float (hasher short-float)
  (hash-single-float hasher short-float))

#-distinct-long-float
(declaim (ftype (function (fx-hasher long-float) (values &optional))
                hash-long-float))
(defun hash-long-float (hasher long-float)
  (hash-double-float hasher long-float))

(declaim (ftype (function (fx-hasher float) (values &optional))
                hash-float))
(defun hash-float (hasher float)
  (etypecase float
    #+distinct-short-float
    (short-float (hash-short-float hasher float))
    (single-float (hash-single-float hasher float))
    (double-float (hash-double-float hasher float))
    #+distinct-long-float
    (long-float (hash-long-float hasher float))))

(macrolet ((define-==-immediate (fname type-name inner-equal)
             (declare (symbol fname type-name inner-equal))
             `(progn
                (declaim (ftype (function (,type-name ,type-name) (values boolean &optional))
                                ,fname)
                         (inline ,fname))
                (defun ,fname (a b)
                  (truthyp (,inner-equal a b)))
                (declaim (notinline ,fname)))))
  (define-==-immediate ==-character character char=)
  #+distinct-short-float
  (define-==-immediate ==-short-float short-float =)
  (define-==-immediate ==-single-float single-float =)
  (define-==-immediate ==-double-float double-float =)
  #+distinct-long-float
  (define-==-immediate ==-long-float long-float =))

#-distinct-short-float
(declaim (ftype (function (short-float short-float) (values boolean &optional))
                ==-short-float)
         (inline ==-short-float))
(defun ==-short-float (a b)
  (==-single-float a b))
(declaim (notinline ==-short-float))

#-distinct-long-float
(declaim (ftype (function (long-float long-float) (values boolean &optional))
                ==-long-float)
         (inline ==-short-float))
(defun ==-long-float (a b)
  (==-double-float a b))
(declaim (notinline ==-short-float))

(declaim (ftype (function (float float) (values boolean &optional))
                ==-float)
         (inline ==-float))
(defun ==-float (a b)
  (typecase-both (a b) nil
    #+distinct-short-float
    (short-float (==-short-float a b))
    (single-float (==-single-float a b))
    (double-float (==-double-float a b))
    #+distinct-long-float
    (long-float (==-long-float a b))))
(declaim (notinline ==-float))

;;; hashing "weird" numbers, i.e. ratios and complexes

(declaim (ftype (function (fx-hasher complex &optional (function (fx-hasher t) (values &optional)))
                          (values &optional))
                hash-complex)
         ;; inlining `hash-complex' may allow the compiler to specialize on the complex number's part
         ;; type, and to inline the HASH-ELEMENT function.
         ;; TODO: define `hash-real' for more specialized dispatch than `hash-dispatch' as a default
         ;;       HASH-ELEMENT function.
         (inline hash-complex))
(defun hash-complex (hasher complex &optional (hash-element #'hash-dispatch))
  (funcall hash-element hasher (realpart complex))
  (funcall hash-element hasher (imagpart complex)))

(declaim (ftype (function (complex complex &optional (function (t t) (values boolean &optional)))
                          (values boolean &optional))
                ==-complex)
         ;; inlining `==-complex' may allow the compiler to specialize on the complex number's part
         ;; type, and to inline the ==-ELEMENT function.
         ;; TODO: define `==-real' for more specialized dispatch than `==' as a default
         ;;       ==-ELEMENT function.
         (inline ==-complex))
(defun ==-complex (a b &optional (==-element #'==))
  (and (funcall ==-element (realpart a) (realpart b))
       (funcall ==-element (imagpart a) (imagpart b))))

(declaim (ftype (function (fx-hasher ratio)
                          (values &optional))
                hash-ratio))
(defun hash-ratio (hasher ratio)
  ;; no point in inlining `hash-bignum' because the size in bits is not constant
  (declare (notinline hash-bignum))
  (hash-bignum hasher (numerator ratio))
  (hash-bignum hasher (denominator ratio)))

(declaim (ftype (function (ratio ratio) (values boolean &optional))
                ==-ratio))
(defun ==-ratio (a b)
  (and (==-bignum (numerator a) (numerator b))
       (==-bignum (denominator a) (denominator b))))

;;; hashing vectors and arrays

(declaim (ftype (function (fx-hasher
                           vector
                           &optional (function (fx-hasher t) (values &optional)))
                          (values &optional))
                hash-vector)
         ;; inlining `hash-vector' may allow the compiler to specialize on the vector's element-type and
         ;; simple-ness, and to inline the HASH-ELEMENT function.
         (inline hash-vector))
(defun hash-vector (hasher vector &optional (hash-element #'hash-dispatch))
  ;; Mix the length into the hash, so as to avoid collisions between all-zeros vectors of different lengths.
  (hash-fixnum hasher (length vector))
  (iter (declare (declare-variables))
    (for element in-vector vector)
    (funcall hash-element hasher element))
  (values))

(declaim (ftype (function (vector
                           vector
                           &optional (function (t t) (values boolean &optional)))
                          (values boolean &optional))
                ==-vector)
         ;; inlining `==-vector' may allow the compiler to specialize on the vector's element-type and
         ;; simple-ness, and to inline the ==-ELEMENT function.
         (inline ==-vector))
(defun ==-vector (a b &optional (==-element #'==))
  (when (= (length a) (length b))
    (iter (declare (declare-variables))
      (for a-elt in-vector a)
      (for b-elt in-vector b)
      (unless (funcall ==-element a-elt b-elt)
        (return nil))
      (finally (return t)))))

(macrolet ((define-hash-specialized-vector (function-name
                                            vector-type
                                            hash-element
                                            &key inline
                                              (inline-hash-element t))
             `(progn
                (declaim (ftype (function (fx-hasher ,vector-type)
                                          (values &optional))
                                ,function-name)
                         (inline ,function-name))
                (defun ,function-name (hasher vector)
                  ,@(when inline-hash-element `((declare (inline ,hash-element))))
                  (hash-vector hasher vector #',hash-element))
                ,@(unless inline `((declaim (notinline ,function-name)))))))

  ;; spec-required specialized vectors
  ;; strings
  (define-hash-specialized-vector hash-simple-base-string simple-base-string hash-character)
  (define-hash-specialized-vector hash-base-string base-string hash-character
    :inline "Inlining may allow specialization on the string's simple-ness.")
  (define-hash-specialized-vector hash-simple-string simple-string hash-character
    :inline "Inlining may allow specialization on the string's ARRAY-ELEMENT-TYPE.")
  (define-hash-specialized-vector hash-string string hash-character
    :inline "Inlining may allow specialization on the string's ARRAY-ELEMENT-TYPE and simple-ness.")

  ;; bit vectors
  ;; Unfortunately, the spec doesn't offer any way to access multiple bits from a bit-vector simultaneously,
  ;; a la `ldb', so we can't do better than visiting each bit one by one.
  (define-hash-specialized-vector hash-simple-bit-vector simple-bit-vector add-to-hasher)
  (define-hash-specialized-vector hash-bit-vector bit-vector add-to-hasher
    :inline "Inlining may allow specialization on the bit-vector's simple-ness.")
  
  ;; simple-vector, i.e. (and simple-array (vector t))
  (define-hash-specialized-vector hash-simple-vector simple-vector hash-dispatch
    :inline-hash-element nil))

(macrolet ((define-==-specialized-vector (function-name
                                          vector-type
                                          ==-element
                                          &key inline
                                            (inline-compare-element t))
             `(progn
                (declaim (ftype (function (,vector-type ,vector-type)
                                          (values boolean &optional))
                                ,function-name)
                         (inline ,function-name))
                (defun ,function-name (a b)
                  ,@(when inline-compare-element `((declare (inline ,==-element))))
                  (==-vector a b #',==-element))
                ,@(unless inline `((declaim (notinline ,function-name)))))))
  (define-==-specialized-vector ==-simple-base-string simple-base-string ==-character)
  (define-==-specialized-vector ==-base-string base-string ==-character
    :inline "Inlining may allow specialization on the string's simple-ness.")
  (define-==-specialized-vector ==-simple-string simple-string ==-character
    :inline "Inlining may allow specialization on the string's ARRAY-ELEMENT-TYPE.")
  (define-==-specialized-vector ==-string string ==-character
    :inline "Inlining may allow specialization on the string's ARRAY-ELEMENT-TYPE and simple-ness.")

  ;; bit vectors
  ;; Unfortunately, the spec doesn't offer any way to access multiple bits from a bit-vector simultaneously,
  ;; a la `ldb', so we can't do better than visiting each bit one by one.
  (define-==-specialized-vector ==-simple-bit-vector simple-bit-vector ==-fixnum)
  (define-==-specialized-vector ==-bit-vector bit-vector ==-fixnum
    :inline "Inlining may allow specialization on the bit-vector's simple-ness.")
  
  ;; simple-vector, i.e. (and simple-array (vector t))
  (define-==-specialized-vector ==-simple-vector simple-vector ==
    :inline-compare-element nil))

(declaim (ftype (function (vector vector) (values boolean &optional))
                ==-vector-dispatch))
(defun ==-vector-dispatch (a b)
  "Select the most specialized ==-VECTOR function that can be applied to both A and B, and call it."
  (declare (notinline ==-simple-base-string
                      ==-base-string
                      ==-string
                      ==-vector
                      ==-simple-bit-vector
                      ==-bit-vector
                      ==-simple-vector
                      ==-vector))
  (macrolet ((match-hierarchies (&rest hierarchies)
               (labels ((make-inner-branch (type ==-function)
                          `(,type (,==-function a b)))

                        (make-inner-dispatch (hierarchy)
                          `(etypecase b
                             ,@(iter (for entry in hierarchy)
                                 (when (eq entry :parents)
                                   (next-iteration))
                                 (for (type ==-function) = entry)
                                 (collect (make-inner-branch type ==-function)))))

                        (transform-hierarchy-to-outer-branch (hierarchy)
                          (iter (for (entry . remaining) on hierarchy)
                            (until (eq entry :parents))
                            (for type = (first entry))
                            (collect `(,type ,(make-inner-dispatch (cons entry remaining)))))))
                 `(etypecase a
                    ,@(iter (for hierarchy in hierarchies)
                        (appending (transform-hierarchy-to-outer-branch hierarchy)))))))
    (match-hierarchies
     ((simple-base-string ==-simple-base-string)
      (base-string ==-base-string)
      :parents
      (string ==-string)
      (vector ==-vector))

     ((simple-string ==-simple-string)
      (string ==-string)
      :parents
      (vector ==-vector))

     ((simple-bit-vector ==-simple-bit-vector)
      (bit-vector ==-bit-vector)
      :parents
      (vector ==-vector))

     ((simple-vector ==-simple-vector)
      (vector ==-vector)))))

(declaim (ftype (function (fx-hasher array &optional (function (fx-hasher t) (values &optional)))
                          (values &optional))
                hash-array)
         ;; Inlining may allow specialization on the array's element-type and rank, and inlining the
         ;; HASH-ELEMENT function.
         (inline hash-array))
(defun hash-array (hasher array &optional (hash-element #'hash-dispatch)
                   &aux (size (array-total-size array)))
  ;; Note: We're assuming ARRAY-RANK is always an unsigned fixnum. Has anyone ever constructed an array with a
  ;;       non-fixnum rank? Does any CL impl even support that? God only knows.
  (add-to-hasher hasher (array-rank array))
  (labels ((repeat (index)
             (if (>= index size)
                 (values)
                 (progn
                   (funcall hash-element hasher (row-major-aref array index))
                   (repeat (1+ index))))))
    (repeat 0)))

(declaim (ftype (function (array array) (values boolean &optional))
                ==-array-dimensions)
         ;; Inlining may allow specialization on the array's rank.
         (inline ==-array-dimensions))
(defun ==-array-dimensions (a b)
  (and (==-fixnum (array-rank a) (array-rank b))
       (iter (declare (declare-variables))
         (for (the (or (eql -1) array-rank) axis) below (array-rank a))
         (unless (==-fixnum (array-dimension a axis) (array-dimension b axis))
           (return nil))
         (finally (return t)))))

(declaim (ftype (function (array array &optional (function (t t) (values boolean &optional)))
                          (values boolean &optional))
                ==-array)
         ;; Inlining may allow specialization on the array's element-type and rank, and inlining the
         ;; ==-ELEMENT function.
         (inline ==-array))
(defun ==-array (a b &optional (==-element #'==))
  (and (==-array-dimensions a b)
       (iter (declare (declare-variables))
         (for (the (or (eql -1) array-index) idx) below (array-total-size a))
         (unless (funcall ==-element
                          (row-major-aref a idx)
                          (row-major-aref b idx))
           (return nil))
         (finally (return t)))))

;;; hashing conses, symbols and lists

(declaim (ftype (function (fx-hasher cons)
                          (values &optional))
                hash-cons))
(defun hash-cons (hasher cons)
  (hash-dispatch hasher (car cons))
  (hash-dispatch hasher (cdr cons)))

(declaim (ftype (function (cons cons) (values boolean &optional))
                ==-cons))
(defun ==-cons (a b)
  (and (== (car a) (car b))
       (== (cdr a) (cdr b))))

(declaim (ftype (function (fx-hasher symbol)
                          (values &optional))
                hash-symbol))
;; TODO: mix the SYMBOL's `symbol-package' to prevent conflicts between symbols with the same name. (SBCL
;;       hashes symbols by name, and I think memoizes.)
(defun hash-symbol (hasher symbol)
  (add-to-hasher hasher (sxhash symbol)))

(declaim (ftype (function (symbol symbol)
                          (values boolean &optional))
                ==-symbol)
         ;; So trivial as to be always inlined.
         (inline ==-symbol))
(defun ==-symbol (a b)
  (eq a b))

(declaim (ftype (function (fx-hasher list)
                          (values &optional))
                hash-list))
(defun hash-list (hasher list)
  (if (consp list)
      (hash-cons hasher list)
      (hash-symbol hasher list)))

(declaim (ftype (function (list list) (values boolean &optional))
                ==-list))
(defun ==-list (a b)
  (typecase-both (a b) nil
    (cons (==-cons a b))
    (null t)))

;; TODO: Profiling to determine if having separate `hash-dispatch' for `etypecase' dispatch and `hash-object' for CLOS
;;       dispatch is more efficient than just using CLOS dispatch always.

(defgeneric hash-object (hasher obj)
  (:documentation "Feed OBJ into HASHER.

HASHER will be an instance of `fx-hasher'. The primite operation on an `fx-hasher' is `add-to-hasher', which
accepts an `fx-hasher' and a `word', and returns no values. The following functions are also provided to hash
objects of built-in CL types:
- Arbitrary objects:
  - `hash-dispatch', which determines an appropriate specialized hasher function to call, or defers to this
                     generic function.
- Integers:
  - `hash-fixnum'.
  - `hash-bignum', which accepts an optional third argument which is the maximum number of bits in the
                   integer. Supplying a constant for this argument may lead to more efficient hashing.
                   It is valid to supply any `integer' to `hash-bignum', including a `fixnum'.
- Floats:
  - `hash-single-float'.
  - `hash-double-float'.
  - `hash-short-float', which defers to `hash-single-float' on platforms without a distinct `short-float'
    type.
  - `hash-long-float', which defers to `hash-double-float' on platforms without a distinct `long-float' type.
  - `hash-float', which dispatches on the float's type and calls one of the specialized functions listed
                  above.
- Other numbers:
  - `hash-ratio'.
  - `hash-complex', which accepts as an optional third argument one of these functions to hash its
                    parts. The default is `hash-dispatch'.
- Characters:
  - `hash-character'.
- Arrays, vectors and strings:
  - `hash-simple-bit-vector'.
  - `hash-bit-vector'.
  - `hash-simple-base-string'.
  - `hash-base-string'.
  - `hash-simple-string'.
  - `hash-string'.
  - `hash-simple-vector'.
  - `hash-vector', which accepts as an optional third argument one of these functions to hash its
                   elements. The default is `hash-dispatch'.
  - `hash-array', which accepts an optional third argument like `hash-vector' to hash its elements. If applied
                  to a vector with a fill pointer, `hash-array' will ignore the fill pointer and hash all
                  elements of the array. `hash-array' also mixes the array's rank into its hash, to avoid
                  collisions between arrays of different ranks with the same elements in row-major order.
- Conses and lists:
  - `hash-cons'.
  - `hash-list'.
- Symbols:
  - `hash-symbol'.

Many of these specialized hashers are declared globally `inline' because they may be able to be specialized,
e.g. on array simple-ness, element-type, or the passed function used to hash elements. Callers for whom none
of these attributes is constant should declare the function locally `notinline'.

Methods should specialize on OBJ, and feed sub-objects of OBJ into HASHER using one of the above functions."))

#+closer-mop
(progn
  (declaim (ftype (function (list) (values list &optional))
                  sort-instance-slots-by-location))
  (defun sort-instance-slots-by-location (all-slots)
    (sort (the list (delete-if (lambda (slot)
                                 (not (eq :instance (closer-mop:slot-definition-allocation slot))))
                               (copy-seq all-slots)))
          #'<
          :key #'closer-mop:slot-definition-location))
  
  (declaim (ftype (function (fx-hasher (or standard-object condition))
                            (values &optional))
                  hash-all-slots))
  (defun hash-all-slots (hasher object &aux (class (class-of object)))
    (iter (declare (declare-variables))
      (for slot in (sort-instance-slots-by-location (closer-mop:class-slots class)))
      (when (closer-mop:slot-boundp-using-class class object slot)
        (hash-dispatch hasher (closer-mop:slot-value-using-class class object slot))))
    (values))

  (defmethod hash-object (hasher (object standard-object))
    (hash-all-slots hasher object))

  (defmethod hash-object (hasher (object condition))
    (hash-all-slots hasher object)))

;; TODO: MOP default method for `hash-object' on `standard-object', `condition'.

(defgeneric ==-object (a b)
  (:documentation "Compare A and B for equality.

The equality defined here must be consistent with the hashing method defined on `hash-object', if any.

Methods must return a `boolean', i.e. either T or nil, not a generalized boolean.

For the most efficiency, methods should recurse into sub-objects using the most specific possible of the
following equality functions:

- Arbitrary objects:
  - `==', which determines an appropriate specialized equality function to call, or defers to this generic
    function.
- Integers:
  - `==-fixnum'.
  - `==-bignum', which actually accepts all `integer's, not only bignums.
- Floats:
  - `==-single-float'.
  - `==-short-float', which defers to `==-single-float' on platforms without a distinct `short-float' type.
  - `==-double-float'.
  - `==-long-float', which defers to `==-long-float' on platforms without a distinct `long-float' type.
  - `==-float', which dispatches on the arguments' types and calls one of the specialized functions listed
                above. Floats of different types with the same numeric value are treated as non-equal.
- Other numbers:
  - `==-ratio'.
  - `==-complex', which accepts as an optional third argument one of these functions to compare its
                  parts. The default is `=='.
- Characters:
  - `==-character'.
- Arrays, vectors and strings:
  - `==-simple-bit-vector'.
  - `==-bit-vector'.
  - `==-simple-base-string'.
  - `==-base-string'.
  - `==-simple-string'.
  - `==-string'.
  - `==-simple-vector'.
  - `==-vector', which accepts as an optional third argument one of these functions to compare the
                 elements of the two vectors. The default is `=='.
  - `==-array', which accepts as an optional third argument one of these functions to compare the
                elements of the two arrays. The default is `=='.
- Conses and lists:
  - `==-cons'.
  - `==-list'.
- Symbols:
  - `==-symbol'."))

(defmethod ==-object (a b)
  "Default method: return nil if equality comparison is impossible."
  (declare (ignorable a b))
  nil)

#+closer-mop
(progn
  (declaim (ftype (function ((or standard-object condition)
                             (or standard-object condition))
                            (values boolean &optional))
                  ==-all-slots))
  (defun ==-all-slots (a b &aux (class (class-of a)))
    (when (eq class (class-of b))
      (let* ((class (class-of a)))
        (labels ((slot-boundp* (slot instance)
                   (closer-mop:slot-boundp-using-class class instance slot))
                 (slot-value* (slot instance)
                   (closer-mop:slot-value-using-class class instance slot))
                 (slot-== (slot)
                   (if (slot-boundp* slot a)
                       (and (slot-boundp* slot b)
                            (== (slot-value* slot a)
                                (slot-value* slot b)))
                       (not (slot-boundp* slot b)))))
          (iter (declare (declare-variables))
            (for slot in (closer-mop:class-slots class))
            (unless (slot-== slot)
              (return nil))
            (finally (return t)))))))
  
  (defmethod ==-object ((a standard-object) (b standard-object))
    "Do A and B have the same class, the same set of bound slots, and `==' values for those slots?

This method uses the metaobject protocol to traverse the slots of A and B, and is therefore probably
catastrophically inefficient. Users are encouraged to define more specialized methods."
    (==-all-slots a b))

  (defmethod ==-object ((a condition) (b condition))
    "Do A and B have the same class, the same set of bound slots, and `==' values for those slots?

This method uses the metaobject protocol to traverse the slots of A and B, and is therefore probably
catastrophically inefficient. Users are encouraged to define more specialized methods."
    (==-all-slots a b)))

;; TODO: MOP default method for `==-object' on `standard-object', `condition'.

;; Save inlining information, because callers with type information may want to locally inline `hash-dispatch'
;; in order to optimize away some type checks.
(declaim (inline hash-dispatch))
(defun hash-dispatch (hasher thing)
  ;; No point in inlining any function called here, because we don't have any extra information to specialize on.
  (declare (notinline hash-bignum
                      hash-complex
                      hash-base-string
                      hash-simple-string
                      hash-string
                      hash-bit-vector
                      hash-vector
                      hash-array))
  (etypecase thing
    ;; TODO: Determine whether SBCL compiles this to a jump table, and if not, sort these branches to catch
    ;;       more-common types earlier.
       
    ;;; numbers
    ;; integers
    (fixnum (hash-fixnum hasher thing))
    (bignum (hash-bignum hasher thing))
    ;; floats
    #+distinct-short-float
    (short-float (hash-short-float hasher thing))
    (single-float (hash-single-float hasher thing))
    (double-float (hash-double-float hasher thing))
    #+distinct-long-float
    (long-float (hash-long-float hasher thing))
    ;; "weird" numbers
    (ratio (hash-ratio hasher thing))
    (complex (hash-complex hasher thing))

    ;;; lists and symbols
    (cons (hash-cons hasher thing))
    (symbol (hash-symbol hasher thing))

    ;;; characters
    (character (hash-character hasher thing))

    ;;; vectors
    ;; TODO: Consider breaking this into a case for `vector' and a sub-match. Does that improve codegen?
    ;; strings
    (simple-base-string (hash-simple-base-string hasher thing))
    (base-string (hash-base-string hasher thing))
    (simple-string (hash-simple-string hasher thing))
    (string (hash-string hasher thing))

    ;; bit-vectors
    (simple-bit-vector (hash-simple-bit-vector hasher thing))
    (bit-vector (hash-bit-vector hasher thing))

    ;; unspecialized vectors
    (simple-vector (hash-simple-vector hasher thing))
    (vector (hash-vector hasher thing))

    ;;; arrays
    (array (hash-array hasher thing))

    ;;; fallback to CLOS dispatch
    (t (hash-object hasher thing))))
(declaim (notinline hash-dispatch))

(declaim (ftype (function (t) (values fixnum &optional))
                hash)
         ;; save inlining information so that IMMUTABLE/DICT can wrap this in a function that truncates the
         ;; hash to a fixnum without boxing a full-length hash.
         (inline hash))
(defun hash (thing)
  (truncate-hash
   (with-hasher (hasher)
     (hash-dispatch hasher thing))))
(declaim (notinline hash))

(declaim (ftype (function (t t) (values boolean &optional))
                ==)
         ;; save inlining information so callers with type information can declare this inline.
         (inline ==))
(defun == (a b)
  (declare (notinline ==-bignum
                      ==-complex
                      ==-base-string
                      ==-simple-string
                      ==-string
                      ==-bit-vector
                      ==-vector
                      ==-array))
  (or (eq a b)
      (typecase-both (a b) (==-object a b)
        (fixnum (==-fixnum a b))
        (bignum (==-bignum a b))

        #+distinct-short-float
        (short-float (==-short-float a b))
        (single-float (==-single-float a b))
        (double-float (==-double-float a b))
        #+distinct-long-float
        (long-float (==-long-float a b))

        (ratio (==-ratio a b))
        (complex (==-complex a b))

        (cons (==-cons a b))
        (symbol (==-symbol a b))

        (character (==-character a b))

        (vector (==-vector-dispatch a b))

        (array (==-array a b)))))
(declaim (notinline ==))
