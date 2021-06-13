;;; contract.el --- Racket-style higher-order contracts for Emacs Lisp -*- lexical-binding: t -*-

;; Copyright © 2021 Langston Barrett <langston.barrett@gmail.com>

;; Author: Langston Barrett <langston.barrett@gmail.com>
;; URL: https://github.com/langston-barrett/contract.el
;; Keywords: lisp, debugging
;; Version: 0.1
;; Package-Requires: ((emacs "27.1"))

;; This file is NOT part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:
;;
;; This library provides facilities for programming Emacs Lisp in the "design by
;; contract" style.  It's implementation and interface are heavily inspired by
;; Racket's contracts.

;; Why:
;;
;; Have you ever seen an error like this pop into your `*Messages*' buffer?
;;
;;     Wrong number of arguments: ((t) nil nil), 1
;;
;; When something like this happens, it's not immediately clear what's wrong. Is
;; it a bug in your Emacs configuration? A third-party package? You might toggle
;; `debug-on-error', try to reproduce the problem, and figure out which package
;; or snippet of configuration is at fault. This can get frustrating fast, and
;; is even more complex in code involving higher-order functions. With
;; contract.el, you can get this message instead:
;;
;;     Wrong function arity. Expected arity at least: 1
;;     Function: <function value>
;;     Blaming: caller of mapcar (assuming the contract is correct)
;;     In:
;;       (contract-> contract-any-c contract-any-c)
;;       in the 0th argument of
;;       (contract-> (contract-> contract-any-c contract-any-c) contract-sequence-c contract-sequence-c)
;;     Call stack:
;;       some-function
;;       another-function
;;
;; This message makes it easier to see
;;
;; 1. What went wrong: `mapcar' expects a function of arity at least 1 as its
;;    first argument.
;;
;; 2. Who is to blame: in this example, it's the caller of `mapcar', namely
;;    `some-function', which passed an invalid argument.
;;
;; For Package Authors:
;;
;; For Emacs Lisp package authors, contracts provide
;;
;; * Detailed, helpful error messages for users interacting with your package
;;
;; * Testable documentation for your API
;;
;; * An escape from the tedium of "defensive programming" - let this package
;;   handle checking inputs and constructing great error messages
;;
;; For Emacs Users:
;;
;; Contracts help you debug errors in your configuration faster!

;; Examples:
;;
;; Here are a few examples of possible contracts for functions in the `seq'
;; library.
;;
;; First, a simple function contract: `seq-first' expects a sequence, and
;; returns its first element. Since `seq-first' works on any sequence, no
;; assertion is made about the return value.
;;
;;     (contract-> contract-sequence-c contract-any-c)
;;
;; Now, let's develop a more complicated contract for `seq-elt' step-by-step.
;; This function takes a sequence and an index in that sequence, and returns the
;; element at that index. This contract just checks that the sequence and index
;; have the right types:
;;
;;     (contract-> contract-sequence-c contract-nat-number-c contract-any-c)
;;
;; This is a good first approximation, but it could be much more specific. The
;; second argument not only has to be a natural number, but has to be in range
;; (less than the length of the sequence). This constraint can be expressed with
;; a dependent function contract, which allows the contracts for the arguments
;; and the contract for the return value to depend on the runtime values of the
;; arguments.
;;
;;     (contract->d
;;      (seq contract-sequence-c)
;;      (n (contract-and-c
;;          contract-nat-number-c
;;          (contract-lt-c (seq-length seq))))
;;      contract-any-c)
;;
;; Note how the sequence argument `seq' was used in the contract for the index
;; `n'. This is a fairly good contract, but it could actually be even more
;; specific! A sequence can't contain itself, so we can assert that the returned
;; value is not equal to the first argument:
;;
;;     (contract->d
;;      (seq contract-sequence-c)
;;      (n (contract-and-c
;;          contract-nat-number-c
;;          (contract-lt-c (seq-length seq))))
;;      (contract-not-c
;;       (contract-eq-c seq)))
;;
;; And we could go on, providing more and more guarantees, documentation, and
;; helpful error messages.

;; Usage:
;;
;; The easiest way to get started is with the `contract-defun' macro, which
;; works like `defun' except it also takes a `:contract' argument:
;;
;;    (contract-defun message-id (x)
;;      :contract (contract-> contract-any-c contract-any-c)
;;      "Print the value X to the messages buffer, and return it."  ; docstring
;;      (message "%s" x)  ; body
;;      x)  ; more body
;;
;; With the above definition, the contract will get checked whenever `mesage-id'
;; is called.
;;
;; Basic Contracts:
;;
;; This package provides a number of basic contracts for simple conditions on
;; values:
;;
;; * `contract-nil-c': Checks that a value is `eq' to nil.
;; * `contract-any-c': Doesn't check anything.
;; * `contract-function-c': Checks that a value is `functionp'.
;; * `contract-nat-number-c': Checks that a value is `natnump'.
;; * and many others...
;;
;; Some are functions that create contracts based some input values:
;;
;; * `contract-eq-c': Checks that a value is `eq' to a given value.
;; * `contract-equal-c': Checks that a value is `equal' to a given value.
;; * `contract-lt-c': Checks that a value is less than a given value.
;; * `contract-substring-c': Checks that a value is a substring to a given string.
;; * and many others...
;;
;; Contract Combinators:
;;
;; In addition to the basic contracts, there are a number of "combinators" that
;; can be used to construct more complex contracts out of simpler ones. The most
;; important are:
;;
;; * `contract-not-c': For negating contracts
;; * `contract-and-c'
;; * `contract-or-c'
;; * `contract->': For describing functions
;; * `contract->d': For very precise, thorough description of functions
;;
;; Discovering New Contracts and Combinators:
;;
;; To find new contract combinators, you can use `apropos-function':
;;
;;    (apropos-function "^contract-.+-c$")
;;
;; To use the above snippet, either copy-paste it into your scratch buffer and
;; call M-x `eval-buffer', or call M-x `apropos-function' and type in the
;; pattern. This only works after you've installed this library.

;; Performance:
;;
;; Contracts can be disabled by setting `contract-enable' to nil.
;;
;; "Slow" contracts (those that are self-reported to take more than
;; constant-time) can be disabled by setting `contract-enable-slow' to nil.
;;
;; Contracts are be written in the "late negative blame" style by default, which
;; can improve performance if contracts are mostly attached to "exported"
;; bindings while avoided on "internal" bindings (see Racket's documentation for
;; more on this).
;;
;; Contracts are also very *lazy*: Very little is computed before explicitly
;; needed (e.g. error messages, contract names, etc.). Once computed, attributes
;; of contracts are cached so they don't need to be recomputed if requested
;; again.

;; Development:
;;
;; PRs and issues welcome! Develop using Cask. Here are a few Makefile targets:
;;
;;     make .cask/
;;     make build
;;     make test
;;
;; Tests are provided using doctest, buttercup, and propcheck.
;;
;; Wishlist:
;;
;; The following is a "wishlist" of features from the Racket contract system
;; that are not (yet?) implemented here:
;;
;; * Generating random data that satisfy a given contract.
;; * Contracts for vectors and other primitive types.
;; * The stronger-than partial ordering on contracts.
;; * "Collapsible" contracts.
;; * "Temporal" contracts.
;;
;; Implementation Notes:
;;
;; In Racket, contracts are implemented as "chaperones" to functions.  This
;; package only supports contracts on functions, and uses "advice" to emulate
;; chaperones in Emacs.  See also "Bibliography" below.

;; Bibliography:
;;
;; These documents heavily influenced the design and implementation of this
;; library.  These would be helpful for users of this library to read, they
;; provide usage examples of Racket's contract system, which has a very similar
;; API.
;;
;; * The Racket Guide
;; * The Racket Reference Manual
;;
;; The following papers provide more theoretical background, and might be
;; helpful to read if you're interested in how this library works under the
;; hood, or want to contribute.
;;
;; * "Correct Blame for Contracts: No More Scapegoating" by Christos Dimoulas,
;;   Robert Bruce Findler, Cormac Flanagan, and Matthias Felleisen: This paper
;;   influenced the implementation of the `contract->d' macro.

;; TODO:
;;
;; These items should be resolved before merge:
;;
;; - Never access slots via oref or oset, always use :reader and :writer
;; - Superclass for "combinators" that uses are-*

;;; Code:

;;;; Imports

(eval-when-compile (require 'cl-lib))
(require 'cl-extra)
(require 'eieio)
(require 'subr-x)

;;;; Variables

(defvar
  contract-enable
  t
  "If nil, then contracts will not be enforced.")

(defvar
  contract-enable-slow
  t
  "If nil, then slow (non-constant-time) contracts will not be enforced.")

;; TODO: Unused
(defvar
  contract-warn-only
  t
  "If nil, then contract violations will emit warnings instead of calling `signal'.")

(defvar
  contract-violations
  '()
  "A log of all contract violations.

Currently spuriously records 'violations' of negated contracts, and contracts
that fail but are part of a disjunction (TODO).")

;;;; Utilities

(eval-when-compile
  (defmacro contract--any (binding &rest forms)
    `(cl-loop
      for ,(car binding) in ,(cadr binding)
      if ,(if (equal 1 (length forms))
              (car forms)
            `(progn ,@forms))
      return t
      finally return nil))

  (defmacro contract--all (binding &rest forms)
    `(cl-loop
      for ,(car binding) in ,(cadr binding)
      if (not ,(if (equal 1 (length forms))
                   (car forms)
                 `(progn ,@forms)))
      return nil
      finally return t))

  (defun contract--or (lst) (contract--any (elem lst) elem))
  (defun contract--and (lst) (contract--all (elem lst) elem)))

;;;;; Bootstrapping


(eval-when-compile
  (defsubst contract--assert (condition message)
    "Assert CONDITION, printing MESSAGE if it fails.

Used for bootstrapping (since we don't yet have contracts!)."
    (unless condition
      (error "%s" message)))

  (defsubst contract--precond (condition func message)
    "Assert CONDITION as a precondition for FUNC, printing MESSAGE if it fails.

Used for bootstrapping (since we don't yet have contracts!)."
    (contract--assert condition (concat "Precondition of " func " violated: " message)))

  ;; TODO: Delete in favor of bootstrap-def*
  (defsubst contract--precond-expect-string (func str)
    "Assert that STR is a string as a precondition of FUNC."
    (contract--precond (stringp str) func "Expected a string."))

  ;; TODO: Delete in favor of bootstrap-def*
  (defsubst contract--precond-expect-function (func function)
    "Assert that FUNCTION is a function as a precondition of FUNC."
    (contract--precond (functionp function) func "Expected a function."))

  (defun contract--zip (lst1 lst2)
    (unless (equal (length lst1) (length lst2))
      (error "`contract--zip' expected lists of the same length"))
    ;; TODO Could be more efficient, this is O(n^2)
    (cl-loop
     for n from 0 to (1- (length lst1))
     collect (cons (nth n lst1) (nth n lst2))))

  ;; TODO: Handle &rest and &optional args
  (defun contract--bootstrap-def
      (def-what name args type body)
    "Create a form that checks types at runtime using `cl-check-type'.

See Info node `(cl)Type Predicates'."
    (unless (symbolp def-what)
      (error "Expected symbol as 0th argument to `contract--bootstrap-def'"))
    (unless (symbolp name)
      (error "Expected symbol as 1st argument to `contract--bootstrap-def'"))
    (unless (sequencep args)
      (error "Expected sequence as 2nd argument to `contract--bootstrap-def'"))
    (unless (sequencep type)
      (error "Expected sequence as 3nd argument to `contract--bootstrap-def'"))
    (unless (sequencep body)
      (error "Expected sequence as 4th argument to `contract--bootstrap-def'"))
    (unless (equal (+ 2 (length args)) (length type))
      (error (string-join
              (list
               "Bad arity in types specifier for"
               (symbol-name name)
               "found"
               (format "%s" (length args))
               "arguments but type specifier had length"
               (format "%s" (length type)))
              " ")))
    (unless (equal '-> (car type))
      (error (concat
              "Expected `->' as the first entry in type specifier for "
              (symbol-name name))))
    `(,def-what ,name ,args
       ;; Check arguments
       ,@(mapcar
          (lambda (pair)
            (if (or
                 (equal (car pair) '&optional)
                 (equal (car pair) '&rest))
                nil
              `(cl-check-type
                ,(car pair)
                ,(cdr pair)
                ,(string-join
                  (list
                   "Expected type"
                   (format "%s" (cdr pair))
                   "for an argument to"
                   (concat "`" (symbol-name name) "'"))
                  " "))))
          (contract--zip args (cdr (butlast type))))
       ;; Check return value
       (let ((ret (progn ,@body)))
         (cl-check-type
          ret
          ,(car (last type))
          ,(string-join
            (list
             "Expected type"
             (format "%s" (car (last type)))
             "for the return value of"
             (concat "`" (symbol-name name) "'"))
            " "))
         ret)))

  (defmacro contract--bootstrap-defun (name args type &rest body)
    "Create a `defun' form that checks types at runtime using `cl-check-type'.

See Info node `(cl)Type Predicates'."
    (contract--bootstrap-def 'defun name args type body))

  (defmacro contract--bootstrap-defmacro (name args type &rest body)
    "Create a `defmacro' form that checks types using `cl-check-type'.

See Info node `(cl)Type Predicates'."
    (contract--bootstrap-def 'defmacro name args type body))

  (defmacro contract--bootstrap-defsubst (name args type &rest body)
    "Create a `defsubst' form that checks types at runtime using `cl-check-type'.

See Info node `(cl)Type Predicates'.."
    (contract--bootstrap-def 'defsubst name args type body))

  (contract--bootstrap-defsubst
   contract--list-of
   (pred lst)
   (-> symbol list boolean)
   "Check that LST is a list and each element satisfies PRED."
   (and (listp lst) (contract--all (elem lst) (funcall pred elem)))))

(contract--bootstrap-defsubst
 contract--non-empty-string-p
 (obj)
 (-> t boolean)
 "Check that OBJ is a non-empty string (`stringp')."
 (and (stringp obj) (< 0 (length obj))))

;;;;; Other

(defsubst contract--ignore (_arg)
  "Ignore an unused variable warning, usually involving macros."
  nil)

(contract--bootstrap-defun
 contract--arity-at-least
 (func arity)
 (-> function natnum boolean)
 "Check if FUNC has arity of at least ARITY.

>> (contract--arity-at-least #'natnump 1)
=> t
>> (contract--arity-at-least #'natnump 2)
=> nil
>> (contract--arity-at-least #'contract--arity-at-least 2)
=> t"
 (let ((max-arity (cdr (func-arity func))))
   (pcase max-arity
     (`'many t)
     ((pred natnump) (>= max-arity arity))
     (_ nil))))

(contract--bootstrap-defsubst
 contract--sexp-str
 (&rest strs)
 (-> &rest list string)
 "Create an s-expression from STRS."
 (concat "(" (mapconcat 'identity strs " ") ")"))

(eval-when-compile
  (contract--bootstrap-defsubst
   contract--trunc
   (len str)
   (-> natnum string string)
   "Truncate STR to LEN characters."
   (if (> (length str) len)
       (concat (substring str 0 (- len 3)) "...")
     str))

  (contract--bootstrap-defsubst
   contract--trunc-format
   (len value)
   (-> natnum t string)
   "Print VALUE using `format' and truncate the string to LEN characters."
   (contract--trunc len (format "%s" value))))

;;;; Blame

(cl-defstruct
    (contract-blame
     (:constructor contract-make-blame))
  "Blame objects satisfy invariants specified in `contract-valid-blame-p'.

See https://docs.racket-lang.org/reference/Building_New_Contract_Combinators.html#%28tech._blame._object%29."

  (context
   '()
   :read-only t
   :type list                           ; of strings
   :documentation "A list of strings used in error messages")
  (positive-party
   "*unknown*"
   :read-only t
   :type string
   :documentation "The positive party/value producer/server")
  (negative-party
   "*unknown*"
   :type string
   :documentation "The negative party/value consumer/client"))

;; TODO: Error messages!
(contract--bootstrap-defun
 contract-valid-blame-p
 (blame)
 (-> contract-blame boolean)
 "Check that BLAME satisfies the invariants of blame objects.

The invariants are: (TODO)"
 (and
  (contract--list-of
   #'contract--non-empty-string-p
   (contract-blame-context blame))
  (contract--non-empty-string-p (contract-blame-positive-party blame))
  (contract--non-empty-string-p (contract-blame-negative-party blame))))

;; TODO: Delete in favor of bootstrap-def*
(defsubst contract--precond-expect-blame (func blame)
  "Assert that BLAME is a blame object as a precondition of FUNC."
  (contract--precond (contract-blame-p blame) func "Expected a blame object."))

(contract--bootstrap-defsubst
 contract--blame-add-context
 (blame context)
 (-> contract-valid-blame contract--non-empty-string contract-valid-blame)
 "Add CONTEXT to the context of BLAME."
 (contract-make-blame
  :context
  (cons context (contract-blame-context blame))
  :positive-party (contract-blame-positive-party blame)
  :negative-party (contract-blame-negative-party blame)))

(contract--bootstrap-defsubst
 contract--blame-swap-add-context
 (blame context)
 (-> contract-valid-blame contract--non-empty-string contract-valid-blame)
 "Swap the positive and negative party in this BLAME, and add CONTEXT."
 (contract-make-blame
  :context
  (cons context (contract-blame-context blame))
  :positive-party (contract-blame-negative-party blame)
  :negative-party (contract-blame-positive-party blame)))

(contract--bootstrap-defsubst
 contract--blame-set-positive-party
 (blame positive)
 (-> contract-valid-blame contract--non-empty-string contract-valid-blame)
 "Create a new blame like BLAME except with positive party POSITIVE."
 (contract-make-blame
  :context (contract-blame-context blame)
  :positive-party positive
  :negative-party (contract-blame-negative-party blame)))

(contract--bootstrap-defsubst
 contract--add-negative-party
 (blame str)
 (-> contract-blame contract--non-empty-string contract--non-empty-string)
 "Add a negative party STR to this BLAME.

Returns STR."
 (setf (contract-blame-negative-party blame) str))

;;;; Violations

;; https://emacs.stackexchange.com/questions/7396/how-can-i-determine-which-function-was-called-interactively-in-the-stack/7405#7405
(contract--bootstrap-defsubst
 contract--call-stack
 ()
 (-> list)                              ; TODO: list of what
 "Return the current call stack frames."
 (let ((frames)
       (frame)
       (index 5))
   (while (setq frame (backtrace-frame index))
     (push frame frames)
     (setq index (+ 1 index)))
   (cl-loop
    for frame in frames
    if (car frame)
    collect frame)))

(contract--bootstrap-defsubst
 contract--function-stack
 ()
 (-> list)
 "Like call-stack but is a list of only the function names."
 (butlast (mapcar 'cl-second (contract--call-stack))))

(cl-defstruct
    (contract-violation
     (:constructor contract--make-violation))
  "A structured representation of a contract violation.

Conforms to the invariants specified in `contract-valid-violation-p'."
  (blame
   nil
   :read-only t
   :documentation "The blame object for this contract violation")
  (contract
   nil
   :read-only t
   :documentation "The contract that has been violated")
  (callstack
   nil
   :read-only t
   :documentation "The callstack in which the violation occurred")
  (format
   nil
   :read-only t
   :documentation "Format string for the error message"))

;; TODO: Error messages!
(contract--bootstrap-defun
 contract-valid-violation-p
 (violation)
 (-> contract-violation boolean)
 "Check that VIOLATION satisfies the invariants of violation objects.

The invariants are: (TODO)"
 (and
  (contract-valid-blame-p (contract-violation-blame violation))
  ;; TODO: Contract validity
  ;; (contract-valid-metadata-p (contract-violation-metadata violation))
  ;; TODO: List of what?
  (listp (contract-violation-callstack violation))
  ;; TODO: Predicate for format strings with one placeholder.
  (or
   (contract--non-empty-string-p (contract-violation-format violation))
   (contract--non-empty-string-p
    (contract--format
     (contract-violation-contract violation))))))

(eval-when-compile
  ;; TODO: Delete in favor of bootstrap-def*
  (defsubst contract--precond-expect-violation (func violation)
    "Assert that VIOLATION is a violation object as a precondition of FUNC."
    (contract--precond
     (contract-violation-p violation)
     func
     "Expected a violation object.")))

(contract--bootstrap-defun
 contract--format-violation
 (violation value)
 (-> contract-valid-violation t string)
 "Format an error message representing VIOLATION with value VALUE."
 (let ((blame (contract-violation-blame violation)))
   (concat
    (format
     "%s\nBlaming: %s (assuming the contract is correct)\nIn:%s\nCall stack:\n  %s"
     (format
      (let ((fmt (contract-violation-format violation)))
        (if fmt
            fmt
          (contract--format (contract-violation-contract violation))))
      (contract--trunc-format
       60
       (if (functionp value) "<function value>" value)))
     (contract-blame-positive-party blame)
     (let ((sep "\n  "))
       ;; Avoid redundant white space.
       (if (equal 0 (length (contract-blame-context blame)))
           ""
         (concat sep (string-join (contract-blame-context blame) sep))))
     (string-join
      (mapcar
       (lambda (f)
         (cond
          ((subrp f) (subr-name f))
          ((symbolp f) (symbol-name f))
          (t "*unknown*")))
       (contract-violation-callstack violation))
      "\n  ")))))

(define-error 'contract-violation "Contract violation")

(contract--bootstrap-defun
 contract-raise-violation
 (violation value)
 (-> contract-valid-violation t t)
 "Signal a VIOLATION with value VALUE."
 (push (cons violation value) contract-violations)
 (signal 'contract-violation (contract--format-violation violation value)))

;;;; Contracts
;;;;; AST

(cl-defstruct
    (contract-ast
     (:constructor contract--make-ast))
  "The AST of a contract."
  (constructor
   nil
   :read-only t
   :type symbol
   :documentation "Constructor.")
  (arguments
   nil
   :read-only t
   :type list
   :documentation "List of arguments to this constructor."))

;;;;; Contracts

;; TODO: Smart constructor that checks that if is-first-order is nil, so is
;; first-order.
(defclass contract-contract ()
  ((ast
    :initarg :ast
    :type contract-ast
    :documentation "The AST of this contract.")
   (name
    :initarg :name
    :type string
    :documentation "Name of this contract, as derived from its AST.")
   (format
    :initarg :format
    :documentation "A format string for constructing the error message")
   (is-constant-time
    :initarg :is-constant-time
    :type boolean
    :documentation "If this is t, then this contract is considered constant-time, and is enabled even when `contract-enable-slow' is nil.")
   (is-first-order
    :initarg :is-first-order
    :type boolean
    :documentation "Indicates whether this is a first-order contract, see also `first-order'.")
   (first-order
    :initarg :first-order
    :initform (lambda (_) t)
    :type function
    :documentation "If this returns nil, then the overall contract is guaranteed to raise an error. If it returns a non-nil value, then no guarantees are made about the overall result, unless `contract-is-first-order' is non-nil, in which case the non-nil value is (must be!) the result of the overall contract.")
   (proj
    :initarg :proj
    :type function
    :documentation "Late-negative projection function. From the Racket guide: \"Specifically, a late neg projection accepts a blame object without the negative blame information and then returns a function that accepts both the value to be contracted and the name of the negative party, in that order. The returned function then in turn returns the value with the contract.\""))
  "`contract-contract' is a class so that its methods have (mutable) access to
its data - many of its properties are lazily calculated from its AST and then
cached.

TODO: When should something subclass this vs. be a function that makes one of
these? And same question further down the line?

Answer: Probably everything should be subclasses, using constructors can make it
\"impossible\" to construct ill-formed structs/structs with necessary values
unset.
"
  :abstract t)

;; TODO
;; (contract--bootstrap-defun
;;  contract-valid-metadata-p
;;  (metadata)
;;  (-> contract-metadata boolean)
;;  "Check that METADATA satisfies the invariants of metadata objects.

;; The invariants are: (TODO)"
;;  (and
;;   (let ((name (contract-metadata-name metadata)))
;;     (or (not name) (contract--non-empty-string-p name)))
;;   ;; TODO: This is bad data normalization...
;;   (let ((is-const (contract-metadata-is-constant-time metadata)))
;;     (or (not is-const) (booleanp is-const)))
;;   (let ((is-fo (contract-metadata-is-first-order metadata)))
;;     (or (not is-fo) (booleanp is-fo)))))

(contract--bootstrap-defun
 contract--name
 (value)
 (-> t string)
 "Helper for `contract-name'. VALUE can be anything."
 (if (and
      (eieio-object-p value)
      (object-of-class-p value 'contract-contract))
     (let* ((ast (contract--ast value))
            (constructor-name
             (symbol-name
              (contract-ast-constructor ast)))
            (args (contract-ast-arguments ast)))
       (if (not args)
           constructor-name
         (apply
          #'contract--sexp-str
          constructor-name
          (mapcar #'contract--name args))))
   (format "%s" value)))

(defmacro contract--oref-or-oset (object slot form)
  "Retrieve the (unquoted) slot SLOT of OBJECT or set it to the result of FORM."
  `(if (slot-boundp ,object (quote ,slot))
       (oref ,object ,slot)
     (oset ,object ,slot ,form)))

(cl-defmethod contract--ast ((contract contract-contract))
  "Get the AST of CONTRACT.

Subclasses must override this method or set the AST slot."
  (oref contract ast))

(cl-defmethod contract-name ((contract contract-contract))
  "Get the cached name of CONTRACT or compute it from the AST.

Should not be overridden by subclasses, this method is \"final\"."
  ;; TODO: bootstrap-defmethod
  ;; (-> contract-contract-p string)
  (contract--oref-or-oset contract name (contract--name contract)))

(cl-defmethod contract--format ((contract contract-contract))
  "Get the format string of CONTRACT.

Subclasses must override this method or set the format slot."
  (contract--oref-or-oset contract format "Unexpected or incorrect value: %s"))

(cl-defmethod contract-is-first-order ((contract contract-contract))
  "Compute whether this contract CONTRACT is first-order."
  (contract--oref-or-oset contract is-first-order nil))

(cl-defmethod contract-is-constant-time ((contract contract-contract))
  "Compute whether this contract CONTRACT is constant-time."
  (contract--oref-or-oset contract is-constant-time nil))

(cl-defmethod contract-first-order ((contract contract-contract))
  "Get the first-order check of CONTRACT."
  (oref contract first-order))

(cl-defmethod contract-projection ((_contract contract-contract))
  "Compute the projection function for CONTRACT."
  (error
   "Subclasses of `contract-contract' must override `contract-projection'"))

(eval-when-compile
  (defsubst contract--make-late-neg-projection (proj)
    "Create a late-negative projection out of a simple projection PROJ."
    (contract--precond-expect-function "contract--make-late-neg-projection" proj)
    (lambda (positive-blame)
      (contract--precond-expect-blame
       "contract--make-late-neg-projection"
       positive-blame)
      (lambda (val neg-party)
        (contract--precond-expect-string
         "contract--make-late-neg-projection"
         neg-party)
        (contract--add-negative-party positive-blame neg-party)
        (funcall proj positive-blame val)))))

;;;; Helpers for Generating Values

(eval-when-compile
  (defsubst contract--generate-one-of (items)
    (lambda (state) (nth (cl-random (length items) state) items))))

;; (defun contract-exercise (func &optional n)
;;   "Exercise FUNC, which is a function defined via `contract-defun'.

;; To \"exercise\" a function is to generate random data according to its argument
;; contracts, and check that it conforms to its contract. N is the number of times
;; to repeat this process (default: 100).

;; This currently only works for contracts defined with `contract->' (TODO: extend
;; to `contract->d')."
;;   (contract--precond-expect-function "contract-exercise" func)
;;   (contract--precond-expect-symbol "contract-exercise" func)
;;   (let ((ast (contract-contract-ast contract)))
;;     (unless (equal 'contract-> (contract-ast-constructor ast)))
;;     (let* ((contract (get func 'contract))
;;            (arg-contracts (contract-ast-arguments ast)))
;;       (dotimes (_ (if n n 100))
;;         (apply
;;          func
;;          (mapcar
;;           (lambda (arg-contract)
;;             ;; TODO seed
;;             (funcall
;;              ;; TODO
;;              (cl-make-random-state)))
;;           arg-contracts))))))

;;;; Simple Contracts
;;;;; Predicate

(defclass contract--predicate (contract-contract)
  ()
  "TODO docs.")

(cl-defmethod initialize-instance :after ((pred contract--predicate) &rest _slots)
  "Initialize PRED with some default slot values."
  (oset pred is-first-order t))

(cl-defmethod contract-projection ((pred contract--predicate))
  "Compute the projection function for PRED."
  (contract--oref-or-oset
   pred
   proj
   (contract--make-late-neg-projection
    (lambda (blame val)
      (if (funcall (contract-first-order pred) val)
          val
        (contract-raise-violation
         (contract--make-violation
          :blame blame
          :contract pred
          :callstack (contract--function-stack))
         val))))))

;; TODO: Rename, make public
(contract--bootstrap-defun
 contract--make-first-order-contract
 (func format name &optional arguments constant-time)
 (-> function string symbol &optional (or nil list) (or nil boolean)
     contract-contract)
 "Create a first-order contract from a predicate FUNC.

The contract's name will be NAME, FORMAT is used to format error messages,
CONSTANT-TIME indicates whether the contract is considered \"fast\"."
 (contract--predicate
  :ast (contract--make-ast :constructor name :arguments arguments)
  :format format
  :is-constant-time constant-time
  :first-order func))

;;;;; compare-c

(defclass contract--compare-c (contract--predicate)
  ((compare
    :initarg :compare
    :documentation "Comparison function.")
   (value
    :initarg :value
    :documentation "The value to be compared to."))
  "Compare values to a given value using a binary relation.")

(cl-defmethod initialize-instance :after ((cmp contract--compare-c) &rest _slots)
  "Initialize CMP with some default slot values."
  (let ((value (oref cmp value))
        (compare (oref cmp compare)))
    (oset cmp first-order (lambda (val) (funcall compare val value)))))

(cl-defmethod contract--ast ((cmp contract--compare-c))
  "Get the AST of CMP."
  (contract--oref-or-oset
   cmp
   ast
   (contract--make-ast
    :constructor 'contract-compare-c
    :arguments (list (oref cmp compare) (oref cmp value)))))

(cl-defmethod contract--format ((cmp contract--compare-c))
  "Get the format string of CMP."
  (contract--oref-or-oset
   cmp
   format
   (format
    "Expected a value that compares to %s with %s"
    (contract--trunc-format 30 (oref cmp value))
    (contract--trunc-format 30 (oref cmp compare)))))

(contract--bootstrap-defun
 contract-compare-c
 (comp value)
 (-> (or subr function) t contract-contract)
 "Check that a value compares to VALUE using COMP.

>> (contract-contract-p (contract-compare-c #'equal nil))
=> t"
 (contract--compare-c
  :compare comp
  :value value))

;;;;; eq-c

(defclass contract--eq-c (contract--compare-c)
  ()
  "Check that a value is `eq' to VALUE.")

(cl-defmethod initialize-instance :before ((eqc contract--eq-c) &rest _slots)
  "Initialize EQC with some default slot values."
  (oset eqc compare #'eq)
  (oset eqc is-constant-time t))

(cl-defmethod contract--ast ((eqc contract--eq-c))
  "Get the AST of EQC."
  (contract--oref-or-oset
   eqc
   ast
   (contract--make-ast
    :constructor 'contract-eq-c
    :arguments (list (oref eqc value)))))

(cl-defmethod contract--format ((eqc contract--eq-c))
  "Get the format string of EQC."
  (contract--oref-or-oset
   eqc
   format
   (format
    "Expected a value that is `eq' to %s"
    (contract--trunc-format 30 (oref eqc value)))))

(contract--bootstrap-defun
 contract-eq-c
 (value)
 (-> t contract-contract)
 "Check that a value is `eq' to VALUE.

>> (contract-contract-p (contract-eq-c nil))
=> t"
 (contract--eq-c :value value))

;;;;; equal-c

(defclass contract--equal-c (contract--compare-c)
  ()
  "Check that a value is `eq' to VALUE.")

(cl-defmethod initialize-instance :before ((eqc contract--equal-c) &rest _slots)
  "Initialize EQC with some default slot values."
  (oset eqc compare #'equal)
  (oset eqc is-constant-time t))

(cl-defmethod contract--ast ((eqc contract--equal-c))
  "Get the AST of EQC."
  (contract--oref-or-oset
   eqc
   ast
   (contract--make-ast
    :constructor 'contract-equal-c
    :arguments (list (oref eqc value)))))

(cl-defmethod contract--format ((eqc contract--equal-c))
  "Get the format string of EQC."
  (contract--oref-or-oset
   eqc
   format
   (format
    "Expected a value that is `equal' to %s"
    (contract--trunc-format 30 (oref eqc value)))))

(contract--bootstrap-defun
 contract-equal-c
 (value)
 (-> t contract-contract)
 "Check that a value is `equal' to VALUE.

>> (contract-contract-p (contract-equal-c nil))
=> t"
 (contract--equal-c :value value))

;;;;; any-c

(defclass contract--any-c (contract--predicate)
  ()
  "Don't check anything.")

(cl-defmethod initialize-instance :after ((anyc contract--any-c) &rest _slots)
  "Initialize ANYC with some default slot values."
  (oset anyc first-order (lambda (_) t))
  (oset anyc is-constant-time t))

(cl-defmethod contract--ast ((anyc contract--any-c))
  "Get the AST of ANYC."
  (contract--oref-or-oset
   anyc
   ast
   (contract--make-ast :constructor 'contract-any-c :arguments '())))

(cl-defmethod contract--format ((anyc contract--any-c))
  "Get the format string of ANYC."
  (contract--oref-or-oset
   anyc
   format
   (format
    "Expected any value, got %s. This is probably a bug in contract.el."
    (contract--trunc-format 30 (oref anyc value)))))

(defconst
  contract-any-c
  (contract--any-c)
  "Don't check anything; accept every value.")

;;;;; none-c

(defclass contract--none-c (contract--predicate)
  ()
  "Reject every value.")

(cl-defmethod initialize-instance :after ((nonec contract--none-c) &rest _slots)
  "Initialize NONEC with some default slot values."
  (oset nonec first-order (lambda (_) nil))
  (oset nonec is-constant-time t))

(cl-defmethod contract--ast ((nonec contract--none-c))
  "Get the AST of NONEC."
  (contract--oref-or-oset
   nonec
   ast
   (contract--make-ast :constructor 'contract-none-c :arguments '())))

(cl-defmethod contract--format ((nonec contract--none-c))
  "Get the format string of NONEC."
  (contract--oref-or-oset nonec format "`nonec' rejects every value, got %s"))

(defconst contract-none-c (contract--none-c) "Reject every value.")

;;;;; Derived

;; TODO: Each of these should get their own class for better error messages,
;; consistency, AST, etc. Maybe create a macro that makes this easy?

(defconst contract-nil-c
  (contract-eq-c nil)
  "Contract that checks that a value is `eq' to nil.")

(defconst contract-t-c
  (contract-eq-c t)
  "Contract that checks that a value is `eq' to t.")

(defconst contract-blame-c
  (contract--make-first-order-contract
   #'contract-blame-p
   "Expected a blame object, but got %s"
   'contract-blame-c
   nil
   t)
  "Contract that checks that a value is a blame object.")

(defconst contract-contract-c
  (contract--make-first-order-contract
   #'contract-contract-p
   "Expected a contract (`contract-contract-c'), but got %s"
   'contract-contract-c
   nil
   t)
  "Contract that checks that a value is a contract.")

(defconst contract-sequence-c
  (contract--make-first-order-contract
   #'sequencep
   "Expected a sequence (`sequencep'), but got %s"
   'contract-sequence-c
   nil
   t)
  "Contract that checks that a value is `sequencep'.")

(defconst contract-function-c
  (contract--make-first-order-contract
   #'functionp
   "Expected a function (`functionp'), but got %s"
   'contract-function-c
   nil
   t)
  "Contract that checks that a value is `functionp'.")

(defconst contract-subr-c
  (contract--make-first-order-contract
   #'subrp
   "Expected a subroutine (`subrp'), but got %s"
   'contract-subr-c
   nil
   t)
  "Contract that checks that a value is `subrp'.")

(defconst contract-nat-number-c
  (contract--make-first-order-contract
   #'natnump
   "Expected a natural number (`natnump'), but got %s"
   'contract-nat-number-c
   nil
   t)
  "Contract that checks that a value is `natnump'.")

(defconst contract-string-c
  (contract--make-first-order-contract
   #'stringp
   "Expected a string (`stringp'), but got %s"
   'contract-string-c
   nil
   t)
  "Contract that checks that a value is `stringp'.")

(contract--bootstrap-defun
 contract-string-suffix-c
 (str)
 (-> string contract-contract)
 "Contract to check that a string is a suffix of STR.

>> (contract-contract-p (contract-string-suffix-c \"haystack\"))
=> t"
 (contract--make-first-order-contract
  (lambda (sub) (string-suffix-p sub str))
  (concat
   (format "Expected a suffix of %s" str)
   ", but got %s")
  'contract-string-suffix-c
  (list str)
  t))

(contract--bootstrap-defun
 contract-string-prefix-c
 (str)
 (-> string contract-contract)
 "Contract to check that a string is a prefix of STR.

>> (contract-contract-p (contract-string-prefix-c \"haystack\"))
=> t"
 (contract--make-first-order-contract
  (lambda (sub) (string-prefix-p sub str))
  (concat
   (format "Expected a prefix of %s" str)
   ", but got %s")
  'contract-string-prefix-c
  (list str)
  t))

(contract--bootstrap-defun
 contract-substring-c
 (str)
 (-> string contract-contract)
 "Contract to check that a string is a substring of STR.

>> (contract-contract-p (contract-substring-c \"haystack\"))
=> t"
 (contract--make-first-order-contract
  (lambda (sub) (string-match-p (regexp-quote sub) str))
  (concat
   (format "Expected a substring of %s" str)
   ", but got %s")
  'contract-substring-c
  (list str)
  nil))

(contract--bootstrap-defun
 contract-lt-c
 (val)
 (-> number contract-contract)
 "Contract to check that a value is less than VAL.

>> (contract-contract-p (contract-lt-c 0))
=> t"
 (contract--make-first-order-contract
  (lambda (less) (< less val))
  (concat
   (format "Expected a value less than %s" val)
   ", but got %s")
  'contract-lt-c
  (list val)
  t))

;;;; Coercion

(contract--bootstrap-defun
 contract--coerce-predicate
 (pred)
 (-> (and symbol function) contract-contract)
 "Coerce function symbol PRED to a first-order contract."
 (contract--make-first-order-contract
  pred
  (concat
   (format
    "Expected a value that is %s"
    (symbol-name pred))
   ", but got %s")
  pred))

;; TODO: Just return nil on failure, have another version that raises. Then use
;; in preconditions, etc.
(contract--bootstrap-defun
 contract--coerce-runtime
 (val)
 (-> t contract-contract)
 "Coerce VAL to a contract at runtime.

Works in case VAL is:

* A contract.
* t or nil.
* A unary predicate.
* TODO: A numeric literal.

>> (contract-contract-p (contract--coerce-runtime nil))
=> t
>> (contract-contract-p (contract--coerce-runtime t))
=> t
>> (contract-contract-p (contract--coerce-runtime contract-nil-c))
=> t
>> (contract-contract-p (contract--coerce-runtime #'natnump))
=> t
>> (condition-case nil (contract--coerce-runtime 0) (error nil))
=> nil"
 (cond
  ((equal nil val) contract-nil-c)
  ((equal t val) contract-t-c)
  ((and
    (symbolp val)
    (functionp val)
    (contract--arity-at-least val 1))
   (contract--coerce-predicate val))
  ((object-of-class-p val 'contract-contract) val)
  (t (error
      "Couldn't coerce value to contract; value: %s; type: %s"
      (contract--trunc-format 40 val)
      (contract--trunc-format 40 (type-of val))))))

(eval-when-compile
  (defmacro contract--coerce (val)
    "Coerce VAL to a contract at compile time, or defer until runtime.

Works in case VAL is:

* A contract.
* t or nil.
* A unary predicate.
* TODO: A numeric literal.

>> (contract-contract-p (contract--coerce nil))
=> t
>> (contract-contract-p (contract--coerce t))
=> t
>> (contract-contract-p (contract--coerce contract-nil-c))
=> t
>> (contract-contract-p (contract--coerce natnump))
=> t
>> (condition-case nil (contract--coerce 0) (error nil))
=> nil"
    (cond
     ((equal val 'nil) 'contract-nil-c)
     ((equal val 't) 'contract-t-c)
     ((and
       (symbolp val)
       (functionp val)
       (contract--arity-at-least val 1))
      (contract--coerce-predicate val))
     (t `(contract--coerce-runtime ,val)))))

(eval-when-compile
  (defsubst contract--precond-expect-contract (func contract)
    "Assert that CONTRACT is a contract object as a precondition of FUNC."
    (contract--precond
     (contract-contract-p (contract--coerce-runtime contract))
     func
     "Expected a contract object.")))

(contract--bootstrap-defun
 contract-check
 (contract value)
 (-> contract-contract t boolean)
 "Check the first-order parts of CONTRACT on VALUE.

>> (contract-check contract-nil-c nil)
=> t
>> (contract-check contract-t-c t)
=> t
>> (contract-check contract-t-c nil)
=> nil"
 (funcall (contract-first-order contract) value))

(contract--bootstrap-defun
 contract-apply
 (contract value blame)
 (-> t t contract-valid-blame t)
 "Apply CONTRACT to VALUE with blame BLAME.

If this CONTRACT is first-order, this function will check that VALUE satisfies
it, and return VALUE.  Otherwise, it will check that VALUE satisfies the
first-order part of CONTRACT (if any), and return a function that has the same
behavior as VALUE, except that it checks the higher-order CONTRACT before and
after applying VALUE.

>> (contract-apply contract-nil-c nil (contract-make-blame))
=> nil
>> (contract-apply contract-t-c t (contract-make-blame))
=> t"
 (funcall
  (funcall (contract-projection (contract--coerce-runtime contract)) blame)
  value
  (contract-blame-negative-party blame)))

;;;; Builders

(contract--bootstrap-defsubst
 contract--are-constant-time
 (contracts)
 (-> list boolean)
 "Are CONTRACTS all constant-time?"
 (cl-loop for c in contracts
          if (not (contract-is-constant-time c)) return nil
          finally return t))

(contract--bootstrap-defsubst
 contract--are-first-order
 (contracts)
 (-> list boolean)
 "Are CONTRACTS all first-order?"
 (cl-loop for c in contracts
          if (not (contract-is-first-order c)) return nil
          finally return t))

;; TODO: This is to be used in avoiding lambdas in contract->d, see below.
;;
;;   (defsubst contract--find-symbols (form)
;;     "Find all the symbols used in FORM.

;; >> (contract--find-symbols nil)
;; => nil
;; >> (contract--find-symbols 'symb)
;; => (symb)
;; >> (contract--find-symbols '(nested (is ok))
;; => (nested is ok)
;; "
;;     (cond
;;      ((nil form) nil)
;;      ((listp form)
;;       (apply
;;        seq-concatenate
;;        'list
;;        (cl-loop
;;         for subform in form
;;         (contract--find-symbols subform))))
;;      ((symbolp form) (list form))
;;      (t
;;       (message "HUH: %s" form))))

;;;;; ->d

(defclass contract-->d (contract-contract)
  ((name-contract-pairs
    :initarg :name-contract-pairs)
   (arg-contract-lambdas
    :initarg :arg-contract-lambdas)
   (ret-contract-lambda
    :initarg :ret-contract-lambda)))

(cl-defmethod initialize-instance :after ((contract contract-->d) &rest _slots)
  "Initialize CONTRACT with some default slot values."
  (oset contract is-first-order nil)
  ;; Can't guarantee that runtime-generated contracts will be constant-time
  (oset contract is-constant-time nil))

(cl-defmethod contract--ast ((contract contract-->d))
  "Get the AST of CONTRACT."
  (contract--oref-or-oset
   contract
   ast
   (contract--make-ast
    :constructor 'contract->d
    :arguments (oref contract name-contract-pairs))))

(cl-defmethod contract-projection ((contract contract-->d))
  "Compute the projection function for CONTRACT."
  (contract--oref-or-oset
   contract
   proj
   (let ((num-arg-contracts (length (oref contract arg-contract-lambdas))))
     (lambda (pos-blame)
       ;; TODO: Add context to argument and return blames here?
       (let ((blame (contract--blame-add-context pos-blame "contract->d")))
         (lambda (function-value neg-party)
           (contract--add-negative-party blame neg-party)
           ;; Check the first-order bits before returning the new closure that
           ;; applies the whole contract.
           (unless (funcall (contract-first-order contract) function-value)
             (contract-raise-violation
              (contract--make-violation
               :blame blame
               :callstack (contract--function-stack)
               :contract contract
               :format
               (concat
                (format
                 "Wrong function arity. Expected arity at least: %s\n"
                 num-arg-contracts)
                "Function: %s"))
              function-value))
           (lambda (&rest args)
             (unless (equal num-arg-contracts (length args))
               (contract-raise-violation
                (contract--make-violation
                 :blame blame
                 :callstack (contract--function-stack)
                 :contract contract
                 :format
                 (concat
                  (format
                   "Wrong number of arguments to function:\nExpected: %s\nFound: %s"
                   num-arg-contracts
                   (length args))
                  "\nArguments: %s"))
                args))
             (cl-loop
              for n from 0 to (1- num-arg-contracts)
              ;; TODO: Allocate argument blame outside the lambda?
              for arg-blame =
              (contract--blame-set-positive-party
               (contract--blame-swap-add-context
                blame
                (concat
                 "in the "
                 (number-to-string n)
                 "in th argument of"))
               "the contract for the return value")
              ;; TODO: Don't use nth here, maybe zip instead
              collect
              (contract-apply
               (apply (nth n (oref contract arg-contract-lambdas)) args)
               (nth n args)
               arg-blame))
             (contract-apply
              (apply
               (oref contract ret-contract-lambda)
               ;; NOTE: The blame change here is what makes this 'indy', i.e.
               ;; conform to the specification laid out in "Correct Blame for
               ;; Contracts: No More Scapegoating".
               (cl-loop
                for n from 0 to (1- num-arg-contracts)
                ;; TODO: Allocate argument blame outside the lambda?
                for arg-blame =
                (contract--blame-set-positive-party
                 (contract--blame-swap-add-context
                  blame
                  (concat
                   "in the "
                   (number-to-string n)
                   "in th argument of"))
                 "the contract for the return value")
                ;; TODO: Don't use nth here, maybe zip instead
                collect
                (contract-apply
                 (apply (nth n (oref contract arg-contract-lambdas)) args)
                 (nth n args)
                 arg-blame)))
              (apply
               function-value
               (cl-loop
                for n from 0 to (1- num-arg-contracts)
                ;; TODO: Allocate argument blame outside the lambda?
                for arg-blame = (contract--blame-swap-add-context
                                 blame
                                 (concat
                                  "in the "
                                  (number-to-string n)
                                  "th argument of"))
                ;; TODO: Don't use nth here, maybe zip instead
                collect
                (contract-apply
                 (apply (nth n (oref contract arg-contract-lambdas)) args)
                 (nth n args)
                 arg-blame)))
              (contract--blame-add-context
               blame
               "in the return value of")))))))))

;; TODO: Optimize to not create a lambda when an argument contract has no
;; dependency on other arguments, and in this case to coerce the "contract-like"
;; value at compile-time.
(defmacro contract->d (&rest name-contract-pairs)
  "Create a dependent function contract.

The argument NAME-CONTRACT-PAIRS is a list of forms.  All but the last should be
pairs of the form \"(argument-name contract)\" where

* \"argument-name\" is an unquoted symbol, and
* \"contract\" is an expression that evaluates to a contract and can mention any
  of the \"argument-name\"s.

The last form is the contract for the return value, and can also mention any of
the argument symbols.

This is analogous to Racket's \"->i\" builder, in that it has correct blame
assignment for contract violations that occur when checking the contract of the
return value."
  (let* ((num-arg-contracts (1- (length name-contract-pairs)))
         (arg-name-contract-pairs (seq-take name-contract-pairs num-arg-contracts))
         (arg-names
          (cl-loop
           for name-contract-pair in arg-name-contract-pairs
           collect
           (car name-contract-pair))))
    `(contract-->d
      :arg-contract-lambdas
      (list
       ,@(cl-loop
          for name-contract-pair in arg-name-contract-pairs
          collect
          `(function
            (lambda ,arg-names
              ;; HACK: Avoid unused variable warnings without actually using them.
              ,@(cl-loop
                 for var in arg-names
                 if (not (equal (symbol-name var) "_"))
                 collect `(contract--ignore ,var))
              ,(car (cdr name-contract-pair))))))
      :ret-contract-lambda
      (function
       (lambda ,arg-names
         ;; HACK: Avoid unused variable warnings without actually using them.
         ,@(cl-loop
            for var in arg-names
            if (not (equal (symbol-name var) "_"))
            collect `(contract--ignore ,var))
         ,(car (last name-contract-pairs))))
      :name-contract-pairs (quote ,name-contract-pairs)
      :first-order
      (lambda (value)
        (and
         (functionp value)
         (contract--arity-at-least value ,num-arg-contracts))))))

;;;;; ->

(defclass contract--> (contract-contract)
  ((arg-contracts
    :initarg :arg-contracts)
   (ret-contract
    :initarg :ret-contract)))

(cl-defmethod initialize-instance :after ((contract contract-->) &rest _slots)
  "Initialize CONTRACT with some default slot values."
  (oset contract is-first-order nil))

(cl-defmethod contract--ast ((contract contract-->))
  "Get the AST of CONTRACT."
  (contract--oref-or-oset
   contract
   ast
   (contract--make-ast
    :constructor 'contract->
    :arguments (append (oref contract arg-contracts)
                       (list (oref contract ret-contract))))))

(cl-defmethod contract-is-constant-time ((contract contract-->))
  "Compute whether this contract CONTRACT is constant-time."
  (contract--oref-or-oset
   contract
   is-constant-time
   (contract--are-constant-time
    (cons
     (oref contract ret-contract)
     (oref contract arg-contracts)))))

(cl-defmethod contract-projection ((contract contract-->))
  "Compute the projection function for CONTRACT."
  (contract--oref-or-oset
   contract
   proj
   (let ((num-arg-contracts (length (oref contract arg-contracts))))
     (lambda (pos-blame)
       (contract--precond-expect-blame "projection of contract->" pos-blame)
       (let* ((name (contract-name contract))
              (blame (contract--blame-add-context pos-blame name)))
         ;; TODO: Add context to argument and return blames here.
         (lambda (function-value neg-party)
           (contract--add-negative-party blame neg-party)
           ;; Check the first-order bits before returning the new closure that
           ;; applies the whole contract.
           (unless (funcall (contract-first-order contract) function-value)
             (contract-raise-violation
              (contract--make-violation
               :blame blame
               :callstack (contract--function-stack)
               :contract contract
               :format
               (concat
                (format
                 "Wrong function arity. Expected arity at least: %s\n"
                 num-arg-contracts)
                "Function: %s"))
              function-value))
           (lambda (&rest args)
             (unless (equal num-arg-contracts (length args))
               (contract-raise-violation
                (contract--make-violation
                 :blame blame
                 :callstack (contract--function-stack)
                 :contract contract
                 :format
                 (concat
                  (format
                   "Wrong number of arguments to function:\nExpected: %s\nFound: %s"
                   num-arg-contracts
                   (length args))
                  "\nArguments: %s"))
                args))
             (contract-apply
              (oref contract ret-contract)
              (apply
               function-value
               (cl-loop
                for n from 0 to (1- num-arg-contracts)
                ;; TODO: Allocate argument blame outside the lambda?
                for arg-blame = (contract--blame-swap-add-context
                                 blame
                                 (concat
                                  "in the "
                                  (number-to-string n)
                                  "th argument of"))
                ;; TODO: Don't use nth here, maybe zip instead
                collect
                (contract-apply
                 (nth n (oref contract arg-contracts))
                 (nth n args)
                 arg-blame)))
              (contract--blame-add-context blame "in the return value of")))))))))

(defmacro contract-> (&rest contracts)
  "Construct a contract for a function out of CONTRACTS.

The last contract is the contract for the function's return value.

>> (contract-contract-p (contract-> contract-nil-c contract-nil-c))
=> t"
  (let* ((num-arg-contracts (- (length contracts) 1))
         (arg-contracts
          (seq-take contracts num-arg-contracts))
         (ret-contract (car (last contracts))))
    `(contract-->
      :arg-contracts (list ,@arg-contracts)
      :ret-contract ,ret-contract
      :first-order
      (lambda (value)
        (and
         (functionp value)
         (contract--arity-at-least value ,num-arg-contracts))))))

;;;;; and-c

(defclass contract--and-c (contract-contract)
  ((subcontracts
    :initarg :subcontracts
    :reader contract--subcontracts)))

(cl-defmethod initialize-instance :after ((contract contract--and-c) &rest _slots)
  "Initialize CONTRACT with some default slot values."
  (oset
   contract
   first-order
   (lambda (v)
     (contract--all
      (contract (contract--subcontracts contract))
      (funcall (contract-first-order contract) v)))))

(cl-defmethod contract--ast ((contract contract--and-c))
  "Get the AST of CONTRACT."
  (contract--oref-or-oset
   contract
   ast
   (contract--make-ast
    :constructor 'contract-and
    :arguments (contract--subcontracts contract))))

(cl-defmethod contract-is-constant-time ((contract contract--and-c))
  "Compute whether this contract CONTRACT is constant-time."
  (contract--oref-or-oset
   contract
   is-constant-time
   (contract--are-constant-time (contract--subcontracts contract))))

(cl-defmethod contract-is-first-order ((contract contract--and-c))
  "Compute whether this contract CONTRACT is constant-time."
  (contract--oref-or-oset
   contract
   is-first-order
   (contract--are-first-order (contract--subcontracts contract))))

(cl-defmethod contract-projection ((contract contract--and-c))
  "Compute the projection function for CONTRACT."
  (contract--oref-or-oset
   contract
   proj
   (lambda (pos-blame)
     (contract--precond-expect-blame "projection of contract-and-c" pos-blame)
     ;; TODO: Call all the projections with pos-blame here?
     (lambda (value neg-party)
       (contract--ignore value)
       (contract--add-negative-party pos-blame neg-party)
       (dolist (c (contract--subcontracts contract))
         (setq value (contract-apply c value pos-blame)))
       value))))

(contract--bootstrap-defun
 contract-and-c
 (&rest contracts)
 (-> &rest list contract-contract)      ; TODO: List of contracts
 "Construct a conjunction of the given CONTRACTS.

>> (contract-contract-p (contract-and-c contract-nil-c contract-nil-c))
=> t
>> (contract-contract-p (contract-and-c contract-nil-c contract-t-c))
=> t
>> (contract-apply (contract-and-c contract-nil-c contract-nil-c) nil
     (contract-make-blame))
=> nil"
 (contract--and-c :subcontracts contracts))

;;;;; or-c

(defclass contract--or-c (contract-contract)
  ((subcontracts
    :initarg :subcontracts
    :reader contract--subcontracts)))

(cl-defmethod initialize-instance :after ((contract contract--or-c) &rest _slots)
  "Initialize CONTRACT with some default slot values."
  (oset
   contract
   first-order
   (lambda (v)
     (let ((contracts (contract--subcontracts contract)))
       (if (not contracts)
           t
         (contract--any
          (contract contracts)
          (funcall (contract-first-order contract) v)))))))

(cl-defmethod contract--ast ((contract contract--or-c))
  "Get the AST of CONTRACT."
  (contract--oref-or-oset
   contract
   ast
   (contract--make-ast
    :constructor 'contract-or
    :arguments (contract--subcontracts contract))))

(cl-defmethod contract-is-constant-time ((contract contract--or-c))
  "Compute whether this contract CONTRACT is constant-time."
  (contract--oref-or-oset
   contract
   is-constant-time
   (contract--are-constant-time (contract--subcontracts contract))))

(cl-defmethod contract-is-first-order ((contract contract--or-c))
  "Compute whether this contract CONTRACT is constant-time."
  (contract--oref-or-oset
   contract
   is-first-order
   (contract--are-first-order (contract--subcontracts contract))))

(cl-defmethod contract-projection ((contract contract--or-c))
  "Compute the projection function for CONTRACT."
  (contract--oref-or-oset
   contract
   proj
   (lambda (pos-blame)
     (contract--precond-expect-blame "projection of contract-or-c" pos-blame)
     ;; TODO: Call all the projections with pos-blame here?
     (lambda (value neg-party)
       (contract--ignore value)
       (contract--add-negative-party pos-blame neg-party)
       ;; TODO: Combine first-order parts?
       (let ((contracts (contract--subcontracts contract)))
         (if (not contracts)
             value
           (if (contract--any
                (contract contracts)
                (contract--doesnt-raise
                 (funcall
                  (funcall (contract-projection contract) pos-blame)
                  value
                  neg-party)))
               value
             (contract-raise-violation
              (contract--make-violation
               ;; TODO format
               :contract contract
               :blame pos-blame
               :callstack (contract--function-stack))
              value))))))))

(contract--bootstrap-defun
 contract-or-c
 (&rest contracts)
 (-> &rest list contract-contract)      ; TODO: List of contracts
 "Construct a conjunction of the given CONTRACTS.

>> (contract-contract-p (contract-or-c contract-nil-c contract-nil-c))
=> t
>> (contract-contract-p (contract-or-c contract-nil-c contract-t-c))
=> t
>> (contract-apply (contract-or-c contract-nil-c contract-nil-c) nil
     (contract-make-blame))
=> nil"
 (unless (contract--are-first-order contracts)
   (error "`contract-or-c' can only handle first-order contracts right now"))
 (contract--or-c :subcontracts contracts))

;;;;; maybe-c

(contract--bootstrap-defsubst
 contract-maybe-c
 (contract)
 (-> contract-contract contract-contract)
 "Check that a value is either nil or conforms to CONTRACT."
 (contract-or-c contract-nil-c contract))

;;;;; not-c

(defmacro contract--does-raise (form)
  `(condition-case nil
       (prog1 nil ,form)
     (contract-violation t)))

(defmacro contract--doesnt-raise (form)
  `(not (contract--does-raise ,form)))

(defclass contract--not-c (contract-contract)
  ((subcontracts                        ; invariant: length 1
    :initarg :subcontracts
    :reader contract--subcontracts)))

(cl-defmethod initialize-instance :after ((contract contract--not-c) &rest _slots)
  "Initialize CONTRACT with some default slot values."
  (oset
   contract
   first-order
   (lambda (v)
     (not
      (funcall
       (contract-first-order
        (car (contract--subcontracts contract))) v)))))

(cl-defmethod contract--ast ((contract contract--not-c))
  "Get the AST of CONTRACT."
  (contract--oref-or-oset
   contract
   ast
   (contract--make-ast
    :constructor 'contract-not
    :arguments (contract--subcontracts contract))))

(cl-defmethod contract-is-constant-time ((contract contract--not-c))
  "Compute whether this contract CONTRACT is constant-time."
  (contract--oref-or-oset
   contract
   is-constant-time
   (contract--are-constant-time (contract--subcontracts contract))))

(cl-defmethod contract-is-first-order ((contract contract--not-c))
  "Compute whether this contract CONTRACT is constant-time."
  (contract--oref-or-oset
   contract
   is-first-order
   (contract--are-first-order (contract--subcontracts contract))))

(cl-defmethod contract-projection ((contract contract--not-c))
  "Compute the projection function for CONTRACT."
  (contract--oref-or-oset
   contract
   proj
   (lambda (pos-blame)
     (contract--precond-expect-blame "projection of contract-not-c" pos-blame)
     (let ((late-neg
            (funcall
             (contract-projection (car (contract--subcontracts contract)))
             pos-blame)))
       (lambda (value neg-party)
         (contract--add-negative-party pos-blame neg-party)
         (if (contract--does-raise (funcall late-neg value neg-party))
             value
           (contract-raise-violation
            (contract--make-violation
             ;; TODO format
             :contract contract
             :blame pos-blame
             :callstack (contract--function-stack))
            value)))))))

(contract--bootstrap-defun
 contract-not-c
 (contract)
 (-> contract-contract contract-contract)
 "Negate CONTRACT.

>> (contract-contract-p (contract-not-c contract-nil-c))
=> t"
 (unless (contract-is-first-order contract)
   (error "`contract-not-c' can only handle first-order contracts right now"))
 (contract--not-c :subcontracts (list contract)))

;; TODO: contract-=-c
;; TODO: contract-xor-c
;; TODO: contract-one-of-c
;; TODO: Handling &optional args, &rest args in contract->.

;;;; Attaching Contracts

(contract--bootstrap-defun
 contract--should-enable
 (contract)
 (-> contract-contract boolean)
 "Check if CONTRACT should be enabled.

Looks at `contract-enable' and `contract-enable-slow'."
 (and
  contract-enable
  (or
   contract-enable-slow
   (contract-is-constant-time contract))))

(contract--bootstrap-defsubst
 contract--blame-for-function
 (func)
 (-> symbol contract-valid-blame)
 ;; TODO: Does this work with e.g. lambdas passed directly? Presumably not?
 (let ((name (symbol-name func)))
   (contract-make-blame
    :positive-party name
    :negative-party (concat "caller of " name))))

(contract--bootstrap-defun
 contract-advise
 (contract func)
 (-> contract-contract function t)
 "Advise FUNC by applying CONTRACT to it.

Cautiously will not advice any function with pre-existing advice."
 (unless (or (advice--p (advice--symbol-function func))
             (not (contract--should-enable contract)))
   (let* ((blame (contract--blame-for-function func))
          (contracted (contract-apply contract func blame)))
     (advice-add func :override contracted))))

;; Dogfooding:
(defconst
  contract--contract-advise-contract
  (contract->
   contract-contract-c
   (contract-and-c contract-function-c (contract-not-c contract-subr-c))
   contract-nil-c))
(defvar contract--contract-advise-advised nil)
(unless contract--contract-advise-advised
  (contract-advise
   contract--contract-advise-contract
   #'contract-advise)
  (setq contract--contract-advise-advised t))

;; TODO: Rewrite recursive calls to avoid contract checking overhead?
;; TODO: add fast-contract kwarg
;; TODO: modifies/preserves kwargs
(contract--bootstrap-defmacro
 contract-defun
 (name arguments &rest forms)
 (-> symbol list &rest list t)
 "Define NAME as a function taking ARGUMENTS and body FORMS.

If the first forms in FORMS is `:contract', the second form is interpreted as a
contract and applied to the defined function."
 (let ((contract (if (equal (car forms) :contract)
                     (progn
                       (pop forms)
                       (pop forms))
                   contract-any-c)))
   `(progn
      (put (quote ,name) 'contract ,contract)
      (setf
       (symbol-function (quote ,name))
       (contract-apply
        ,contract
        (lambda ,arguments ,@forms)
        (contract-make-blame
         :positive-party
         ,(symbol-name name)
         :negative-party
         ,(concat "caller of " (symbol-name name))))))))

;; TODO: contract-defconst
;; TODO: contract-setf
;; TODO: contract-setq

;;;; Contracts for Built-Ins

(defun contract-apply-contracts-for-built-ins ()
  "Apply contracts to Emacs built-in functions via advise.

CAUTION: This function may mess up your Emacs! Do not enable it e.g. in your
Emacs config file.  This library is considered unstable, and this is mostly a
mechanism for testing this package.

Also it doesn't really work because you mostly can't advise built-ins (at least,
in byte-compiled code)."
  (interactive)
  (contract-advise
   (contract->d (i contract-any-c) (contract-eq-c i))
   #'identity)
  (contract-advise
   (contract-> contract-nat-number-c)
   #'buffer-size)
  ;; Also: "This is 1, unless narrowing (a buffer restriction) is in effect."
  (contract-advise
   (contract-> contract-nat-number-c)
   #'point-min)
  ;; Also: "This is (1+ (buffer-size)), unless narrowing (a buffer restriction)
  ;; is in effect, in which case it is less."
  (contract-advise
   (contract-> contract-nat-number-c)
   #'point-max))

(provide 'contract)

;;; contract.el ends here
