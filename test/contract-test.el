;;; contract-test.el --- ERT tests for contract -*- lexical-binding: t -*-

;;; Code:

;;;; Imports

(require 'contract)
;; (require 'doctest)
(require 'propcheck)
(require 'seq)
(require 'subr-x)

;;;; Test Helpers

(defun pred (fun)
  "Make a first-order contract out of a predicate (pure function) FUN."
  (contract-predicate
   fun
   (if (symbolp fun)
       (concat "Violation of `" (symbol-name fun) "': %s")
     (concat "Violation of `phony': %s"))
   (if (symbolp fun)
       fun
     'phony)))

(defmacro print-error (&rest body)
  "Print and re-raises any errors that occur in BODY."
  `(condition-case err
       (progn ,@body)
     (t (progn
          (message "%s" (error-message-string err))
          (error (error-message-string err))))))

(defmacro ignore-wrong-type (&rest body)
  "Ignore `wrong-type-argument' errors, returning t if they occur.

BODY is evaluated in a `progn'."
  `(print-error
    (not
     (ignore-error 'wrong-type-argument
       (not
        (progn ,@body))))))


;; TODO: This doesn't appear to work?
;; (ert-deftest doctests ()
;;   (contract--should (equal 0 (progn (doctest "../contract.el")))))

;;;; Test Data

(defconst
  predicates
  (list
   #'arrayp
   #'atom
   #'booleanp
   #'consp
   #'floatp
   #'functionp
   #'integerp
   #'listp
   #'natnump
   #'numberp
   #'seq-empty-p
   #'sequencep
   #'stringp
   #'subrp
   #'symbolp
   #'vectorp))

;; Stolen from suggest.el:
(defconst pure-functions
  (append
   predicates
   (list
    #'seq-set-equal-p
    ;; TODO: add funcall, apply and map?
    ;; Boolean functions
    #'not
    ;; Built-in functions that access or examine lists.
    #'car
    #'cdr
    #'cadr
    #'cdar
    #'last
    #'cons
    #'nth
    #'nthcdr
    #'list
    #'length
    #'safe-length
    #'reverse
    #'remove
    #'remq
    #'append
    #'butlast
    ;; Built-in functions that create lists.
    #'make-list
    #'number-sequence
    ;; Sequence functions
    #'elt
    #'aref
    #'seq-subseq
    #'seq-drop
    #'seq-take
    #'seq-sort
    #'seq-reverse
    #'seq-concatenate
    #'seq-into
    #'seq-position
    #'seq-uniq
    #'seq-partition
    #'seq-intersection
    #'seq-difference
    ;; alist functions
    #'assoc
    #'alist-get
    ;; plist functions
    #'plist-get
    #'lax-plist-get
    #'plist-member
    ;; hash tables
    #'gethash
    #'hash-table-keys
    #'hash-table-values
    ;; vectors
    ;; TODO: there must be more worth using
    #'vector
    #'vconcat
    ;; Arithmetic
    #'+
    #'-
    #'*
    #'/
    #'%
    #'mod
    #'max
    #'min
    #'ash
    #'lsh
    #'log
    #'expt
    #'sqrt
    #'abs
    #'float
    #'round
    #'truncate
    #'ceiling
    #'fceiling
    #'ffloor
    #'fround
    #'ftruncate
    #'1+
    #'1-
    #'cl-evenp
    #'natnump
    #'cl-oddp
    #'zerop
    ;; Logical operators
    #'lsh
    #'logand
    #'logior
    #'logxor
    #'lognot
    ;; Strings
    #'string
    #'make-string
    #'upcase
    #'downcase
    #'substring
    #'concat
    #'split-string
    #'capitalize
    #'replace-regexp-in-string
    #'format
    #'string-join
    #'string-remove-prefix
    #'string-remove-suffix
    #'prin1-to-string
    #'string-prefix-p
    #'string-suffix-p
    ;; Quoting strings
    #'shell-quote-argument
    #'regexp-quote
    ;; Symbols
    #'symbol-name
    #'symbol-value
    #'symbol-file
    #'intern
    ;; Converting between types
    #'string-to-list
    #'string-to-number
    #'string-to-char
    #'number-to-string
    #'char-to-string
    ;; Paths
    #'file-name-as-directory
    #'file-name-base
    #'file-name-directory
    #'file-name-nondirectory
    #'file-name-extension
    #'expand-file-name
    #'abbreviate-file-name
    #'directory-file-name
    ;; Keyboard codes
    #'kbd
    #'key-description
    ;; Generic functions
    #'identity
    #'ignore)))

;; It's good to have them all in here, at least to check that they're resilient
;; against ill-typed arguments.
(defconst
  first-order-contracts
  (append
   (mapcar
    (lambda (p) (pred (lambda (v) (ignore-wrong-type (funcall p v)))))
    predicates)
   (list
    contract-any-c
    contract-nil-c
    contract-sequence-c
    contract-function-c
    contract-subr-c
    ;; Booleans
    contract-t-c
    contract-nil-c
    contract-boolean-c
    ;; Numbers
    contract-number-c
    contract-nat-number-c
    (contract-<=-c 2)
    (contract->=-c 2)
    (contract->-c 2.0)
    (contract-<-c 2.0)
    ;; Strings
    contract-string-c
    (contract-string-prefix-c "pre")
    (contract-string-suffix-c "suf")
    ;; (contract-substring-c "sub")
    (contract-match-c "^.$")
    ;; EIEIO
    )))

(defconst
  contracts
  (append
   first-order-contracts
   (list
    ;; TODO:
    (contract-> contract-any-c contract-any-c)
    )))

(defconst
  values
  (list
   nil
   t
   (cons 0 0)
   (list nil t nil)
   (list 0 1)
   #'identity
   ;; (lambda () 'x)
   ;; (lambda (x y) x)
   ;; (lambda (x) (lambda (y) x))
   ;; (lambda (&rest all) (car all))
   0
   -1
   0.1
   2
   ""
   "foo"))

;;;; Test DSL

(defconst empty-blame (contract-make-blame))

(defun passes (value contract)
  (contract-check contract value))

(defun fails (value contract)
  (not (passes value contract)))

(defun appc (value contract)
  (contract-apply contract value empty-blame))

(defun expect-pass (value contract)
  (prog1 t (appc value contract)))

(defun passes-apply (value contract)
  (ignore-error contract-violation
    (expect-pass value contract)))

;;;;; Relational Observations

(defmacro contract--should (&rest forms)
  "Propcheck weirdly doesn't print out errors on its own; FORMS."
  `(propcheck-should
    (print-error ,@forms)))

(defun equivalent-pred-contract (p contract value)
  "CONTRACT is equivalent to `pred' of P on VALUE."
  (let* ((pass-p (ignore-wrong-type (passes value contract)))
         (call-p (ignore-wrong-type (funcall p value)))
         (result (equal pass-p call-p)))
    (unless result
      (message "predicate: %s" p)
      (message "contract: %s" (contract-name contract))
      (message "value: %s" value)
      (message "passes predicate: %s" call-p)
      (message "passes contract: %s" pass-p))
    result))

(fails t contract-nil-c)
(fails t (contract-and-c contract-nil-c contract-nil-c))

(defmacro forall (name pairs &rest body)
  `(propcheck-deftest
    ,name ()
    (print-error
     (let (,@(mapcar
              (lambda (pair)
                `(,(car pair)
                  (propcheck-generate-one-of nil :values ,(cadr pair))))
              pairs))
       ,@body))))

;; TODO: Make a higher-order version that actually calls the resulting
;; contracted value
(defun c-= (contract1 contract2)
  "Assert that CONTRACT1 and CONTRACT2 are observationally equivalent.

In other words, CONTRACT1 fails if and only if CONTRACT2 fails on VALUE."
  (let ((value (propcheck-generate-one-of nil :values values)))
    (contract--should
     (let ((one (fails value contract1))
           (two (fails value contract2)))
       (if (equal one two)
           t
         (message "value: %s" value)
         (message "contract1: %s" (contract-name contract1))
         (message "contract2: %s" (contract-name contract2))
         nil)))))

;; TODO: Make a higher-order version that actually calls the resulting
;; contracted value
(defun c-< (contract1 contract2)
  "Assert that CONTRACT1 is observationally stricter than CONTRACT2.

In other words,CONTRACT2 fails only if CONTRACT1 fails on VALUE."
  (let ((value (propcheck-generate-one-of nil :values values)))
    (contract--should
     (let ((one (fails value contract1))
           (two (fails value contract2)))
       (if (not (and (not one) two))
           t
         (message "value: %s" value)
         (message "contract1: %s" (contract-name contract1))
         (message "contract2: %s" (contract-name contract2))
         nil)))))

;;;; Tests

;; `contract-check' agrees with `contract-apply' on first-order contracts.
;; TODO: re-enable
(quote
 (forall
  contract-check-first-order
  ((contract first-order-contracts)
   (value values))
  (contract--should
   (let ((result (equal
                  (passes-apply value contract)
                  (passes value contract))))
     (unless result
       (message "contract-check-first-order failed:")
       (message "contract: %s" (contract-name contract))
       (message "value: %s" value))))))

;;;;; pred

;; (propcheck-deftest
;;  pred-basic ()
;;  (let ((p (propcheck-generate-one-of nil :values predicates)))
;;    (contract--should
;;     (contract-contract-p (pred p)))))

(forall
 pred-arity
 ((p predicates))
 (contract--should
  (contract--arity-at-least p 1)))

(forall
 pred
 ((p predicates)
  (v values))
 (contract--should
  (equivalent-pred-contract p (pred p) v)))

(forall
 pred-not
 ((p predicates)
  (v values))
 (contract--should
  (equivalent-pred-contract
   (lambda (x) (not (funcall p x)))
   (contract-not-c (pred p))
   v)))

(forall
 pred-and
 ((p1 predicates)
  (p2 predicates)
  (v values))
 (contract--should
  (equivalent-pred-contract
   (lambda (x) (and (funcall p1 x) (funcall p2 x)))
   (contract-and-c (pred p1) (pred p2))
   v)))

(forall
 pred-or
 ((p1 predicates)
  (p2 predicates)
  (v values))
 (contract--should
  (equivalent-pred-contract
   (lambda (x) (or (funcall p1 x) (funcall p2 x)))
   (contract-or-c (pred p1) (pred p2))
   v)))

;;;;; not

(forall
 not-any
 ()
 (c-=
  contract-none-c
  (contract-not-c contract-any-c)))

(forall
 not-none
 ()
 (c-=
  contract-any-c
  (contract-not-c contract-none-c)))

;; TODO: Expand to higher-order
(forall
 not-idempotent
 ((contract first-order-contracts))
 (c-=
  contract
  (contract-not-c (contract-not-c contract))))

;;;;; and

(forall
 and-dup
 ((contract contracts))
 (c-=
  contract
  (contract-and-c contract contract)))

(forall
 and-commutes
 ((contract1 contracts)
  (contract2 contracts))
 (c-=
  (contract-and-c contract1 contract2)
  (contract-and-c contract2 contract1)))

(forall
 and-any
 ((contract contracts))
 (c-=
  contract
  (contract-and-c contract-any-c contract)))

(forall
 and-none
 ((contract contracts))
 (c-=
  contract-none-c
  (contract-and-c contract-none-c contract)))

(forall
 and-stricter
 ((contract1 contracts)
  (contract2 contracts))
 (c-<
  (contract-and-c contract1 contract2)
  contract1))

;; TODO: Expand to higher-order
(forall
 and-not
 ((contract first-order-contracts))
 (c-=
  contract-none-c
  (contract-and-c contract (contract-not-c contract))))

(forall
 and-assoc
 ((contract1 contracts)
  (contract2 contracts)
  (contract3 contracts))
 (c-=
  (contract-and-c (contract-and-c contract1 contract2) contract3)
  (contract-and-c contract1 (contract-and-c contract2 contract3))))

;;;;; or

;; TODO: Expand to higher-order
(forall
 or-dup
 ((contract first-order-contracts))
 (c-=
  contract
  (contract-or-c contract contract)))

;; TODO: Expand to higher-order
(forall
 or-commutes
 ((contract1 first-order-contracts)
  (contract2 first-order-contracts))
 (c-=
  (contract-or-c contract1 contract2)
  (contract-or-c contract2 contract1)))

(forall
 or-not
 ((contract first-order-contracts))
 (c-=
  contract-any-c
  (contract-or-c contract (contract-not-c contract))))

;; TODO: Expand to higher-order
(forall
 or-any
 ((contract first-order-contracts))
 (c-=
  contract-any-c
  (contract-or-c contract-any-c contract)))

;; TODO: Expand to higher-order
(forall
 or-none
 ((contract first-order-contracts))
 (c-=
  contract
  (contract-or-c contract-none-c contract)))

;; TODO: Expand to higher-order
(forall
 or-stricter
 ((contract1 first-order-contracts)
  (contract2 first-order-contracts))
 (c-<
  contract1
  (contract-or-c contract1 contract2)))

;; TODO: Expand to higher-order
(forall
 or-assoc
 ((contract1 first-order-contracts)
  (contract2 first-order-contracts)
  (contract3 first-order-contracts))
 (c-=
  (contract-or-c (contract-or-c contract1 contract2) contract3)
  (contract-or-c contract1 (contract-or-c contract2 contract3))))

;;;;; Numbers

;; (forall
;;  ((n numbers))
;;  (c-=
;;   contract-number-c
;;   (contract-or-c (contract-<=-c n) (contract->-c n))))

;;; contract-test.el ends here
