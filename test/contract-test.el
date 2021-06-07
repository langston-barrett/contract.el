;;; contract-test.el --- ERT tests for contract -*- lexical-binding: t -*-

;;; Code:

(require 'contract)
;; (require 'doctest)
(require 'propcheck)
(require 'seq)
(require 'subr-x)

;; TODO: This doesn't appear to work?
;; (ert-deftest doctests ()
;;   (should (equal 0 (progn (doctest "../contract.el")))))

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

(defun pred (fun)
  "Make a first-order contract out of a predicate (pure function) FUN."
  (contract--make-first-order-contract
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

(defconst
  first-order-contracts
  (append
   (mapcar
    (lambda (p) (pred (lambda (v) (ignore-wrong-type (funcall p v)))))
    predicates)
   (list
    contract-any-c
    contract-nil-c
    contract-t-c
    contract-sequence-c
    contract-function-c
    contract-subr-c
    contract-nat-number-c
    contract-string-c)))

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
   (list nil t nil)
   (list 0 1)
   #'identity
   (lambda (x y) x)
   0
   -1
   0.1
   2
   ""
   "foo"))

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

(fails t contract-nil-c)
(fails t (contract-and-c contract-nil-c contract-nil-c))

;; `contract-check' agrees with `contract-apply' on first-order contracts.
(propcheck-deftest
 contract-check-first-order ()
 (let ((contract (propcheck-generate-one-of nil :values first-order-contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equal
     (passes-apply value contract)
     (passes value contract)))))

(defun stricter-contract (contract1 contract2 value)
  "CONTRACT2 fails only if CONTRACT1 fails on VALUE."
  (let ((one (fails value contract1))
        (two (fails value contract2)))
    (if (not (and (not one) two))
        t
      (message "value: %s" value)
      (message "contract1: %s" (contract-name contract1))
      (message "contract2: %s" (contract-name contract2))
      nil)))

(defun equivalent-contracts (contract1 contract2 value)
  "CONTRACT1 fails if and only if CONTRACT2 fails on VALUE."
  (let ((one (fails value contract1))
        (two (fails value contract2)))
    (if (equal one two)
        t
      (message "value: %s" value)
      (message "contract1: %s" (contract-name contract1))
      (message "contract2: %s" (contract-name contract2))
      nil)))

(propcheck-deftest
 pred-basic ()
 (let ((p (propcheck-generate-one-of nil :values predicates)))
   (propcheck-should
    (contract-contract-p (pred p)))))

(defun equivalent-pred-contract (p contract value)
  "CONTRACT is equivalent to `pred' of P on VALUE."
  (let ((result (ignore-wrong-type
                 (equal
                  (passes value contract)
                  (funcall p value)))))
    (unless result
      (message "predicate: %s" p)
      (message "contract: %s" (contract-name contract))
      (message "value: %s" value))
    result))

(propcheck-deftest
 pred ()
 (let ((p (propcheck-generate-one-of nil :values predicates))
       (v (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-pred-contract p (pred p) v))))

(propcheck-deftest
 pred-not ()
 (let ((p (propcheck-generate-one-of nil :values predicates))
       (v (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-pred-contract
     (lambda (x) (not (funcall p x)))
     (contract-not-c (pred p))
     v))))

(propcheck-deftest
 pred-and ()
 (let ((p1 (propcheck-generate-one-of nil :values predicates))
       (p2 (propcheck-generate-one-of nil :values predicates))
       (v (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-pred-contract
     (lambda (x) (and (funcall p1 x) (funcall p2 x)))
     (contract-and-c (pred p1) (pred p2))
     v))))

(propcheck-deftest
 pred-or ()
 (let ((p1 (propcheck-generate-one-of nil :values predicates))
       (p2 (propcheck-generate-one-of nil :values predicates))
       (v (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-pred-contract
     (lambda (x) (or (funcall p1 x) (funcall p2 x)))
     (contract-or-c (pred p1) (pred p2))
     v))))

(propcheck-deftest
 not-any ()
 (let ((value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     contract-none-c
     (contract-not-c contract-any-c)
     value))))

(propcheck-deftest
 not-none ()
 (let ((value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     contract-any-c
     (contract-not-c contract-none-c)
     value))))

(propcheck-deftest
 not-idempotent ()
 ;; TODO: Expand to higher-order
 (let ((contract (propcheck-generate-one-of nil :values first-order-contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     contract
     (contract-not-c (contract-not-c contract))
     value))))

(propcheck-deftest
 and-dup ()
 (let ((contract (propcheck-generate-one-of nil :values contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     contract
     (contract-and-c contract contract)
     value))))

(propcheck-deftest
 and-commutes ()
 (let ((contract1 (propcheck-generate-one-of nil :values contracts))
       (contract2 (propcheck-generate-one-of nil :values contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     (contract-and-c contract1 contract2)
     (contract-and-c contract2 contract1)
     value))))

(propcheck-deftest
 and-any ()
 (let ((contract (propcheck-generate-one-of nil :values contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     contract
     (contract-and-c contract-any-c contract)
     value))))

(propcheck-deftest
 and-none ()
 (let ((contract (propcheck-generate-one-of nil :values contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     contract-none-c
     (contract-and-c contract-none-c contract)
     value))))

(propcheck-deftest
 and-stricter ()
 (let ((contract1 (propcheck-generate-one-of nil :values contracts))
       (contract2 (propcheck-generate-one-of nil :values contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (stricter-contract
     (contract-and-c contract1 contract2)
     contract1
     value))))

(propcheck-deftest
 and-not ()
 ;; TODO: Expand to higher-order
 (let ((contract (propcheck-generate-one-of nil :values first-order-contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     contract-none-c
     (contract-and-c contract (contract-not-c contract))
     value))))

(propcheck-deftest
 and-assoc ()
 (let ((contract1 (propcheck-generate-one-of nil :values contracts))
       (contract2 (propcheck-generate-one-of nil :values contracts))
       (contract3 (propcheck-generate-one-of nil :values contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     (contract-and-c (contract-and-c contract1 contract2) contract3)
     (contract-and-c contract1 (contract-and-c contract2 contract3))
     value))))

(propcheck-deftest
 or-dup ()
 ;; TODO: Expand to higher-order
 (let ((contract (propcheck-generate-one-of nil :values first-order-contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     contract
     (contract-or-c contract contract)
     value))))

(propcheck-deftest
 or-commutes ()
 ;; TODO: Expand to higher-order
 (let ((contract1 (propcheck-generate-one-of nil :values first-order-contracts))
       (contract2 (propcheck-generate-one-of nil :values first-order-contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     (contract-or-c contract1 contract2)
     (contract-or-c contract2 contract1)
     value))))

(propcheck-deftest
 or-not ()
 ;; TODO: Expand to higher-order
 (let ((contract (propcheck-generate-one-of nil :values first-order-contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     contract-any-c
     (contract-or-c contract (contract-not-c contract))
     value))))

(propcheck-deftest
 or-any ()
 ;; TODO: Expand to higher-order
 (let ((contract (propcheck-generate-one-of nil :values first-order-contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     contract-any-c
     (contract-or-c contract-any-c contract)
     value))))

(propcheck-deftest
 or-none ()
 ;; TODO: Expand to higher-order
 (let ((contract (propcheck-generate-one-of nil :values first-order-contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     contract
     (contract-or-c contract-none-c contract)
     value))))

(propcheck-deftest
 or-stricter ()
 ;; TODO: Expand to higher-order
 (let ((contract1 (propcheck-generate-one-of nil :values first-order-contracts))
       (contract2 (propcheck-generate-one-of nil :values first-order-contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (stricter-contract
     contract1
     (contract-or-c contract1 contract2)
     value))))

(propcheck-deftest
 or-assoc ()
 ;; TODO: Expand to higher-order
 (let ((contract1 (propcheck-generate-one-of nil :values first-order-contracts))
       (contract2 (propcheck-generate-one-of nil :values first-order-contracts))
       (contract3 (propcheck-generate-one-of nil :values first-order-contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     (contract-or-c (contract-or-c contract1 contract2) contract3)
     (contract-or-c contract1 (contract-or-c contract2 contract3))
     value))))

;;; contract-test.el ends here
