;;; contract-test.el --- ERT tests for contract -*- lexical-binding: t -*-

;;; Code:

(require 'contract)
;; (require 'doctest)
(require 'propcheck)

;; TODO: This doesn't appear to work?
;; (ert-deftest doctests ()
;;   (should (equal 0 (progn (doctest "../contract.el")))))

;; TODO: Add (contract-> contract-any-c contract-any-c)
(defconst
  contracts
  (list
   contract-any-c
   contract-nil-c
   contract-t-c
   contract-sequence-c
   contract-function-c
   contract-subr-c
   contract-nat-number-c
   contract-string-c))

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

(defun appc (value contract)
  (contract-apply contract value empty-blame))

(defun passes (value contract)
  (prog1 t (appc value contract)))

(defun fails (value contract)
  (not (ignore-error contract-violation
         (passes value contract))))

(fails t contract-nil-c)
(fails t (contract-and-c contract-nil-c contract-nil-c))

;; TODO: Weaker-than
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
 and-not ()
 (let ((contract (propcheck-generate-one-of nil :values contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     (contract-not-c contract-any-c)
     (contract-and-c contract (contract-not-c contract))
     value))))

(propcheck-deftest
 or-dup ()
 (let ((contract (propcheck-generate-one-of nil :values contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     contract
     (contract-or-c contract contract)
     value))))

(propcheck-deftest
 or-commutes ()
 (let ((contract1 (propcheck-generate-one-of nil :values contracts))
       (contract2 (propcheck-generate-one-of nil :values contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     (contract-or-c contract1 contract2)
     (contract-or-c contract2 contract1)
     value))))

(propcheck-deftest
 or-not ()
 (let ((contract (propcheck-generate-one-of nil :values contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     contract-any-c
     (contract-or-c contract (contract-not-c contract))
     value))))

(propcheck-deftest
 not-idempotent ()
 (let ((contract (propcheck-generate-one-of nil :values contracts))
       (value (propcheck-generate-one-of nil :values values)))
   (propcheck-should
    (equivalent-contracts
     contract
     (contract-not-c (contract-not-c contract))
     value))))

;;; contract-test.el ends here
