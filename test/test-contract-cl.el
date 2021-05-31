;;; -*- lexical-binding: t -*-

(require 'contract-cl)
(require 'buttercup)

;; TODO: Deduplicate all this between tests! See what bigger projects do.

(defconst empty-blame (contract-make-blame))

(defun appc (value contract)
  (contract-apply contract value empty-blame))

(defun expect-pass (value contract)
  (prog1 t (appc value contract)))

(defun passes (value contract)
  (ignore-error contract-violation
    (expect-pass value contract)))

(defun fails (value contract)
  (not (passes value contract)))

(buttercup-define-matcher-for-binary-function
    :to-pass passes
  :expect-match-phrase "Expected `%A' to match contract."
  :expect-mismatch-phrase "Expected `%A' to fail contract.")

(buttercup-define-matcher-for-binary-function
    :to-fail fails
  :expect-match-phrase "Expected `%A' to fail to pass contract."
  :expect-mismatch-phrase "Expected `%A' to pass contract.")

(describe
    "contract-the-c"
  (it
      "accepts nil with (contract-the-c t)."
    (expect nil :to-pass (contract-the-c t)))
  (it
      "accepts t with (contract-the-c t)."
    (expect t :to-pass (contract-the-c t)))
  (it
      "accepts #'identity with (contract-the-c t)."
    (expect #'identity :to-pass (contract-the-c t)))
  (it
      "rejects nil with (contract-the-c function)."
    (expect nil :to-fail (contract-the-c 'function)))
  (it
      "accepts #'identity with (contract-the-c function)."
    (expect #'identity :to-pass (contract-the-c 'function))))
