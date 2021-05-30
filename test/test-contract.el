;;; -*- lexical-binding: t -*-

(require 'contract)
(require 'buttercup)

(defconst empty-blame (contract-make-blame))

(defun appc (value contract)
  (contract-apply contract value empty-blame))

(defun passes (value contract)
  (prog1 t (appc value contract)))

(defun fails (value contract)
  (not (ignore-error contract-violation
         (passes value contract))))

(defun get-error-message (value contract blame action)
  (condition-case pair
      (prog1 nil
        (funcall action (contract-apply contract value blame)))
    (contract-violation
     (pcase pair
       (`(,_ . ,message)
        message)))))

(defun blames (value contract blame party action)
  ;; HACK
  (string-match-p
   (regexp-quote (concat "Blaming: " party))
   (get-error-message value contract blame action)))

(defun get-violation (value contract blame action)
  (condition-case pair
      (prog1 nil
        (funcall action (contract-apply contract value blame)))
    (contract-violation
     (car contract-violations))))

(defun format-without-callstack (violation value)
  (contract--format-violation
   (contract--make-violation
    :blame (contract-violation-blame violation)
    :metadata (contract-violation-metadata violation)
    :callstack '()
    :format (contract-violation-format violation))
   value))

(defun golden (value contract blame action)
  (let ((violation-and-value (get-violation value contract blame action)))
    (format-without-callstack
     (car violation-and-value)
     (cdr violation-and-value))))

;; TODO Matchers for blame.

(buttercup-define-matcher-for-binary-function
    :to-pass passes
  :expect-match-phrase "Expected `%A' to match contract."
  :expect-mismatch-phrase "Expected `%A' to fail contract.")

(buttercup-define-matcher-for-binary-function
    :to-fail fails
  :expect-match-phrase "Expected `%A' to fail to pass contract."
  :expect-mismatch-phrase "Expected `%A' to pass contract.")

(describe
    "contract-apply"
  (it "coerces nil to a contract." (expect nil :to-pass nil))
  (it "coerces t to a contract." (expect t :to-pass t))
  (it "coerces natnump to a contract." (expect 0 :to-pass #'natnump)))

(describe
    "contract-any-c"
  (it "accepts nil." (expect nil :to-pass contract-any-c))
  (it "accepts t." (expect t :to-pass contract-any-c))
  (it "accepts identity." (expect #'identity :to-pass contract-any-c))
  (it "accepts a lambda." (expect (lambda (_) 0) :to-pass contract-any-c)))

(describe
    "contract-nil-c"
  (it "accepts nil." (expect nil :to-pass contract-nil-c))
  (it "rejects t." (expect t :to-fail contract-nil-c)))

(describe
    "contract-t-c"
  ;; TODO: Maybe this should match its name as a variable?
  (it "has a name."
    (expect (contract-name contract-t-c) :to-equal "eq-to-t"))
  (it "accepts t." (expect t :to-pass contract-t-c))
  (it "rejects nil." (expect nil :to-fail contract-t-c)))

(describe
    "contract-not-c"
  (it "accepts t with contract-nil-c."
    (expect t :to-pass (contract-not-c contract-nil-c)))
  (it "accepts nil with contract-t-c."
    (expect nil :to-pass (contract-not-c contract-t-c))))

(describe
    "contract-lt-c"
  (it "passes." (expect 1 :to-pass (contract-lt-c 2)))
  (it "fails." (expect 2 :to-fail (contract-lt-c 2))))

(describe
    "contract-substring-c"
  (it "passes." (expect "sub" :to-pass (contract-substring-c "substring")))
  (it "fails." (expect "not" :to-fail (contract-substring-c "sub"))))

(describe
    "contract-nat-number-c"
  (it
      "provides decent error messages"
    (expect
     (golden
      nil
      contract-nat-number-c
      empty-blame
      #'identity)
     :to-equal
     "Expected a natural number (`natnump'), but got nil
Blaming: *unknown* (assuming the contract is correct)
In:
Call stack:
  ")))

(describe
    "contract->"
  (it "rejects nil with arity 0." (expect nil :to-fail (contract-> contract-any-c)))
  (it "rejects t with arity 0." (expect t :to-fail (contract-> contract-any-c)))
  (it "rejects nil with arity 1."
    (expect nil :to-fail (contract-> contract-any-c contract-any-c)))
  (it "rejects t with arity 1."
    (expect t :to-fail (contract-> contract-any-c contract-any-c)))
  (it
      "gives back a function."
    (expect
     (functionp (appc #'identity (contract-> contract-any-c contract-any-c)))
     :to-equal t))
  (xit
      "accepts point as arity 0 with (contract-> contract-any-c)."
    (expect #'point :to-pass (contract-> contract-any-c)))
  (xit
      "accepts point as arity 0 with (contract-> #'natnump)."
    (expect #'point :to-pass (contract-> #'natnump)))
  (it "rejects point with arity 1."
    (expect #'point :to-fail (contract-> contract-any-c contract-any-c)))
  ;; What on earth is going on here?
  (it
      "accepts identity as arity 1."
    (expect
     #'identity
     :to-pass
     (contract-> contract-any-c contract-any-c)))
  (it
      "doesn't modify identity as arity 1."
    (expect
     (funcall (appc #'identity (contract-> contract-any-c contract-any-c)) t)
     :to-equal t))
  (it "rejects identity as arity 2."
    (expect
     #'identity
     :to-fail
     (contract-> contract-any-c contract-any-c contract-any-c)))
  (it "blames identity with (contract-> contract-t-c contract-nil-c) and argument t."
    (expect
     (blames
      #'identity
      (contract-> contract-t-c contract-nil-c)
      (contract-make-blame
       :positive-party "identity"
       :negative-party "caller of identity")
      "identity"
      (lambda (id) (funcall id t)))
     :to-be-truthy))
  (it "blames caller of identity with (contract-> contract-t-c contract-nil-c) and argument nil."
    (expect
     (blames
      #'identity
      (contract-> contract-t-c contract-nil-c)
      (contract-make-blame
       :positive-party "identity"
       :negative-party "caller of identity")
      "caller of identity"
      (lambda (id) (funcall id nil)))
     :to-be-truthy)))

(describe
    "contract->d"
  (it "rejects nil with arity 0." (expect nil :to-fail (contract->d contract-any-c)))
  (it "rejects t with arity 0." (expect t :to-fail (contract->d contract-any-c)))
  (it
      "accepts identity with its most permissive contract."
    (expect
     #'identity
     :to-pass
     (contract->d (_ contract-any-c) contract-any-c)))
  (it
      "accepts identity with its most restrictive contract."
    (expect
     #'identity
     :to-pass
     (contract->d (i contract-any-c) (contract-make-eq-contract i))))
  (it
      "accepts identity with its most restrictive contract and argument nil."
    (expect
     (funcall
      (appc
       #'identity
       (contract->d
        (i contract-any-c)
        (contract-make-eq-contract i)))
      nil)
     :to-equal
     nil))
  (it "blames the contract itself when appropriate."
    (expect
     (blames
      #'identity
      (contract->d
       (input-fun (contract-> contract-t-c contract-t-c))
       (prog1 contract-any-c (funcall input-fun nil)))
      (contract-make-blame
       :positive-party "identity"
       :negative-party "caller of identity")
      "the contract for the return value"
      (lambda (id) (funcall id t)))
     :to-be-truthy))
  )

(describe
    "contract-and-c"
  (it
      "accepts nil with (contract-and-c)."
    (expect nil :to-pass (contract-and-c)))
  (it
      "accepts nil with (contract-and-c contract-any-c)."
    (expect nil :to-pass (contract-and-c contract-any-c)))
  (it
      "accepts nil with (contract-and-c contract-any-c contract-any-c)."
    (expect
     nil
     :to-pass
     (contract-and-c contract-any-c contract-any-c)))
  (it
      "accepts nil with (contract-and-c contract-nil-c contract-any-c)."
    (expect
     nil
     :to-pass
     (contract-and-c contract-nil-c contract-any-c)))
  (it
      "rejects t with (contract-and-c contract-nil-c contract-nil-c)"
    (expect t :to-fail (contract-and-c contract-nil-c contract-nil-c)))
  (it
      "rejects nil with (contract-and-c contract-t-c)."
    (expect nil :to-fail (contract-and-c contract-t-c)))
  (it
      "rejects nil with (contract-and-c contract-nil-c contract-t-c)."
    (expect
     nil
     :to-fail
     (contract-and-c contract-nil-c contract-t-c)))
  (it
      "rejects nil with (contract-and-c contract-t-c contract-nil-c)."
    (expect
     nil
     :to-fail
     (contract-and-c contract-t-c contract-nil-c))))

(describe
    "contract-or-c"
  (it
      "accepts nil with (contract-or-c)."
    (expect nil :to-pass (contract-or-c)))
  (it
      "accepts nil with (contract-or-c contract-any-c)."
    (expect nil :to-pass (contract-or-c contract-any-c)))
  (it
      "accepts nil with (contract-or-c contract-any-c contract-any-c)."
    (expect
     nil
     :to-pass
     (contract-or-c contract-any-c contract-any-c)))
  (it
      "accepts nil with (contract-or-c contract-nil-c contract-any-c)."
    (expect
     nil
     :to-pass
     (contract-or-c contract-nil-c contract-any-c)))
  (it
      "accepts t with (contract-or-c contract-t-c contract-t-c)"
    (expect t :to-pass (contract-or-c contract-t-c contract-t-c)))
  (it
      "rejects t with (contract-or-c contract-nil-c)."
    (expect t :to-fail (contract-or-c contract-nil-c)))
  (it
      "rejects nil with (contract-or-c contract-t-c)."
    (expect nil :to-fail (contract-or-c contract-t-c)))
  (it
      "accepts nil with (contract-or-c contract-nil-c contract-t-c)."
    (expect
     nil
     :to-pass
     (contract-or-c contract-nil-c contract-t-c)))
  (it
      "accepts nil with (contract-or-c contract-t-c contract-nil-c)."
    (expect
     nil
     :to-pass
     (contract-or-c contract-t-c contract-nil-c))))

(describe
    "A really simple example"
  (it
      "works."
    (expect
     (golden
      #'identity
      (contract-> contract-nil-c contract-nil-c)
      (contract-make-blame
       :positive-party "identity"
       :negative-party "caller of identity")
      (lambda (my-identity) (funcall my-identity t)))
     :to-equal
     "Expected a value that is `eq' to nil
Blaming: caller of identity (assuming the contract is correct)
In:
  in the 0th argument of
  (contract-> eq-to-nil eq-to-nil)
Call stack:
  ")))

(defun my-mapcar (_f _l))
(describe
    "The README example"
  (it "works."
    (expect
     (let ((violation-and-value
            (get-violation
             #'my-mapcar
             (contract->
              (contract-> contract-any-c contract-any-c)
              contract-sequence-c
              contract-sequence-c)
             (contract-make-blame
              :positive-party "my-mapcar"
              :negative-party "caller of my-mapcar")
             (lambda (my-mapcar-local) (funcall my-mapcar-local (lambda () nil) '())))))
       (format-without-callstack
        (car violation-and-value)
        (cdr violation-and-value)))
     :to-equal
     "Wrong function arity. Expected arity at least: 1
Function: <function value>
Blaming: caller of my-mapcar (assuming the contract is correct)
In:
  (contract-> contract-any-c contract-any-c)
  in the 0th argument of
  (contract-> (contract-> contract-any-c contract-any-c) contract-sequence-c contract-sequence-c)
Call stack:
  ")))

(describe
    "contract-defun"
  (it "works with id and (contract-> contract-nil-c contract-nil-c)."
    (expect
     (progn
       (contract-defun
        id (x)
        :contract (contract-> contract-nil-c contract-nil-c)
        x)
       (id nil))
     :to-equal
     nil))
  (it "fails with id and (contract-> contract-nil-c contract-t-c)."
    (expect
     (progn
       (contract-defun
        id (x)
        :contract (contract-> contract-nil-c contract-t-c)
        x)
       (not (ignore-error contract-violation
              (id nil))))
     :to-equal
     t)))
