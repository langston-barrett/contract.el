;;; contract-seq.el --- Contracts for 'seq' -*- lexical-binding: t -*-

;; Copyright © 2021 Langston Barrett <langston.barrett@gmail.com>

;; Author: Langston Barrett <langston.barrett@gmail.com>
;; URL: https://github.com/langston-barrett/contract.el
;; Keywords: lisp, debugging
;; Version: 0.1

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
;; This library provides a set of contracts for the 'seq' library.
;;
;;; Code:

(require 'contract)
(require 'seq)

(defvar
  contract-seq-contracts
  (list
   (cons
    #'seq-elt
    (contract->d
     (seq contract-sequence-c)
     (n (contract-and-c
         contract-nat-number-c
         (contract-<-c (seq-length seq))))
     ;; Slightly more specific than contract-any-c. A sequence can't be an
     ;; element of itself.
     (contract-not-c (contract-eq-c seq))))

   ;; Return the first element of SEQUENCE.
   (cons #'seq-first (contract-> contract-sequence-c contract-any-c))

   ;; Return a sequence of the elements of SEQUENCE except the first one.
   (cons #'seq-rest (contract-> contract-sequence-c contract-sequence-c))

   ;; Apply FUNCTION to each element of SEQUENCE and return nil.
   ;; Unlike ‘seq-map’, FUNCTION takes two arguments: the element of
   ;; the sequence, and its index within the sequence.
   (cons
    #'seq-do-indexed
    (contract->
     (contract-> contract-any-c #'natnump contract-any-c)
     contract-sequence-c
     contract-nil-c))

   ;; Return the result of applying FUNCTION to each element of SEQUENCE.
   ;; Unlike ‘seq-map’, FUNCTION takes two arguments: the element of
   ;; the sequence, and its index within the sequence.
   (cons
    #'seq-map-indexed
    (contract->
     (contract-> contract-any-c #'natnump contract-any-c)
     contract-sequence-c
     contract-sequence-c))

   ;; Sort SEQUENCE using PRED as a comparison function.
   ;; Elements of SEQUENCE are transformed by FUNCTION before being
   ;; sorted.  FUNCTION must be a function of one argument.
   (cons
    #'seq-sort-by
    (contract->
     (contract-> contract-any-c #'natnump contract-any-c)
     contract-sequence-c
     contract-sequence-c))))

(defun contract-seq-apply-contracts-seq ()
  "Apply contracts to the built-in \"seq\" library.

CAUTION: This function may mess up your Emacs! Do not enable it e.g. in your
Emacs configuration. This library is considered unstable, and this is mostly a
mechanism for testing this package."
  (interactive)
  (mapcar
   (lambda (pair)
     (contract-advise (cdr pair) (car pair)))
   contract-seq-contracts))

(provide 'contract-seq)

;;; contract-seq.el ends here
