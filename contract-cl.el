;;; contract-cl.el --- Contracts + 'cl' -*- lexical-binding: t -*-

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
;; This library provides a set of contract combinators that use and are relevant
;; to the 'cl' library.
;;
;;; Code:

(eval-and-compile
  (require 'contract))
(require 'cl-lib)

(contract--bootstrap-defun
 contract-the-c
 (some-cl-type)
 ;; TODO: Why doesn't this work?
 ;; (-> t contract-contract)
 (-> t t)
 "Check a (quoted) CL type annotation.

See Info node `(cl)Type Predicates'."
 (contract-predicate
  (lambda (value) (cl-typep value some-cl-type))
  (concat
   (format "Expected a value of (cl-)type %s" some-cl-type)
   ", but got %s")
  'contract-the-c
  (list some-cl-type)
  t))

(provide 'contract-cl)

;;; contract-cl.el ends here
