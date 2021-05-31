# contract - Racket-style higher-order contracts for Emacs Lisp

*Author:* Langston Barrett <langston.barrett@gmail.com><br>
*Version:* 0.1<br>

This library provides facilities for programming Emacs Lisp in the "design by
contract" style.  It's implementation and interface are heavily inspired by
Racket's contracts.

## Why

Have you ever seen an error like this pop into your `*Messages*` buffer?

    Wrong number of arguments: ((t) nil nil), 1

When something like this happens, it's not immediately clear what's wrong. Is
it a bug in your Emacs configuration? A third-party package? You might toggle
`debug-on-error`, try to reproduce the problem, and figure out which package
or snippet of configuration is at fault. This can get frustrating fast, and
is even more complex in code involving higher-order functions. With
contract.el, you can get this message instead:

    Wrong function arity. Expected arity at least: 1
    Function: <function value>
    Blaming: caller of mapcar (assuming the contract is correct)
    In:
      (contract-> contract-any-c contract-any-c)
      in the 0th argument of
      (contract-> (contract-> contract-any-c contract-any-c) contract-sequence-c contract-sequence-c)
    Call stack:
      some-function
      another-function

This message makes it easier to see

1. What went wrong: `mapcar` expects a function of arity at least 1 as its
   first argument.

2. Who is to blame: in this example, it's the caller of `mapcar`, namely
   `some-function`, which passed an invalid argument.

### For Package Authors

For Emacs Lisp package authors, contracts provide

* Detailed, helpful error messages for users interacting with your package
* Testable documentation for your API
* An escape from the tedium of "defensive programming" - let this package
  handle checking inputs and constructing great error messages

### For Emacs Users

Contracts help you debug errors in your configuration faster!

## Examples

Here are a few examples of possible contracts for functions in the `seq`
library.

First, a simple function contract: `seq-first` expects a sequence, and
returns its first element. Since `seq-first` works on any sequence, no
assertion is made about the return value.

        (contract-> contract-sequence-c contract-any-c)

Now, let's develop a more complicated contract for `seq-elt` step-by-step.
This function takes a sequence and an index in that sequence, and returns the
element at that index. This contract just checks that the sequence and index
have the right types:

        (contract-> contract-sequence-c contract-nat-number-c contract-any-c)

This is a good first approximation, but it could be much more specific. The
second argument not only has to be a natural number, but has to be in range
(less than the length of the sequence). This constraint can be expressed with
a dependent function contract, which allows the contracts for the arguments
and the contract for the return value to depend on the runtime values of the
arguments.

        (contract->d
         (seq contract-sequence-c)
         (n (contract-and-c
             contract-nat-number-c
             (contract-<-c (seq-length seq))))
         contract-any-c)

Note how the sequence argument `seq` was used in the contract for the index
`n`. This is a fairly good contract, but it could actually be even more
specific! A sequence can't contain itself, so we can assert that the returned
value is not equal to the first argument:

        (contract->d
         (seq contract-sequence-c)
         (n (contract-and-c
             contract-nat-number-c
             (contract-<-c (seq-length seq))))
         (contract-not-c
          (contract-eq-c seq)))

And we could go on, providing more and more guarantees, documentation, and
helpful error messages.

## Usage

The easiest way to get started is with the `contract-defun` macro, which
works like `defun` except it also takes a `:contract` argument:

       (contract-defun message-id (x)
         :contract (contract-> contract-any-c contract-any-c)
         "Print the value X to the messages buffer, and return it."  ; docstring
         (message "%s" x)  ; body
         x)  ; more body

With the above definition, the contract will get checked whenever `mesage-id`
is called.

### Basic Contracts

This package provides a number of basic contracts for simple conditions on
values:

* `contract-nil-c`: Checks that a value is `eq` to nil.
* `contract-any-c`: Doesn't check anything.
* `contract-function-c`: Checks that a value is `functionp`.
* `contract-nat-number-c`: Checks that a value is `natnump`.
* and many others...

Some are functions that create contracts based some input values:

* `contract-eq-c`: Checks that a value is `eq` to a given value.
* `contract-equal-c`: Checks that a value is `equal` to a given value.
* `contract-<-c`: Checks that a value is less than a given value.
* `contract-substring-c`: Checks that a value is a substring to a given string.
* `contract-length-c`: Checks that a sequence has a given length.
* `contract-the-c`: Checks a CL type predicate (see `cl-the`).
* and many others...

### Contract Combinators

In addition to the basic contracts, there are a number of "combinators" that
can be used to construct more complex contracts out of simpler ones. The most
important are:

* `contract-not-c`: For negating contracts
* `contract-and-c`
* `contract-or-c`
* `contract-cons-of-c`: For pairs of contracts that describe a cons cell
* `contract->`: For describing functions
* `contract->d`: For very precise, thorough description of functions

### Discovering New Contracts and Combinators

To find new contract combinators, you can use `apropos-function`:

       (apropos-function "^contract-.+-c$")

To use the above snippet, either copy-paste it into your scratch buffer and
call M-x `eval-buffer`, or call M-x `apropos-function` and type in the
pattern. This only works after you've installed this library.

## Performance

Contracts can be disabled by setting `contract-enable` to nil.

"Slow" contracts (those that are self-reported to take more than
constant-time) can be disabled by setting `contract-enable-slow` to nil.

Contracts are be written in the "late negative blame" style by default, which
can improve performance if contracts are mostly attached to "exported"
bindings while avoided on "internal" bindings (see Racket's documentation for
more on this).

Contracts are also very *lazy*: Very little is computed before explicitly
needed (e.g. error messages, contract names, etc.). Once computed, attributes
of contracts are cached so they don't need to be recomputed if requested
again.

## Development

PRs and issues welcome! Develop using Cask. Here are a few Makefile targets:

    make .cask/
    make build
    make test

Tests are provided using doctest, buttercup, and propcheck.

### Wishlist

The following is a "wishlist" of features from the Racket contract system
that are not (yet?) implemented here:

* Generating random data that satisfy a given contract.
* Contracts for vectors and other primitive types.
* The stronger-than partial ordering on contracts.
* "Collapsible" contracts.
* "Temporal" contracts.

### Implementation Notes

In Racket, contracts are implemented as "chaperones" to functions.  This
package only supports contracts on functions, and uses "advice" to emulate
chaperones in Emacs.  See also "Bibliography" below.

## Bibliography

These documents heavily influenced the design and implementation of this
library.  These would be helpful for users of this library to read, they
provide usage examples of Racket's contract system, which has a very similar
API.

* The Racket Guide
* The Racket Reference Manual

The following papers provide more theoretical background, and might be
helpful to read if you're interested in how this library works under the
hood, or want to contribute.

* "Correct Blame for Contracts: No More Scapegoating" by Christos Dimoulas,
  Robert Bruce Findler, Cormac Flanagan, and Matthias Felleisen: This paper
  influenced the implementation of the `contract->d` macro.


---
Converted from `contract.el` by [*el2markdown*](https://github.com/Lindydancer/el2markdown).
