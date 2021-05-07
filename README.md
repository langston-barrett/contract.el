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
             (contract-lt-c (seq-length seq))))
         contract-any-c)

Note how the sequence argument `seq` was used in the contract for the index
`n`. This is a fairly good contract, but it could actually be even more
specific! A sequence can't contain itself, so we can assert that the returned
value is not equal to the first argument:

        (contract->d
         (seq contract-sequence-c)
         (n (contract-and-c
             contract-nat-number-c
             (contract-lt-c (seq-length seq))))
         (contract-not-c
          (contract-make-eq-contract seq)))

And we could go on, providing more and more guarantees, documentation, and
helpful error messages.

## Performance

Contracts can be disabled by setting `contract-enable`.

"Slow" contracts (those that are self-reported to take more than
constant-time) can be disabled by setting `contract-enable-slow`.

Contracts are be written in the "late negative blame" style by default, which
can improve performance if contracts are mostly attached to "exported"
bindings while avoided on "internal" bindings (see Racket's documentation for
more on this).

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
