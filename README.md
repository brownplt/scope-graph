### Scope Inference and Scope-Safe Programming

This repository contains two projects:

- The [reference implementation](https://github.com/brownplt/scope-graph/tree/master/scope-inference) for
  [Inferring Scope through Syntactic Sugar](http://cs.brown.edu/~sk/Publications/Papers/Published/pkw-inf-scope-syn-sugar/), ICFP'17.
- An [experimental attempt](https://github.com/brownplt/scope-graph/tree/master/scope-safe-programming) at using
  the ideas from the paper to provide a representation of terms in
  Haskell that is *scope safe*, such that unhygienic transformations
  do not type check. (This is not discussed in the paper.)
