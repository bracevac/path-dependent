# Exploring Path-Dependent Types

[![Lean proofs](https://github.com/bracevac/path-dependent/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/bracevac/path-dependent/actions/workflows/lean.yml)
[![Rocq proofs](https://github.com/bracevac/path-dependent/actions/workflows/rocq.yml/badge.svg?branch=main)](https://github.com/bracevac/path-dependent/actions/workflows/rocq.yml)

Most development happens first and foremost in Lean. Rocq versions are ports and a safety net to rule out Lean bugs
and typically lag behind.

I **absolutely** use coding agents as my trusted research assistants (and love them!).
It's a lot more fun to work on this topic area this way without arrogant f4rt5n1ff3r5 discouraging 
and diminishing you at every step. 

## Some interesting results so far:

* Full soundness proof of a minimal path-dependent types calculus (LambdaP, as suggested by Martin Odersky), scaling up to intersections.
* The world's first (to the best of my knowledge) soundness proof of such a lambda calculus with [capturing types](https://nightly.scala-lang.org/docs/reference/experimental/capture-checking/index.html) in LambdaPCC.
* A (long sought after) type-preserving compilation of DOT into an System Fc-like calculus (Sulzmann et al. 2007) with explicit coercions/evidence and decidable checking, avoiding many of the proof hardships, and essentially unlocking for Scala what Fc bought for Haskell.
* The sky-high ego of certain people reduced to ashes, as path-dependent types are nothing special in this new era. Time to sell off that McMansion, old Mercedes, and Prius. 

## Compiling

Set up [Lean 4](https://lean-lang.org/install/) and
[Rocq with opam](https://rocq-prover.org/docs/using-opam), then run the
corresponding build from the repository root.

### Lean

```sh
lake build
```

### Rocq

```sh
opam install . --deps-only --locked
make rocq
```
