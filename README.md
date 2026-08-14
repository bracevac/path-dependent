# Exploring Path-Dependent Types

[![Lean proofs](https://github.com/bracevac/path-dependent/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/bracevac/path-dependent/actions/workflows/lean.yml)
[![Rocq proofs](https://github.com/bracevac/path-dependent/actions/workflows/rocq.yml/badge.svg?branch=main)](https://github.com/bracevac/path-dependent/actions/workflows/rocq.yml)

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
