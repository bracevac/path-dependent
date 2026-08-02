# LambdaP

`LambdaP` is a monadic-normal-form calculus of paths through immutable
dependent pairs. Pair members may be terms or type definitions, and a member
signature may mention the pair's first component. The Lean development proves
that every state reachable from a closed, well-typed initial term is final or
can take another step.

Term singleton types `{p}` and abstract type selections `p.A` have separate
syntax. Pair subtyping changes a dependent member while the first component
has singleton type, after which a separate rule widens the first component.
The unrestricted pair rule remains an open case.

## Build

From the repository root, run:

```sh
lake build
```

The repository is pinned to the Lean version in `lean-toolchain` and has no
external Lean dependencies. The default target builds the calculus, machine,
soundness proof, examples, and counterexample regression.

## Main results

`Safety.lean` states initial progress, one-step preservation, finite-run
preservation, and the combined theorem
`LambdaP.Tm.Ty.closed_type_safety`.

`Examples.lean` checks the intended dependent abstract-member pattern.
`CounterexampleRegression.lean` establishes that the historical false alias
is blocked. `Realization.lean` contains the semantic-coercion argument and its
fundamental lemma.

The paper presentation is in `../lambda_p.tex`. It can be rebuilt from the
repository root with:

```sh
mkdir -p tmp/pdfs
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=tmp/pdfs lambda_p.tex
```
