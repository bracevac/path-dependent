# LambdaP

`LambdaP` is a small, monadic-normal-form calculus of paths through immutable
dependent pairs. Pair members may be terms or type definitions, and a member
signature may mention the pair's first component. The development includes an
unconditional Lean proof that every finite execution endpoint of a closed,
well-typed term is final or can take another step.

Two details distinguish the proved system:

- term singleton types `{p}` and abstract type selections `p.A` have separate
  syntax; and
- pair subtyping changes a dependent member only while the first component has
  singleton type, then widens the first component separately.

The second restriction is conservative. The unrestricted, syntax-separated
pair rule is not known to be unsound.

## Build

The repository is pinned to the Lean version in `lean-toolchain` and has no
external Lean dependencies.

```sh
lake build
```

This builds the canonical `LambdaP` library. The historical reconstruction and
its checked counterexample are a separate target:

```sh
lake build LambdaPHistory
```

The source-facing safety result is
`LambdaP.Tm.Ty.closed_type_safety` in `LambdaP/Safety.lean`. The same module
exports initial progress, one-step preservation, finite-run preservation, and
the combined finite-run safety theorem.

## Repository layout

- `LambdaP/` contains the current calculus, machine, and soundness proof.
- `LambdaPHistory/` retains the earlier unsound calculus and proof attempts.
- `LambdaP/Examples.lean` checks the intended dependent abstract-member
  pattern under the restricted pair rules.
- `LambdaP/CounterexampleRegression.lean` proves that the historical false
  alias is blocked, including through primitive transitivity.
- `docs/proof-history.md` records the counterexample and the proof attempts
  that led to the current design.
- `lambda_p.tex` presents the calculus and proof in paper form.

To rebuild the paper:

```sh
mkdir -p tmp/pdfs
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=tmp/pdfs lambda_p.tex
```

The checked PDF is published at `output/pdf/lambda-p.pdf`.
