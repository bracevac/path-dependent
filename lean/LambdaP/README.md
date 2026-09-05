# LambdaP

`LambdaP` is the original calculus of paths through immutable dependent
pairs, in monadic normal form. A pair member may be a term reference or a
type definition, and a member signature may mention the pair's first
component. Term singleton types `{p}` and abstract type selections `p.A`
have separate syntax, and the paper gives a closed, well-typed program that
gets stuck when the two are conflated. Pair subtyping is restricted: a
dependent member is widened only while the first component has singleton
type, and a separate rule then widens the first component. The unrestricted
pair rule is left open here and is the subject of `../LambdaPFC`.

## Main theorems

All in `Safety.lean`, all stated for the initial state of a closed,
well-typed term, and all depending on `propext` and `Quot.sound` only.

```
Tm.Ty.closed_progress             the initial state is final or steps
Tm.Ty.closed_finite_preservation  every finite run preserves exact structural typing
Tm.Ty.closed_finite_safety        every finite run ends in a typed, progressing state
Tm.Ty.closed_type_safety          no finite run of a closed well-typed term gets stuck
```

## Design

* **Exact stores.** Store typing records the exact introduction type of each
  stored value, and the machine invariant is stated at that precision. The
  runtime judgments form a *structural* family that mirrors every source
  judgment (path checking, subtyping, well-formedness, term checking), so
  that inversion never has to look inside an opaque source derivation.
* **Pair subtyping without circularity.** A naive canonical-forms or
  pushback argument fails for the pair rule with a widened member, for a
  strict-positivity reason explained at the head of `Realization.lean`.
  The proof instead interprets structural subtyping derivations as finite,
  defunctionalized semantic maps and discharges the operational obligations
  of the invariant through them.
* **Two proof lines.** An earlier precise-store line (`PreciseStore`,
  `PreciseProgress`, `Canonical`, `CanonicalForms`, `RefinedPathProgress`,
  `RuntimeConversion`) is kept, and the structural line (`Structural*`)
  is the one `Safety.lean` runs through.

## Modules

### Syntax and typing

| module | contents |
|---|---|
| `FinFun` | finite renamings between scopes |
| `Syntax` | intrinsically scoped paths, types, and terms, with singletons and selections as distinct constructors |
| `Context` | typing contexts |
| `Typing` | path typing, pair-member typing, interval selection with nonempty bounds |
| `TypingInversion`, `ValueInversion` | syntax-directed inversion of term and value typing |
| `Renaming`, `Opening` | renaming lemmas for every static judgment, the exact-type opening lemma |

### Runtime

| module | contents |
|---|---|
| `Store`, `StoreRefinement` | the store, weakening on extension, a proof-only refinement retaining the precise introduction type |
| `PathReduction`, `Lookup` | big-step path reduction to a location, and the alternate lookup following the static selection's prefix |
| `Cont`, `State`, `Machine` | let-frames, configurations and final states, the small-step CK machine |
| `RuntimeConversion`, `ScopedRuntimeEq` | store-justified path-equation closure of subtyping, lifted one scope deeper |
| `PreciseStore`, `StructuralPreciseStore` | value and store typing recording exact introduction types, and its structural version |
| `StructuralResolution` | generalized path resolution to term and type-definition endpoints |

### Metatheory

| module | contents |
|---|---|
| `Canonical`, `CanonicalForms` | canonical-head facts, canonical forms through semantic realization maps |
| `PathFunctionality`, `PathPreservation`, `PathProgress` | functionality, preservation, and totality of path lookup under an exact store |
| `PreciseProgress`, `Progress`, `AdministrativePreservation`, `RefinedPathProgress` | progress and preservation of the precise-store line |
| `Realization` | proof-relevant semantic maps that discharge pair subtyping without circularity |
| `StructuralRuntimeTyping`, `StructuralRuntimeLemmas`, `StructuralTermTyping` | the structural runtime judgments and their concrete-store instances |
| `StructuralNarrowing`, `StructuralPathSubstitution` | narrowing and path substitution for the structural judgments |
| `StructuralConversionInversion`, `StructuralValueInversion` | inversion of structural conversion under binders, and of values |
| `StructuralRealization`, `StructuralPreciseCanonical` | store-indexed realization for generalized types, exact-store observation interfaces |
| `StructuralPreciseProgress`, `StructuralPrecisePreservation`, `StructuralPreciseSafety` | progress, preservation, and finite-run safety for the exact structural invariant |
| `StructuralApplicationBoundary`, `StructuralApplicationCompatibility` | the application boundary and the function-specific canonical-forms property at a store location |
| `StructuralRefinedProgress`, `StructuralMachineInvariant` | progress obligations for refined stores, the machine invariant from structural judgments |
| `StructuralProgress`, `StructuralPreservation` | progress and preservation for the fully structural invariant |
| `Safety` | the unconditional closed-program theorems |

### Examples and regressions

| module | contents |
|---|---|
| `Examples` | the two restricted pair rules support the dependent abstract-member pattern |
| `CounterexampleRegression` | the historical closed alias counterexample is blocked |

Both are hand-built derivations.

## Paper

`lambda_p.tex`, "λ_P: Paths through Dependent Pairs", is the paper
presentation of this proof. From the repository root:

```sh
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error lean/LambdaP/lambda_p.tex
```

## Building

From the repository root, `lake build LambdaP`. A Rocq port lives in
`../../rocq/LambdaP`.
