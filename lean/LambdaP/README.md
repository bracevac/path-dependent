# LambdaP

Paths through immutable dependent pairs, in monadic normal form. A pair member is a term or a type definition and may depend on the first component. Term singletons `{p}` and type selections `p.A` are distinct. Pair subtyping widens a member only under a singleton-typed first component. The general rule is left open here and handled in `../LambdaPFC`.

## Main theorems

In `Safety.lean`, for the initial state of a closed well-typed term. Axioms: `propext`, `Quot.sound`.

```
Tm.Ty.closed_progress
Tm.Ty.closed_finite_preservation
Tm.Ty.closed_finite_safety
Tm.Ty.closed_type_safety          no finite run gets stuck
```

## Design

* Stores are typed at exact introduction types, and every source judgment has a structural runtime counterpart.
* Pair subtyping is interpreted by finite semantic maps (`Realization`), since a syntactic canonical-forms argument fails for the widening rule.
* An earlier precise-store line (`Precise*`, `Canonical*`, `RefinedPathProgress`, `RuntimeConversion`) is kept. `Safety` runs through the `Structural*` line.

## Modules

### Syntax and typing

| module | contents |
|---|---|
| `FinFun` | finite renamings |
| `Syntax`, `Context` | scoped syntax and contexts |
| `Typing` | path typing, member typing, interval selection |
| `TypingInversion`, `ValueInversion` | inversion |
| `Renaming`, `Opening` | renaming and opening lemmas |

### Runtime

| module | contents |
|---|---|
| `Store`, `StoreRefinement` | the store and its precise refinement |
| `PathReduction`, `Lookup` | big-step path resolution |
| `Cont`, `State`, `Machine` | the CK machine |
| `RuntimeConversion`, `ScopedRuntimeEq` | store-justified path equations |
| `PreciseStore`, `StructuralPreciseStore` | exact store typing |
| `StructuralResolution` | resolution to term and type-definition endpoints |

### Metatheory

| module | contents |
|---|---|
| `Canonical`, `CanonicalForms` | canonical forms via realization maps |
| `PathFunctionality`, `PathPreservation`, `PathProgress` | path lookup under an exact store |
| `PreciseProgress`, `Progress`, `AdministrativePreservation`, `RefinedPathProgress` | the precise-store line |
| `Realization` | semantic maps for pair subtyping |
| `StructuralRuntimeTyping`, `StructuralRuntimeLemmas`, `StructuralTermTyping` | structural runtime judgments |
| `StructuralNarrowing`, `StructuralPathSubstitution` | narrowing and substitution |
| `StructuralConversionInversion`, `StructuralValueInversion` | inversion |
| `StructuralRealization`, `StructuralPreciseCanonical` | realization and observation interfaces |
| `StructuralPreciseProgress`, `StructuralPrecisePreservation`, `StructuralPreciseSafety` | the exact structural invariant |
| `StructuralApplicationBoundary`, `StructuralApplicationCompatibility` | application |
| `StructuralRefinedProgress`, `StructuralMachineInvariant` | refined stores and the machine invariant |
| `StructuralProgress`, `StructuralPreservation` | progress and preservation |
| `Safety` | the closed-program theorems |

### Examples

| module | contents |
|---|---|
| `Examples` | the dependent abstract-member pattern |
| `CounterexampleRegression` | the historical alias counterexample is blocked |

## Paper and build

`lambda_p.tex`. `lake build LambdaP`. Rocq port in `../../rocq/LambdaP`.
