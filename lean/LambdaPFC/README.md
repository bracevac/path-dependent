# LambdaPFC

Paths through immutable dependent pairs with the general covariant pair rule. A pair member is a term with a proper type or a type member with an interval, and may depend on the first component. Typing is proof-relevant.

## Main theorems

In `SemanticSafety.lean`. Axioms: `propext`, `Quot.sound`.

```
Tm.Ty.closed_progress
Tm.Ty.closed_finite_preservation
State.Steps.preservation
Tm.Ty.closed_type_safety          no finite run gets stuck
```

## Design

* Subtyping derivations compile to store-local coercions (`Tau.Sub.compile`) acting on realizations at store referents.
* Dependent premises (function codomains, pair members) are suspended as closures until the store supplies the location.
* Coercion action terminates by the allocation order of the store (`StoreStratification`), then by coercion size.
* Runtime typing normalizes subsumption into one coercion per constructor (`TermEvidence`).

## Modules

| module | contents |
|---|---|
| `FinFun` | finite renamings |
| `Syntax`, `Context`, `Typing` | scoped syntax, contexts, static semantics |
| `Runtime`, `StoreStratification` | stores, path resolution, the CK machine, allocation order |
| `RuntimeEquality`, `Valuation` | runtime path equality, valuations |
| `SemanticEvidence`, `SemanticAction`, `SemanticTyping` | coercions, their action, runtime typing |
| `SemanticWeakening`, `SemanticTypingWeakening`, `SemanticAllocation` | weakening and allocation |
| `SemanticFundamental` | the fundamental theorem |
| `SemanticProgress`, `SemanticPreservation`, `SemanticSafety` | progress, preservation, safety |
| `GeneralPairRegression`, `RecordRegression` | regressions |

## Paper and build

`lambda_p.tex`. `Metatheory.md`, `MetatheorySlides.md` are notes. `lake build LambdaPFC`. Rocq port in `../../rocq/LambdaPFC`.
