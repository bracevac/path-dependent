# LambdaPFCI

`../LambdaPFC` plus binary intersection and union types, self-contained. An intersection is realized at one store location, a union as a tagged alternative, and two views of one record spine are merged by a recursive plan (`Tau.Merge`). A merge gives no well-formedness proof for its result.

## Main theorems

Axioms: `propext`, `Quot.sound`.

```
Tm.Ty.interpret                   fundamental theorem      (SemanticFundamental)
State.Evidence.progress                                    (SemanticProgress)
State.Evidence.preservation                                (SemanticPreservation)
Tm.Ty.closed_progress                                      (SemanticSafety)
Tm.Ty.closed_finite_preservation                           (SemanticSafety)
Tm.Ty.closed_type_safety          no finite run gets stuck (SemanticSafety)
```

## Modules

| module | contents |
|---|---|
| `FinFun` | finite renamings |
| `Syntax`, `Context`, `Typing` | scoped syntax, contexts, static semantics with intersections, unions, merges |
| `Runtime`, `StoreStratification` | stores, path resolution, the CK machine, allocation order |
| `RuntimeEquality`, `Valuation` | runtime path equality, valuations |
| `SemanticEvidence`, `SemanticAction`, `SemanticTyping` | coercions, their action, runtime typing |
| `SemanticWeakening`, `SemanticTypingWeakening`, `SemanticAllocation` | weakening and allocation |
| `SemanticFundamental`, `SemanticProgress`, `SemanticPreservation`, `SemanticSafety` | fundamental theorem, progress, preservation, safety |
| `GeneralPairRegression`, `RecordRegression` | the `LambdaPFC` regressions |
| `IntersectionRegression`, `RecordIntersectionRegression`, `AlignedRecordIntersectionRegression`, `RecursiveRecordMergeRegression` | intersections and merges |
| `TypeMemberIntersectionRegression`, `TypeMemberUnionRegression` | abstract-member merges |

## Paper and build

`lambda_p.tex`. `lake build LambdaPFCI`.
