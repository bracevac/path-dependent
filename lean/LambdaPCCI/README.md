# LambdaPCCI

`../LambdaPCC` plus binary intersection and union types, self-contained. Merges are capture-aware and conservative: distinct capture annotations widen to their union, so precision can be lost, and distinct upper bounds on capture members are not merged.

## Main theorems

Axioms: `propext`, `Quot.sound`.

```
Tm.Ty.closed_progress                                                    (CaptureSafety)
Tm.Ty.closed_finite_preservation                                         (CaptureSafety)
Tm.Ty.closed_type_safety                        no finite run gets stuck (CaptureSafety)
Cap.Tm.Ty.closed_finite_application_coverage                             (CaptureBounds)
Cap.Tm.Ty.closed_finite_returned_capture_bound                           (CaptureBounds)
```

## Modules

| module | contents |
|---|---|
| `FinFun` | finite renamings |
| `Syntax`, `Context`, `Typing` | syntax with capture sets, contexts, subtyping, merge plans, term typing with use sets |
| `Runtime`, `StoreStratification` | stores, path resolution, the CK machine, allocation order |
| `RuntimeEquality`, `Valuation` | runtime path equality, valuations |
| `CaptureEvidence`, `CaptureAction`, `CaptureStatic`, `CaptureCoercion` | capture-aware evidence, coercions, merge plans |
| `CaptureWeakening`, `CaptureAllocation`, `CaptureTyping` | weakening, allocation, the type-and-use invariant |
| `CaptureInterpretation`, `CapturePreservation`, `CaptureSafety` | interpretation, preservation, safety |
| `CaptureBounds` | coverage and the returned-value bound |
| `CaptureRegression`, `GeneralPairRegression`, `RecordRegression` | the `LambdaPCC` regressions |
| `IntersectionRegression`, `RecordIntersectionRegression`, `RecursiveRecordMergeRegression` | intersections and merges |
| `TypeMemberIntersectionRegression`, `TypeMemberUnionRegression` | abstract-member merges |

## Build

`lake build LambdaPCCI`. No paper. `../LambdaPCC/paper/` covers the baseline.
