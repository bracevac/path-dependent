# LambdaPCC

`../LambdaPFC` plus capture checking. Types carry capture sets, term typing assigns a use set, and pairs may have abstract capture-set members. Capture sets hold paths of any length and capture-set selections. The runtime has no capability primitives, so coverage is about the paths inspected by application.

## Main theorems

Axioms: `propext`, `Quot.sound`.

```
Tm.Ty.closed_progress                                                    (CaptureSafety)
Tm.Ty.closed_finite_preservation                                         (CaptureSafety)
Tm.Ty.closed_type_safety                        no finite run gets stuck (CaptureSafety)
Cap.Tm.Ty.closed_finite_application_coverage    operands are covered by the use set (CaptureBounds)
Cap.Tm.Ty.closed_finite_returned_capture_bound  a returned value's capture set is below its type's (CaptureBounds)
```

## Modules

| module | contents |
|---|---|
| `FinFun` | finite renamings |
| `Syntax`, `Context`, `Typing` | syntax with capture sets, contexts, subcapturing, subtyping, term typing with use sets |
| `Runtime`, `StoreStratification` | stores, path resolution, the CK machine, allocation order |
| `RuntimeEquality`, `Valuation` | runtime path equality, valuations |
| `CaptureEvidence`, `CaptureAction`, `CaptureStatic`, `CaptureCoercion` | capture-aware evidence and coercions |
| `CaptureWeakening`, `CaptureAllocation`, `CaptureTyping` | weakening, allocation, the type-and-use invariant |
| `CaptureInterpretation`, `CapturePreservation`, `CaptureSafety` | interpretation, preservation, safety |
| `CaptureBounds` | coverage and the returned-value bound |
| `CaptureRegression`, `GeneralPairRegression`, `RecordRegression` | regressions |

## Paper and build

`paper/`, built with `make -C lean/LambdaPCC/paper`. `lake build LambdaPCC`. Rocq port in `../../rocq/LambdaPCC`.
