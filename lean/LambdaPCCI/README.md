# LambdaPCCI

`LambdaPCCI` is `../LambdaPCC` with binary intersection and union types.
It is self-contained and leaves `LambdaPCC` unchanged as the baseline.
Intersections of shapes are realized simultaneously at one store location
and unions as a tagged realization of one alternative, as in
`../LambdaPFCI`, and aligned record spines are merged by a recursive,
binder-aware plan interpreted under the merged first-component type. The
merge is capture-aware and conservative: distinct capture annotations on
first components or term members widen to their union while the shapes are
merged or intersected, abstract type-member intervals join their lower
shapes and merge their upper shapes, and abstract capture-member intervals
join distinct lower bounds when their upper bound agrees.

The union produced by a merge is a common upper bound, not a capture-set
intersection, so a merge can lose capture precision. Distinct upper bounds
on abstract capture members are not merged, since keeping both would need
capture-set intersection syntax. A merge supplies no well-formedness proof
for its result. As in `LambdaPCC`, the runtime has no primitive capability
operations and the recorded capture set of a value is the one assigned by
its introduction rule.

## Main theorems

All depending on `propext` and `Quot.sound` only.

```
Tm.Ty.closed_progress                          the initial state progresses                        (CaptureSafety)
Tm.Ty.closed_finite_preservation               every reached state keeps joint type-and-use evidence (CaptureSafety)
Tm.Ty.closed_type_safety                       no finite run of a closed well-typed term gets stuck (CaptureSafety)
Cap.Tm.Ty.closed_finite_application_coverage   both operand paths of every application step are covered by the transported use set (CaptureBounds)
Cap.Tm.Ty.closed_finite_returned_capture_bound the capture set assigned to a returned value subcaptures that of its result type (CaptureBounds)
```

## Modules

| module | contents |
|---|---|
| `FinFun` | finite renamings between scopes |
| `Syntax`, `Context`, `Typing` | syntax with capture sets and member kinds, contexts, path typing, subtyping, capture-aware recursive merge plans, term typing with use sets |
| `Runtime`, `StoreStratification` | stores, generalized path resolution, the CK machine, allocation-order lemmas |
| `RuntimeEquality`, `Valuation` | proof-relevant runtime path equality and type conversion, valuations |
| `CaptureEvidence`, `CaptureAction`, `CaptureStatic`, `CaptureCoercion` | capture-aware evidence, composition and capture relations, environments and the compilation of subtyping, action of coercions and merge plans |
| `CaptureWeakening`, `CaptureAllocation`, `CaptureTyping` | weakening across a fresh cell, valid store entries, the joint type-and-use invariant |
| `CaptureInterpretation`, `CapturePreservation`, `CaptureSafety` | interpretation of source typing, progress and one-step preservation, finite preservation and closed type safety |
| `CaptureBounds` | application coverage and the returned-value capture bound |
| `CaptureRegression`, `GeneralPairRegression`, `RecordRegression` | the regressions of `LambdaPCC` |
| `IntersectionRegression` | a closed self-application through two incomparable function views with empty capture sets |
| `RecordIntersectionRegression` | two empty-capture aliases of one record, then one merged alias using the member at both shapes |
| `TypeMemberIntersectionRegression` | a shared-lower abstract type-member merge with empty captures and uses |
| `TypeMemberUnionRegression` | the distinct-lower merge, with a shape union |
| `RecursiveRecordMergeRegression` | a recursive merge of a two-cell spine joining a capture member's lower bounds and two views of a captured capability |

The regressions are hand-built derivations, the last five mirroring those
of `../LambdaPFCI` with capture annotations.

## Building

From the repository root, `lake build LambdaPCCI`. There is no paper for
this variant. `../LambdaPCC/paper/` covers the baseline.
