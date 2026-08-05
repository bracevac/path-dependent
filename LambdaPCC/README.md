# LambdaPCC

`LambdaPCC` is a self-contained capture-checking extension of the
path-dependent-pair calculus. It defines its own intrinsically scoped syntax,
static semantics, store, path resolution, CK machine, and soundness proof.

The calculus has capture-annotated types and a term-typing judgment that
records the paths used by a term. Capture sets contain proper paths and
selections of abstract capture-set members. Dependent function results and
pair members may mention the bound argument or first component, including in
capture sets. Pairs support term members, abstract type members, and abstract
capture-set members; the latter two are represented by lower and upper
bounds. Dependent-pair covariance is kind-generic and compares the second
component under the source first-component type.

The development proves:

- deterministic resolution of paths to locations, stored types, or stored
  capture sets;
- context-respecting renaming and weakening for all static judgments;
- preservation of type- and capture-interval consistency by member
  subtyping;
- a joint type-and-use interpretation of source typing derivations;
- progress, heterogeneous one-step preservation, and finite preservation for
  the qualifier-aware CK-machine invariant;
- closed type safety;
- use prediction for both operand paths of every application step reached by
  a closed execution; and
- capture prediction for final results: the qualifier retained when the
  returned value was introduced subcaptures the outer qualifier of its
  result type.

The public theorems are `Tm.Ty.closed_progress`,
`Tm.Ty.closed_finite_preservation`, `Tm.Ty.closed_type_safety`,
`Cap.Tm.Ty.closed_finite_use_prediction`, and
`Cap.Tm.Ty.closed_finite_capture_prediction`.

The runtime calculus has no primitive capability operations. Use prediction
therefore accounts for the paths inspected by function application, while the
development makes no platform-effect-safety claim. A value's introduction
qualifier is the qualifier retained by its typing derivation; the static
semantics does not require this qualifier to be minimal.

`CaptureRegression.lean` checks abstract capture-member selection,
capture-kind pair covariance, capture-dependent result types, and root
accounting for proper term paths. `GeneralPairRegression.lean` gives closed
allocation traces for general dependent-pair covariance at both
abstract-member kinds and for lower/upper selection of a stored capture-set
member.

## Files

- `Syntax.lean`, `Context.lean`, and `Typing.lean`: source syntax, capture
  sets, static judgments, and term use sets.
- `StaticMetatheory.lean`: renaming and weakening of the static semantics.
- `Runtime.lean` and `StoreStratification.lean`: stores, generalized path
  resolution, the CK machine, and allocation-order lemmas.
- `RuntimeEquality.lean` and `Valuation.lean`: runtime path equality,
  conversion, and binder-aware valuations.
- `CaptureEvidence.lean`, `CaptureAction.lean`, `CaptureStatic.lean`, and
  `CaptureCoercion.lean`: qualifier-aware worlds,
  evidence, subcapturing relations, and coercions.
- `CaptureWeakening.lean`, `CaptureAllocation.lean`, and
  `CaptureTyping.lean`: store extension, allocation, and the joint
  type-and-use machine invariant.
- `CaptureInterpretation.lean`, `CapturePreservation.lean`, and
  `CaptureSafety.lean`: source interpretation, progress, one-step and finite
  preservation, and closed type safety.
- `CapturePrediction.lean`: application-operand use prediction and
  final-result capture prediction.
- `CaptureRegression.lean` and `GeneralPairRegression.lean`: checked examples
  for capture members and general dependent-pair covariance.
- `lambda_p.tex`: paper-style presentation of the calculus and proof.

## Building

From the repository root:

```sh
lake build LambdaPCC
```

Build the version-local report with:

```sh
latexmk -cd -pdf LambdaPCC/lambda_p.tex
```
