# LambdaPCC

`LambdaPCC` is a self-contained capture-checking extension of the
path-dependent-pair calculus. It defines its own intrinsically scoped syntax,
static semantics, store, path resolution, CK machine, and soundness proof.

The calculus has capturing types and a term-typing judgment that assigns a
use set, an upper bound on the capabilities used during evaluation. Capture
sets contain term paths and selections of abstract capture-set members.
Dependent function results and pair members may mention the bound argument or
first component, including in capture sets. Pairs support term members,
abstract type members, and abstract capture-set members; the latter two are
represented by lower and upper
bounds. Dependent-pair covariance is uniform across term, type, and
capture-set members and compares the second component under the source
first-component type.

The development proves:

- deterministic resolution of paths to locations, shape-type definitions,
  or capture-set definitions;
- a source typing interpretation that preserves use sets;
- progress, one-step preservation, and finite preservation for
  the runtime typing invariant;
- closed type safety;
- application coverage for both operand paths of every application step
  reached by a closed execution; and
- a returned-value capture-set bound: the capture set assigned by the value's
  introduction rule subcaptures the capture set of its result type.

The public theorems are `Tm.Ty.closed_progress`,
`Tm.Ty.closed_finite_preservation`, `Tm.Ty.closed_type_safety`,
`Cap.Tm.Ty.closed_finite_application_coverage`, and
`Cap.Tm.Ty.closed_finite_returned_capture_bound`.

The runtime calculus has no primitive capability operations. Application
coverage therefore accounts for the paths inspected by function application,
while the development makes no platform-effect-safety claim. The capture set
recorded for a value is the one assigned by its introduction rule; the static
semantics does not require this set to be minimal.

`CaptureRegression.lean` checks abstract capture-set-member selection,
capture-set-member pair covariance, capture-dependent result types, and root
contraction for term paths. `GeneralPairRegression.lean` gives closed
allocation traces for general dependent-pair covariance at both
interval-member forms and for lower/upper selection of a stored capture-set
member.

## Files

- `Syntax.lean`, `Context.lean`, and `Typing.lean`: source syntax, capture
  sets, static judgments, and term use sets.
- `Runtime.lean` and `StoreStratification.lean`: stores, generalized path
  resolution, the CK machine, and allocation-order lemmas.
- `RuntimeEquality.lean` and `Valuation.lean`: runtime path equality,
  conversion, and binder-aware valuations.
- `CaptureEvidence.lean`, `CaptureAction.lean`, `CaptureStatic.lean`, and
  `CaptureCoercion.lean`: annotated stores, location and value typing,
  store-indexed subcapturing, and coercions.
- `CaptureWeakening.lean`, `CaptureAllocation.lean`, and
  `CaptureTyping.lean`: store extension, allocation, and the joint
  type-and-use machine invariant.
- `CaptureInterpretation.lean`, `CapturePreservation.lean`, and
  `CaptureSafety.lean`: source interpretation, progress, one-step and finite
  preservation, and closed type safety.
- `CaptureBounds.lean`: application coverage and the returned-value
  capture-set bound.
- `CaptureRegression.lean` and `GeneralPairRegression.lean`: checked examples
  for capture-set members and general dependent-pair covariance.
- `paper/`: paper-style presentation of the calculus and proof.

## Building

From the repository root:

```sh
lake build LambdaPCC
```

Build the version-local report with:

```sh
make -C lean/LambdaPCC/paper
```
