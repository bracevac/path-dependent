# LambdaPCCI

`LambdaPCCI` is the self-contained intersection-and-union-type variant of the
capture-checking path-dependent-pair calculus. It defines its own intrinsically
scoped syntax, static semantics, store, path resolution, CK machine, and
soundness proof, leaving `LambdaPCC` unchanged as the baseline calculus.

The calculus has capturing types and a term-typing judgment that assigns a
use set, an upper bound on the capabilities used during evaluation. Capture
sets contain term paths and selections of abstract capture-set members.
Dependent function results and pair members may mention the bound argument or
first component, including in capture sets. Pairs support term members,
abstract type members, and abstract capture-set members; the latter two are
represented by lower and upper bounds.

The development proves:

- deterministic resolution of paths to locations, shape-type definitions,
  or capture-set definitions;
- binary intersections of shape types, interpreted as simultaneous
  realization at one store location;
- binary unions of shape types, interpreted as a tagged realization of one
  alternative at one store location;
- recursive, binder-aware merging of aligned same-label record spines, with
  member plans interpreted under the merged first-component type;
- conservative capture-aware merging: distinct capture annotations on first
  components or term members widen to `C ∪ D`, while their shapes are
  recursively merged or intersected;
- merging of abstract type-member intervals by joining their lower shapes and
  recursively merging their upper shapes, and of abstract capture-member
  intervals by joining distinct lowers when their upper bound agrees;
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

The capture union produced by a merge is a common upper bound, not a
capture-set intersection; it can therefore lose capture precision. Distinct
upper bounds on abstract capture members are not merged, because preserving
both would require capture-set intersection syntax. As with ordinary
subtyping, a merge supplies no target well-formedness proof; clients must
separately establish any resulting interval bounds.

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
member. `RecordRegression.lean` checks a right-nested record whose function
consumes a value at an earlier path-dependent type member.
`IntersectionRegression.lean` checks a closed self-application that uses one
closure through two incomparable function views with empty capture sets.
`RecordIntersectionRegression.lean` first checks two empty-capture aliases of
one record whose same stored member is used through incomparable function
views, then merges those views so one alias uses the member at both component
shapes. `TypeMemberIntersectionRegression.lean` merges two views of one
abstract type member and uses its selected type through the shared lower bound
and both merged upper views. `TypeMemberUnionRegression.lean` removes that
shared-lower restriction by merging the two lowers with a shape union.
`RecursiveRecordMergeRegression.lean` recursively merges a two-cell spine:
its inner abstract capture member joins lower bounds, while its outer term
member joins two distinct views of one genuinely captured capability and
intersects their shape views. The final selected member exposes that nonempty
capture union at an empty evaluation-use set before a closed self-application.

## Files

- `Syntax.lean`, `Context.lean`, and `Typing.lean`: source syntax, capture
  sets, static judgments, recursive merge plans, and term use sets.
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
- `CaptureRegression.lean`, `GeneralPairRegression.lean`, and
  `RecordRegression.lean`: checked examples for capture-set members, general
  dependent-pair covariance, and nested record lookup.
- `IntersectionRegression.lean`: capture-aware use of both projections of an
  opaque shape intersection.
- `RecordIntersectionRegression.lean`: a closed same-label record intersection
  with both a two-alias view and a merged one-alias view of the same member.
- `TypeMemberIntersectionRegression.lean`: a closed shared-lower abstract
  type-member merge, with empty captures and uses.
- `TypeMemberUnionRegression.lean`: the corresponding distinct-lower merge,
  with empty captures and uses.
- `RecursiveRecordMergeRegression.lean`: recursive capture-member and term-
  member merging with distinct dependent capture contracts.

## Building

From the repository root:

```sh
lake build LambdaPCCI
```
