# LambdaPFCI

`LambdaPFCI` is the self-contained intersection-and-union-type variant of
`LambdaPFC`.
It contains its own intrinsically scoped syntax, declarative static semantics,
store, generalized path resolution, and CK machine, leaving `LambdaPFC`
unchanged as the baseline calculus. The static judgments are proof-relevant,
and the soundness proof interprets their derivations as store-local semantic
evidence.

The development proves:

- deterministic path resolution to location and type-definition referents;
- binary intersections of proper types, interpreted as simultaneous
  realization at one store location;
- binary unions of proper types, interpreted as a tagged realization of one
  alternative at one store location;
- merging of same-label term-member record views into one view whose member
  retains the intersection of their proper types;
- merging aligned first-component views of one pair, allowing intersections
  of same-layout record telescopes to normalize to one selectable spine;
- merging of same-first-component, same-label abstract type-member views with
  arbitrary lower bounds into one interval whose lower bound is their union
  and whose upper bound is their intersection;
- binder-dependent subtyping for function results and pair members;
- a finite semantic interpretation of every declarative subtyping derivation;
- a fundamental theorem for path typing, subtyping, and term typing under
  store valuations;
- progress and heterogeneous one-step preservation for the CK machine; and
- non-stuckness of the last state of every finite execution of a closed, well-typed
  program.

The main result is `Tm.Ty.closed_type_safety` in `SemanticSafety.lean`.

## Proof structure

An `Environment` maps each source variable to a store location that realizes
its renamed type. `Path.Ty.resolve` interprets typed paths, and
`Tau.Sub.compile` turns subtyping derivations into finite store-local
`Coercion` evidence.

`Store.Possible` and `Path.Referent.Realizes` describe the observations
available at a path referent. Coercion action
preserves these observations. Function codomain coercions and body typings are
closed over their source environments and instantiated when execution supplies
the argument location. A `MemberClosure` similarly retains a dependent-member
subtyping derivation until a stored pair supplies its first-component
location. Coercions serve as semantic evidence in the proof; the source and
runtime syntax are defined in `Syntax.lean` and `Runtime.lean`.

For a dependent pair, the comparison of member signatures is suspended until
the first component has a concrete store location. Its termination follows
from the append-only store order: a pair's first component and member referent
are older than the pair cell. The mechanization uses referent stratum as the
primary termination measure and coercion-tree size for recursive calls at the
same referent.

`TermEvidence` normalizes subsumption into a final coercion at each runtime
constructor. This yields direct inversion for progress and preservation.
Allocation weakens all old evidence and records the corresponding weakening of
the final result type through `Ty.Extends`.

## Files

- `Syntax.lean`, `Context.lean`, and `Typing.lean`: source calculus.
- `Runtime.lean` and `StoreStratification.lean`: stores, path resolution, the
  CK machine, and the allocation-order lemmas used by coercion action.
- `RuntimeEquality.lean` and `Valuation.lean`: runtime path equality,
  conversion, and binder-aware valuations.
- `SemanticEvidence.lean`, `SemanticAction.lean`, and
  `SemanticTyping.lean`: finite coercions, their interpretation, and the
  runtime invariant.
- `SemanticWeakening.lean`, `SemanticTypingWeakening.lean`, and
  `SemanticAllocation.lean`: binder instantiation and store extension.
- `SemanticFundamental.lean`, `SemanticProgress.lean`,
  `SemanticPreservation.lean`, and `SemanticSafety.lean`: the fundamental
  theorem and type safety.
- `GeneralPairRegression.lean`: proper-member and interval-member regression
  examples for dependent pair subtyping.
- `RecordRegression.lean`: a closed three-member record spine whose function
  consumes a value at an earlier path-dependent type member.
- `IntersectionRegression.lean`: a closed self-application that uses one
  closure through two incomparable function views of an intersection.
- `RecordIntersectionRegression.lean`: a closed same-label record intersection
  that first selects one stored member through two aliases, then merges the
  views so one alias uses the member at both incomparable component types.
- `AlignedRecordIntersectionRegression.lean`: a closed two-member telescope
  whose aligned outer views merge their record tails, normalize the older
  member, and select it through the outer member with one precise alias.
- `TypeMemberIntersectionRegression.lean`: a closed abstract-member merge whose
  selected type is used through its shared lower bound and both merged upper
  views.
- `TypeMemberUnionRegression.lean`: a closed abstract-member merge with
  distinct lower bounds, using their union through selection and both
  components of the intersected upper bound.

## Building

From the repository root:

```sh
lake build LambdaPFCI
```

The paper presentation for this proof is `lambda_p.tex`. From the repository
root it can be rebuilt with:

```sh
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error \
  lean/LambdaPFCI/lambda_p.tex
```
