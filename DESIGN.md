# LambdaP design

This note records the design choices that matter to the formal result. The
paper in `lambda_p.tex` gives the full rules and proof sketch;
`docs/proof-history.md` explains how the current system was reached.

## Scope

`LambdaP` isolates paths and dependent pair members. It is not a DOT
formalization. The source language has:

- immutable dependent pairs;
- term members and exact type definitions;
- term singleton types and selected abstract types;
- dependent functions;
- paths through first projections and named members; and
- monadic-normal-form terms with an allocation-explicit CK machine.

There are no recursive objects, recursive allocation, mutation,
intersections, unions, or unrestricted source evaluation contexts.

The mechanization uses intrinsically scoped syntax. A single `Fin n`
namespace represents source variables and allocated store locations. Store
extension weakens existing terms, types, and continuations into the new scope.

## Static semantics

### Generalized pair members

Pairs have one uniform form:

```text
<x : S; a : tau^k>
```

The kind `k` distinguishes a term member from a type member. A term member
has a proper type. A type member has an interval `L..U`. The binder `x`
is in scope in the member signature.

Paths synthesize generalized types with the precise judgment
`Gamma |- p :: tau`. A matching selection opens the member at `p.1`. A
missed label continues at `p.1.a`, reflecting the representation of records
as pair chains.

### Singletons are not selections

`Ty.Single p`, written `{p}`, is a term singleton. `Ty.TSel p A`,
written `p.A`, is an abstract type selection. They are separate syntax and
have separate well-formedness rules.

This is a soundness condition, not merely a presentation choice. The
historical calculus used one constructor for both notions, which allowed
singleton symmetry to turn a binding `z : q.A` into the false relation
`q.A <: {z}`. `LambdaPHistory/SourceUnsoundnessCounterexample.lean`
contains a closed, well-typed program that exploits this relation and becomes
stuck.

### Dependent pair subtyping

The calculus replaces the natural unrestricted pair rule with two rules:

1. `pair_fst` widens the first component and leaves the member unchanged.
2. `pair_single_member` changes the member when the first component is
   `{p}`. It records the comparison both below the singleton binder and
   after opening both members at `p`.

Primitive transitivity composes these operations. The rules validate the
intended sealing pattern:

```text
<x : {p}; A : {p}..{p}>
  <: <x : {p}; A : Bot..{x}>
  <: <x : P;   A : Bot..{x}>
```

The examples are checked in `LambdaP/Examples.lean`.

The unrestricted rule for the syntax-separated calculus is an open question.
No counterexample is known. The restriction is used because a direct
realization proof needs a member coercion specialized to the run-time first
component; the opened premise of `pair_single_member` supplies finite proof
evidence for that coercion.

### Bounds and transitivity

Abstract selection, interval well-formedness, and interval subtyping retain
explicit nonempty-bounds premises. Declarative subtyping includes primitive
transitivity. The safety theorem does not depend on proving transitivity
admissible.

## Dynamics

A store is an immutable, append-only sequence of values. Stored values may
refer only to earlier cells. Big-step path resolution returns the location
denoted by a term path. Matching term members return their stored location;
a missed label resumes lookup at the pair's first component.

Machine states are `<store, continuation, term>`. Monadic normal form leaves
only let frames. The six transitions are application, path normalization,
let-frame push, return of an existing location, allocation of a syntactic
value, and ascription erasure.

A state is final when its continuation is empty and its term is a valid store
location or a syntactic value.

## Soundness invariant

Literal source typing is not the preservation invariant for intermediate CK
states. The proof uses the following layers.

1. **Exact stores.** Each allocated cell is recorded at its syntax-directed
   value-introduction type. Value inversion and narrowing justify allocation.
2. **Run-time path equality.** Paths that resolve to the same store location
   generate a congruence. A scoped lift carries this relation below binders
   without giving the fresh variable equations from the old scope.
3. **Structural run-time judgments.** Proof-only path, subtyping, term, and
   continuation judgments expose source constructors and admit conversion by
   run-time path equality. Source derivations embed into them.
4. **Generalized endpoints.** Proof-level path resolution may return a value
   location or a stored type definition. Its term fragment agrees with source
   path resolution.
5. **Semantic maps.** `Tau.SemMap` is a finite, proof-relevant code for a
   semantic coercion. Realized intervals store a lower map into the concrete
   definition and an upper map out of it.
6. **Fundamental lemma.** Under a semantically realized simultaneous path
   substitution, structural path checking produces a realizing endpoint and
   structural subtyping produces a semantic map.
7. **Canonical forms.** Acting on the realization of a location singleton
   exposes the stored function or pair, including the function-signature
   residuals needed by beta preservation.

The source-facing theorem is
`LambdaP.Tm.Ty.closed_type_safety`: every endpoint of a finite execution of
a closed, well-typed source term is final or can step. Finite-run preservation
returns an extended exact context and a weakened result type because
allocation changes the intrinsic scope.

The development does not prove termination, normalization, algorithmic
typing, inference, admissibility of transitivity, or machine-step
determinism. Path resolution itself is deterministic.

## Code map

- `LambdaP/Syntax.lean`, `Context.lean`, `Typing.lean`: source system.
- `LambdaP/PathReduction.lean`, `Machine.lean`, `State.lean`: dynamics.
- `LambdaP/RuntimeConversion.lean`, `ScopedRuntimeEq.lean`: run-time
  conversion.
- `LambdaP/StructuralPreciseStore.lean`: exact state invariant.
- `LambdaP/Realization.lean`: semantic maps and fundamental lemma.
- `LambdaP/CanonicalForms.lean`: unconditional canonical forms.
- `LambdaP/Safety.lean`: source-facing progress, preservation, and safety.
- `LambdaPHistory/`: historical calculus and counterexamples; it is not
  imported by the canonical library.
