# Soundness report

`LambdaP` now has a machine-checked finite-run type-safety proof. This note
records the argument that matters: where the original proof failed, the
counterexample found during that investigation, the changes made to the
calculus, and the structure of the successful proof.

## The calculus

The language is a small calculus of immutable dependent pairs. A pair has a
first component and either a term member or a type member; the type of the
second component may mention the first. Paths traverse first projections and
named members, and records are represented by chains of pairs. The source
language is in monadic normal form and executes on a CK machine with an
append-only store.

The calculus includes dependent functions, singleton types, abstract type
members with lower and upper bounds, subsumption, and primitive declarative
transitivity. It deliberately omits recursive objects, mutation,
intersections, and unions.

## Where the original proof failed

The first difficulty was preservation for big-step path resolution. A path
does not in general retain its *precise* synthesized type when it is replaced
by the location to which it resolves. For example, a projection may
synthesize a singleton type, while the resulting store location synthesizes
its context entry. The correct statement is weaker: under a well-typed store,
resolution preserves ordinary term typing of the endpoint.

That statement is still not strong enough with a store typing that records
locations at arbitrary supertypes. Application progress needs an inversion
principle saying that a location viewed as a function actually contains an
abstraction. The runtime invariant therefore records every location at the
syntax-directed type of the value allocated there. This *exact store*
invariant provides the needed connection between static typing and the shape
of stored values.

Exact stores repair the lookup argument, but they do not repair the original
calculus. Attempts to prove the resulting canonical-form lemma exposed a way
to derive false singleton equalities through abstract type selection. The same
derivation can be expressed entirely in the source language, yielding a
closed counterexample to progress.

## The counterexample

Let `f` be a function, let `q` be a pair containing the exact type definition
`A = Top`, and define

```text
h = lambda (z : q.A). q
```

The original rules accepted the body of `h` at the singleton type `{z}` using
the chain

```text
{q} <: Top <: q.A <: {z}.
```

The final step is invalid. The context says that `z` belongs to the abstract
type `q.A`; it does not say that `q.A` is the singleton of `z`. The original
syntax represented term singleton types and selected abstract types with the
same constructor, so the singleton-symmetry rule could not distinguish these
two readings.

The complete program is

```text
let f = lambda (x : Top). x in
let q = <f; A = Top> in
let h = lambda (z : q.A). q in
let r = h f in
r f
```

Typing assigns `h f` the singleton type `{f}`, although evaluation returns
`q`. Consequently `r f` is accepted as a function application, but at run
time `r` denotes a stored pair. The machine reaches an application whose
operator is not an abstraction and cannot step.

This is not a bad-bounds example: all intervals used in the derivation are
`Top..Top`. Nor does it depend on taking transitivity as primitive; any
ordinary transitivity lemma composes the displayed chain. The historical
calculus, derivation, and nine-step execution are checked in
`LambdaPHistory/SourceUnsoundnessCounterexample.lean`.

## Changes to the static semantics

The first change separates term singleton types `{p}` from abstract
selections `p.A`. Singleton symmetry now applies only when precise path typing
produces a term singleton. A variable of type `q.A` can no longer be used as
evidence that `q.A` and the variable are aliases. This directly blocks the
counterexample.

The second change is a conservative restriction on dependent-pair subtyping.
The natural rule would change both the first-component type and the dependent
member in one step. Its semantic interpretation must produce a member
coercion specialized to the pair's actual first component. The subtyping
derivation under an abstract binder does not itself provide finite evidence
for that specialization.

Several direct formulations reach the same obstruction. Keeping raw bound
derivations does not support recursive interpretation of selections; a
head-form inversion argument is not stable under transitivity; and a simple
step index does not resolve the contravariant use of lower bounds.
Proof-relevant coercion codes handle functions, selections, bounds, and
transitivity, but the unrestricted pair rule still requires a family of
coercions indexed by semantic inhabitants.

The proved calculus therefore separates pair subtyping into two operations:

1. the first-component type may be widened while the member is unchanged;
2. the member may change when the first component has singleton type `{p}`
   and an explicit premise compares the two members after opening them at
   `p`.

The opened premise is precisely the finite coercion evidence used by the
soundness proof. Primitive transitivity composes the two operations. These
rules still support the intended abstraction pattern: an exact type
definition can be hidden behind dependent abstract bounds and the first
component can then be widened.

There is no known counterexample to the unrestricted pair rule after
singletons and selections have been separated. Its admissibility remains an
open question; the current restriction should not be read as an unsoundness
result for that rule.

## Structure of the proof

The proof is direct and does not use inert contexts, tight typing, or another
DOT-specific stratification. Its preservation invariant has three main
ingredients.

First, the exact store context records the introduction type of every stored
value. Second, paths that resolve to the same location generate a
store-indexed equivalence used for conversion in proof-only structural typing
judgments. This accounts for the fact that reduction changes the spelling of
paths without changing what they denote. Third, structural subtyping is
interpreted by finite, proof-relevant coercion codes. Realized abstract
members retain coercions from their lower bound to the stored definition and
from the definition to their upper bound.

The fundamental lemma is proved under simultaneous substitution of source
variables by realized runtime paths. Its path part says that a well-typed path
resolves to an endpoint realizing its type. Its subtyping part says that a
subtyping derivation produces a coercion between realizations. Applying such
a coercion to the singleton of a store location yields the canonical forms
needed by the machine: a location used at function type contains an
abstraction, and a location used at pair type contains a pair.

Progress and preservation then follow by induction on the structural runtime
typing judgment. Allocation extends both the store and its intrinsic scope,
so finite-run preservation returns an extended context and the correspondingly
weakened result type. The source-facing theorem is the usual non-stuckness
statement:

> If a closed term is well typed and its initial state takes finitely many
> steps to a state `s`, then `s` is final or can take another step.

The theorem is `LambdaP.Tm.Ty.closed_type_safety` in `LambdaP/Safety.lean`.
The proof establishes neither termination nor normalization, and it leaves
declarative transitivity primitive. `LambdaP/Realization.lean` contains the
fundamental semantic argument; `LambdaPHistory` retains the failed calculus
and checked counterexample.
