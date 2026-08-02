# Soundness investigation and proof history

The current `LambdaP` calculus has an unconditional finite-run type-safety
proof. This report records why its historical predecessor was unsound, which
direct proof attempts failed, and which two static changes lead to the proved
system.

## Result

The final pre-restart calculus is not type safe as stated.  There is a closed
term of type `Top` which takes nine machine steps to an application whose
operator is a stored pair.  The resulting state is neither final nor able to
step.  The complete source typing derivation and execution are checked in
`LambdaPHistory/SourceUnsoundnessCounterexample.lean`; the summary theorem is
`closed_source_unsoundness`.

This is a counterexample to soundness of the source calculus, rather than a
failure of a particular proof invariant.  Consequently no proof of the
historical progress-and-preservation statement can be completed without
changing a static rule or restricting the language.

## Baseline

The reconstruction uses commit `8c6a06d`, the last snapshot before the 2026
mechanization restart.  Its main judgments are:

```text
Γ ⊢ p :: τ          precise path typing
Γ ⊢ τ₁ <: τ₂        generalized subtyping
Γ ⊢ τ wf            well-formedness
Γ ⊢ t : T           term typing
```

The second component of a dependent pair is scoped over the first.  It can be
a term member or an abstract type member with bounds `L..U`; concrete type
definitions receive exact bounds `T..T`.  Selection opens the component with
the first projection.  The lower- and upper-bound subtyping rules, interval
formation, and interval subtyping all retain the historical nonemptiness
premises.  Declarative transitivity also remains primitive.

The reconstruction changes no typing or reduction rule.  It only replaces the
historical implementation of opening with standard capture-avoiding
substitution: the old definition substituted the wrong variable underneath a
nested binder.  All files under `LambdaPHistory` are checked without
   `sorry` or user-declared axioms.

## Closed counterexample

Let `f` be an ordinary stored function and let `q` be a pair with an exact type
member `A = Top`.  Thus precise selection gives:

```text
Γ ⊢ q.A :: Top..Top
```

Now define a dependent function `h` whose argument has type `q.A` and whose
declared result is the singleton of its argument:

```text
h = λ(z : q.A). q
```

The body is accepted because the source subtyping rules derive:

```text
{q} <: Top <: q.A <: {z}
```

The last edge is the crucial one.  Since the context binds `z : q.A`, precise
variable typing supplies the premise of `Tau.Sub.symm`, and that rule concludes
`q.A <: {z}`.

The function `f` is accepted as an argument to `h`:

```text
{f} <: type(f) <: Top <: q.A
```

Dependent application therefore assigns `h f` the result type `{f}`, although
evaluation of the body returns the location `q`.  The complete closed program
is, schematically:

```text
let f = (λ(x : Top). x) in
let q = <f, A = Top> in
let h = (λ(z : q.A). q) in
let r = h f in
r f
```

Statically, `r : {f}`, so singleton widening exposes the function type stored
at `f` and validates `r f`.  Dynamically, `r` is replaced by `q`.  The machine
reaches `q f`; lookup finds a pair at `q`, while the application rule requires
an abstraction.  No transition applies.

The Lean development proves all four parts separately and packages them in
`closed_source_unsoundness`:

1. the initial empty-store state has source type `Top`;
2. a heterogeneous nine-step trace reaches the displayed endpoint;
3. the endpoint is not final; and
4. the endpoint has no successor state.

Every bound used in the example is `Top..Top`, and every nonemptiness side
condition is discharged by reflexivity.  The example therefore does not
exploit bad bounds.  It also does not depend on whether transitivity is proved
admissible or included as a declarative rule: the displayed chain can be
composed by any ordinary transitivity lemma.

## Static cause

The historical syntax uses one constructor, `Ty.Single p`, for two different
notions:

- the singleton type of a term-denoting path, written `{p}`; and
- a selected abstract type, written `p.A`, when the path has interval kind.

Singleton symmetry is valid for aliases: if a term path `p` has singleton type
`{q}`, then `p` denotes the same value as `q`.  It is not valid when the type
in that premise is an abstract selection.  From `z : q.A` one may conclude
that `z` belongs to `q.A`; one may not conclude that `q.A` is the singleton
`{z}`.  Because both forms are represented by `Ty.Single`, `Tau.Sub.symm`
cannot distinguish those cases.

The dependent result of `h` is what turns this local mistake into a closed
failure.  It exports the false equality as `{f}`.  A later `let` consumes that
type in a fresh source derivation and treats the pair returned by `h` as the
function `f`.  Strengthening only the store invariant cannot prevent this:
all three allocated values have their exact introduction types.

## Proof-attempt log

The investigation proceeded directly from the source judgments; it did not
import inert contexts, tight typing, step indexing, or another DOT/System D
proof discipline.

1. **Reconstruction and binding lemmas.**  The pre-restart syntax, contexts,
   source judgments, store, continuation, and CK machine were restored under
   `LambdaPHistory`.  Renaming, weakening, simultaneous path substitution,
   and opening laws are machine checked.

2. **Big-step path lookup.**  `Path.lookup_iff_reduce` proves that the two
   historical presentations of big-step lookup agree, including recursive
   missed-label lookup.  The literal claim that resolution preserves the same
   *precise* synthesized type is false: a projection may synthesize a
   singleton while the resulting store variable synthesizes its context
   entry.  The useful theorem `Path.reduce_preserves_typing` instead recovers
   ordinary term typing of the result.  Under an exact store,
   `State.Ty.path_step_precise_preservation` proves preservation for the
   machine's path-normalization step.

3. **Publicly widened stores.**  Historical `Store.Ty` permits a value to be
   recorded at a supertype.  A checked two-cell example in
   `LookupCounterexample.lean` shows that the literal historical preservation
   theorem for arbitrary typed states already fails at path normalization.
   That example is not closed and does not itself refute program safety; it
   motivated keeping exact introduction types in the runtime invariant.

4. **Opening and the machine cases.**  A structural, proof-only version of
   path checking and subtyping was used to test the remaining proof.  Standard
   renaming, narrowing, dependent opening, lookup replacement, allocation,
   continuation, `let`, and ascription cases were proved.  Application
   preservation and progress reduced to canonical-form properties for exact
   store entries.

5. **Failure of the proposed canonical invariant.**  Exact store typing alone
   does not validate the broad structural canonical-form property.  The
   checked examples in `StructuralPrecisePushbackCounterexample.lean` and
   `StructuralPreciseFunctionPushbackCounterexample.lean` show how promotion,
   abstract selection, and singleton symmetry can make a pair appear to have
   a function head and can falsify function-domain inversion.  At first this
   could still have been an over-permissive proof judgment rather than a source
   problem.

6. **Staging the same derivation in the source language.**  The dependent
   function `h` above recreates the problematic use of symmetry using only
   historical source rules.  Its result type transports the false singleton
   relation across an application, after which the final source `let` exposes
   the stuck call.  This closes the distinction left open by the structural
   examples: the source calculus itself is unsound.

## First repair: separate singletons and selections

The first repair is to give term singleton types and abstract type selections
different syntax and different well-formedness rules, for example `single p`
and `tsel p A`.  Then singleton symmetry is stated only for `single`; a
variable of type `tsel q A` cannot trigger it.  This is the distinction made
in `LambdaP`, and here it is justified by a concrete source
counterexample rather than by a desire to imitate DOT.  The checked theorems
`historical_body_subtyping_blocked` and
`selection_to_argument_singleton_blocked` in
`CounterexampleRegression.lean` show that the crucial final edges of the
historical counterexample are no longer derivable.

A smaller but less transparent repair would retain the shared syntax and add
a premise to `Tau.Sub.symm` requiring its inner path `q` to have a proper,
term-denoting classification:

```text
Γ ⊢ p :: {q}    Γ ⊢ q :: U
-------------------------
Γ ⊢ {q} <: {p}
```

The second premise fails for the interval-kinded path `q.A` in the
counterexample.  Neither repair is silently applied to the historical
reconstruction.  The remainder of this report concerns the separate
`LambdaP` development, which implements the syntax split.

## Soundness proof for the current calculus

### A second, conservative restriction

The syntax split blocks the known counterexample, but the direct soundness
proof exposed a separate difficulty in the historical pair-subtyping rule:

```text
Γ ⊢ S <: S'      Γ, x:S ⊢ d <: d'
------------------------------------
Γ ⊢ Pair S a d <: Pair S' a d'
```

To interpret the conclusion, a runtime pair whose first component realizes
`S` must be shown to realize `d'` after substituting that component for `x`.
The required member coercion depends on semantic evidence for that runtime
component.  Storing it as a function gives a negative occurrence in the
mutually inductive realization relation; storing only the raw subtyping
derivation leaves no structurally smaller semantic coercion when the pair is
later used.

Several direct proof designs were checked before changing the rule:

1. A relation recording only raw lower- and upper-bound derivations gets stuck
   at `sel_lo` and `sel_hi`: interpreting the stored bound is not a recursive
   call on the current derivation.
2. A head-only canonical-form argument does not survive arbitrary
   transitivity and abstract selections.
3. A simple step-indexed relation loses an index when following a selection,
   and interval subtyping needs the lower-bound coercion in the opposite
   variance position.
4. Defunctionalized, proof-relevant coercions handle conversion, functions,
   selections, bounds, and transitivity, but the unrestricted pair rule still
   requires a family of member coercions indexed by semantic inhabitants.
5. Explicit derivation ranks do not give a decreasing measure: a selection
   may continue through bound evidence whose rank is unrelated to the current
   pair derivation.

These failures are not a counterexample to the syntax-split calculus, and the
report does not claim that the unrestricted rule is unsound.  They motivate a
conservative restriction which supplies exactly the evidence used by the
direct proof, without importing inert contexts, tight typing, stratification,
or another published DOT/System D proof discipline:

```text
Γ ⊢ S <: S'
---------------------------------
Γ ⊢ Pair S a d <: Pair S' a d

Γ ⊢ p : P      Γ, x:{p} ⊢ d <: d'      Γ ⊢ d[p/x] <: d'[p/x]
----------------------------------------------------------------
Γ ⊢ Pair {p} a d <: Pair {p} a d'
```

The first rule changes only the first component.  The second changes a member
when the first component is a term singleton; its scoped premise retains the
ordinary dependent comparison, while its opened premise records the coercion
at the path denoted by that singleton.  Primitive transitivity composes the
two operations.  `Examples.lean` checks that this is still enough to
hide a concrete exact definition behind dependent abstract bounds: an exact
member `{p}..{p}` is widened to `Bot..{x}`, where `x` is the pair binder, and
the first component is then widened independently.

### Proof structure

The runtime invariant uses an exact store context: every allocated location
is recorded at its value-introduction type.  Source typing embeds into a
proof-only structural judgment which exposes every subtyping rule and admits
conversion by paths that co-resolve in the current store.  Generalized path
resolution returns either a value location or a stored type definition, so
the same statement covers term paths and abstract type selections.

`Realization.lean` defines a proof-relevant logical relation.
Its finite coercion codes (`Tau.SemMap` in Lean) replace semantic functions;
realized intervals store codes for their lower and upper coercions.  The
mutual fundamental lemmas `Path.StructCheck.mapped_subst` and
`Tau.StructSub.mapped_subst` are proved for an arbitrary realized path
substitution.  Their identity instances, `mapped_resolves` and `mapped`, say
respectively that checked paths resolve to endpoints realizing their types
and that runtime structural subtyping acts on realizations in every exact
store.

Applying such a coercion to the realization of the singleton `{x}` gives the
canonical-form facts needed by the machine.  In particular, a subtype from
`{x}` to a function exposes the abstraction stored at `x` together with the
contravariant domain and covariant codomain residues needed for beta
preservation; the analogous pair result supplies path progress.  These
corollaries discharge the formerly conditional assumptions in
`StructuralPreciseProgress.lean` and `StructuralPrecisePreservation.lean`.

The final source-facing results are in `Safety.lean`:

- `closed_progress` proves progress of the initial state;
- `closed_step_preservation` and `closed_finite_preservation` preserve the
  exact structural runtime invariant, with explicit context growth for store
  allocation; and
- `closed_type_safety` proves that every endpoint of a finite execution of a
  closed, source-typed term is final or can take another step.

Preservation is deliberately stated for the store-indexed structural runtime
judgment, not as closure of the original source judgment under machine
states.  This is the invariant required by the operational proof and is
sufficient for the standard non-stuckness theorem.  The complete current
development contains no `sorry`, `admit`, or user-declared axiom.
