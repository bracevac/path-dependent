# Selective subtyping for DOT

This directory defines a calculus for WadlerFest DOT in monadic normal form in which
subtyping has no transitivity rule and the only coercions are

```text
c ::= step[S, T] | c ; d
```

A `step` is one use of primitive subtyping `≤₀` between the two types it writes, and
`c ; d` composes. The calculus has its own typing, its own machine and its own type
safety proof. [`Vanilla/`](Vanilla) relates it to the DOT-MNF of this repository.

## Receivers

DOT's selection rules read a bound of `x.A` from a type of the receiver `x`, and that
type may itself need a conversion. Here the conversion is a cast on the receiver, and
a receiver is a path:

```text
p ::= x | p ▷ c
```

Types are DOT's: `⊤`, `⊥`, `{A : S..T}`, `{a : T}`, `x.A`, `μ(x) T`, `∀(x : S) T` and
`S ∧ T`. They are the types in contexts, binders and judgments. The two types written
in a `step` are endpoints: they have the same constructors, but a selection `p.A` is
on a path. Erasing an endpoint replaces each path by its variable, and
`step[S, T]` converts the erasure of `S` to the erasure of `T`. So a cast on a term,
a cast on a path and a composition match types up to the casts written in paths.

A path has the declared type of its variable, the target of its last cast, and every
type of the path under that cast:

```text
                    Γ ⊢ p : S    Γ ⊢ c : S ⇒ T         Γ ⊢ p : S    Γ ⊢ c : S ⇒ T    Γ ⊢ p : U
─────────────       ──────────────────────────         ───────────────────────────────────────
Γ ⊢ x : Γ(x)        Γ ⊢ p ▷ c : T                      Γ ⊢ p ▷ c : U
```

`Rec-I`, `Rec-E` and `And-I` are rules of path typing as in DOT, without syntax. There
is no subsumption rule. Two casts on one variable are combined by stacking them and
using `And-I`.

## Primitive subtyping

`≤₀` relates endpoints. It has the rules for `⊤` and `⊥`, reflexivity up to the casts
in paths, the two left rules and the right rule for `∧`, congruence for field
declarations, type declarations and function types, and the two selection rules, which
use the receiver as it is written:

```text
Γ ⊢ p : {A : L..U}             Γ ⊢ p : {A : L..U}
──────────────────             ──────────────────
Γ ⊢ p.A ≤₀ U                    Γ ⊢ L ≤₀ p.A
```

There is no rule that composes two steps, and transitivity is not admissible. A
derivation of `S ≤₀ T` checks every cast stored in `S` and `T`: both endpoints are
valid (`Prim.wf_left`, `Prim.wf_right`), also under binders, and a function type is
checked under its own domain.

A receiver written in an endpoint can carry a composed certificate, as in the third
example below. That evidence is written and checked like any other. So one `step` is
one use of a rule of `≤₀` between its two endpoints; it is not a bound on the evidence
inside them. An annotation of a program need not record every use of transitivity of
a source derivation, and a program can have several annotations.

## Terms

Application and projection take paths, and any term can be cast:

```text
t ::= p | v | p q | p.a | let x = t in u | t ▷ c
```

Term typing has no subsumption rule. One comparison `≤₀` is applied without a
certificate, at the argument of an application, between types without casts: its
receivers are variables, so it cannot supply a cast. Every other conversion is a
cast. Erasure removes all casts, and the machine runs erased
terms.

## Examples

[`Probes.lean`](Probes.lean) has the derivations.

In `b : {B : ⊥..⊤}, c : {C : ⊥..⊤}, x : {A : b.B..c.C}` both `b.B ≤₀ x.A` and
`x.A ≤₀ c.C` hold and `b.B ≤₀ c.C` does not (`gap`), so `≤₀` is not transitive
(`prim_nontrans`, and `primitive_nontrans` for the implicit comparison). The certificate
`step[b.B, x.A] ; step[x.A, c.C]` converts `b.B` to `c.C`.

A receiver that needs a conversion:

```text
R = {A : ⊥..{a : ⊤}}
w : {B : ⊥..R}, y : w.B, u : y.A
r = y ▷ step[w.B, R]
(u ▷ step[r.A, {a : ⊤}]).a
```

The declared type of `y` has no member `A`. The cast that gives `y` the type `R` is
written in the path `r`, and `step[r.A, {a : ⊤}]` converts `y.A`, so it applies to `u`
(`cSel_typed`, `ex2_typed`). With `y` in place of `r` the step is rejected
(`ex2_bare_gap`).

A receiver whose cast needs a variable bound in a type: with `y : ⊤`,
`D = {A : ⊤..{B : ⊥..{a : ⊤}}}` and, under `x : D`,
`r = y ▷ (step[⊤, x.A] ; step[x.A, {B : ⊥..{a : ⊤}}])`, the step
`step[∀(x : D) r.B, ∀(x : D) {a : ⊤}]` converts `∀(x : D) y.B` (`certY_typed`).

An invalid cast is rejected wherever it is stored: in a path that keeps an earlier
type (`pBad_untyped`), in a reflexive step (`step_refl_validates`), under a binder
(`step_refl_validates_under_binder`), and in the body of a function type that is only
valid under the other domain (`step_checks_source_body`).

## Type safety

The machine of DOT-MNF runs the erasure of a term: a store of values, a stack of `let`
frames and a term. A state is typed when its store, frames and term are erasures of
typed annotated ones.

```text
progress      : StateTy st → st.Final ∨ ∃ st', Step st st'
preservation  : StateTy st → Step st st' → StateTy st'
safety        : HasTy .nil t T → Steps ⟨.nil, .nil, t.erase⟩ st → ¬ st.Stuck
```

`StateTy st` says that some context and some types make the store, the term and the
continuation of `st` typed. So `preservation` keeps the invariant that `safety` needs;
it does not say that a result type fixed in advance is kept, which the preservation
theorem of the F-sub calculus does. It proves that annotations for the next state
exist and does not compute them. The proof follows Rapoport, Kabir, He and Lhoták (OOPSLA 2017): the context of a
typed store is inert; in an inert context every path, primitive step and certificate
is tight (`PathTy.tight`, `Prim.tight`, `CertTy.tight`), where the tight relation
`TSub` is an auxiliary declarative subtyping with transitivity whose selection rules
use only the precise type of a variable; invertible typing gives the canonical forms.
What the tight relation finds is turned back into certificates (`TSub.cert`) to type
the next state, with substitution of typed paths for variables (`HasTy.psubst`), of
which narrowing and variable substitution are instances. The proof uses no result
about DOT-MNF or FCdot. The modules below `Vanilla/` are not imported by it.

## Correspondence with DOT-MNF

[`Vanilla/`](Vanilla) is the library `SelectiveDotVanilla`. The two syntaxes agree on
terms without casts (`toDot`, `ofDot`).

```text
typability_iff : (∃ d, d : Γ ⊢DOT t : T)   ↔   ∃ h, erase(h) = t ∧ Γ ⊢ h : T
coercion_iff   : (∃ d, d : Γ ⊢DOT S <: T)  ↔   ∃ c, Γ ⊢ c : S ⇒ T
```

From left to right the witnesses are computed by functions on DOT-MNF derivations:
`Sub.elab` gives the certificate, with `Sub.trans d₁ d₂` mapped to
`d₁.elab ; d₂.elab` (`trans_is_seq`), `HasTy.toPath` gives the cast path of a
variable typing, and `HasTy.elab` the annotated term, which erases to the source term
(`elab_erase`) and has the same type (`elab_typed`). From right to left, erasure maps
typed terms to typed terms (`hasTy_sound`).

The machine of this calculus and the machine of DOT-MNF take the same steps on
translated states (`step_ofDot`, `step_of_ofDot`). With the elaboration and `safety`
this gives the type safety of DOT-MNF without the translation to FCdot:

```text
dot_safety_direct : (d : ⊢DOT t : T) → Steps ⟨∅, ∅, t⟩ st → ¬ st.Stuck
```

## What is not claimed

There is no checker here: `≤₀` and the typing judgments are relations, and neither
decidability nor an algorithm is proved. `≤₀` relates written endpoints, and the
witness shows that it is not transitive on them. A different question is left open:
whether, for the same three types, another choice of casts in the endpoints lets a
single step do the conversion. A cast cannot be written in a binder annotation or a
context entry. Paths are variables under casts; there are no field paths.

## Modules

| file | content |
| --- | --- |
| `Syntax.lean` | types, paths, endpoints, certificates, terms; renaming, erasure |
| `Typing.lean` | `PathTy`, `Wf`, `Prim`, `CertTy`, `HasTy`, `DefsTy`; `Prim.wf_left`, `Prim.wf_right` |
| `Machine.lean` | stores, continuations, `Step`, `Steps`, `Final`, `Stuck` |
| `Probes.lean` | the examples above; the types of a path without casts |
| `RenameTy.lean`, `Rename.lean` | renaming equations; exact renaming of every judgment |
| `Subst.lean` | substitution of typed paths for variables; narrowing; substitution of a path |
| `Lift.lean` | certificates under each type constructor, from `step` and `;` |
| `Tight.lean` | inert contexts, precise, tight and invertible typing; general to tight |
| `State.lean` | typing of stores, continuations and states |
| `Canonical.lean` | tight relation to certificates; canonical forms |
| `Safety.lean` | `progress`, `preservation`, `safety` |
| `Axioms.lean` | axiom audit |
| `Vanilla/Translate.lean` | the two syntaxes |
| `Vanilla/Sound.lean` | erasure of typed terms and certificates is typed in DOT-MNF |
| `Vanilla/Elab.lean` | the elaboration as functions on derivations |
| `Vanilla/Exact.lean` | `typability_iff`, `coercion_iff`, `trans_is_seq` |
| `Vanilla/Machine.lean` | the two machines agree; `dot_safety_direct` |
| `Vanilla/Axioms.lean` | axiom audit of the correspondence |

From the repository root:

```sh
lake build SelectiveDot SelectiveDotVanilla
lake env lean lean/Coercions/Selective/Dot/Axioms.lean
lake env lean lean/Coercions/Selective/Dot/Vanilla/Axioms.lean
```

The audits use at most `propext` and `Quot.sound`.
