# Plan III: DOT-MNF into an Explicit-Evidence Coercion Calculus

Milestone specification, September 2026.  Companion to Plan I
(`plan1-dot-to-system-fc-coercions-plan.md`) and Plan II
(`plan-2-many-sorted-abstract-members.md`).  Written after the audit and cut
of the first `lean/Coercions` attempt (branch `coercions-cut`).

## 0. Status and purpose

This document is the contract for the next development.  It fixes the source
calculus, the target calculus, the scoping discipline, and the exact theorem
statements per milestone.  A milestone is complete when the theorem stated
here type-checks with that statement, with `#print axioms` showing only
`propext` and `Quot.sound`.

The surviving code (`FCsub`, `DOT/Acyclic`, `Translation/Acyclic`,
`Translation/StableRoots`, the static layer of `ManySortedFC`) is reference
material and a source of reusable infrastructure.  It is not the base of the
new development: the target defined here differs from `FCsub` in its treatment
of binders and object types (Section 1), and the source differs from
`DOT/Acyclic` in having term members, recursive self types, intersections,
and a store semantics.

The scope is the variable-path exercise: WadlerFest DOT in monadic normal
form.  pDOT paths are Section 9, hooks only.

## 1. Why Stage B changes: view identity through bounds

Plan I Stage B proposed: open each variable once into an existential over its
declared members, and obtain every further member fact from subtyping views
translated as coercions between package types.  This is not total.

Counterexample.  Let

```text
S = { A : ⊥..⊤ }        T = { A : Int..⊤ }
Γ = x : { A : S..T },  w : S
```

DOT derives `S <: x.A` (<:-Sel), `x.A <: T` (Sel-<:), hence `w : T` by
subsumption, hence `w : { A : Int..⊤ }`, hence `Int <: w.A`.  Then

```text
let g = λ(y : w.A). y in g n          with  n : Int
```

is well typed.  In the Stage B target, `w.A` denotes the name `α` opened from
`w`'s declared type `S`.  The view of `w` at `T` is a coercion between two
package types; using it requires opening the coerced package, which yields a
fresh name `α'` with `Int ≤ α'`.  Nothing relates `α'` to `α`.  The
application `g n` has no translation.  The context is unrealizable (no `R`
satisfies `S <: R <: T`), but a total translation over derivations has to
cover it.  `Translation/StableRoots` was total only because its
`StableHasTy` fragment excludes precisely the derivations that pass through
a bound in this way.

Consequence.  Member identity must be attached to the binder, not to the
type through which the binder is viewed, and evidence about a binder's type
must be usable at that binder's members regardless of how the evidence was
obtained.  Concretely:

1. Every term binder `x` carries a block of type names `x.ℓ`, one per label
   `ℓ` of a fixed finite label set.  Types refer to blocks; there is no other
   form of selection.  Opening is implicit at every binder.  Packing (choosing
   witnesses for a block) happens only at object literals and at allocation.
2. Object types are telescopes of propositions over a self block,
   `Obj(y. Tel)`.  Inclusion between object types is pointwise: evidence
   `e : S ≤ Obj(y. Tel)` may be eliminated at any binder `x : S` to give
   `Tel[y := x]`.  This is sound under DOT's own reading of `x : T` as "the
   members of `x` satisfy `T`", and it is exactly what turns a bad-bounds
   derivation into an explicit path through locally assumed evidence.

The target is therefore not System F-sub with existentials.  Its types
mention binder blocks, so syntactically it is closer to an explicit-evidence
DOT than to FC.  What it keeps from FC: no subsumption, evidence as checked
proof terms, a total and complete checker, erasable coercions, and a
metatheory whose only source-specific content is one lemma about closed
evidence.  The closest related work is the F-ing modules elaboration
(Rossberg, Russo, Dreyer), extended with lower bounds, bounded members,
intersections, and recursive self types.

The research claim becomes:

> DOT type safety is store typing plus normalization of closed evidence.
> Neither tight nor invertible typing is needed.  Adding a sort of member
> (captures, classifiers, later paths) adds relation sorts and evidence
> rules to the target and rules to the translation; the soundness proof
> shape does not change.

Working name for the target: `FCdot`.  Rename at will.

## 2. Fixed decisions

- Source: WadlerFest DOT, MNF (`let` right-hand sides are arbitrary terms;
  application and selection take variables).  Intersections are restricted
  by well-formedness to declaration level (Section 3.2).  Store machine.
- Target: `FCdot` (Section 5).  No subsumption.  Store machine.
- One shared untyped runtime (Section 4).  Erasure from both source and
  target is literal into it.  No administrative equivalence anywhere.
- Scoping: the `Sig`/`BVar`/`Rename` discipline of
  `~/projects/semantic/Semantic/ModalCapybara/Debruijn.lean`, with its names
  and notations (`Kind`, `Sig := List Kind`, `BVar s k` with `here`/`there`,
  `structure Rename` with `var`, `lift`, `liftMany`, `succ`; notations `,x`
  and `,,`).  Term binders are the only binder kind in this plan; the
  discipline is kept so that Plan II can add `cvar` without restructuring.
- Labels: a fixed finite type `Label`, split as `Label.type ⊕ Label.term`.
  Formalize as a parameter `(L : Type) [DecidableEq L]` with the split as two
  injections, or as `Fin n ⊕ Fin m`.  Blocks are indexed by `Label`.
- No Mathlib.  The repo has no dependencies and stays that way.
- Every fragment restriction is a `Wf` predicate on source syntax.  No side
  predicates on derivations.
- Compilers are total functions on derivations, never `Option` or `Except`.
- `native_decide` only in `*Examples.lean`.  `#print axioms` on every
  milestone theorem.

## 3. Source: DOT-MNF

Namespace `DotMNF`.  All syntax is indexed by `s : Sig`.

### 3.1 Syntax

```text
Path         p ::= x                                  (variables only, this plan)
Types        S, T ::= ⊤ | ⊥ | { A : S..T } | { a : T } | p.A | μ(x. T) | ∀(x : S) T | S ∧ T
Terms        t, u ::= p | v | x y | x.a | let x = t in u
Values       v ::= ν(x. d) | λ(x : T) t
Definitions  d ::= { A = T } | { a = t } | d ∧ d
```

`Path` is an inductive with the single constructor `var`.  Every judgment
that mentions a receiver takes a `Path`.  This costs nothing now and makes
Section 9 additive.

Object literals `ν(x. d)` carry no type annotation; the annotation in
WadlerFest DOT is recoverable from definition typing and is not needed for
a derivation-directed translation.  If a later milestone wants it for the
checker, add it then.

### 3.2 Well-formedness and the fragment

`Ty.Wf : Ctx s → Ty s → Prop` is standard except for one clause:

```text
Wf(S ∧ T)   requires   Decl(S) ∧ Decl(T)

Decl(⊤)  Decl({A : S..T})  Decl({a : T})  Decl(μ(x. T)) if Decl(T)  Decl(S ∧ T) if Decl(S) ∧ Decl(T)
```

So intersections occur only between declaration-shaped types.  `p.A` and
`∀` are not intersected.  Bounds `S`, `T` inside declarations are arbitrary
well-formed types.  Bad bounds are allowed: `Wf({A : S..T})` does not ask
for `S <: T`.

Definition well-formedness requires distinct labels in `d₁ ∧ d₂`.

### 3.3 Subtyping

`Sub : Ctx s → Ty s → Ty s → Prop`, mutually with `HasTy`:

```text
Top     Γ ⊢ T <: ⊤                       Bot     Γ ⊢ ⊥ <: T
Refl    Γ ⊢ T <: T                       Trans   Γ ⊢ S <: M   Γ ⊢ M <: T  ⟹  Γ ⊢ S <: T
And₁    Γ ⊢ S ∧ T <: S                   And₂    Γ ⊢ S ∧ T <: T
And     Γ ⊢ S <: T   Γ ⊢ S <: U   ⟹  Γ ⊢ S <: T ∧ U
Fld     Γ ⊢ T <: U   ⟹  Γ ⊢ {a : T} <: {a : U}
Typ     Γ ⊢ S₂ <: S₁   Γ ⊢ T₁ <: T₂   ⟹  Γ ⊢ {A : S₁..T₁} <: {A : S₂..T₂}
Sel-<:  Γ ⊢ x : {A : S..T}   ⟹  Γ ⊢ x.A <: T
<:-Sel  Γ ⊢ x : {A : S..T}   ⟹  Γ ⊢ S <: x.A
All     Γ ⊢ S₂ <: S₁   Γ, x : S₂ ⊢ T₁ <: T₂   ⟹  Γ ⊢ ∀(x : S₁) T₁ <: ∀(x : S₂) T₂
```

There is no `Rec` subtyping rule; recursion is handled by the typing rules
`Rec-I`/`Rec-E` on variables, as in WadlerFest DOT.

### 3.4 Typing

```text
Var     Γ(x) = T  ⟹  Γ ⊢ x : T
All-I   Γ, x : S ⊢ t : T  ⟹  Γ ⊢ λ(x : S) t : ∀(x : S) T
All-E   Γ ⊢ x : ∀(z : S) T   Γ ⊢ y : S  ⟹  Γ ⊢ x y : T[z := y]
{}-I    Γ, x : T ⊢ d : T  ⟹  Γ ⊢ ν(x. d) : μ(x. T)
{}-E    Γ ⊢ x : {a : T}  ⟹  Γ ⊢ x.a : T
Let     Γ ⊢ t : T   Γ, x : T ⊢ u : U↑  ⟹  Γ ⊢ let x = t in u : U
Rec-I   Γ ⊢ x : T[x]  ⟹  Γ ⊢ x : μ(x. T)          Rec-E  the converse
And-I   Γ ⊢ x : T   Γ ⊢ x : U  ⟹  Γ ⊢ x : T ∧ U
Sub     Γ ⊢ t : T   Γ ⊢ T <: U  ⟹  Γ ⊢ t : U

Def-Typ Γ ⊢ {A = T} : {A : T..T}
Def-Trm Γ ⊢ t : T  ⟹  Γ ⊢ {a = t} : {a : T}
Def-And Γ ⊢ d₁ : T₁   Γ ⊢ d₂ : T₂   dom d₁ ∩ dom d₂ = ∅  ⟹  Γ ⊢ d₁ ∧ d₂ : T₁ ∧ T₂
```

`U↑` in `Let` is the intrinsically scoped form of "`x` not free in `U`".
`T[z := y]` is a renaming.  All judgments live in `Prop`; the translation
recurses on derivations, so they must be inductive families with
`Type`-valued elimination where needed.  State them in `Type` from the
start; converting later is painful.

### 3.5 Machine

```text
State s = ⟨ σ : Store s , K : Cont s , t : Tm s ⟩

Store      σ ::= ∅ | σ, v                   (indexed by s; entry i is a value)
Cont       K ::= ∅ | K ▹ (x. u)             (frames let x = □ in u)

⟨σ, K, let x = t in u⟩            ⟶  ⟨σ, K ▹ (x. u), t⟩
⟨σ, K ▹ (x. u), v⟩                ⟶  ⟨σ, v ; K↑, u⟩                  (allocate)
⟨σ, K ▹ (x. u), y⟩                ⟶  ⟨σ, K, u[x := y]⟩              (rename)
⟨σ, K, x y⟩     σ(x) = λ(z : T) t  ⟶  ⟨σ, K, t[z := y]⟩
⟨σ, K, x.a⟩     σ(x) = ν(z. d), d ∋ {a = t}   ⟶  ⟨σ, K, t[z := x]⟩

final ⟨σ, ∅, v⟩        final ⟨σ, ∅, x⟩
```

`K↑` weakens the continuation under the new store binder.  All substitutions
are renamings.  Store typing `Γ ⊢ σ` types entry `i` at `Γ(i)` in `Γ`; state
typing `Γ ⊢ ⟨σ, K, t⟩ : T` composes store, continuation, and term typing.

### 3.6 Erasure

`⌊·⌋ : Tm s → Runtime.Tm s`, `⌊·⌋ : State s → Runtime.State s`.  Drops
types and `{A = T}` definitions, keeps everything else.

## 4. Shared runtime

Namespace `Runtime`.  Indexed by `s : Sig` with a single kind.

```text
Terms    t ::= x | λx. t | ν(x. {a = t, …}) | x y | x.a | let x = t in u
Values   v ::= λx. t | ν(x. {…})
State, Store, Cont, ⟶, final:   as in 3.5 with types removed
Stuck s  :=  ¬ final s  ∧  ¬ ∃ s'. s ⟶ s'
```

The source erasure is the identity on signatures.  The target erasure
(Section 5.8) is also the identity on signatures, because `FCdot` has only
term binders in this plan.

## 5. Target: FCdot

Namespace `FCdot`.  `Kind := var` for now; `Sig := List Kind`.

### 5.1 Types, propositions, telescopes

```text
Types          S, T ::= ⊤ | ⊥ | x.ℓ | Π(x : S) T | Obj(x. Tel) | Rec(B, i)
Propositions   P ::= S ≤ T | S ≃ T | has ℓ            (ℓ ∈ Label.term for has)
Telescope      Tel ::= [] | Tel, P                    (over the self block)
Rec blocks     B  ::= as FCsub.RecBodies: n head-guarded bodies over n self names
```

`x.ℓ` is the ℓ-name of the block of term binder `x`; `x : BVar s var`.
`Obj(x. Tel)` binds a self block for `Tel`.  The self binder is a term
binder kind with no runtime content of its own beyond the block; represent
it as an ordinary `,x` extension of the signature.

`Π(x : S) T` is dependent through `x`'s block only; `T` may mention `x.ℓ`
and nothing else about `x`, since types never contain terms.

`Rec(B, i)` is `FCsub.Ty.recProj`, unchanged: closed recursive type
definitions used as witnesses for self-referential exact members.

Source-type shapes as target types:

```text
{A : S..T}   ↦  Obj(y. [ S ≤ y.A , y.A ≤ T ])
{a : T}      ↦  Obj(y. [ has a , y.a ≤ T ])
μ(x. T)      ↦  Obj(x. Tel_T)                     (self block is x's block)
S ∧ T        ↦  Obj(y. Tel_S ++ Tel_T)
⊤            ↦  ⊤   (equivalently Obj(y. []))
```

Field labels get a name in the block too: `y.a` for a term label `a` is the
type of the field `a`.  This is what makes `{a : T} ∧ {a : U}` a
conjunction of propositions rather than a type-level intersection.

### 5.2 Evidence

Two proof-term families, `EqCo` and `LeCo`, indexed by the signature only;
endpoints are assigned by `LeCo.HasType : Ctx s → LeCo s → Ty s → Ty s → Type`
as in `FCsub.Evidence`.

```text
EqCo   φ ::= refl T | symm φ | trans φ φ | unfold(B, i) | def x ℓ
LeCo   e ::= refl T | trans e e | top T | bot T | eqToLe φ
           | pi (e_dom) (x. e_cod)                           contravariant domain
           | obj (x. m)                                       pointwise object coercion
           | member (a) (P)                                   elimination at an atom (5.4)
Morphism  m : Tel ⇒ Tel'   ::= for each P' ∈ Tel', a LeCo/EqCo/has-derivation of P'[x]
                                from the propositions of Tel[x] and the ambient context
```

`def x ℓ : x.ℓ ≃ W` is available only when the context binding of `x` is
transparent (5.5) with definition `W` at `ℓ`.  `unfold(B, i)` is
`FCsub.EqCo.unfoldRec`.

Typing of `obj`:

```text
Δ, x : Obj(x. Tel) ⊢ m : Tel[x] ⇒ Tel'[x]
─────────────────────────────────────────
Δ ⊢ obj (x. m) : Obj(x. Tel) ≤ Obj(x. Tel')
```

The premise context binds the self block opaquely and makes `Tel[x]`
available as evidence through `member` (5.4).  The morphism is checked
proposition by proposition.  `has ℓ` propositions may only be derived from
`has ℓ` premises; there is no other introduction of `has` inside a morphism.

Source subtyping rules map to evidence as follows (the M3 theorem makes this
a total function):

```text
Top ↦ top      Bot ↦ bot      Refl ↦ refl      Trans ↦ trans
And₁, And₂ ↦ obj with the projection morphism
And ↦ obj with the pairing morphism           (pointwise, this is where And is easy)
Fld ↦ obj mapping (has a, y.a ≤ T) to (has a, y.a ≤ U) by trans with ⟦T <: U⟧
Typ ↦ obj mapping bounds by trans with the translated bound derivations
Sel-<: ↦ member (⟦x : {A : S..T}⟧) (y.A ≤ T)        <:-Sel ↦ member (…) (S ≤ y.A)
All ↦ pi ⟦S₂ <: S₁⟧ (x. ⟦T₁ <: T₂⟧)
```

The `All` case needs no narrowing lemma.  The codomain evidence is checked
under `x : ⟦S₂⟧`, and `T₁`, `T₂` mention only `x`'s block, which does not
depend on `x`'s type.

### 5.3 Atoms and terms

MNF over atoms.  An atom is a variable under erasure-invisible wrappers.

```text
Atoms    a ::= x | cast a e | foldSelf a | unfoldSelf a
Terms    t ::= a | v | app a a | proj a ℓ | let x = t in u | cast t e
Values   v ::= λ(x : S) t
           | ν(x. W⃗ ; E⃗ ; {a = t, …})           object literal: witnesses, evidence, fields
           | cast v e                              adapted value (wrapper, no step)
```

`root(a)` is the variable under the wrappers.  `block(a) := block(root a)`.

`ν(x. W⃗ ; E⃗ ; fields)`: `W⃗ : Label → Ty` closed with respect to `x`'s block
(they may use `Rec` blocks), `E⃗` evidence for the object's telescope at
`W⃗`, fields are terms under `x`.  `W⃗` and `E⃗` erase.

`foldSelf`/`unfoldSelf` are the atom forms of `Rec-I`/`Rec-E`:

```text
Δ ⊢ a : Obj(y. Tel[y])                      Δ ⊢ a : Obj(y. Tel[root a])
──────────────────────────────              ──────────────────────────────
Δ ⊢ unfoldSelf a : Obj(y. Tel[root a])      Δ ⊢ foldSelf a : Obj(y. Tel[y])
```

At the binder these two object types denote the same propositions, so both
directions are sound pointwise; the distinction matters only when `a` is
passed to a `Π` expecting one shape or the other.

### 5.4 Elimination at an atom

```text
Δ ⊢ a : S       Δ ⊢ e : S ≤ Obj(y. Tel)       P ∈ Tel
──────────────────────────────────────────────────────
Δ ⊢ member (cast a e) P  :  P[y := root a]
```

Read: any evidence that the type of `a` is included in an object type yields
that object type's propositions at `a`'s block.  With `e = refl` this is the
`Var` case: a binder of object type satisfies its telescope.  With
`e = bot` it is absurdity: a binder of type `⊥` satisfies anything.  With
`e = trans γ⁻ γ⁺` through a bound it is the counterexample of Section 1,
resolved.

`member` produces evidence of relation `P`'s sort: an `LeCo` for `≤`, an
`EqCo` for `≃`, and a `Has` witness for `has ℓ`.

### 5.5 Contexts

```text
Δ ::= ∅ | Δ, x : T | Δ, x : T := W⃗
```

Opaque binders have an abstract block.  Transparent binders have a defined
block and provide `def x ℓ : x.ℓ ≃ W_ℓ`.  Two uses:

- Inside an object literal `ν(x. W⃗ ; E⃗ ; fields)`, the fields are typed
  under `x : Obj(x. Tel) := W⃗`.  This is how `{A = T}` yields both bounds:
  `eqToLe (def x A)` and its symmetric.
- Store typing (5.7) uses fully transparent contexts: every allocated
  binder's block is defined by the witnesses of the stored value.

Weakening from transparent to opaque is admissible: a term typed with `x`
opaque is typed with `x` transparent.  The converse is not.  Preservation
uses the admissible direction when a `let` allocates.

### 5.6 Typing

```text
Var       Δ(x) = T  ⟹  Δ ⊢ x : T
Cast      Δ ⊢ a : S   Δ ⊢ e : S ≤ T  ⟹  Δ ⊢ cast a e : T          (and for terms)
Lam       Δ, x : S ⊢ t : T  ⟹  Δ ⊢ λ(x : S) t : Π(x : S) T
App       Δ ⊢ a : Π(z : S) T   Δ ⊢ b : S  ⟹  Δ ⊢ app a b : T[z := root b]
Proj      Δ ⊢ a : S   Δ ⊢ member (cast a e) (has ℓ)  ⟹  Δ ⊢ proj a ℓ : (root a).ℓ
Let       Δ ⊢ t : T   Δ, x : T ⊢ u : U↑  ⟹  Δ ⊢ let x = t in u : U
Obj       Δ, x : Obj(x. Tel) := W⃗ ⊢ fieldᵢ : x.aᵢ      for each field aᵢ
          Δ ⊢ E⃗ : Tel[x := W⃗]                          closed evidence for the telescope
          has aᵢ ∈ Tel  ⟺  aᵢ is a field
          ⟹  Δ ⊢ ν(x. W⃗ ; E⃗ ; fields) : Obj(x. Tel)
```

`App`'s result renames `z`'s block to `root b`'s block; the type of an
application mentions the argument's block, as in DOT.  `Let` requires the
result not to mention `x`'s block.

There is no subsumption and no `IsValue` restriction anywhere.

### 5.7 Store machine and resolution

```text
State s = ⟨ σ , K , t ⟩      as in 3.5, over FCdot terms
Static store  θ_σ : (x : loc) → Label → closed Ty      the block definitions of σ's entries
```

Allocation of a value `v` at a new binder defines its block: for an object
literal, `θ(x) := W⃗`; for a lambda or an adapted lambda, `θ(x) := ⊤` at
every label.  A wrapped object `cast v e` allocates with the witnesses of
`v` after resolution.

`resolve σ a : Value` looks up `root a` and pushes the wrappers into the
value: `cast (λ…) (pi e_dom (x. e_cod))` becomes an adapted lambda whose
application inserts `cast … e_dom` on the argument and `cast … e_cod` on the
result; `cast (ν …) (obj m)` becomes the object with `E⃗` mapped through
`m`; `foldSelf`/`unfoldSelf` are identities on values; `eqToLe` casts are
identities.  `resolve` is a total function by structural recursion on the
wrapper stack.  It replaces `FCsub`'s cast-normalization step rules
(`appCastArrow`, `openCastExists`, `castTrans`, …) with equations.  There
are therefore no silent steps: every target step erases to exactly one
runtime step.

Steps:

```text
⟨σ, K, let x = t in u⟩                        ⟶  ⟨σ, K ▹ (x. u), t⟩
⟨σ, K ▹ (x. u), v⟩                            ⟶  ⟨σ, v ; K↑, u⟩
⟨σ, K ▹ (x. u), a⟩                            ⟶  ⟨σ, K, u[x := a]⟩            (atom substitution)
⟨σ, K, app a b⟩   resolve σ a = λ(z : S) t   ⟶  ⟨σ, K, t[z := b]⟩
⟨σ, K, proj a ℓ⟩  resolve σ a = ν(z. …{ℓ = t}…)  ⟶  ⟨σ, K, t[z := a]⟩
⟨σ, K, cast t e⟩  (t a computation)          ⟶  ⟨σ, K ▹ cast(□, e), t⟩
⟨σ, K ▹ cast(□, e), v⟩                        ⟶  ⟨σ, K, cast v e⟩
```

Atom substitution `t[z := a]` replaces the variable `z` by the atom `a` in
terms and renames `z`'s block to `root a`'s block in types and evidence.
Cast frames erase to nothing and their two steps erase to zero runtime
steps; they are the only administrative steps, and they are bounded by the
syntactic nesting of `cast` in the term, so silent termination is trivial.
If that bookkeeping proves annoying, make `cast t e` a derived form
`let x = t in cast x e`; then erasure stops being literal by one renaming
let, which we do not want.  Keep the frame.

Store typing: `Δ_σ ⊢ σ` where `Δ_σ` is the fully transparent context
`x₁ : T₁ := θ(x₁), …`, and each entry is typed in `Δ_σ`.  State typing
`Δ_σ ⊢ ⟨σ, K, t⟩ : T`.

### 5.8 Erasure

`⌊·⌋ : FCdot.Tm s → Runtime.Tm s`: atoms to their root variable, `cast t e`
to `⌊t⌋`, `ν(x. W⃗ ; E⃗ ; fields)` to `ν(x. ⌊fields⌋)`, `app`/`proj`/`let`
pointwise.  On states, cast frames are dropped and store entries erased.

### 5.9 Checker

`check : Ctx s → Tm s → Ty s → Bool` and `synth`, total, by the
`FCsub.Checker` architecture: an `Option`-valued kernel returning the
derivation, wrapped in a Boolean.  Evidence checking is syntax directed
because every constructor determines its endpoints from its arguments and
the context.  `member` requires looking up the proposition in the object
type's telescope; `obj` requires checking a morphism, which is a list of
evidence terms.

## 6. Milestone M1: FCdot metatheory

Deliverables: `FCdot/{Debruijn, Syntax, Evidence, Context, Typing, Checker,
CheckerCompleteness, Resolve, Machine, Preservation, Progress, Erasure,
Simulation, Examples}.lean`.  Reuse `FCsub`'s renaming infrastructure,
`RecBodies`, and the checker architecture.  Rename to the Capybara
conventions while doing so.

```lean
theorem Tm.check_iff (Δ : Ctx s) (t : Tm s) (T : Ty s) :
    check Δ t T = true ↔ Nonempty (HasType Δ t T)

theorem LeCo.check_iff (Δ : Ctx s) (e : LeCo s) (S T : Ty s) :
    checkLe Δ e S T = true ↔ Nonempty (LeCo.HasType Δ e S T)

theorem resolve_typed {σ : Store s} {a : Atom s} {S : Ty s}
    (hσ : StoreTyped σ) (ha : HasType (ctxOf σ) a S) :
    HasType (ctxOf σ) (resolve σ a) S

theorem preservation {st : State s} {st' : State s'} {T : Ty s}
    (h : StateTyped st T) (step : st ⟶ st') :
    StateTyped st' (T.rename (embed st st'))

theorem progress {st : State s} {T : Ty s}
    (h : StateTyped st T) :
    st.Final ∨ ∃ s' (st' : State s'), st ⟶ st'

theorem erase_step {st st'} (step : st ⟶ st') :
    (IsCastFrameStep step ∧ ⌊st⌋ = ⌊st'⌋) ∨ ⌊st⌋ ⟶ ⌊st'⌋

theorem erase_reflect {st : State s} {r : Runtime.State s'}
    (h : StateTyped st T) (step : ⌊st⌋ ⟶ r) :
    ∃ st', st ⟶⁺ st' ∧ ⌊st'⌋ = r

theorem castFrame_steps_bounded : ∀ st, ∃ n, ∀ (run : CastFrameRun st), run.length ≤ n
```

`embed st st'` is the signature embedding when a step allocates.

The lemma that carries the weight, needed by `progress`, is head
normalization of closed evidence.  Three routes were considered while
writing this section:

- Syntactic cut elimination on closed evidence terms.  Composing two object
  coercions substitutes one morphism into the other; with self-referential
  witnesses (E2) there is no rank measure that decreases, and without them
  E2 is excluded.  Rejected.
- A step-indexed semantic model of evidence over the current store.  Object
  types must cost a step to break self-reference, and then eliminating a
  member fact lands one index later than where it is needed.  Repairing
  that requires a "later" modality in the typing rules, as in gDOT.
  Rejected for this plan.
- Head normalization with closures.  Normal forms of object views are
  computed once per elimination and stored as data in an environment;
  evidence under an opaque self binder is normalized against that data and
  never substituted back into itself.  The recursion is structural on the
  evidence term, with the store's own literal evidence normalized first by
  induction on store position.  This is the route taken.

Definitions (`Canonical.lean`):

```lean
inductive Form (s : Sig)                 -- head normal forms of closed inclusion evidence
  | bot | top | refl
  | pi (dom : Closure s) (cod : Closure (s,x))
  | obj (view : Atom s → View s → View s)  -- the target telescope's forms at a given self
-- View s := List (PropForm s); a Closure is an evidence term with the environment
-- that closes its opaque binders by store atoms and their views.

def Ctx.resolve : Ctx s → Ty s → Ty s    -- follow transparent definitions to a non-name head
def hnf : Env s → LeCo s → Form s        -- structural on the evidence
def storeView : Store s → BVar s .var → View s   -- by induction on the store, from each literal's E
```

Theorems:

```lean
theorem EqCo.resolve_eq  (hΓ : Transparent Γ) (h : EqCo.HasType Γ φ S T) : Γ.resolve S = Γ.resolve T
theorem hnf_typed (hΓ : Transparent Γ) (h : LeCo.HasType Δ e S T) (hη : EnvTyped Γ η Δ) :
    FormTyped Γ (hnf η e) (S.close η) (T.close η)
theorem storeView_typed (h : Store.Typed σ Γ) (x) : ViewTyped Γ (storeView σ x) (Γ.lookupTy x) x
theorem closed_pi_inversion (h : Store.Typed σ Γ) (ha : Atom.HasType Γ a (.pi S T)) :
    ∃ S₀ t₀, σ.lookup a.root = .lam S₀ t₀
theorem closed_has_field (h : Store.Typed σ Γ) (hh : Has.HasType Γ h x ℓ) :
    ∃ Tel W E F, σ.lookup x = .obj Tel W E F ∧ F.Has ℓ
```

`FormTyped` says: `bot` only if the source resolves to `⊥`, `top` only if
the target resolves to `⊤`, `refl` only if both resolve equally, `pi` only
between two function types with the closed domain and codomain closures
typed contravariantly and covariantly, `obj` only between two object types
with the view function sending every typed self view to a typed view of the
target telescope.  Corollaries: no closed `⊤ ≤ ⊥`; no closed `obj ≤ Π`; a
closed `has ℓ` at a store binder comes from an actual field.  This is the
target-side residue of DOT's invertible typing, proven once, over stores,
with no semantic model and no restriction on recursive members.

Mandatory examples (Section 10, E1 to E4) must type-check in `FCdot`
before M1 is called done.

## 7. Milestone M2: DOT-MNF source

Deliverables: `DotMNF/{Debruijn, Syntax, Wf, Typing, Machine, Erasure,
Examples}.lean`.

```lean
theorem erase_step {st st' : State s} (step : st ⟶ st') : ⌊st⌋ ⟶ ⌊st'⌋

theorem erase_reflect {st : State s} {r : Runtime.State s'}
    (step : ⌊st⌋ ⟶ r) : ∃ st', st ⟶ st' ∧ ⌊st'⌋ = r
```

No other source metatheory.  In particular no progress, no preservation, no
narrowing, no inversion.  The examples E1 to E4 must have `HasTy`
derivations.

## 8. Milestones M3, M4, M5: the bridge

Namespace `DotToFCdot`.

### 8.1 M3: type and evidence translation

Types translate homomorphically; there is no polarity and no layout.
Contexts translate binder by binder.

```lean
def Ty.translate : DotMNF.Ty s → FCdot.Ty s
def Ctx.translate : DotMNF.Ctx s → FCdot.Ctx s

theorem translate_rename (T : DotMNF.Ty s) (ρ : Rename s s') :
    (T.rename ρ).translate = T.translate.rename ρ
```

Evidence translation is mutual with the atom translation of variable
typings, because `Sel` rules have typing premises and `Var` typings can go
through subsumption:

```lean
mutual
  def Sub.translate : DotMNF.Sub Γ S T → FCdot.LeCo s
  def HasTy.translateAtom : DotMNF.HasTy Γ (.path x) T → FCdot.Atom s
end

theorem Sub.translate_typed (d : DotMNF.Sub Γ S T) :
    FCdot.LeCo.HasType Γ.translate d.translate S.translate T.translate

theorem HasTy.translateAtom_typed (d : DotMNF.HasTy Γ (.path x) T) :
    FCdot.HasType Γ.translate d.translateAtom T.translate
  ∧ root d.translateAtom = x
```

Both are total functions on derivations.  The `root` conjunct is what makes
`Sel` translate to `member`: the atom for `x : {A : S..T}` has root `x`, so
`member` yields propositions about `x.A`.

### 8.2 M4: term translation and the safety corollary

```lean
def HasTy.translate : DotMNF.HasTy Γ t T → FCdot.Tm s

theorem HasTy.translate_typed (d : DotMNF.HasTy Γ t T) :
    FCdot.HasType Γ.translate d.translate T.translate

theorem HasTy.translate_erase (d : DotMNF.HasTy Γ t T) :
    ⌊d.translate⌋ = ⌊t⌋

theorem coherence (d₁ d₂ : DotMNF.HasTy Γ t T) :
    ⌊d₁.translate⌋ = ⌊d₂.translate⌋          -- immediate from translate_erase

theorem dot_safety {t : DotMNF.Tm []} {T} (d : DotMNF.HasTy .nil t T)
    {st : DotMNF.State s} (run : ⟨∅, ∅, t⟩ ⟶* st) :
    st.Final ∨ ∃ st', st ⟶ st'
```

Proof of `dot_safety`, so nobody reinvents it: by `translate_erase`,
`⌊t⌋ = ⌊d.translate⌋`.  Induction along `run` using M2 `erase_step` and M1
`erase_reflect` maintains a target state `st̂` with `⌊st̂⌋ = ⌊st⌋` and
`StateTyped st̂ T.translate` by M1 `preservation`.  M1 `progress` gives
`st̂` final or stepping; cast-frame steps are bounded, so a real step
exists, M1 `erase_step` turns it into a runtime step of `⌊st⌋`, and M2
`erase_reflect` lifts it to `st`.  Finality transfers through erasure.

The `Obj` case of `HasTy.translate` is the one to watch.  Given
`Γ, x : T ⊢ d : T`, the witnesses `W⃗` are chosen from the exact definitions
`{A = T_A}`: `W_A := T_A.translate` with `x.A` replaced by the corresponding
`Rec` projection when `T_A` mentions `x`'s own block; field witnesses
`W_a := T_a.translate` for `{a = t : T_a}`; labels not defined get `⊤`.
The evidence `E⃗` for `Tel_T[x := W⃗]` comes from translating the definition
typing under the transparent binder and then substituting definitions,
which is the closing step of `Translation/RecursiveObjects/Realizability.lean`
generalized to open contexts.

### 8.3 M5: consistency corollaries

These follow from M1 `closed_evidence_canonical` and store typing; they are
stated so the claim in Section 1 is a theorem.

```lean
theorem reachable_consistent {t : DotMNF.Tm []} (d : DotMNF.HasTy .nil t T)
    {st̂ : FCdot.State s} (run : ⟨∅, ∅, d.translate⟩ ⟶* st̂) :
    ¬ ∃ e, FCdot.LeCo.HasType (ctxOf st̂.store) e ⊤ ⊥

theorem reachable_realized {…} (run : …) :
    ∀ (x : BVar s var) ℓ, ∃ W, θ st̂.store x ℓ = W ∧ (ctxOf st̂.store) ⊢ def x ℓ : x.ℓ ≃ W
```

Bad bounds remain expressible under a lambda; they never reach the store.

## 9. Milestone M6: pDOT hooks (not in scope)

Three places change, nothing else:

1. `Path` gains `sel : Path s → Label.term → Path s`, and singleton types
   `p.type` join `Ty`.  Typing gains path typing with precise lookup, path
   replacement, and singleton rules.
2. Blocks are keyed by paths, not variables.  The translation let-binds every
   path prefix that a type mentions (`let y = x.a`), so a target block
   exists for it, and singleton evidence `y ≃ x.a` becomes `EqCo` between
   blocks.  This is the only place the translation stops being
   homomorphic on types.
3. Object fields hold paths or values, and allocation defines the blocks of
   field-reachable objects lazily on selection.

`member`, `obj`, pointwise elimination, `closed_evidence_canonical`, and the
safety corollary are unchanged in shape.

## 10. Mandatory examples

Each must appear as a `HasTy` derivation in `DotMNF/Examples.lean`, as a
`FCdot` term with `check = true` in `FCdot/Examples.lean`, and the two must
have equal erasures.  E4 is the acceptance test for the whole exercise.

- E1, bad bounds under a lambda.  `λ(x : {A : ⊤..⊥}). let y = (x : {B : Int..Int}) in y` with the
  derivation through `⊤ <: x.A <: ⊥`.  Target: `member` through `trans`,
  no `absurd` constructor needed.
- E2, recursive object with self-referential member.
  `ν(x. {A = ∀(y : x.A) x.A} ∧ {id = λ(y : x.A). y})`, then `x.id` applied to
  itself.  Target: `W_A` is a `Rec` projection; `E⃗` uses `unfold`.
- E3, intersection with a shared member.  `x : {A : ⊥..Int} ∧ {A : Nat..⊤}`
  used at both bounds.  Target: one block name `x.A`, two propositions.
- E4, the Section 1 counterexample, closed under a lambda binding `x` and
  `w`, applied to nothing.  Must type-check; must be provably unreachable
  only in the sense that E4's lambda is never applied in any test.
- E5, an object returned from a function and selected after a `let`.
  Exercises `App`'s block renaming and `Let`'s nonescape.

## 11. Rules for the implementer

1. State every judgment in `Type`, intrinsically scoped, from day one.
2. No `Option`, `Except`, or `partial` on any translation function.
   Totality is the theorem, not a hope.
3. No structure whose fields are proof obligations passed in by the caller.
   `LeafCompiler`, `EvidenceContext`, and `StableHasTy` are the patterns to
   avoid.  If a case needs a fact, prove the lemma.
4. No `AdministrativeEq` or any equivalence coarser than equality on erased
   terms.  If erasure stops being literal, stop and report why.
5. `native_decide` only in `*Examples.lean`.  Core files: `decide` at most,
   and rarely.
6. `#print axioms` on every theorem in Sections 6 to 8, recorded in the
   milestone's README.
7. Each milestone ends with a README paragraph listing what the theorems
   do not cover.  Overclaiming in prose is a defect.
8. The order is M1, M2, M3, M4, M5.  M1 is roughly half the work.  Do not
   start M3 before `closed_evidence_canonical` is proven; if it fails, the
   evidence language is wrong and everything downstream changes.
9. Do not add features not in this document.  Captures, classifiers, and
   paths are Plans II and M6.

## 12. Risks, in order

1. `closed_evidence_canonical` with `member` and `trans` through `Rec`
   heads.  Mitigation: prove it first for the fragment without `Rec`, then
   add `Rec` with a fuel-free measure on head-guarded unfolding.
2. The `Obj` case of `HasTy.translate` for mutually recursive exact members
   (`{A = x.B}`, `{B = x.A}`): `Rec` handles it if head-guarded; DOT allows
   the unguarded case.  Decide: either exclude by `Wf` (state it) or use
   `Rec` with a distinguished `⊤` unfolding for unguarded cycles.
3. `App`'s block renaming interacting with atom substitution in
   `preservation`: the substituted atom may carry wrappers, and types in the
   body must rename to the root.  Prove an atom-substitution lemma early.
4. Field labels as block names means a field's type is abstract (`x.a`) and
   only bounded above.  Selecting a field and then applying it requires a
   cast through `x.a ≤ Π(…)`.  Check E2 covers this before believing it.

## 13. Decision log (implementation, September 2026)

Decisions taken while implementing M1, each confirmed with the author:

1. **Object telescope evidence is checked with the self binder at `⊤`.**
   A literal's `E` may use only its definitions (`def`) and fields
   (`field`) plus outer evidence; it cannot assume its own telescope.  This
   removes self-justifying evidence and makes store views well-founded.
2. **Allocation strips casts.**  `let x = cast^n v in u` stores the literal
   `v` at its own type and rewrites `u` so that `x` is used under the
   composite cast (`Tm.adjust`).  Field bodies are therefore always typed
   at the literal's declared type, which is what `proj` needs.
3. **Application through a cast atom uses the normalizer.**  The step reads
   the domain and codomain evidence off the head normal form of the atom's
   casts (`closedAtomForm σ n a = some (_, pi d c)`), casts the argument by
   `d` and the result by `c` at the argument.  The earlier inversion
   constructors `piDom`/`piCod` were removed: they forced the normalizer to
   normalize evidence that is not a subterm of its input.  Preservation of
   this one rule takes the typedness of the form as a hypothesis
   (`FormsTyped`), discharged by the canonical-forms theorem.
4. **Canonical forms by a fuel-indexed normalizer with closures.**  Views
   of opaque binders are data in an environment; object coercions compose
   by chaining closures; evidence is never substituted back into itself.
   Typedness of forms is a step-indexed relation: an object form at depth
   `j+1` sends an input view typed at depth `j' ≤ j` to an output typed at
   depth `j' − L`, provided `j'` is at least a threshold `t`.  Threshold
   and loss are per input (a uniform pair per form is impossible: the loss
   of applying a closure depends on the closures inside the input view).
   Composition of forms is unconditional (`Form.combine_typed`).
5. **Threshold and loss are computed, not existential.**  Packaging `t`
   and `L` existentially inside the depth quantifier loses them: an entry
   extracted from an applied view is typed at every depth, but each depth's
   proof may carry a different (possibly vacuous) threshold, and a later
   elimination through that entry needs one threshold valid at all depths.
   Carrying witness data through the relation fails on positivity (output
   witnesses genuinely depend on the input view's witnesses, since the
   `var` case returns the environment's view).  So a cost normalizer
   mirrors `hnf`/`atomView`/`morphismView`/`applyChain` and returns the
   elimination cost per input; the object clause of `FormTyped` uses this
   fixed function, and per-depth typedness at unbounded depth then implies
   uniform validity because the same number appears at every depth.
   Threshold and loss coincide (one cost per input; `member` pays `+1`).

   *Correspondence with the DOT soundness proofs.*  This is the same
   difficulty as transitivity pushback in Amin–Rompf–Odersky and the sized
   subtyping judgments there, and as possible types (WadlerFest) and
   invertible typing (Rapoport et al.): eliminating through a member
   declaration re-derives a subderivation, and the proof needs a measure
   showing the re-derivation is bounded.  Correspondences:
   - inert contexts ↔ prefix-typed stores with literal evidence checked at
     self `⊤` (`Store.Typed`); we get this for free;
   - invertible/tight typing ↔ the canonical-forms theorem; the derivation
     is a term here, so "rewrite to an invertible shape" is "normalize";
   - the size index and pushback accounting ↔ the depth index with
     computed costs.
   Ours is heavier because a closure stored in a view can be applied by a
   morphism that is not its ancestor, which breaks the subterm structure
   that lets Rapoport's proof be an induction on derivations.

6. **Inert stores, opened object coercions (2026-09-03).**  Three
   simplifications, all DOT-faithful, replace items 1, 4 and 5:
   - **S1.** Object literals carry witnesses and fields only; their precise
     type is the telescope generated from them (`eq self.A W.A`, `has ℓ`).
     No stored evidence, no self-at-`⊤` rule.  Facts beyond definitions are
     established by coercions in the term, as DOT's typing does.
   - **S3.** Object coercions `obj Tel m` are between *opened* telescopes
     (no self binder): the morphism is typed in `Γ` and mentions the roots
     it talks about; `has` entries of the target are inherited from the
     source by index.  Closed, self-mentioning object types are reached only
     by `foldSelf` at an atom.  This is exactly DOT, which has no subtyping
     rule between `μ` types.
   - (S2, DOT-shaped telescopes, turned out not to be needed.)
   Consequence: a coercion's normal form does not depend on the atom it is
   applied to, closures need no environments, `applyChain` is selection,
   and the normalizer is structural on closed evidence over the store.
   Termination is structural, typedness of forms is syntactic, and the
   depth-indexed relation, costs, thresholds, and the inversion/descent
   program (`notes-descent-lemma.md`) are unnecessary.  The difficulty they
   addressed was an artifact of *generic* self-eliminating morphisms, which
   the DOT translation never produces.

   *For later: a syntactic measure.*  Store evidence is well-founded by
   store position (self at `⊤` cannot be eliminated; prefix typing forbids
   forward references), so store views are canonical by induction on the
   store.  For closures from the term, every attempted loop (a closure
   applied inside its own run, two sibling closures applying each other)
   is blocked by a telescope-size argument: re-entering a closure's source
   type needs an `eq` entry or witness mentioning that object type, which
   forces strict containment.  This suggests termination by a measure on
   (store position, telescope containment), which would delete the depth
   apparatus and give a proof of the "simple soundness" shape.  Not
   pursued: forms are copied across coercions into entries typed by names
   (`self.ℓ`), so the measure needs a global invariant about which
   telescopes can be closure sources, and witness definitions break plain
   containment.  Revisit once the computed-cost proof is complete.

7. **Canonical forms, preservation, progress: done (2026-09-04).**
   `CanonicalForms.lean` proves, by structural induction on typing
   derivations over a typed store, that every closed inclusion normalizes
   to a typed head form, every atom has a typed view, and presence evidence
   names a field of the object at the root.  Two details found while
   proving:
   - *Typedness has two modes.*  A coercion form and a view are typed with
     plain shapes (`Γ.resolve`); their endpoints are closed types and are
     unrelated to any particular atom.  Only the chain of casts of an atom
     (`closedAtomForm`) is typed *at the atom's root*, where the shape of a
     type is its resolution with the self block opened at that root, so
     `foldSelf`/`unfoldSelf` are invisible to the chain.  Typing coercion
     forms at a root instead would be wrong: the `member` case extracts an
     entry form from a view and must re-use it as a coercion, at no root.
     Final form (2026-09-04, afternoon): there is one plain inductive
     `Γ ⊨ F : S ≤ T`, and the rooted judgment is a definition,
     `Γ ⊨[r] F : S ≤ T := Γ ⊨ F : Γ.resolveAt r S ≤ Γ.resolveAt r T`, so
     composition is proven once and plain typedness lifts to any root
     (`FormTyped.atRoot`) without any well-definedness hypothesis.  Entries
     of object forms and views of atoms are telescope-shaped inductives
     (`Entries`, `View`, with `∋ (i ↦ _)` like `Telescope.At`), and their
     typedness (`Γ ⊨ Es : Tel₁ ⇒ Tel₂`, `Γ ⊨[r, σ] V : Tel`) mirrors the
     telescope constructor by constructor.
   - *Object-form entries live over opened telescopes* (`Telescope s`, no
     self binder), so no instantiation root is needed; this also removes the
     corner case of a scope with no variables at all.
   The same file derives the chain theorem and discharges the
   `FormsTyped` obligation of `preservation` and the canonical-forms
   hypothesis of `erase_reflect` (`preservation'`, `erase_reflect'`);
   `Progress.lean` proves `progress` and `not_stuck`.  Modules in build
   order: `Normalizer`, `Resolution`, `FormTyping`, `FormAlgebra`,
   `CanonicalForms`, `Progress` (reorganized 2026-09-04 from nine files,
   with paper notation added throughout; see `FCdot/README.md`).  The
   depth/environment/cost modules of
   items 4-5 were deleted (last in commit `ed258ca`).  No `sorry`; axioms
   are `propext`, `Quot.sound`, plus `Classical.choice` in `progress` and
   `erase_reflect'`.  Cast-frame runs are bounded by `State.castMeasure`
   (`castRedex_normalize`).
