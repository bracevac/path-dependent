# DotMNF, at stage A3a of captures

DOT-MNF^cc, the capturing source of the translation in `../DotToFCdot`.

| module | contents |
|---|---|
| `Syntax` | paths, capture atoms (`{x} {κ} {x.C}`) and capture sets with union, decidable inclusion and pointwise renaming; shapes (`⊤ ⊥ {A:S..S} {a:T} {C:c..c} p.A μ ∀ ∧ □`) and types `S ^ C`; terms with the unboxing `C ⊸ x`, values with the box `□ x`, definitions with the capture member `{C = c}`; `Defs.labels`, `lookupTyp`, `lookupCap`, `lookupTrm`; `Shape.Decl` and its decision procedure `Shape.isDecl`, `Shape.Wf` and `Ty.Wf`, `Distinct` across the three definition kinds; `Tm.inspects` |
| `Typing` | contexts (`cons`, `consSelf` carrying the definitions, the self shape and the assigned use set, `consC` for a platform capture binder); `Subcap`, `SubShape`, `Sub`, `HasTy` with the use set as its first index, `DefsTy`, all Type-valued in one mutual block; the derived rules `Sub.refl`, `Subcap.empty`, `Subcap.ofVar`, `HasTy.widen`, `DefsTy.widen`; intersections are unrestricted (`And₁`, `And₂`, `And`, `And-I` and `Wf.and` carry no `Decl` premise); `Decl` still restricts the body of a `μ` (`Wf.mu`, `Rec-I`, `Rec-E`); `{}-I` admits same-block aliases (alias-tolerant resolution on the target side, no self-alias restriction here) |
| `Machine` | store with a data-free capture slot (`consC`), continuations, `Step` with the `unbox` step, `Steps`, `Final`, `Stuck`, `State.inspects`, the platform prefix and its initial store |
| `Erasure` | erasure to `Runtime`, a box becoming the runtime's inert box and an unboxing the runtime's `unbox`; `erase_step`, `erase_reflect`, `Tm.inspects_erase`, `State.inspects_erase` |
| `Examples` | E1 to E8 as `HasTy` derivations, restated at pure types and empty use sets; E8 is the refinement of an abstract type, `x.A ∧ {a : ⊤}`, with two derivations of its projection and an `And-I` derivation; the capture examples S3, C2 and C7 over the platform prefix of two capture binders |

Stage A3a replays on the source the split stage A0 made on the target: what the vanilla line called a
type is a shape, and a type is a shape with a capture set beside it.  Beyond the split the source gains
capture members, boxes, use sets and a platform capture binder.  A value is pure and its type's capture
set is the use set of its body without the binder; `Var` refines the binder's capture set to `{x}`, and
`sc-var` reads the declared set back off the context, so a `let` body that uses its binder is avoided by
subsumption.  Type-member bounds are shapes, so a capturing type enters a type member through a box.

One statement changed form.  `Subcap.var` is the context-reading `sc-var`, and the plan's form with a
typing premise is the derived rule `Subcap.ofVar`, admissible by induction on the typing derivation.
`erase_reflect` keeps the vanilla statement with no side condition: the runtime has an inert box of its
own, so a source box and a source object literal never share an erasure and a runtime step out of an
erased state names the source step that produced it.

`any` by position is stage A3b, and is not here yet.

## Stage A3a

| module | what A3a changed |
|---|---|
| `Syntax` | the split: `Shape` is the vanilla `Ty` and `Ty` is `Shape` with a `CaptureSet`, written `S ^ C`; `CapAtom` and `CaptureSet` with `∪`, `Subset` decided, and pointwise renaming; the new shapes `cap` and `box`; the new term `unbox` and the new value `box`; the new definition `cap`; `Shape.Decl`, `Shape.Wf` and `Ty.Wf` at the two sorts, with `cap` a declaration and `box` not one; `Defs.lookupCap`; `Tm.inspects` reads the root of an unboxing |
| `Typing` | `Ctx.consC`, the rigid platform binder, and `Ctx.lookup` weakening through it; `Subcap` as a judgement of its own, with `var`, `selLower` and `selUpper` in the mutual block; `SubShape` is the vanilla subtyping on shapes, with the new rules `cap` and `box`; `Sub` is the one rule `capt`; `HasTy` carries the use set as its first index, with the new rules `box` and `unbox` and with `sub` carrying the use-set subsumption beside the subtyping; `DefsTy` carries the use set and gains `cap`; the derived rules `Subcap.empty`, `Subcap.ofVar`, `HasTy.widen`, `DefsTy.widen` |
| `Machine` | `Store.consC` and lookup through it, the `unbox` step, the `Platform` prefix and `Platform.store`; a box is allocated by `alloc` like any value |
| `Erasure` | a box erases to the runtime's box and an unboxing to the runtime's unboxing, `⌊□ x⌋ = box x` and `⌊C ⊸ x⌋ = unbox x`; a capture slot erases to a capture slot; `step_unbox_erase`, `reflect_unbox`, and `erase_reflect` with no side condition |
| `Examples` | E1 to E8 restated at pure types and empty use sets, with the helpers `var'`, `subS`, `lam'`, `obj'`; the new helpers `varSelf`, `varAt`, `subC`, `HasTy.widenTo`; the platform prefix `plat` and its context `platCtx`; S3, C2 and C7 |

### The rules

```text
Ctx     ::= nil | cons Γ T | consSelf Γ d S U | consC Γ
Subcap  : Ctx s → CaptureSet s → CaptureSet s → Type
  refl, trans, elem (a decided inclusion), union
  var      : Γ ⊢ {x} <:ᶜ (Γ(x)).captureSet
  selLower : U; Γ ⊢ x : {C : c₁..c₂} ^ D  ⟹  Γ ⊢ c₁ <:ᶜ {x.C}
  selUpper : U; Γ ⊢ x : {C : c₁..c₂} ^ D  ⟹  Γ ⊢ {x.C} <:ᶜ c₂
SubShape : vanilla subtyping on shapes, plus
  cap      : Γ ⊢ c₁' <:ᶜ c₁ → Γ ⊢ c₂ <:ᶜ c₂' → Γ ⊢ {C : c₁..c₂} <: {C : c₁'..c₂'}
  box      : Γ ⊢ T <: T' → Γ ⊢ □ T <: □ T'
Sub      : capt (SubShape Γ S S') (Subcap Γ C C') : Γ ⊢ S ^ C <: S' ^ C'
HasTy    : CaptureSet s → Ctx s → Tm s → Ty s → Type
  Var    : {x}; Γ ⊢ x : (Γ(x)).shape ^ {x}
  All-I  : U↑ ∪ {x}; Γ, x : T₁ ⊢ t : T₂ → Ty.Wf T₁ → {}; Γ ⊢ λ(x : T₁) t : (∀(x : T₁) T₂) ^ U
  {}-I   : U↑ ∪ {x}; Γ, x : (μ(x. S)) ^ U ⊢ d : S → Distinct d → {}; Γ ⊢ ν(x. d) : (μ(x. S)) ^ U
  Box    : U; Γ ⊢ x : T → {}; Γ ⊢ □ x : (□ T) ^ {}
  Unbox  : U; Γ ⊢ x : (□ (S ^ C)) ^ D → Γ ⊢ C <:ᶜ U → U; Γ ⊢ C ⊸ x : S ^ C
  Sub    : U; Γ ⊢ t : T → Γ ⊢ T <: T' → Γ ⊢ U <:ᶜ U' → U'; Γ ⊢ t : T'
  All-E, {}-E, Let, Rec-I, Rec-E, And-I as vanilla, the use set passed through
DefsTy   : typ, trm and and as vanilla, at the use set, plus
  cap    : U; Γ ⊢ {C = c} : {C : c..c}
```

`{}-I` is stated with the binder `x : (μ(x. S)) ^ U` rather than with the opened self type, as the
vanilla rule is, since with intrinsic scoping a context entry lives before its own binder.  `Rec-I` and
`Rec-E` convert between the two.

### Theorems, restated and new

Nothing of the vanilla source is a theorem beyond the machine and the erasure, and every statement of
those is kept.  `erase_reflect` lost a hypothesis in the course of the stage and gained none.

```
DotMNF.erase_step        : Step st st' → Runtime.Step st.erase st'.erase
DotMNF.erase_reflect     : Runtime.Step st.erase r → ∃ st', Step st st' ∧ st'.erase = r
DotMNF.Tm.inspects_erase : t.inspects = some x → (Tm.erase t).inspects = some x
DotMNF.State.inspects_erase : st.inspects = some x → st.erase.t.inspects = some x
```

New in this stage, all in `Examples`:

```
DotMNF.Examples.S3_typed : [];            platCtx ⊢ S3tm : S3Ty
DotMNF.Examples.C2_typed : {κ₁,κ₂};       platCtx ⊢ C2tm : (Unit → Unit) ^ {κ₁,κ₂}
DotMNF.Examples.C7_typed : [];            platCtx ⊢ C7tm : C7Ty
DotMNF.Examples.C7Lit    : [];            C7Ctx2  ⊢ ν(z. {e₁ = □ f₁} ∧ {e₂ = □ f₂}) : (μ …) ^ {}
```

S3 is a type member instantiated with a boxed capturing type, `{A = □((Unit → Unit) ^ {f})}`, a field
`{elem = □ f}` declared at `z.A ^ {}`, and a client that projects, opens the member by its upper bound,
and unboxes at the use set `{f}`.  C2 is explicit capture polymorphism: one client typed against the
abstract member `{C : {}..{κ₁,κ₂}}`, whose call is charged to `{κ₁,κ₂}` by `sc-var` and `sc-sel-upper`,
and two literals that define `C` as `{κ₁}` and as `{κ₂}`, each retyped at the abstract member on its own
variable.  C7 is a container of two boxed capabilities, pure because both fields are declared at the
empty capture set, whose client unboxes the first element at the use set `{κ₁}` and never mentions
`{κ₂}`.  All three live over the platform prefix `Platform.cons (Platform.cons Platform.nil)`, whose
context is `platCtx` and whose store is `plat.store`.

Axioms (`#print axioms`): `propext` for the three derivations, and `propext` with `Quot.sound` for the
erasure theorems.  No `sorry`, `axiom`, `partial`, `unsafe`, or `native_decide`, and no Mathlib.
