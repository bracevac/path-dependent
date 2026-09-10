# DotMNF, at stage B0 of captures the compiler's way (unchanged since A3b)

DOT-MNF^cc, the capturing source of the translation in `../DotToFCdot`.

| module | contents |
|---|---|
| `Syntax` | paths, capture atoms (`{x} {κ} {x.C}`) and capture sets with union, decidable inclusion and pointwise renaming; shapes (`⊤ ⊥ {A:S..S} {a:T} {C:c..c} p.A μ ∀ ∧ □`) and types `S ^ C`; terms with the unboxing `C ⊸ x`, values with the box `□ x`, definitions with the capture member `{C = c}`; `Defs.labels`, `lookupTyp`, `lookupCap`, `lookupTrm`; `Shape.Decl` and its decision procedure `Shape.isDecl`, `Shape.Wf` and `Ty.Wf`, `Distinct` across the three definition kinds; `Tm.inspects` |
| `Typing` | contexts (`cons`, `consSelf` carrying the definitions, the self shape and the assigned use set, `consC` for a platform capture binder); `Subcap`, `SubShape`, `Sub`, `HasTy` with the use set as its first index, `DefsTy`, all Type-valued in one mutual block; the derived rules `Sub.refl`, `Subcap.empty`, `Subcap.ofVar`, `HasTy.widen`, `DefsTy.widen`; intersections are unrestricted (`And₁`, `And₂`, `And`, `And-I` and `Wf.and` carry no `Decl` premise); `Decl` still restricts the body of a `μ` (`Wf.mu`, `Rec-I`, `Rec-E`); `{}-I` admits same-block aliases (alias-tolerant resolution on the target side, no self-alias restriction here) |
| `Machine` | store with a data-free capture slot (`consC`), continuations, `Step` with the `unbox` step, `Steps`, `Final`, `Stuck`, `State.inspects`, the platform prefix and its initial store |
| `Erasure` | erasure to `Runtime`, a box becoming the runtime's inert box and an unboxing the runtime's `unbox`; `erase_step`, `erase_reflect`, `Tm.inspects_erase`, `State.inspects_erase` |
| `Examples` | E1 to E8 as `HasTy` derivations, restated at pure types and empty use sets; E8 is the refinement of an abstract type, `x.A ∧ {a : ⊤}`, with two derivations of its projection and an `And-I` derivation; the capture examples S3, C2 and C7 over the platform prefix of two capture binders; the `any` examples S1, S2 and C5, each written with `any`, expanded at the platform set, and typed at the expanded type |

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

`any` by position is stage A3b, below: it is a notation, expanded before a program is typed, and no
rule of the calculus mentions it.

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

## Stage A3b

`any` by position.  A capture set may hold the atom `any`, which the calculus never interprets: no
rule of `Subcap`, `SubShape`, `Sub`, `HasTy` or `DefsTy` mentions it, `elem` compares it syntactically
like any other atom, and renaming maps it to itself.  Its meaning is by position, and `expand` is what
gives it that meaning.  The codomain of an arrow reads `any` as the arrow's own set weakened together
with the parameter, a field type or a capture-member upper bound of an object reads it as the object's
set weakened together with the self, and the top of a program reads it as the platform set.  Each
former resets the reading for what is under it, so a nested occurrence is read by its own enclosing
former and no level is needed.  Every `any` is therefore a closed set once expanded, and an expanded
program is a program of stage A3a.

Four positions get no reading, and `AnyOk` refuses `any` there: the outer capture set of a parameter
type, both bounds of a type member, the lower bound of a capture member, and everything under a box.
The first is universal quantification over capture sets, which a program writes as an explicit capture
member instead, as S1 does; the other three are the compiler's tunneling.  Both decisions are the
user's to revisit, and the stage report records what each would cost.

| module | what A3b changed |
|---|---|
| `Syntax` | the atom `CapAtom.any` and its renaming clause; `CaptureSet.expand`, `Shape.expand`, `Ty.expand` and `Shape.expandSelf`; `CaptureSet.NoAny`, `Shape.NoAny`, `Ty.NoAny`, `Shape.AnyOk`, `Ty.AnyOk`, their decision procedures `noAny`/`anyOk` and their `Decidable` instances; the renaming facts the expansion lemmas need; the three required lemmas of the stage |
| `Typing` | nothing.  No rule mentions `any`, and `DecidableEq` still derives for `CapAtom`, so every `decide` of the A3a examples stands |
| `Machine`, `Erasure` | nothing, byte for byte A3a's |
| `Examples` | S1, S2 and C5, each written with `any`, `AnyOk` decided, `expand` at the platform set computed, and the derivation at the expanded type; the platform set `platSet`, the binders `fs1` to `fs5`, and the new helpers `Subcap.consAtom`, `HasTy.useSub`, `HasTy.captTo`, `fileLit`, `unitVal` |

### New definitions

```text
CapAtom.any                                          the inert atom
CaptureSet.expand C D                                every `any` of C replaced by the atoms of D
Ty.expand    (S ^ C) D = (S.expand (C.expand D)) ^ (C.expand D)
Shape.expand S D₀      D₀ the set of the type this shape sits in
  all T₁ T₂   ↦ all (T₁.expand []) (T₂.expand (D₀↑ ∪ {x}))
  mu S        ↦ mu (S.expandSelf (D₀↑ ∪ {z}))
  fld a T     ↦ fld a (T.expand D₀)
  cap C c₁ c₂ ↦ cap C (c₁.expand []) (c₂.expand D₀)
  typ A S₁ S₂ ↦ typ A (S₁.expand []) (S₂.expand [])
  box T       ↦ box (T.expand [])
  top, bot, sel unchanged, and pointwise
Shape.expandSelf S D                                 the `μ` body, D already under the self
CaptureSet.NoAny, Shape.NoAny, Ty.NoAny              no `any` at all, decided
Shape.AnyOk, Ty.AnyOk                                `any` only where `expand` reads it, decided
```

### New lemmas

```
CaptureSet.expand_of_noAny : C.NoAny → C.expand D = C
CaptureSet.noAny_expand    : D.NoAny → (C.expand D).NoAny
CaptureSet.expand_rename   : (C.expand D).rename ρ = (C.rename ρ).expand (D.rename ρ)
Shape.expand_of_noAny, Ty.expand_of_noAny : expansion is the identity where there is no `any`
Shape.noAny_expand,    Ty.noAny_expand    : AnyOk T → NoAny D → NoAny (T.expand D)
Shape.expand_rename,   Ty.expand_rename   : expansion commutes with renaming, the reading set renamed
Shape.expand_weaken,   Ty.expand_weaken   : the same at `Rename.succ`
```

with the clause lemmas `CaptureSet.expand_nil`, `expand_cons_any`, `expand_cons_var`,
`expand_cons_cvar`, `expand_cons_sel`, `expand_cons_of_ne`, `expand_append`, the `NoAny` clauses
`noAny_nil`, `noAny_cons_of_ne`, `noAny_of_cons`, `noAny_append`, `noAny_rename`, `noAny_weaken`, the
two facts `CaptureSet.self_rename` and `CaptureSet.noAny_self` about the set an arrow or an object
reads `any` as under its own binder, the renaming facts `CaptureSet.rename_cons`, `rename_append`,
`rename_rename`, `weaken_rename` and `CapAtom.rename_rename`, `Shape.expandSelf_eq`, `Shape.expand_mu`,
and the twenty-two clause lemmas `Shape.noAny_*`, `Ty.noAny_capt`, `Shape.anyOk_*`, `Ty.anyOk_capt`,
which read the four decision procedures as the propositions they stand for.

### The examples

```
DotMNF.Examples.S1_anyOk  : (S1TyAny k1).AnyOk
DotMNF.Examples.S1_expand : (S1TyAny k1).expand platSet = S1Ty k1
DotMNF.Examples.S1_typed  : {fs};  platCtx ⊢ S1tm : ⊤ ^ {fs}
DotMNF.Examples.S2_anyOk  : (S2MkTyAny k1).AnyOk
DotMNF.Examples.S2_expand : (S2MkTyAny k1).expand platSet = S2MkTy k1
DotMNF.Examples.S2_typed  : {fs};  platCtx ⊢ S2tm : ⊤ ^ {fs}
DotMNF.Examples.C5_typed  : {fs};  S2Ctx3  ⊢ let n = it.next in n un : ⊤ ^ {fs}
```

S1 is `withFile` with an explicit capture parameter,

```text
withFile : (∀(cp : (μ(c. {C : {}..{fs}})) ^ {})
             (∀(op : (∀(f : File ^ {fs}) ⊤) ^ {cp.C}) (⊤ ^ {any})) ^ {fs, cp}) ^ {fs}
```

with `File := μ(f. {read : (⊤ → ⊤) ^ {f}})`.  The member bound is written out, because a member-bound
`any` would read as the parameter object's own set with its self, which is not what a pure parameter
object wants; the result `any` reads as `{fs, cp, op}`, and `S1_expand` computes that.  The caller
allocates `ν(c. {C = {fs}})` at the precise member `{fs}..{fs}`, passes it at the abstract member by
`Rec-E`, `Cap` and `Rec-I`, and passes an operation declared at `{fs}`, which the *lower* bound of the
precise member puts below `{cp.C}`.  The answer avoids both binders through the member's upper bound,
so the program's use set is `{fs}`.

S2 is a class with a capture-set parameter and `any` in the result,

```text
Iterator := μ(i. {C : {}..{fs}} ∧ {next : (∀(v : ⊤) (⊤ ^ {i.C})) ^ {i.C}})
mk       : (∀(u : ⊤) (Iterator ^ {any})) ^ {fs}
```

The result `any` reads as `{fs, u}`.  The callee returns a literal that defines `C = {fs}`, retyped at
the abstract member on its own variable, which is the packing.  The caller types
`let it = mk un in let n = it.next in n un` against the abstract member: `sc-var` and then
`sc-sel-upper` charge its call, so its use set is `{fs}` and the literal's own `{fs}` is never named.

C5 is that caller on its own, the existential result at the compiler's reading: the only step of it
that names `{fs}` is `sc-sel-upper` at the member's upper bound.  Its target side is in
`../FCdot/README.md`.

Axioms (`#print axioms`): none for `S1_anyOk`, `S1_expand`, `S2_anyOk`, `S2_expand` and `C5_typed`,
`propext` for `S1_typed` and `S2_typed`.

## Stage B0

B0 changed nothing here.  The stage adds the universal root, levels and the level rule to the
target only, and it adds no source former: `DOT-MNF^cc` has no atom for the universal root, so
every capture set the source writes is a list of concrete atoms, exactly as at A3b.  No rule,
no theorem, no example and no line of this directory moved.
