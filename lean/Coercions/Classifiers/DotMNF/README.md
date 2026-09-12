# DotMNF, at stage K3 of classifiers

DOT-MNF^cc, the capturing source of the translation in `../DotToFCdot`.

**Stages K0 and K1 of classifiers changed nothing here, K2 is the stage that classifies the source,
and K3 adds only the three mandatory examples.**  Through K1 the source wrote no classifier and no
projected capture atom, so no syntax, no rule, no judgment and no theorem of this directory moved.
K2 gives the source the projected capture atom, the kind-bounded capture member, the classified
context binder and its own capture-kinding judgment.  K3 adds no new form: E1, E2 and E3, each a
platform, a program typed against it, and the source half of its kinding and prediction facts, are
appended to `Examples.lean` after C2, and the stage's section is the last one below.  Every statement
of the stages before K3 is the statement it was, with the proof it had, except the three rows K2
lists.

| module | contents |
|---|---|
| `Syntax` | paths, capture atoms (`{x} {κ} {x.C}`) and capture sets with union, decidable inclusion and pointwise renaming; shapes (`⊤ ⊥ {A:S..S} {a:T} {C:c..c} p.A μ ∀ ∧ □`) and types `S ^ C`; terms with the unboxing `C ⊸ x`, values with the box `□ x`, definitions with the capture member `{C = c}`; `Defs.labels`, `lookupTyp`, `lookupCap`, `lookupTrm`; `Shape.Decl` and its decision procedure `Shape.isDecl`, `Shape.Wf` and `Ty.Wf`, `Distinct` across the three definition kinds; `Tm.inspects` |
| `Typing` | contexts (`cons`, `consSelf` carrying the definitions, the self shape and the assigned use set, `consC` for a platform capture binder, `consRoot` for a scope root, `consInst` for an instance binding); `Subcap`, `SubShape`, `Sub`, `ESub`, `HasTy` with the use set as its first index and an answer as its type index, `DefsTy`, all Type-valued in one mutual block; the derived rules `Sub.refl`, `Subcap.empty`, `Subcap.ofVar`, `HasTy.widen`, `DefsTy.widen`; intersections are unrestricted (`And₁`, `And₂`, `And`, `And-I` and `Wf.and` carry no `Decl` premise); `Decl` still restricts the body of a `μ` (`Wf.mu`, `Rec-I`, `Rec-E`); `{}-I` admits same-block aliases (alias-tolerant resolution on the target side, no self-alias restriction here) |
| `Machine` | store with a data-free capture slot (`consC`), continuations with the unpacking frame `consE`, `Step` with the `unbox`, `letex`, `unpack` and `allocE` steps, `Steps`, `Final`, `Stuck`, `State.inspects`, the platform prefix and its initial store |
| `Erasure` | erasure to `Runtime`, a box becoming the runtime's inert box and an unboxing the runtime's `unbox`; `erase_step`, `erase_reflect`, `Tm.inspects_erase`, `State.inspects_erase` |
| `Examples` | E1 to E8 as `HasTy` derivations, restated at pure types and empty use sets; E8 is the refinement of an abstract type, `x.A ∧ {a : ⊤}`, with two derivations of its projection and an `And-I` derivation; the capture examples S3, C2 and C7 over the platform prefix of two capture binders; the `any` examples S1, S2 and C5, each written with `any`, expanded at the platform set, and typed at the expanded type, and the `fresh` examples Z1, Z2 and Z3, each written with `fresh`, decided `FreshOk`, expanded by `rfl` and typed at the expanded type, with a caller for Z1 that unpacks by `letex` |

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
rule of the calculus mentions it.  Stage B3 keeps the notation and changes the reading: a position is
read by the root that encloses it and no longer by the former it sits in.  The A3b section below is
the historical record of the first reading, and every clause and every lemma of it that B3 replaced
is restated in the B3 section at the end.

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
two facts about the set an arrow or an object read `any` as under its own binder (deleted in B3, with
`CaptureSet.noAny_weaken`, `CaptureSet.weaken_rename`, `CaptureSet.noAny_cvar` and
`CaptureSet.cvar_here_rename` in their place), the renaming facts `CaptureSet.rename_cons`, `rename_append`,
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

## Stage B1

B1 moves the source, because the source arrow has to bind the same binders in the same places
as the target's.  That is what keeps the translation homomorphic on types and erasure equality
free.  `Shape.all` becomes `Ty (Sig.dom s) → Ty (Sig.cod s) → Shape s`, which B2 re-sorts to
`Ty (Sig.dom s) → ETy (Sig.cod s) → Shape s`, so a source arrow
carries the parameter's `any` as one capture binder for the whole domain, and a lambda body and
an object body are scopes with a root of their own.

The source's context gains a root constructor beside its rigid one rather than a payload, so
`Platform.ctx` and `Platform.store` are textually unchanged and every platform binder is still
rigid.  The argument premise of `app` costs the source nothing: its variable rule already gives
a variable its shape at the singleton set `{y}`, which is `T₁⟦κ := {y}⟧` when the parameter's
`any` is at the top of the domain, and that is the source-side counterpart of the target's
`recap`.

| module | what B1 changed |
|---|---|
| `Syntax` | `Shape.all` at `Sig.dom s` and `Sig.cod s`, with `Dom`, `Cod`, `Dom.underRoot`, `Dom.inBody`, `Cod.underRoot`, the source's copies of the target's five names.  `Value.obj` at `Defs ((s,c),x)` and `Value.lam` at `Ty (Sig.dom s)` and `Tm (Sig.body s)`.  One lift per binder in `Shape.rename` and `Value.rename`, and `Shape.expand` weakening its carried set once more.  the two-binder twins of the A3b self facts, both deleted again in B3.  The substitution block: `Subst` with an atom-valued capture component, `Subst.ofRename`, `.lift`, `.liftC`, `.singleC`, `.arg`, `.enter` and `.enterObj` (which write `any` where the target writes `⊤ᶜ`), the eight traversals `CapAtom.subst` to `Defs.subst`, `Subst.funext` and the eight `X.subst_ofRename` |
| `Typing` | the context constructor `Ctx.consRoot`, with one clause in `Ctx.lookup`.  `Shape.underRoot`, `Ctx.scope`, `Ctx.body`, `Ctx.objBody`.  The rules `SubShape.all`, `HasTy.lam`, `HasTy.app` and `HasTy.obj` |
| `Machine` | `Step.app` continues at `t.subst (Subst.enter y)` and `Step.proj` at `t.subst (Subst.enterObj x)`.  `Platform.store`, `alloc`, `rename`, `let` and the two `unbox` steps are untouched |
| `Erasure` | the `lam` and `obj` clauses of `Value.erase_rename` carry one lift per binder.  The new block "erasure commutes with substitution": `Subst.lift_var`, `Subst.liftC_var`, `Subst.enter_var`, `Subst.enterObj_var`, `appendFields_map`, and the mutual `Tm.erase_subst`, `Value.erase_subst`, `Defs.erase_subst`.  `Tm.erase` keeps its type and every other statement of the file keeps its form |
| `Examples` | every derivation E1 to E8, S1 to S3 and C1 to C7 keeps its name and its conclusion, with the contexts rebuilt as `Ctx.body` and `Ctx.objBody` chains and outer binders read through the new `up` and `up2`.  `lam'` and `obj'` are the two helpers for writing a body over the scope signature.  `E4G'` and `E4GS'` are replaced by the parameterised `E4G w` and `E4GS w`, and `C7k1` and `C7k2` are new |

### The rules

```
DotMNF.SubShape.all : Sub Γ.scope T2.underRoot T1.underRoot →
                      Sub (Γ.body T2) U1.underRoot U2.underRoot →
                      SubShape Γ (.all T1 U1) (.all T2 U2)
DotMNF.HasTy.lam    : HasTy (U↑↑↑ ∪ [.var .here]) (Γ.body T₁) t T₂.underRoot → Ty.Wf T₁ →
                      HasTy [] Γ (.val (.lam T₁ t)) ((Shape.all T₁ T₂) ^ U)
DotMNF.HasTy.app    : HasTy U Γ (.path (.var x)) ((Shape.all T₁ T₂) ^ C) →
                      HasTy U Γ (.path (.var y)) (T₁.subst (Subst.singleC (.var y))) →
                      HasTy U Γ (.app x y) (T₂.subst (Subst.arg y))
DotMNF.HasTy.obj    : DefsTy (U↑↑ ∪ [.var .here]) (Γ.objBody d S U) d S.underRoot →
                      Defs.Distinct d → HasTy [] Γ (.val (.obj d)) ((Shape.mu S) ^ U)
DotMNF.Step.app     : ⟨σ, K, .app x y⟩ ⟶ ⟨σ, K, t.subst (Subst.enter y)⟩
DotMNF.Step.proj    : ⟨σ, K, .proj x ℓ⟩ ⟶ ⟨σ, K, t.subst (Subst.enterObj x)⟩
```

### Statements restated

Nothing was weakened, and no rule gained a hypothesis.

```
DotMNF.Shape.all                 : Ty (Sig.dom s) → Ty (Sig.cod s) → Shape s
                                     the arrow gains the parameter's any as one capture
                                     binder, in the target's position.  B2 re-sorts the
                                     codomain to ETy (Sig.cod s)
DotMNF.Shape.rename, .expand     : one lift per binder, the same set carried further out
DotMNF.Shape.noAny_all, .anyOk_all : the same propositions at the arrow's new arities
DotMNF.Value.lam, .obj           : the body root and the class root as binders of the value,
                                     mirroring FCdot.Value.lam and .obj
DotMNF.Ctx.lookup                : one clause at consRoot, which binds no term variable
DotMNF.SubShape.all              : both arrows' capture binders opened at one scope
DotMNF.HasTy.lam, .obj           : the same body and the same charge, under the new binders
DotMNF.HasTy.app                 : the argument premise is what the variable rule already gave
DotMNF.Step.app, .proj           : the same variable instantiated by the same argument, and
                                     the new capture binders carry no runtime data
DotMNF.Tm.erase                  : keeps its type Tm s → Runtime.Tm s
DotMNF.dot_safety, .dot_not_stuck, .reachable_consistent, .reachable_realized,
DotMNF.dot_capture_prediction, .dot_effect_safety : unchanged
DotMNF.erase_step, .erase_reflect : unchanged
```

### New definitions and lemmas

```
DotMNF.Dom, .Cod, .Dom.underRoot, .Dom.inBody, .Cod.underRoot
DotMNF.Ctx.consRoot, .Shape.underRoot, .Ctx.scope, .Ctx.body, .Ctx.objBody
DotMNF.Subst and the eight traversals, with Subst.funext and the eight X.subst_ofRename
DotMNF.Tm.erase_subst, .Value.erase_subst, .Defs.erase_subst
```

No `Subst.comp` and no fusion lemmas exist on the source side, because nothing in the source
needs them.  The only composite the source performs is `Subst.ofRename`, and
`X.subst_ofRename` covers it.

### The examples

Every example of A3a and A3b is here, rewritten for the new arrow and otherwise unchanged.  The
`any` examples S1, S2 and C5 are still written with `any`, expanded at the platform set by
`rfl`, and typed at the expanded type, so `S2_expand` still reads the result `any` as `{fs, u}`.
That concrete set is what the target's `S2_level` and `C5a_level` put below a scope root.

## Stage B2

B2 gives the source a result `fresh` and the reading that expands it.  `fresh` is a capture
atom, inert: no rule of `Subcap`, `SubShape`, `Sub`, `ESub`, `HasTy` or `DefsTy` mentions it,
and the translation drops it as it drops `any`.  What reads it is `Ty.expandFresh`, a function
run before typing, exactly as `expand` reads `any`.  A result `fresh` becomes an existential
bounded by what the function can hold: its own assigned capture set united with its parameter.
That bound is decision 18, and it is exactly the set the callee's own closing evidence proves,
so every pack the examples need types with `refl`, `elem` and one instance step.

The source's answer sort mirrors the target's, binder for binder.  `Shape.all` re-sorts its
codomain to `ETy (Sig.cod s)`, `Cod` follows, and `ETy` has the same two constructors with the
same declared bound.  `Ctx` gains an instance binding, `Ctx.consInst`, which is Capless's
`CBinding.inst`, and `Ctx.scopeInst` opens a root of its own and then the instance binder, as
the target's does.  `Subcap` gains one rule, `inst`, which is Capless's `cinstr` and is the
source twin of the target's `CapEq.instC`.  `ESub` is inclusion between answers, with `ty`,
`pack` and `exist`.  Packing is subsumption on the source side, which is decision 19: there is
no source term former for a pack, and `HasTy.sub` carries it.  `Tm` gains `letex` and `HasTy`
gains the matching rule, with the declared use set of D6 and the avoidance of Capless.

`FreshOk` is a `Bool`-valued test, so `decide` closes it, and `expandFresh` computes, so the
expanded type is stated and checked by `rfl`.  A `fresh` is allowed in exactly one position,
the top-level capture set of the result of the very arrow that carries it, and `Ty.freshOk`
refuses every other.  A `fresh` in a parameter is refused, which is checked.

| module | what B2 changed |
|---|---|
| `Syntax` | `ETy` with `∃ᶜ[C] T`, its traversals, its `expand`, `noAny`, `anyOk` and `Wf`, and `Cod s = ETy (Sig.cod s)` with `Shape.all` spelling the same type out.  `Cod.underRoot` one sort up.  `CapAtom.fresh`, with one clause each in `CapAtom.rename`, `CapAtom.subst`, `CaptureSet.expand` and `CaptureSet.noAny`.  The `fresh` machinery: `CaptureSet.noFresh`, `CaptureSet.substFresh`, the three `noFresh` and three `substFresh` traversals, `ETy.codFreshOk`, `Shape.freshOk`, `Ty.freshOk`, `Ty.NoFresh`, `Ty.FreshOk` and `Ty.expandFresh`.  `Tm.letex` with one clause in each term traversal |
| `Typing` | `Ctx.consInst` with one clause in `Ctx.lookup`, `Ctx.instSet?`, `abbrev Ctx.InstOf`, `Ctx.scopeInst`.  `Subcap.inst`.  `ESub` with `ty`, `pack` and `exist`, and `ESub.refl` beside `Sub.refl`.  `SubShape.all`'s codomain premise at the answer sort.  `HasTy` indexed by `ETy s`, with `abbrev HasTyP` for a plain answer, `HasTy.sub` at `ESub`, and the new rule `HasTy.letex` |
| `Machine` | `Cont.consE` with one clause in `Cont.rename`, `Cont.weakenC`, and the three steps `Step.letex`, `Step.unpack` and `Step.allocE`.  `State.Final` and `State.Stuck` are untouched |
| `Erasure` | `Tm.erase` and `Cont.erase` gain the `letex` and `consE` clauses, so the source and the target erase a `letex` to the same runtime term.  `erase_step` gains three cases and `erase_reflect` ten, and neither gains a hypothesis |
| `Examples` | the three `fresh` examples Z1, Z2 and Z3 with their `FreshOk`, `expandFresh` and `NoFresh` statements, the callee of each typed at the expanded type, and a caller for Z1 that unpacks by `letex`.  Every older derivation keeps its name and its conclusion, with `HasTy` at a plain answer spelled `HasTyP` and arrow codomains spelled `.ty` |

### The rules

```
DotMNF.Subcap.inst    : Ctx.InstOf Γ κ C → Subcap Γ C [.cvar κ]
DotMNF.ESub.ty        : Sub Γ T T' → ESub Γ (.ty T) (.ty T')
DotMNF.ESub.pack      : Subcap Γ C C₀ →
                        Sub (Γ.scopeInst C) ((T'↑)↑) (Dom.underRoot T) →
                        ESub Γ (.ty T') (∃ᶜ[C₀] T)
DotMNF.ESub.exist     : Subcap Γ C₀ C₀' →
                        Sub Γ.scope (Dom.underRoot T) (Dom.underRoot T') →
                        ESub Γ (∃ᶜ[C₀] T) (∃ᶜ[C₀'] T')
DotMNF.HasTy.sub      : HasTy U Γ t E → ESub Γ E E' → Subcap Γ U U' → HasTy U' Γ t E'
DotMNF.HasTy.letex    : HasTy U₁ Γ t (∃ᶜ[C₀] T) → Subcap Γ C₀ U₂ →
                        HasTy ((U₂↑)↑ ∪ [.cvar (.there .here)]) ((Γ.consC).cons T) u ((E↑)↑) →
                        HasTy (U₁ ∪ U₂) Γ (.letex t u) E
DotMNF.Step.letex     : ⟨σ, K, .letex t u⟩ ⟶ ⟨σ, K.consE u, t⟩
DotMNF.Step.unpack    : the frame is opened at a variable, the store pushes consC
DotMNF.Step.allocE    : the same at a value, allocated first
```

### Statements restated

Nothing was weakened, and no rule gained a hypothesis.

```
DotMNF.Shape.all            : Ty (Sig.dom s) → ETy (Sig.cod s) → Shape s
                                the constructor keeps its arity and both positions, only the
                                sort of the second widens, and a plain codomain is .ty T
DotMNF.Cod, .Cod.underRoot  : the codomain is an ETy, the same renaming one sort up
DotMNF.Shape.rename, .subst, .expand, .noAny, .anyOk : .all clauses letter for letter, with
                                the codomain call resolving to the ETy twin
DotMNF.Shape.noAny_all, .anyOk_all, .expand_of_noAny, .noAny_expand, .expand_rename,
  .subst_ofRename, .rename_inj : statements unchanged, the .all case citing the ETy twin
DotMNF.Shape.Wf.all         : the same obligation on the same two sides, the codomain read at
                                the answer sort, where ETy.Wf (.ty T) is Ty.Wf T
DotMNF.SubShape.all         : codomain premise at the answer sort, mirroring the target's
                                ShapeCo.HasType.pi
DotMNF.CapAtom              : one constructor more, fresh, additive and inert
DotMNF.Ctx, DotMNF.Ctx.lookup : one constructor more, consInst, additive
DotMNF.Subcap               : one rule more, inst, additive
DotMNF.Tm                   : one former more, letex, additive
DotMNF.HasTy                : indexed by ETy s, with HasTyP U Γ t T = HasTy U Γ t (.ty T)
                                every rule keeps its text with .ty written round its plain
                                type, so every statement written HasTy U Γ t T at a type is
                                HasTyP U Γ t T, which is the proposition it was
DotMNF.HasTy.sub            : the answer premise is an ESub
                                at a plain answer ESub.ty d is the old premise, so the rule is
                                the rule it was
DotMNF.HasTy.widen          : stated at an answer, which is forced by the index and not chosen
DotMNF.DefsTy.trm           : premise at .ty T, which is the old premise
DotMNF.Subcap.ofVar         : argument at .ty (S ^ C), and the dependent match excludes the
                                two ESub constructors with an existential right endpoint
DotMNF.Tm.erase, .Cont.erase : one clause each, and a source letex erases to the runtime letex
DotMNF.erase_step, .erase_reflect : unchanged, with three and ten cases more
DotMNF.dot_safety, .dot_not_stuck, .reachable_consistent, .reachable_realized,
DotMNF.dot_capture_prediction, .dot_effect_safety : unchanged, at a plain answer
```

### New definitions and lemmas

```
DotMNF.ETy, with rename, subst, weaken, substVar, expand, noAny, anyOk, NoAny, AnyOk, Wf
DotMNF.ETy.expand_of_noAny, .noAny_expand, .expand_rename, .subst_ofRename
DotMNF.CapAtom.fresh
DotMNF.CaptureSet.noFresh, .substFresh
DotMNF.Shape.noFresh, .Ty.noFresh, .ETy.noFresh
DotMNF.Shape.substFresh, .Ty.substFresh, .ETy.substFresh
DotMNF.ETy.codFreshOk, .Shape.freshOk, .Ty.freshOk, .Ty.NoFresh, .Ty.FreshOk
DotMNF.Ty.expandFresh
DotMNF.Ctx.consInst, .Ctx.instSet?, .Ctx.InstOf, .Ctx.scopeInst
DotMNF.Subcap.inst, .ESub, .ESub.refl, .HasTyP, .HasTy.letex
DotMNF.Tm.letex, .Cont.consE, .Cont.weakenC
DotMNF.Step.letex, .Step.unpack, .Step.allocE
DotMNF.Tm.erase_letex, .Cont.erase_weakenC, .reflect_letex
```

### The examples

Every example of A3a, A3b, B0 and B1 is here and unchanged in meaning.  Three are new, and each
is written with `fresh`, decided `FreshOk`, expanded by `rfl` to a stated `fresh`-free type,
and then typed at that type.

```
DotMNF.Examples.Z1_freshOk     : (Z1TyF k1).FreshOk
DotMNF.Examples.Z1_expandFresh : (Z1TyF k1).expandFresh = Z1Ty k1
DotMNF.Examples.Z1_noFresh     : (Z1Ty k1).NoFresh
DotMNF.Examples.Z1_typed       : HasTyP [] Γ Z1Tm (Z1Ty fs)
DotMNF.Examples.Z1_caller      : HasTyP (Z1Use ∪ Z1Use) Z1Ctx
                                   (.letex (.app (.there .here) .here) (.let ... unitTm)) unitTy
DotMNF.Examples.Z2_freshOk, .Z2_expandFresh, .Z2_noFresh, .Z2_typed
DotMNF.Examples.Z3_freshOk, .Z3_expandFresh, .Z3_noFresh, .Z3_typed
DotMNF.Examples.Z1_plat, .Z2_plat, .Z3_plat : the three callees over the platform prefix
```

**Z1, `freshCell`.**  The callee is `λ(u : ⊤). let c = ν(f. {read = λ(v). v}) in c`, written at
`(∀(u : ⊤) (Cell ^ {fresh})) ^ {fs}`.  `expandFresh` reads the result `fresh` as `{fs, u}`, the
callee's own assigned set with its parameter, and the pack's witness is `{u}`, the set the
literal was allocated at.  The residual inclusion of the pack is `sc-inst`, which is the one
new `Subcap` rule.  The caller unpacks by `letex`, charges the read of the unpacked cell to the
opened binder itself, and hands back a pure closure.  No root is named anywhere in it, which is
what the declared bound buys.

**Z2, `makeLogger`.**  The parameter is a capability at the arrow's own capture binder and the
callee is pure, so `expandFresh` reads the result `fresh` as `{x}`, the parameter alone.  The
witness is the parameter and not a platform binder, and that is the example's point.

**Z3, C5b.**  S2's `mk` with the result declared `fresh` instead of `any`.  The capture member
packs the literal's `{fs}`, exactly as it did at A3b, and the existential packs the whole
result on top of it.  `expandFresh` reads the bound as `{fs, u}`, which is the same concrete
set S2's `any` expanded to.

## Stage B3

B3 is the source read the compiler's way.  The notation `any` is unchanged and no rule of the
calculus mentions it, but the reading is by position now: `expand` threads the set that the root
enclosing the position stands for, and passes it under an arrow's codomain and under a `μ` body
without touching it.  It is reset at exactly two kinds of place, the positions where `any` is
forbidden and an arrow's domain.  A domain reads `any` as the arrow's own capture binder, which is
what turns the arrow into a capture-parameter arrow.  A3b recomputed the reading at every former, so
an `any` was read by what stood at its position.  The compiler's way reads it by where it stands.

The source has no universal root atom, and it must not have one.  A top-level `any` therefore reads
as the program's platform set.  `Ctx.reading` is the statement of where a reading comes from: the
innermost root binder of the context as a singleton, and the platform set where the context has
none.  It is not used by `expand`, which takes the reading as its argument.  It is what an example
cites when it writes a type at a position.

B3 also gives the source the target's level machinery and one rule.  A level is a position on the
spine and not a field on a binding: the level of a binder is the innermost root binder of the prefix
before it, a root is its own level, and `none` is the outermost level.  `Ctx.lvlLeB e r` says that
the level of `e` is `r` or encloses it, and `Subcap.level` reads that order.  It is the compiler's
`acceptsLevelOf`.  Because the source names no universal root, a notation is below no root, so
`lvlLeB` is `false` at `any` and at `fresh` on either side.

The source has never had a term-level expansion, and it has one now.  A lambda's domain annotation
may hold `any` in its outer set and nowhere else, and `Tm.expand` descends at `let`, at `letex` and
through a value into a lambda's body, so a notation written inside a program is read and not left
standing.

| module | what B3 changed |
|---|---|
| `Syntax` | three clauses of `Shape.expand` (`.mu`, and the domain and the codomain of `.all`) and one of `Ty.expand`.  The `.all` clause of `Shape.anyOk` and its characterisation `Shape.anyOk_all`.  The proofs, not the statements, of `Shape.noAny_expand`, `Ty.noAny_expand` and `Shape.expand_rename`.  `Shape.expand_mu` restated.  The four A3b self helpers deleted, with `CaptureSet.noAny_cvar` and `CaptureSet.cvar_here_rename` added.  The term level: `Ty.domAnyOk` and `Ty.DomAnyOk`, `Defs.noAny`, `Value.noAny`, `Tm.noAny`, `Value.anyOk`, `Tm.anyOk` with their `abbrev` propositions, `Value.expand` and `Tm.expand`, and `Ty.noAny_expand_dom` |
| `Typing` | `Ctx.root?` and `Ctx.reading`.  The whole `Levels` section, `Ctx.lvl`, `Ctx.rootB`, `Ctx.isRootB`, `Ctx.lvlLeB`, `Ctx.IsRoot`, `Ctx.LvlLe`, the nine spine facts, the five weakening commutations and the four scope-order facts of T-B3.1.  One rule, `Subcap.level`.  One import line, `FCdot.Context`, for `BVar.depth` and `depthGe`, which are reused and not copied |
| `Machine`, `Erasure` | nothing, byte for byte B2's |
| `Examples` | S1 and S2 re-expanded at the new reading, with both readings of each printed side by side.  The worked examples W1 to W6 of the compiler's write-up on the source side.  The two `Ctx.reading` facts.  `C2_anyOk`, `C2_expand`, `C5b_anyOk` and `C5b_expand`, the regression that expansion is inert where no notation is written.  The two-call context `Z1BodyCtxSrc` with its level facts.  The five weakened platform sets `platSet1` to `platSet5` and the two readers `readUnder` and `S1ReadAt` |

### The rules

```
DotMNF.Subcap.level : Ctx.IsRoot Γ (.cvar κ) → Ctx.LvlLe Γ e (.cvar κ) →
                      Subcap Γ [e] [.cvar κ]
```

One rule, additive.  Both premises are `Bool` computable, so every instance is decided in the
kernel.  The rule is directional where the compiler's test is not, and that is decision 34: the level
order relates the arrow's capture binder and the body root in both directions, but the rule asks for
a root on its right and the arrow binder is a `consC`, so only one direction is an instance.

### Statements restated

Nothing was weakened and no rule gained a hypothesis.  What changed is which set a notation stands
for, and no soundness statement depends on that: no rule of `Subcap`, `SubShape`, `Sub`, `ESub`,
`HasTy` or `DefsTy` mentions `expand`.

```
DotMNF.Shape.expand, .mu clause   : S.expand D₀↑ where it was S.expand (D₀↑ ∪ {self})
                                      decision 26.  A μ binds only the self, so the class root is
                                      not nameable in it and the self is not part of the reading.
                                      A field that captures the self writes {self}
DotMNF.Shape.expand, .all domain  : T₁.expand [κ] where it was T₁.expand []
                                      decision 24.  The atom is the consC of Ctx.scope, a de Bruijn
                                      reference into the domain's own signature, so the clause
                                      produces no root atom and no atom changes its binder
DotMNF.Shape.expand, .all codomain: the reading is only weakened twice, where it was also united
                                      with the arrow's set and its parameter
                                      decision 25.  A source arrow binds no body root, so a result
                                      any reads as the root enclosing the arrow
DotMNF.Ty.expand                  : .capt (C.expand D) (S.expand D)
                                      decision 22.  The reading of a position is the root enclosing
                                      it and not the type written there, so the type's own set is
                                      no longer the reading of its shape
DotMNF.Shape.expand_mu            : the μ clause read as an equation, still by rfl
DotMNF.Shape.anyOk, .all clause   : S₁.noAny && ETy.anyOk T₂, where it was
                                      C₁.noAny && S₁.anyOk && ETy.anyOk T₂
                                      decision 24.  A parameter any becomes legal and an any deeper
                                      in a domain becomes illegal, both checked by decide.  The
                                      predicate is still the decision procedure of "every any sits
                                      in a position expand gives a reading to"
DotMNF.Shape.anyOk_all            : the new clause read as a proposition, nothing more
DotMNF.Shape.noAny_expand, .Ty.noAny_expand, .Shape.expand_rename
                                  : statements kept, proofs rewritten at the new clauses
DotMNF.ETy.expand                 : textually unchanged, its value moving through Ty.expand
DotMNF.Examples.S1_expand         : (S1TyAny k1).expand platSet = S1Ty k1 S1Read
                                      S1Ty gained the reading as a parameter, so the equation names
                                      the reading it is taken at instead of leaving it implicit
DotMNF.Examples.S2_expand         : (S2MkTyAny k1).expand platSet = S2MkTyCC, the same
DotMNF.Examples.S1_typed          : the program's type and use set are the platform set, where
                                      they were {fs}: the result any it hands back reads as the
                                      platform set now, which is the observable content of B3
DotMNF.Examples.S2_typed          : the program's type is still ⊤ ^ {fs}, charged through the
                                      member's upper bound.  The use set is the platform set, as
                                      it is declared at the platform set
DotMNF.Examples.C5_typed          : the same, type kept and use set widened
```

### New definitions and lemmas

```
DotMNF.Ctx.root?, .Ctx.reading
DotMNF.Ctx.lvl, .Ctx.rootB, .Ctx.isRootB, .Ctx.lvlLeB, .Ctx.IsRoot, .Ctx.LvlLe
DotMNF.Ctx.depthGe_step, .Ctx.depthGe_there
DotMNF.Ctx.root?_isRoot, .Ctx.lvl_root, .Ctx.lvl_isRoot, .Ctx.root?_min, .Ctx.root?_none
DotMNF.Ctx.LvlLe.refl_of_root, .Ctx.LvlLe.trans
DotMNF.Ctx.lvlLeB_weaken, .lvlLeB_weakenSelf, .lvlLeB_weakenC, .lvlLeB_weakenRoot,
  .lvlLeB_weakenInst                              appending a binder never changes an old comparison
DotMNF.Ctx.body_lvl_param, .body_lvl_arrow, .body_lvl_root, .body_isRoot     T-B3.1
DotMNF.Subcap.level
DotMNF.CaptureSet.noAny_cvar, .CaptureSet.cvar_here_rename
DotMNF.Ty.domAnyOk, .Ty.DomAnyOk, .Ty.noAny_expand_dom
DotMNF.Defs.noAny, .Value.noAny, .Tm.noAny, .Defs.NoAny, .Value.NoAny, .Tm.NoAny
DotMNF.Value.anyOk, .Tm.anyOk, .Value.AnyOk, .Tm.AnyOk
DotMNF.Value.expand, .Tm.expand
DotMNF.Value.expand_of_noAny, .Tm.expand_of_noAny
DotMNF.Value.noAny_expand, .Tm.noAny_expand
DotMNF.Value.expand_rename, .Tm.expand_rename, .Tm.expand_weaken
DotMNF.Examples.readUnder, .S1ReadAt, .platSet1 to .platSet5
```

### The examples

Every example of A3a, A3b, B0, B1 and B2 is here and keeps its name.  S1 and S2 are re-expanded, and
each is printed under both readings.  W1 to W6 are the four worked programs of the compiler's
write-up, read on the source side, with the two of them that the target already covered stated at
real binder positions instead of a spine written by hand.

```
DotMNF.Examples.reading_plat       : Ctx.reading platCtx platSet = platSet
DotMNF.Examples.reading_body       : Ctx.reading (Γ.body T) P = [κ_body]
DotMNF.Examples.S1_anyOk, .S1_expand, .S1_readings, .S1_noAny, .S1_typed
DotMNF.Examples.S2_anyOk, .S2_expand, .S2_readings, .S2_noAny, .S2_typed, .C5_typed
DotMNF.Examples.W1_reading1, .W1_reading2, .W1_roots
DotMNF.Examples.W1_inner_absorbs_outer  : Subcap W1Ctx2 [κ_out] [κ_in]
DotMNF.Examples.W1_outer_param_absorbed : Subcap W1Ctx2 [x_out] [κ_in]
DotMNF.Examples.W1_inner_param_absorbed : Subcap W1Ctx2 [x_in]  [κ_in]
DotMNF.Examples.W1_outer_not_inner      : ¬ LvlLe κ_in κ_out ∧ ¬ LvlLe x_in κ_out
DotMNF.Examples.W2_anyOk, .W2_expand, .W2_deep_rejected, .W2_arg
DotMNF.Examples.W2_level, .W2_level_param, .W2_typed, .W2_call
DotMNF.Examples.W3_anyOk, .W3_freshOk, .W3_expand, .W3_expandFresh, .W3_typed
DotMNF.Examples.W4_anyOk, .W4_expand, .W4_expand_expandFresh
DotMNF.Examples.W5_scope_order, .W5_no_level, .W5_level_own
DotMNF.Examples.W6_lvl, .W6_fires
DotMNF.Examples.C2_anyOk, .C2_expand, .C5b_anyOk, .C5b_expand
DotMNF.Examples.Z_body_no_root, .Z_two_calls_no_level, .Z_two_calls_lvl
DotMNF.Examples.Z1TyTop, .Z1_widen, .Z1CtxTop, .Z1BodyCtxTop, .Zx1', .Zx2'
DotMNF.Examples.Z_top_body_no_root, .Z_top_two_calls_no_level, .Z_top_two_calls_lvl
```

**S1, `withFile` with an explicit capture parameter.**  The written type is unchanged.  The member
bound stays explicit, and decision 26 is what makes it necessary: a member-bound `any` reads as the
root enclosing the object type and not as the class root.  The result `any` now reads as the
platform set, because `withFile` is written at the top of the program and the source has no
universal root, so the caller's answer and the program's use set are the platform set.  `S1_readings`
prints the two readings apart: A3b read the same `any` as `{fs, cp, op}`.  Everything else of the
example is as it was, the caller's `Rec-E`, `Cap`, `Rec-I` packing included, and `cp` and `op` are
named in no use set, through the member's bounds.

**S2, a class with a capture-set parameter and `any` in the result.**  Both readings are printed.
A3b's is `(∀(u : ⊤) (Iterator ^ {fs, u})) ^ {fs}`, the compiler's is
`(∀(u : ⊤) (Iterator ^ {κ₁, κ₂})) ^ {fs}`, and the second is checked by `rfl`.  The callee types
more easily than the reading suggests: its literal is assigned `[]` and the packing widens it at an
arbitrary set by `sc-elem`.  The caller's answer is still `⊤ ^ {fs}` and the only step that names
`{fs}` is `sc-sel-upper` at the member's upper bound, so S2's own point survives the change of
reading.  What the new reading does move is the caller's use set: `it` is declared at the platform
set now, so reading `it.next` charges the platform set.  These two lines side by side are the single
most informative output of the stage.

**W1, local `any`s and the level hierarchy.**  A lambda inside a lambda over the platform prefix.
The outer body root is below the inner one and so is a binder of the outer body.  The inner root is
not below the outer one and neither is a binder of the inner body.  Two of the four are
`Subcap.level` instances and two are negations of `Ctx.LvlLe`.  That is `{any₂} <: {any₃}` and its
failure, at the binder order the rules produce.

**W2, the parameter `any`.**  `process : (∀(x : File ^ {any}) ⊤) ^ {}` reads as
`(∀(x : File ^ {κ}) ⊤) ^ {}`, at every reading, because the domain clause does not use the reading
it is given.  An `any` deeper in the domain is refused, which is the other half of decision 24.
Inside the body the binder is below the body root by `Subcap.level`, and at a call `HasTy.app` reads
the argument at `T₁.subst (Subst.singleC (.var y))`, so the parameter `any` becomes the argument
variable itself, one instance per call.  That is more precise than the compiler, which makes a fresh
capability per call, and decision 35 records the difference.

**W3, `makeLogger` with the parameter written `any`.**  `Z2TyF` with `FileSystem ^ {any}` in place
of `^ {κ}`.  The expansion lands on `Z2TyF` unchanged, so `Z2_expandFresh` and the whole target side
are reused byte for byte.  The point is the witness: it is the parameter and not a platform binder.

**W4, `freshCell` read the compiler's way.**  `Z1TyF` holds no `any`, so the reading leaves it where
it stood, at every reading set.  That is the regression half of the stage.  The result `fresh` is
B2's existential and two calls open two binders that the level order does not relate.

**W5, the `withFile` escape at the source.**  The page writes the example with a type argument, and
`Shape.anyOk` refuses `any` in a type-member bound, so the source renders it monomorphically, which
is decision 36.  `W5_no_level` decides that the level rule fires neither on the callback's parameter
nor on its arrow binder at the root of the scope outside the call, and `W5_level_own` shows that it
does fire at the callback's own body root.  The second half, that no member-free evidence at all
escapes, is T17 and is stated on the target side, because it names `⊤ᶜ`.

**W6, the counterfactual binder order.**  The source's own X5.  Under the rejected order
`κ_f, f, κ_b`, the level of `f` is the innermost root older than it, and the platform prefix has
none, so `f` is at the outermost level and the level rule fires at the body root.  The escape types.
That is why `Ctx.body` binds the body root first.

**Two calls of `freshCell`.**  `Z1BodyCtxSrc` is the context the source's two `letex`es build.  It
opens no root, so every binder of it is at the outermost level and neither opened binder is a root,
so `Subcap.level` has no instance with either of them on its right.  That the two are incomparable
under *all* evidence is a canonical-forms fact and is in the tree, as

```text
FCdot.Examples.Z_two_calls_incomparable :
  (¬ ∃ f, ⟦Z1BodyCtxTop⟧ ⊢ᶜ f : [κ₁'] ⊑ [κ₂']) ∧ (¬ ∃ f, ⟦Z1BodyCtxTop⟧ ⊢ᶜ f : [x₁] ⊑ [x₂])
```

It is the target's own `two_calls_incomparable` redone over a translated source context: a typed
store `ZStore` for it, a `Ctx.Refines` into the transparent context that store types, the resolution
of the two opened binders and of the two cells, and `cap_canon`.  `Z1BodyCtxTop` is the same two
calls with the answer widened from `File` to `⊤` before each `letex` unpacks it, and the widening is
`Z1_widen`, a source subtyping derivation.  The widening is what makes a store available: a store
binds literals, a target literal has its own precise type, and that type is a telescope of
definitions and presences, while the translation of a source object type is a telescope of bounds
whose newest entry is a capture bound.  So no target literal has the type `⟦File ^ C⟧`, which is
`FCdot.Examples.Z_no_literal_at_file`, and no store binds a variable at it.  Nothing of the
statement's content moves with the widening: the two opened capture binders are where they were and
the two cells are declared at the sets the two calls assigned them.

Axioms (`#print axioms`): none or `propext` for every fact above, `propext` for every derivation.

## Stage K2

K2 is the stage that classifies the source (`plan-5f-classifiers-stages.md` §K2).  A capture atom may
be projected by a kind, a capture member may be declared at a kind instead of at a pair of sets, a
context binder may declare a classifier, and the source gets its own capture-kinding judgment,
`CapKind`, whose ten rules mirror the target's `KindCo`.

Four sentences fix the shape of the stage.

The kinding judgment is `Type` valued and it lives in the big mutual block that holds `Subcap`,
`SubShape`, `Sub`, `ESub`, `HasTy` and `DefsTy`.  Two reasons, and both are forced.  `ksel` premises
`HasTy`, and a Lean mutual inductive block may not mix a `Prop`-valued inductive with `Type`-valued
ones.  And `CapKind.translate` is a function into the target's `KindCo`, which is `Type`, and a
ten-constructor `Prop` has no large elimination.  That is the argument that made `Subcap`
`Type`-valued, and the source side follows it.  The cost is decision 19: two derivations of the same
kinding judgment are two terms, nothing quantifies over them, and the source has no kinding checker
of its own, only the target's read through the translation.

A projected `any` is legal and a projected `fresh` is not, which is decision 20.  The asymmetry is
forced by where the two notations are read.  `any` is read by `CaptureSet.expand`, which pushes the
reading under a projection, so `{any ↾ except[ThreadLocal]}` in a parameter's capture set expands to
the arrow's own capture binder projected, which is `cap` with a filter.  `fresh` is read by
`Ty.expandFresh`, which tests a syntactic membership of the bare atom at the top of a result set, so
a projected `fresh` would survive expansion and then be dropped by the translation, which would make
the declared set smaller than the program justifies.  `ETy.codFreshOk` refuses it, and the conjunct
it gains is vacuously true on every projection-free set.

At the four positions where `any` is forbidden the reading is the empty set, so `noAny` has to
descend through a projection.  Without the descent `Shape.AnyOk (.typ A (⊤ ^ [any ↾ only Control]) ⊤)`
is true and the bound expands to `{}`, so the program is typed at a bound it never wrote.  The two
`decide` facts at the end of `Syntax.lean` are that counterexample and its refusal.

There is no definition form for a kind-bounded capture member, which is decision 17.  A literal's
capture witnesses are read off its declaration shape, `.capk A φ` carries no set, and a literal
declared at it would be untypable.  So `Defs`, `Defs.Distinct`, `Defs.labels`, `Defs.erase` and
`DefsTy` are untouched, a literal writes `Defs.cap A c` as it always did, and `SubShape.capkI`
retypes it at the kind bound, exactly as C2 already retypes through `Rec-E`, `Cap` and `Rec-I`.

`Ctx.consCls` is a seventh context constructor and not a payload on `consC`, which is decision 10 one
stage further on.  The price is one clause in each function that recurses on a context, and the
reward is that every existing example, `Platform.ctx`, `Platform.store` and `Platform.targetStore`
stay textually unchanged.

| module | what K2 changed |
|---|---|
| `Syntax` | the constructors `CapAtom.proj` and `Shape.capk`, with `CapAtom.base`, `CapAtom.kindOf`, `CapAtom.projBy` and `CaptureSet.proj`, the source twins of the target's four.  The four atom-level helpers `CapAtom.expandA`, `noAnyA`, `substFreshA` and `noFreshA`, through which `CaptureSet.expand`, `noAny`, `substFresh` and `noFresh` are restated.  `CapAtom.freshTop` and `CaptureSet.freshTopOk`, the test `ETy.codFreshOk` gains.  The `capk` clauses of `Shape.rename`, `subst`, `expand`, `substFresh`, `noAny`, `anyOk`, `noFresh`, `isDecl`, `Shape.Decl` and `Shape.Wf`.  The two repaired `_cons_of_ne` lemmas, and the two acceptance facts |
| `Typing` | `Ctx.consCls` with its clauses in `lookup`, `instSet?`, `root?`, `lvl` and `rootB` and in the five spine inductions; `Ctx.clsOfB`, `Ctx.clsOf?` and `Ctx.ClsOf`; `Ctx.lvlLeB`'s projection clause; `CapKind` with its ten rules; three `Subcap` rules and two `SubShape` rules; `CapKind.MemberFree`, mutual with `Subcap.MemberFree`, which moves here from `../DotToFCdot/Evidence.lean` |
| `Machine` | `Platform.consCls`, whose `store` clause is `.consC`, because a classifier is not runtime content, and `Platform.classOf` |
| `Erasure`, `Examples` | nothing.  A projection and a kind bound erase to nothing, and no existing example writes either |

### The rules

The ten rules of `CapKind`.  `a` is a general atom throughout: `a.base` is the atom under its
projections and `a.kindOf` is the intersection of the kinds they carry, which is `Cls.Kind.top` when
there are none.

```
nil    : CapKind Γ [] φ
cons   : CapKind Γ [a] φ → CapKind Γ C φ → CapKind Γ (a :: C) φ
kproj  : a.kindOf.Subkind φ → CapKind Γ [a] φ
kcls   : Ctx.ClsOf Γ a.base c → (a.kindOf.Contains c → φ.Contains c) → CapKind Γ [a] φ
kvar   : a.base = CapAtom.var x →
           CapKind Γ ((Γ.lookup x).captureSet.proj a.kindOf) φ → CapKind Γ [a] φ
kcvar  : a.base = CapAtom.cvar κ → Ctx.InstOf Γ κ C →
           CapKind Γ (C.proj a.kindOf) φ → CapKind Γ [a] φ
ksel   : HasTy U Γ (.path (.var x)) (.ty ((Shape.capk A φ) ^ D)) → CapKind Γ [.sel x A] φ
kprojS : CapKind Γ C φ → CapKind Γ (C.proj ψ) φ
ksub   : CapKind Γ C φ₁ → φ₁.Subkind φ₂ → CapKind Γ C φ₂
kle    : Subcap Γ C D → CapKind Γ D φ → CapKind Γ C φ
```

`kcls` reads a classifier at a `consCls` binder alone.  A `consC` binder declares none, so it is
kinded only by `kproj`, which asks that `φ` admit every classifier: an unwritten classifier means
unknown, which is the revised decision 9, and it is why the examples write their platform
capabilities as `consCls` binders.

The three new subcapturing rules and the two new shape rules, all five additive.

```
Subcap.unproj   : Subcap Γ (C.proj φ) C
Subcap.proj     : CapKind Γ C φ → Subcap Γ C (C.proj φ)
Subcap.projMono : Subcap Γ C D → Subcap Γ (C.proj ψ) (D.proj ψ)
SubShape.capkI  : CapKind Γ c2 φ → SubShape Γ (.cap A c1 c2) (.capk A φ)
SubShape.capk   : φ₁.Subkind φ₂ → SubShape Γ (.capk A φ₁) (.capk A φ₂)
```

`sc-var` at a projection is `projMono` composed with `var` and needs no rule of its own, since
`[a].proj ψ` is `[a ↾ ψ]`.  `capkI` is how a literal reaches a kind bound, and its translation is the
hardest lemma of the stage, in `../DotToFCdot/README.md`.

### Statements restated

Three, and all three are rows of K2.9.  No theorem gains a hypothesis and no conclusion is weakened.

| statement | change | why the meaning is the same |
|---|---|---|
| `CaptureSet.expand_cons_of_ne` | the premise `a ≠ .any` becomes `a.base ≠ .any` | a projected `any` satisfies the old premise and expands like `any`, so the old form is false, and it is machine checked false by the witness `.proj .any Cls.Kind.top`.  On a projection-free atom `base` is the identity and the premise is the old one word for word |
| `CaptureSet.noAny_cons_of_ne` | the same | the same, with `CapAtom.noAnyA_iff` as the bridge, and the thirteen call sites inside the file each discharge the new premise by `simp [CapAtom.base]` |
| `ETy.codFreshOk` | the plain-answer clause gains the conjunct `C.freshTopOk` | every atom of a projection-free set is `fresh` or is `noFreshA`, so `freshTopOk` is `true` there and the function is the copied one.  `Ty.expandFresh` is untouched |

Four definitions are restated in the new representation with the same meaning on every copied
constructor, and no hypothesis is added anywhere.

| definition | change | why the meaning is the same |
|---|---|---|
| `CaptureSet.expand`, `CaptureSet.substFresh` | each becomes the append of an atom-level helper over the list | the helper agrees with the copied clause on every copied constructor, and all five `@[simp]` clause lemmas stay `rfl`, because `[a] ++ L` reduces to `a :: L`.  `expand_append` and `expand_rename` keep their statements.  The helper maps with the constructor `CapAtom.proj` and not with `CapAtom.projBy`, because a normalising map makes the repaired `expand_cons_of_ne` false again at a nested projection |
| `CaptureSet.noAny`, `CaptureSet.noFresh` | each becomes a fold of an atom-level helper that recurses at `proj` | `false && b` is `false` and `true && b` is `b`, both by iota, so every copied clause holds by `rfl` |
| `CapAtom`, `Shape`, `Ctx` | one constructor each, `proj`, `capk` and `consCls` | additive, and every existing constructor and every existing clause is untouched.  `consC` is `consCls` at no declaration |
| `Ctx.lvlLeB` | one clause, `.proj a _` reading through to `a` | D8.  The three copied clauses and the wildcard are untouched, no copied atom matches the new clause, and the target reads through a projection on both sides already |
| `Subcap.MemberFree` | moves here from `../DotToFCdot/Evidence.lean`, keeping its seven constructors word for word and gaining one clause per new rule | a relocation inside one namespace: the full name and every constructor is unchanged, so every reference in `../DotToFCdot/` still resolves.  It has to move, because `Subcap.proj` premises a `CapKind` and `CapKind.kle` premises a `Subcap`, so the two member-free families are mutual and a mutual block lives in one file |
| `Defs`, `Defs.Distinct`, `Defs.labels`, `Defs.erase`, `DefsTy`, `Ty.expandFresh`, `Machine`, `Erasure` | nothing | there is no new definition form, which is decision 17, and a projection and a kind bound erase to nothing |

### New definitions and lemmas

```
DotMNF.CapAtom.base, .kindOf, .projBy, DotMNF.CaptureSet.proj    the source twins of the target's
DotMNF.CapAtom.expandA, .noAnyA, .substFreshA, .noFreshA         the four atom-level helpers
DotMNF.CapAtom.noAnyA_iff : a.noAnyA = true ↔ a.base ≠ .any      the bridge of the two repaired rows
DotMNF.CapAtom.freshTop, DotMNF.CaptureSet.freshTopOk            the test codFreshOk gains
DotMNF.Ctx.clsOfB, .clsOf?, .ClsOf                               the classifier reader, decidable
DotMNF.Ctx.clsOf_consCls                                         the classifier is read back
DotMNF.Ctx.rootB_consCls, .root?_consCls                         a classified binder is no scope root
DotMNF.Ctx.lvlLeB_proj                                           the new clause as an equation
DotMNF.Ctx.lvlLe_depth_step                                      the inner step of LvlLe.trans
DotMNF.Ctx.lvlLeB_weakenCls                                      the sixth weakening commutation
DotMNF.Platform.consCls, .classOf                                the classified platform binder
```

### The acceptance facts

Four, at the end of `Syntax.lean`, each with the clause it forces.

```
DotMNF.Shape.anyOk projAnyBound = false                         by decide
DotMNF.CaptureSet.expand [any ↾ only Control] [] = []           by rfl
DotMNF.ETy.codFreshOk (.ty (⊤ ^ [fresh ↾ only Control])) = false by decide
DotMNF.ETy.codFreshOk (.ty (⊤ ^ [fresh])) = true                by decide
```

The first two are the counterexample of decision 20 and its refusal: without the descent of `noAnyA`
through a projection the shape is `AnyOk`, and the bound would then be read at the empty set.  The
last two are the other half: a projected `fresh` in a result set is refused and a bare `fresh` stays
legal where `Ty.expandFresh` reads it.

Axioms (`#print axioms`): `propext` and `Quot.sound`, or less, for every theorem of the stage.

## Stage K3

K3 is the closing stage of classifiers (`plan-5f-classifiers-stages.md` §K3), the three mandatory
examples of `plan-5-extensions.md` §5.  No syntax, no rule, no judgment and no theorem of the stages
before it moves.  The source half of each example lives here, appended after C2: E1 is `Try.apply`
of `exceptions.tex:60-66`, whose one field holds its body closure filtered to `only[Control]`.  E2 is
`Future.apply` of `exceptions.tex:74-92`, whose parameter is filtered to `except[ThreadLocal]`, with
two total refutations that no argument declared `ThreadLocal` passes.  E3 is C2 retyped at the kind
bound `{C : only[Control]}` in place of the set bound, with a stability fact over an extended
platform.  Every verdict is `decide`, `rfl`, or a `CapKind` or `HasTy` term, closed against the
target through `checkKindCo` on the translation in `../FCdot/Examples.lean`.

```
DotMNF.Examples.E1_classOf_ctl, .E1_classOf_io, .E1_disjoint
DotMNF.Examples.E1_only_admits_ctl, .E1_only_excludes_io
DotMNF.Examples.E1_anyOk, .E1_freshOk, .E1_expand
DotMNF.Examples.E1_try_anyOk, .E1_try_freshOk, .E1_try_expand
DotMNF.Examples.E1_field_plat_kind, .E1_field_kind, .E1_kind
DotMNF.Examples.E1_lit_typed, .E1_typed

DotMNF.Examples.E2_control_le_threadLocal, .E2_only_control_except_empty
DotMNF.Examples.E2_except_excludes_tl, .E2_except_excludes_ctl
DotMNF.Examples.E2_except_admits_io, .E2_except_admits_top, .E2_top_not_subkind
DotMNF.Examples.E2_classOf_tl, .E2_classOf_ctl, .E2_classOf_io
DotMNF.Examples.E2_anyOk, .E2_freshOk, .E2_expand, .E2_dom_expand, .E2_arg_instance
DotMNF.Examples.E2_kind, .E2_io_kind, .E2_io_arg_kind, .E2_io_arg, .E2_arg_kind
DotMNF.Examples.E2_typed

DotMNF.Examples.E3_classOf_k1, .E3_classOf_k2, .E3_clsOf_k1, .E3_clsOf_k2
DotMNF.Examples.E3_only_admits_control, .E3_only_excludes_io
DotMNF.Examples.E3AbsDecl, .E3AbsWf, .E3abstract, .E3_cap_kind
DotMNF.Examples.E3_kind_a, .E3_kind_b, .E3_abstract_a, .E3_abstract_b
DotMNF.Examples.E3xCap, .E3_client_kind, .E3call, .E3ClientWf
DotMNF.Examples.E3_anyOk, .E3_freshOk, .E3_expand
DotMNF.Examples.E3_abs_anyOk, .E3_abs_freshOk, .E3_abs_expand
DotMNF.Examples.E3_kind, .E3_typed
DotMNF.Examples.E3_classOf_k3, .E3_stable_clsOf, .E3_stable_classOf
DotMNF.Examples.E3_third_lit, .E3_kind_c, .E3_abstract_c, .E3_kind3
```

E1's and E2's effect-safety facts, `E1_effect_safety` and `E2_effect_safety`, instances of
`dot_classified_effect_safety'` (T9') at `only[Control]` and at `except[ThreadLocal]`, and E3's
prediction facts, `E3_prediction` and `E3_prediction'`, instances of `dot_classified_prediction` (T8)
and its primed form, are all stated on the target side, in `../FCdot/Examples.lean`, because both
theorems read the target's `CapLe` or `State` in their conclusion.

| module | what K3 added |
|---|---|
| `Examples` | E1, E2 and E3, each a platform (`E1Plat`, `E2Plat`/`E2PlatIO`, `E3Plat`/`E3Plat3`), a program typed against it, and the source half of its kinding and effect-safety facts, appended after C2 |
| every other module | nothing |

Axioms (`#print axioms`): `propext` and `Quot.sound`, or less, for every theorem of the stage.
