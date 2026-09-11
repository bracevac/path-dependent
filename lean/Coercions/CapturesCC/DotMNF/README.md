# DotMNF, at stage B2 of captures the compiler's way

DOT-MNF^cc, the capturing source of the translation in `../DotToFCdot`.

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
| `Syntax` | `Shape.all` at `Sig.dom s` and `Sig.cod s`, with `Dom`, `Cod`, `Dom.underRoot`, `Dom.inBody`, `Cod.underRoot`, the source's copies of the target's five names.  `Value.obj` at `Defs ((s,c),x)` and `Value.lam` at `Ty (Sig.dom s)` and `Tm (Sig.body s)`.  One lift per binder in `Shape.rename` and `Value.rename`, and `Shape.expand` weakening its carried set once more.  `CaptureSet.selfC_rename` and `CaptureSet.noAny_selfC`, the two-binder twins of the existing pair.  The substitution block: `Subst` with an atom-valued capture component, `Subst.ofRename`, `.lift`, `.liftC`, `.singleC`, `.arg`, `.enter` and `.enterObj` (which write `any` where the target writes `⊤ᶜ`), the eight traversals `CapAtom.subst` to `Defs.subst`, `Subst.funext` and the eight `X.subst_ofRename` |
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
DotMNF.CaptureSet.selfC_rename, .noAny_selfC
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
