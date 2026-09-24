import Coercions.FCdotR.TermTyping

/-!
# Over an honest store, the location rules derive nothing the source cannot

`VcTy.vcLocAny` and `AtomTy.varConcAny` type a location `ℓ` at any type `B`
that matches the literal stored at `ℓ` (`Typing.LitMatch`).  That is not
`T_Vary` (`dot.v:220-226`): no method body is re-typed, members may be left
out, and `B` need not be the type of any re-typing of the literal.  This module
proves that over an **honest** store (`StoreTyping.Store.Honest`) the two rules
are nevertheless admissible in `Oopsla16`: whatever type they give a location,
the source gives it too.

Honesty is needed although the two rules never read the store typing `W`.
They take a stored method's annotations on trust, and honesty is what says the
stored body has the annotated type.  Over the annotated store holding
`{def 0(y : ⊤) : ⊥ = y}`, which has no honest store typing, they type `ℓ.0(ℓ)`
at `⊥` at every store typing, and the source types it at no type
(`Coverage.UncheckedBody`).  More simply, at any location without a `T_Vary`
typing they type `loc ℓ ⊤` at `⊤`, where the source types `ℓ` at no type
(`Coverage.noVary_not_admissible`).

```text
Store.Honest G W,  LitMatch (G ℓ).get? B  ⟹  ⊢ tyOf W ℓ <: B     (Store.Honest.litMatch_stp)
Store.Honest G W,  LitMatch (G ℓ).get? B  ⟹  ⊢ ℓ : B             (Store.Honest.litMatch_hasType)
```

The argument goes conjunct by conjunct.  A matched type is `⊤` or a
right-nested intersection of members, and each member is a conjunct of the
recorded type `tyOf W ℓ`:

* a type member `{a : TX .. TX}`, because the stored literal defines `a` as
  `TX` and `D_Typ` makes the recorded member exact (`Store.Honest.member`);
* a method member `{a : S → U}`, because the match finds the method stored
  with both annotations, `some S` and `some U`, and `D_Fun`'s `EqSome`
  premises then make the recorded member `{a : S → U}` itself
  (`Store.Honest.method`).

The second item is where the match's demand for both annotations is used.  With
an annotation absent, `EqSome` fixes nothing.  Over a store holding
`{def 0(y) = y}` without annotations the recorded type may be
`{0 : ⊤ → ⊤} ∧ ⊤`, and a match that accepted any method type there would accept
`{0 : ⊤ → ⊥} ∧ ⊤`, whose method member is not a conjunct of the recorded type;
the argument below would then break, and the target would type `ℓ.0(ℓ)` at
`⊥`.  An earlier version of `LitMatch` did accept it.  The match now refuses
every method member at such a location: a method member needs a method stored
with both annotations at its label (`StoreTyping.LitMatch.storedMethod`,
`LitMatch.no_unannotated_method`).  `CheckerExamples` (section *Unannotated
stored methods*) runs two instances, at `{0 : ⊤ → ⊤} ∧ ⊤` and at
`{0 : ⊤ → ⊥} ∧ ⊤`.

So `stp_and2`, `stp_and11`/`stp_and12`, reflexivity (`Oopsla16.Stp.refl`) and
`stp_top` build `tyOf W ℓ <: B` in the source, and `T_Vary` at the honesty
witness (`Store.Honest.vary`) followed by `T_Sub` types `ℓ` at `B`.  Labels
are positional, so the member stored at a label is unique; the proof does not
need that, only that the conjunct it asks for is present.

Two sections read the result off the two rules themselves: every typing of an
atom `loc ℓ T` over an honest store, and every observation of `ℓ` by the node
`vcLocAny ℓ T`, is a source typing of `ℓ` at the same type
(`Store.Honest.varConcAny_admissible`, `Store.Honest.vcLocAny_admissible`).
The next section goes the other way at a location holding a method without
both annotations: there the two rules give the location no type `T_Vary` gives
it (`varConcAny_not_vary`, `vcLocAny_not_vary`), although `AtomTy.varConc`
still types `var (conc ℓ)` at the recorded type.  The target's two primitive
inclusions that are no single source rule's image, `refl` and `muDrop`, are
derivable in the source as well (`Oopsla16.Stp.refl`, `muDrop_admissible`).
The module ends with a worked instance, an honest store holding a method
without annotations (`CurryStore`).

What this module does **not** contain: anything about the target's other rules.
It does not translate target *evidence* back into `Stp`, so it does not show
that FCdotR as a whole derives nothing `Oopsla16` cannot.  `selL`/`selR` at a
location, and the observation rules `vcPack`, `vcUnfold` and `vcSub` built on a
location node, are not covered; `DEVIATIONS.md` lists what remains.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Dm Dms Ctx Store Subst HasType Stp renameNil)

/-! ## A conjunct is a supertype -/

/-- **An intersection is a source subtype of each of its conjuncts**:
`stp_and12` along the spine, then `stp_and11` at reflexivity
(`Oopsla16.Stp.refl`).  The source counterpart of `Conjunct.typed`, at any
context. -/
def Conjunct.stp {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {T M : Ty σ s} :
    Conjunct T M → Stp G Γ T M
  | .here => .stp_and11 (Stp.refl _)
  | .there h => .stp_and12 h.stp

/-! ## The match, admitted -/

/-- **(a) Over an honest store, a matched type is a source supertype of the
recorded type.**  If `W` is honest and `B` matches the literal stored at `ℓ`
(`Typing.LitMatch`, the premise of `VcTy.vcLocAny` and `AtomTy.varConcAny`),
then `Oopsla16` proves `tyOf W ℓ <: B` in the empty context.  Each conjunct of
`B` is a conjunct of `tyOf W ℓ` (`Store.Honest.member` for a type member,
`Store.Honest.method` for a method member), and `stp_and2` collects them; the
trailing `⊤` is `stp_top`. -/
def Store.Honest.litMatch_stp {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) {l : BVar σ .var} :
    {B : Ty σ []} → LitMatch (G.lookup l).get? B → Stp G Ctx.nil (tyOf W l) B
  | _, .top => .stp_top
  | _, .typ hg r => .stp_and2 (h.member l hg).stp (h.litMatch_stp r)
  | _, .fn hg r => .stp_and2 (h.method l hg).stp (h.litMatch_stp r)

/-- **(a), at any context**: the same inclusion with both endpoints weakened out
of the empty local scope by `renameNil`, which is how `T_Vary` and
`AtomTy.varConcAny` report a location's type in a context `Γ`.  The conjuncts
are renamed along (`Conjunct.subst`); the source needs no weakening lemma. -/
def Store.Honest.litMatch_stpAt {σ s : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) {l : BVar σ .var} (Γ : Ctx σ s) :
    {B : Ty σ []} → LitMatch (G.lookup l).get? B →
    Stp G Γ ((tyOf W l).rename renameNil) (B.rename renameNil)
  | _, .top => .stp_top
  | _, .typ hg r =>
      .stp_and2 (Conjunct.subst (Subst.ofRename renameNil) (h.member l hg)).stp
        (h.litMatch_stpAt Γ r)
  | _, .fn hg r =>
      .stp_and2 (Conjunct.subst (Subst.ofRename renameNil) (h.method l hg)).stp
        (h.litMatch_stpAt Γ r)

/-- **(b) Over an honest store, the location rules' typing of a location is a
source typing.**  If `W` is honest and `T[ℓ]` matches the literal stored at `ℓ`
— the premise of `VcTy.vcLocAny` and `AtomTy.varConcAny` at the self type `T`
— then `Oopsla16` types `ℓ` at `T[ℓ]` in the empty context.  `T_Vary` at the
honesty witness (`Store.Honest.vary`) types `ℓ` at the recorded type
`tyOf W ℓ`, and `T_Sub` along (a) widens it to `T[ℓ]`.  The source derivation
re-types the stored literal only at the recorded type; nothing re-types it at
`T`, which may be impossible, since the match checks no method body. -/
def Store.Honest.litMatch_hasType {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) {l : BVar σ .var} {T : Ty σ ([],x)}
    (hm : LitMatch (G.lookup l).get? (T.substVr (.conc l))) :
    HasType G Ctx.nil (.tvar (.conc l)) (T.substVr (.conc l)) := by
  have hv := h.vary (Γ := Ctx.nil) l
  rw [Ty.rename_renameNil_nil] at hv
  exact .T_Sub hv (h.litMatch_stp hm)

/-- **(b), at any context**: `ℓ` at `T[ℓ]` weakened by `renameNil`, which is
exactly the conclusion of `AtomTy.varConcAny` in the context `Γ`. -/
def Store.Honest.litMatch_hasTypeAt {σ s : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) (Γ : Ctx σ s) {l : BVar σ .var} {T : Ty σ ([],x)}
    (hm : LitMatch (G.lookup l).get? (T.substVr (.conc l))) :
    HasType G Γ (.tvar (.conc l)) ((T.substVr (.conc l)).rename renameNil) :=
  .T_Sub (h.vary l) (h.litMatch_stpAt Γ hm)

/-! ## The two location rules, admitted -/

/-- **`AtomTy.varConcAny` is admissible in the source over an honest store.**
The atom `loc ℓ T` has one typing rule, `varConcAny`, so every typing of it is
at `T[ℓ]` weakened, from a match, and `litMatch_hasTypeAt` turns it into a
source typing of the variable `ℓ` at the same type, in the same context. -/
def Store.Honest.varConcAny_admissible {σ s : Sig} {G : Store σ σ} {W : StoreTy σ}
    {Γ : Ctx σ s} (h : Store.Honest G W) {l : BVar σ .var} {T : Ty σ ([],x)}
    {U : Ty σ s} (d : AtomTy G W Γ (.loc l T) U) : HasType G Γ (.tvar (.conc l)) U := by
  cases d with
  | varConcAny hm => exact h.litMatch_hasTypeAt Γ hm

/-- **`VcTy.vcLocAny` is admissible in the source over an honest store.**  An
observation of `ℓ` by the node `vcLocAny ℓ T` has one typing rule, so it is at
`T[ℓ]`, from a match, and `litMatch_hasType` gives the source typing of `ℓ` at
that type.  An observation of a location lives in the empty local scope, so the
source typing is in the empty context. -/
def Store.Honest.vcLocAny_admissible {σ s : Sig} {G : Store σ σ} {W : StoreTy σ}
    {Γ : Ctx σ s} (h : Store.Honest G W) {l : BVar σ .var} {T : Ty σ ([],x)}
    {U : Ty σ []} (d : VcTy G W Γ (.conc l) (.vcLocAny l T) U) :
    HasType G Ctx.nil (.tvar (.conc l)) U := by
  cases d with
  | vcLocAny hm => exact h.litMatch_hasType hm

/-! ## At an unannotated location the location rules give no `T_Vary` type

The converse direction, at a location holding a method without both
annotations.  A `T_Vary` typing of such a location lists that method, and a
type that lists it does not match (`StoreTyping.varyLitMatch_annotated`), so
neither location rule types the location at a type `T_Vary` gives it.  In
particular the node the elaboration of `T_Vary` builds, `loc ℓ T` at the
source's own self type `T`, has no typing at all.

This is about the two location rules only.  The atom `var (conc ℓ)` is typed
by `AtomTy.varConc` at `tyOf W ℓ`, and over an honest store typing that is a
type `T_Vary` gives (`Store.Honest.vary`; `CurryStore.varConcTyped` below). -/

/-- **`AtomTy.varConcAny` gives no `T_Vary` type at an unannotated location.**
Let `ds` and `T` be the premises of a `T_Vary` at `ℓ`, and let the literal
stored at `ℓ` have a method without both annotations.  Then no atom `loc ℓ T'`
whose self type instantiates to the same type, `T'[ℓ] = T[ℓ]`, has a typing,
in any context and at any store typing: its one rule needs `T[ℓ]` to match the
stored literal. -/
theorem varConcAny_not_vary {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {l : BVar σ .var} {T : Ty σ ([],x)} {ds : Dms σ ([],x)}
    (hd : Oopsla16.DmsHasType G (Ctx.nil.cons T) ds T)
    (hs : ds.substVr (.conc l) = G.lookup l) (hna : ¬ Dms.Annotated (G.lookup l))
    {T' : Ty σ ([],x)} (hT : T'.substVr (.conc l) = T.substVr (.conc l)) {U : Ty σ s}
    (d : AtomTy G W Γ (.loc l T') U) : False := by
  cases d with
  | varConcAny hm => exact hna (varyLitMatch_annotated hd hs (hT ▸ hm))

/-- **`VcTy.vcLocAny` gives no `T_Vary` type at an unannotated location**: the
observation counterpart of `varConcAny_not_vary`, with the same premises.  No
node `vcLocAny ℓ T'` with `T'[ℓ] = T[ℓ]` observes `ℓ` at all. -/
theorem vcLocAny_not_vary {σ s : Sig} {G : Store σ σ} {W : StoreTy σ} {Γ : Ctx σ s}
    {l : BVar σ .var} {T : Ty σ ([],x)} {ds : Dms σ ([],x)}
    (hd : Oopsla16.DmsHasType G (Ctx.nil.cons T) ds T)
    (hs : ds.substVr (.conc l) = G.lookup l) (hna : ¬ Dms.Annotated (G.lookup l))
    {T' : Ty σ ([],x)} (hT : T'.substVr (.conc l) = T.substVr (.conc l)) {U : Ty σ []}
    (d : VcTy G W Γ (.conc l) (.vcLocAny l T') U) : False := by
  cases d with
  | vcLocAny hm => exact hna (varyLitMatch_annotated hd hs (hT ▸ hm))

/-! ## The two primitive inclusions the source derives

`LeTy.refl` and `LeTy.muDrop` are not the image of any one source rule:
`Elaboration.elabStp` sends `stp_selx` to `refl` and `stp_bind1` to
`trans (bindx …) (muDrop …)`.  Both are derivable in `Oopsla16`, at every store
and context: `refl` is `Oopsla16.Stp.refl`, and `muDrop` is below. -/

/-- **`LeTy.muDrop` is admissible in the source**: `μ(T↑) <: T` is `stp_bind1`
(`dot.v:328-333`) at reflexivity, the body `T↑` not mentioning its self. -/
def muDrop_admissible {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} (T : Ty σ s) :
    Stp G Γ (.TBind T.weaken) T :=
  .stp_bind1 (Stp.refl _)

/-! ## A worked instance: a stored method without annotations

One location, holding the Curry-style identity `{def 0(y) = y}`.  The source
types the location by `T_Vary` at `{0 : ⊤ → ⊤} ∧ ⊤`, which is the honest store
typing `W`.  The location rules give it no type with a method member: a method
member needs a method stored with both annotations at its label
(`LitMatch.storedMethod`), and the one stored method has none
(`LitMatch.no_unannotated_method`).  In particular `loc ℓ` at the identity's
type has no typing at any store typing (`loc_untypable`).  `CheckerExamples`
rejects `loc ℓ` at that type, which is the one `T_Vary` gives, and at
`{0 : ⊤ → ⊥} ∧ ⊤`, which we argue, without a proof, is not a `T_Vary` type
either (`D_Fun` would have to type the body `y : ⊤` at `⊥`).  The location
rules give the location `⊤`, and that typing is admitted by the source.  The atom
`var (conc ℓ)` is typed by `varConc` at the recorded type, which is the type
`T_Vary` gives (`varConcTyped`).  The store is not annotated, so the
elaboration of `T_Vary` does not apply to it, and no honesty witness at the
location is in `DmsFrag`, so the honest-store safety theorems do not apply
either (`Coverage.CurryGap`). -/

namespace CurryStore

/-- One location. -/
abbrev S1 : Sig := ([],x)

/-- That location. -/
abbrev l : BVar S1 .var := .here

/-- The identity, Curry-style: `{def 0(y) = y}`, neither annotation present.
Generic in the local scope, so that it serves as the stored literal and as its
own witness. -/
abbrev idDefs {s : Sig} : Dms S1 s := .dcons (.dfun none none (.tvar (.abs .here))) .dnil

/-- The store. -/
abbrev G : Store S1 S1 := .cons .nil idDefs

/-- The identity's type, `{0 : ⊤ → ⊤} ∧ ⊤`, as `D_Fun` and `D_Nil` give it. -/
abbrev Tid {s : Sig} : Ty S1 s := .TAnd (.TFun 0 .TTop .TTop) .TTop

/-- The store typing: the identity's type. -/
def W : StoreTy S1 := fun _ => Tid

/-- The store typing is honest: `D_Fun` types the identity at `⊤ → ⊤`, its
body by `T_Varz` and `stp_top`, and both absent annotations agree with `⊤` by
`EqSome`. -/
def honest : Store.Honest G W where
  at' := fun
    | .here =>
        { defs := idDefs
          typed := .D_Fun (T11 := .TTop) (T12 := .TTop) .D_Nil (.T_Sub .T_Varz .stp_top)
            (Or.inl rfl) (Or.inl rfl)
          stored := rfl }

/-- The store is not annotated, so `Elaboration.elabAtom` does not apply to a
typing over it. -/
theorem not_annotated : ¬ Store.Annotated G := by decide

/-- The literal at the location is not annotated. -/
theorem lit_not_annotated : ¬ Dms.Annotated (G.lookup l) := by decide

/-- The source types the location at the identity's type, by `T_Vary`. -/
def varyTyped : HasType G Ctx.nil (.tvar (.conc l)) Tid := by
  have h := honest.vary (Γ := Ctx.nil) l
  rw [Ty.rename_renameNil_nil] at h
  exact h

/-- **The location rules do not give the location the type `T_Vary` gives
it**: `loc ℓ` at the identity's type has no typing, at any store typing, in any
context (`varConcAny_not_vary`, at the honesty witness). -/
theorem loc_untypable {s : Sig} {W' : StoreTy S1} {Γ : Ctx S1 s} {U : Ty S1 s}
    (d : AtomTy G W' Γ (.loc l Tid) U) : False :=
  varConcAny_not_vary (T := W l) (honest.at' l).typed (honest.at' l).stored
    lit_not_annotated rfl d

/-- **`varConc` does type the location at the type `T_Vary` gives**, because
the store typing records that type: at the honest `W`, the typing `varyTyped`
has an image in the target, the atom `var (conc ℓ)`.  At a store typing that
records another type, `varConc` gives that other type and only that one
(`CheckerCompleteness.AtomTy.type_unique`); `CheckerExamples` (section
*Unannotated stored methods*) runs an instance. -/
def varConcTyped : AtomTy G W Ctx.nil (.var (.conc l)) Tid := .varConc

/-- The location rules' `⊤` at the location, which leaves the method out, is
a source typing: `T_Vary` at the recorded type, widened by `stp_top`. -/
def topTyped : HasType G Ctx.nil (.tvar (.conc l)) .TTop :=
  honest.litMatch_hasType (T := .TTop) .top

end CurryStore

end FCdotR
