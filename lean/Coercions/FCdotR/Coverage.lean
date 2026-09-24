import Coercions.FCdotR.SourceSafety
import Coercions.FCdotR.Admissibility

/-!
# What the safety theorems reach, and what the location rules trust

Three groups of results about the reach of `SourceSafety`'s theorems and of the
location rules.  In earlier rounds each was checked only by a scratch file
outside the repository, or only argued.

* **The headline theorems rule programs out** (`NonVacuity`).  The stuck
  predicate `SrcStuck` is inhabited (`badTerm_stuck`).  The ill-typed closed
  program `(new {}).0(new {})` reaches a stuck configuration from the empty
  store (`ill_reaches_stuck`), so `Oopsla16.oopsla16_safety` refutes every
  typing of it (`ill_untypable`).  `Oopsla16.oopsla16_safety_honest` over the
  honest two-object store refutes every `Oopsla16` typing of
  `PackingCounterexample.badTerm`, which only the packing extension types
  (`badTerm_untypable`).  Typed closed programs exist:
  `Oopsla16.Examples.ex0` and `SourceSafety.RecursiveArg.progTy`.
* **A store with a Curry-style method is beyond the honest-store theorems**
  (`CurryGap`).  Over `Admissibility.CurryStore`, which stores
  `{def 0(y) = y}` without annotations, `id.0(id)` is typed by `T_Vary`
  (`idApp_typed`) and takes a step (`idApp_steps`), so the reference's
  `type_safety` (`dot_soundness.v:1131`) covers it.  No honesty witness at
  that location is in `DmsFrag` (`not_frag`), at any store typing, so neither
  `oopsla16_safety_honest` nor `oopsla16_not_stuck_honest` applies; the
  empty-store theorems do not apply either.
* **The location rules take the stored annotations on trust**
  (`UncheckedBody`).  `VcTy.vcLocAny` and `AtomTy.varConcAny` read a method
  member's types off the two annotations of the stored method and never type
  its body.  The store typing `W` plays no part in them, but they trust the
  store's annotations the way `vcLoc` trusts `W`.  Over the store holding
  `{def 0(y : ⊤) : ⊥ = y}`, whose body does not have its declared codomain,
  the target types `ℓ.0(ℓ)` at `⊥` at every store typing (`appBot_typed`).
  `Oopsla16` types it at no type at all (`app_untypable`): `T_Vary` re-types
  the body, so the location has no type (`loc_untypable`), and the store has
  no honest store typing (`not_honest`).  The failure of admissibility is not
  special to this store.  A store has an honest store typing exactly when
  every location has a `T_Vary` typing (`Store.Honest.varyWitness`,
  `honestOfVaryWitness`), and at a location without one the location rules
  type `loc ℓ ⊤` at `⊤` at every store typing, where the source types `ℓ` at
  no type (`noVary_not_admissible`).  `Admissibility` proves admissibility
  over honest stores; over a store without an honest store typing it fails,
  classically, whatever `W` is.
  `UncheckedBody` shows more than that: its store is annotated, so it meets
  the hypothesis of the term elaboration, and the rules type a term at `⊥`.

`not_honest` uses the honest-store safety theorem as a proof tool: an honest
store typing would type `(ℓ.0(ℓ)).1(ℓ)`, which gets stuck after one step.  Two
general facts support it.  Every source typing of a location rests on a
`T_Vary` at that location (`HasType.varyWitness`), and the fragment `DmsFrag`
is reflected by substitution (`DmsFrag.ofSubst`), so the witness a `T_Vary`
supplies is in the fragment when the stored literal is.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Dm Dms Ctx Store Subst Grows HasType DmsHasType Stp)

/-! ## Every source typing of a location rests on a `T_Vary` -/

/-- **The two premises of `T_Vary` at a location**, as data: a literal, a self
type it has under that self, and the location's contents as its instance.  An
honesty witness (`StoreTyping.HonestAt`) is one of these at the recorded
type. -/
structure VaryWitness {σ : Sig} (G : Store σ σ) (l : BVar σ .var) : Type where
  /-- The self type. -/
  T : Ty σ ([],x)
  /-- The literal, before its self is instantiated. -/
  defs : Dms σ ([],x)
  /-- It has type `T` under the self `T`. -/
  typed : DmsHasType G (Ctx.nil.cons T) defs T
  /-- Instantiating the self by the location gives what the location stores. -/
  stored : defs.substVr (.conc l) = G.lookup l

/-- **Every source typing of a location contains a `T_Vary` at it.**  The only
rules that conclude at a location are `T_Vary`, which supplies the witness,
and `T_VarPack`, `T_VarUnpack` and `T_Sub`, whose premise types the same
location.  The term is passed with an equation so that the recursion runs over
derivations of any term. -/
def HasType.varyWitness {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {l : BVar σ .var} :
    {t : Oopsla16.Tm σ s} → {T : Ty σ s} → HasType G Γ t T →
    t = .tvar (.conc l) → VaryWitness G l
  | _, _, .T_Vary (ds := ds) (T := T) hd hs, h => by
      cases h
      exact ⟨T, ds, hd, hs⟩
  | _, _, .T_Varz, h => by cases h
  | _, _, .T_VarPack d, h => HasType.varyWitness d h
  | _, _, .T_VarUnpack d, h => HasType.varyWitness d h
  | _, _, .T_Obj _, h => by cases h
  | _, _, .T_App _ _, h => by cases h
  | _, _, .T_AppVar _ _, h => by cases h
  | _, _, .T_Sub d _, h => HasType.varyWitness d h

/-- An honest store typing supplies a `T_Vary` witness at every location: the
honesty witness, at the recorded type. -/
def Store.Honest.varyWitness {σ : Sig} {G : Store σ σ} {W : StoreTy σ} (h : Store.Honest G W)
    (l : BVar σ .var) : VaryWitness G l :=
  ⟨W l, (h.at' l).defs, (h.at' l).typed, (h.at' l).stored⟩

/-- **A store has an honest store typing when every location has a `T_Vary`
witness**: record each witness's self type.  With `Store.Honest.varyWitness`,
a store has an honest store typing exactly when every location has a `T_Vary`
typing. -/
def honestOfVaryWitness {σ : Sig} {G : Store σ σ} (w : (l : BVar σ .var) → VaryWitness G l) :
    (W : StoreTy σ) × Store.Honest G W :=
  ⟨fun l => (w l).T, ⟨fun l => ⟨(w l).defs, (w l).typed, (w l).stored⟩⟩⟩

/-- **At a location without a `T_Vary` typing the location rules are not
admissible.**  `loc ℓ ⊤` has type `⊤` at every store typing and in every
context, by `AtomTy.varConcAny` at the match `⊤`, which every literal has;
the source types `ℓ` at no type, since every source typing of a location
contains a `T_Vary` at it.  By `honestOfVaryWitness`, a store with no honest
store typing has, classically, a location of this kind; there the location
rules derive what the source does not, whatever the store typing. -/
theorem noVary_not_admissible {σ s : Sig} {G : Store σ σ} {l : BVar σ .var}
    (hno : VaryWitness G l → False) (W : StoreTy σ) (Γ : Ctx σ s) :
    Nonempty (AtomTy G W Γ (.loc l .TTop) .TTop) ∧
      ∀ {T : Ty σ s}, HasType G Γ (.tvar (.conc l)) T → False :=
  ⟨⟨.varConcAny .top⟩, fun d => hno (HasType.varyWitness d rfl)⟩

/-! ## The fragment is reflected by substitution

A substitution sends variables to variables.  It changes neither the shape of
a term nor whether an annotation is present, so a term, member or list whose
instance is in the fragment of `Elaboration` is in it already. -/

mutual

/-- A term whose instance under `θ` is in `TmFrag` is in `TmFrag`. -/
def TmFrag.ofSubst {σ1 s1 σ2 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) :
    (t : Oopsla16.Tm σ1 s1) → TmFrag (t.subst θ) → TmFrag t
  | .tvar _, _ => .tvar
  | .tobj ds, h => by
      cases h with
      | tobj hd => exact .tobj (DmsFrag.ofSubst θ.lift ds hd)
  | .tapp (.tvar _) _ (.tvar _), _ => .tapp
  | .tapp (.tvar _) _ (.tobj _), h => nomatch h
  | .tapp (.tvar _) _ (.tapp _ _ _), h => nomatch h
  | .tapp (.tobj _) _ _, h => nomatch h
  | .tapp (.tapp _ _ _) _ _, h => nomatch h

/-- A member whose instance under `θ` is in `DmFrag` is in `DmFrag`. -/
def DmFrag.ofSubst {σ1 s1 σ2 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) :
    (d : Dm σ1 s1) → DmFrag (d.subst θ) → DmFrag d
  | .dty _, _ => .dty
  | .dfun (some _) (some _) t, h => by
      cases h with
      | dfun ht => exact .dfun (TmFrag.ofSubst θ.lift t ht)
  | .dfun none _ _, h => nomatch h
  | .dfun (some _) none _, h => nomatch h

/-- **A definition list whose instance under `θ` is in `DmsFrag` is in
`DmsFrag`.** -/
def DmsFrag.ofSubst {σ1 s1 σ2 s2 : Sig} (θ : Subst σ1 s1 σ2 s2) :
    (ds : Dms σ1 s1) → DmsFrag (ds.subst θ) → DmsFrag ds
  | .dnil, _ => .dnil
  | .dcons d ds, h => by
      cases h with
      | dcons hd hds => exact .dcons (DmFrag.ofSubst θ d hd) (DmsFrag.ofSubst θ ds hds)

end

/-! ## The headline theorems rule programs out -/

namespace NonVacuity

open Oopsla16.PackingCounterexample (S2 badTerm badTerm_not_answer)

/-- A closed typed program: the empty object at `⊤`. -/
example : HasType Store.nil Ctx.nil (.tobj .dnil) .TTop := Oopsla16.Examples.ex0

/-- A closed typed program outside `TmFrag`, typed through two `stp_bindx`. -/
example : HasType Store.nil Ctx.nil SourceSafety.RecursiveArg.prog .TTop :=
  SourceSafety.RecursiveArg.progTy

/-- **The stuck predicate is inhabited**: `PackingCounterexample.badTerm` over
the two-object store is not an answer and does not step. -/
theorem badTerm_stuck : SrcStuck Oopsla16.PackingCounterexample.G badTerm :=
  ⟨badTerm_not_answer, Oopsla16.PackingCounterexample.badTerm_stuck⟩

/-- `(new {}).0(new {})`: a method call on an object with no members. -/
abbrev ill : Oopsla16.Tm [] [] := .tapp (.tobj .dnil) 0 (.tobj .dnil)

/-- **It reaches a stuck configuration from the empty store**, in two steps:
`ST_App1` allocates the receiver, `ST_App2` the argument, and `ST_AppAbs` finds
no method at label `0`. -/
theorem ill_reaches_stuck :
    ∃ (σ : Sig) (g : Grows [] σ) (G' : Store σ σ) (t' : Oopsla16.Tm σ []),
      Oopsla16.Steps g Store.nil ill G' t' ∧ SrcStuck G' t' := by
  refine ⟨_, _, _, _, .tail (.tail .refl (.ST_App1 .ST_Obj)) (.ST_App2 .ST_Obj), ?_, ?_⟩
  · intro h; exact h
  · rintro ⟨σ', g, G', t', h⟩
    cases h with
    | ST_AppAbs hf => cases hf
    | ST_App1 h => cases h
    | ST_App2 h => cases h

/-- **So `Oopsla16.oopsla16_safety` refutes every typing of it.** -/
theorem ill_untypable {T : Ty [] []} (ht : HasType Store.nil Ctx.nil ill T) : False := by
  obtain ⟨_, _, _, _, run, hs⟩ := ill_reaches_stuck
  exact Oopsla16.oopsla16_safety ht run hs

/-- **`Oopsla16.oopsla16_safety_honest` refutes every `Oopsla16` typing of
`badTerm`** over the honest two-object store, whose witnesses are in the
fragment (`SourceSafety.HonestCall.frag`).  `PackingCounterexample` types it
with the packing rule `htp_pack` added. -/
theorem badTerm_untypable {T : Ty S2 []}
    (ht : HasType Oopsla16.PackingCounterexample.G Ctx.nil badTerm T) : False :=
  Oopsla16.oopsla16_safety_honest TwoObjectStore.honest SourceSafety.HonestCall.frag ht .refl
    badTerm_stuck

end NonVacuity

/-! ## A store with a Curry-style method is beyond the honest-store theorems

`Admissibility.CurryStore` stores the identity `{def 0(y) = y}` without
annotations, and its store typing `CurryStore.W` is honest.  The reference's
`type_safety` holds over every store, so it covers the configuration
`id.0(id)` there: the configuration is typed, and it steps.  The Lean theorems
do not.  The empty-store theorems need the empty store, and the honest-store
theorems need every witness in `DmsFrag`, which no witness at this location
is. -/

namespace CurryGap

open CurryStore (S1 l G varyTyped lit_not_annotated)

/-- `id.0(id)`. -/
abbrev idApp : Oopsla16.Tm S1 [] := .tapp (.tvar (.conc l)) 0 (.tvar (.conc l))

/-- **`id.0(id)` is typed at `⊤`**: the receiver by `T_Vary` at the identity's
type (`CurryStore.varyTyped`), narrowed to its method, and the argument at
`⊤`. -/
def idApp_typed : HasType G Ctx.nil idApp .TTop :=
  .T_App (T1 := .TTop) (T2 := .TTop) (.T_Sub varyTyped (.stp_and11 (Stp.refl _)))
    (.T_Sub varyTyped .stp_top)

/-- **It steps**, by `ST_AppAbs`, to the argument. -/
theorem idApp_steps : Oopsla16.Step .refl G idApp G (.tvar (.conc l)) :=
  .ST_AppAbs (OT1 := none) (OT2 := none) (t12 := .tvar (.abs .here)) rfl

/-- **No honesty witness at the location is in the fragment**, at any store
typing.  A fragment witness is annotated (`Elaboration.DmsFrag.annotated`),
substitution keeps annotations (`StoreTyping.Dms.annotated_subst`), and the
stored literal is not annotated (`CurryStore.lit_not_annotated`).  So the
hypothesis `hf` of `Oopsla16.oopsla16_safety_honest` and
`oopsla16_not_stuck_honest` fails at every honest store typing of `G`. -/
theorem not_frag {W : StoreTy S1} (h : Store.Honest G W) (f : DmsFrag (h.at' l).defs) :
    False :=
  lit_not_annotated (by
    rw [← (h.at' l).stored]
    exact (Dms.annotated_subst _ _).mpr f.annotated)

end CurryGap

/-! ## The location rules take the stored annotations on trust

One location, holding `{def 0(y : ⊤) : ⊥ = y}`.  Both annotations are present,
so the store is annotated, and the location rules read the method's type
`⊤ → ⊥` off them.  The body `y` has type `⊤`, not `⊥`, and nothing in the
location rules looks at it.  The source's `T_Vary` does. -/

namespace UncheckedBody

/-- One location. -/
abbrev S1 : Sig := ([],x)

/-- That location. -/
abbrev l : BVar S1 .var := .here

/-- `{def 0(y : ⊤) : ⊥ = y}`: both annotations present, and a body that does
not have the declared codomain.  Generic in the local scope, so that it serves
as the stored literal and as its self-abstracted form. -/
abbrev badDefs {s : Sig} : Dms S1 s :=
  .dcons (.dfun (some .TTop) (some .TBot) (.tvar (.abs .here))) .dnil

/-- The store holding it. -/
abbrev G : Store S1 S1 := .cons .nil badDefs

/-- **The store is annotated**, so it satisfies the hypothesis of the term
elaboration (`ElaborationFull.elabTm`). -/
instance annotated : Store.Annotated G := ⟨fun | .here => ⟨⟨rfl, rfl⟩, trivial⟩⟩

/-- The self type the annotations declare, `{0 : ⊤ → ⊥} ∧ ⊤`. -/
abbrev Tbot : Ty S1 ([],x) := .TAnd (.TFun 0 .TTop .TBot) .TTop

/-- `ℓ.0(ℓ)` in FCdotR: the receiver observed by `loc` at `Tbot` and narrowed
to its method, the argument observed by `loc` at `⊤`. -/
abbrev appBot : Tm S1 [] :=
  .app (.cast (.loc l Tbot) (.andE1 .TTop (.refl (.TFun 0 .TTop .TBot)))) 0 (.loc l .TTop)

/-- **At every store typing, the target types `ℓ.0(ℓ)` at `⊥`.**  Both atoms
are typed by `AtomTy.varConcAny`, whose premise `LitMatch` finds the stored
method with the annotations `⊤` and `⊥`; no rule looks at `W`, and none at the
method's body. -/
def appBot_typed (W : StoreTy S1) : TmTy G W Ctx.nil appBot .TBot :=
  TmTy.app (U := .TBot)
    (AtomTy.cast (AtomTy.varConcAny (LitMatch.fn rfl .top)) (LeTy.andE1 .TTop (LeTy.refl _)))
    (AtomTy.varConcAny .top)

/-- `ℓ.0(ℓ)` in the source. -/
abbrev srcApp : Oopsla16.Tm S1 [] := .tapp (.tvar (.conc l)) 0 (.tvar (.conc l))

/-- `appBot` erases to it. -/
theorem appBot_erase : appBot.erase = srcApp := rfl

/-- `ℓ.1(ℓ)`: a call at a label the object does not have. -/
abbrev stuckTm : Oopsla16.Tm S1 [] := .tapp (.tvar (.conc l)) 1 (.tvar (.conc l))

/-- `(ℓ.0(ℓ)).1(ℓ)`. -/
abbrev stuckProg : Oopsla16.Tm S1 [] := .tapp srcApp 1 (.tvar (.conc l))

/-- **An honest store typing would type `(ℓ.0(ℓ)).1(ℓ)`.**  Over an honest
store, `ℓ` has the type the annotations declare
(`Admissibility.Store.Honest.litMatch_hasType`), so `ℓ.0(ℓ)` has type `⊥`,
which is below the method type `{1 : ⊤ → ⊤}`. -/
def stuckProg_typed {W : StoreTy S1} (h : Store.Honest G W) :
    HasType G Ctx.nil stuckProg .TTop :=
  have hl : HasType G Ctx.nil (.tvar (.conc l)) (.TAnd (.TFun 0 .TTop .TBot) .TTop) :=
    h.litMatch_hasType (T := Tbot) (.fn rfl .top)
  .T_App (T1 := .TTop) (T2 := .TTop)
    (.T_Sub (.T_App (T1 := .TTop) (T2 := .TBot) (.T_Sub hl (.stp_and11 (Stp.refl _)))
      (.T_Sub hl .stp_top)) .stp_bot)
    (.T_Sub hl .stp_top)

/-- It steps to `ℓ.1(ℓ)`: `ST_App1` around `ST_AppAbs`, which runs the body
`y` at `ℓ`. -/
theorem stuckProg_run : Oopsla16.Steps (Grows.refl.comp Grows.refl) G stuckProg G stuckTm :=
  .tail .refl (.ST_App1 (.ST_AppAbs (OT1 := some .TTop) (OT2 := some .TBot)
    (t12 := .tvar (.abs .here)) rfl))

/-- `ℓ.1(ℓ)` is stuck: the object has no member at label `1`. -/
theorem stuckTm_stuck : SrcStuck G stuckTm := by
  refine ⟨fun h => h, ?_⟩
  rintro ⟨σ', g, G', t', h⟩
  cases h with
  | ST_AppAbs hf => cases hf
  | ST_App1 h => cases h
  | ST_App2 h => cases h

/-- **The store has no honest store typing.**  The witness at `ℓ` is in the
fragment, because the stored literal is (`DmsFrag.ofSubst`), so
`Oopsla16.oopsla16_safety_honest` applies to `stuckProg_typed`, and the run
`stuckProg_run` reaches the stuck `ℓ.1(ℓ)`. -/
theorem not_honest {W : StoreTy S1} (h : Store.Honest G W) : False := by
  have hf : ∀ l, DmsFrag (h.at' l).defs := fun
    | .here => DmsFrag.ofSubst (Subst.one (.conc .here)) _ (by
        show DmsFrag ((h.at' .here).defs.substVr (.conc .here))
        rw [(h.at' .here).stored]
        exact .dcons (.dfun .tvar) .dnil)
  exact Oopsla16.oopsla16_safety_honest h hf (stuckProg_typed h) stuckProg_run stuckTm_stuck

/-- **The source types the location at no type**, in any context.  A typing
would contain a `T_Vary` at `ℓ` (`HasType.varyWitness`), the store's only
location, and so give an honest store typing (`honestOfVaryWitness`). -/
theorem loc_untypable {s : Sig} {Γ : Ctx S1 s} {T : Ty S1 s}
    (d : HasType G Γ (.tvar (.conc l)) T) : False :=
  not_honest (honestOfVaryWitness (G := G) fun (l' : BVar S1 .var) => match l' with
    | .here => HasType.varyWitness d rfl).2

/-- `loc_untypable` for a call on `ℓ`: every typing of `ℓ.0(ℓ)` types its
receiver.  Stated with an equation, for the recursion through `T_Sub`. -/
theorem app_untypable_aux {s : Sig} {Γ : Ctx S1 s} :
    {t : Oopsla16.Tm S1 s} → {T : Ty S1 s} → HasType G Γ t T →
    t = .tapp (.tvar (.conc l)) 0 (.tvar (.conc l)) → False
  | _, _, .T_App d _, h => by cases h; exact loc_untypable d
  | _, _, .T_AppVar d _, h => by cases h; exact loc_untypable d
  | _, _, .T_Sub d _, h => app_untypable_aux d h
  | _, _, .T_Vary _ _, h => by cases h
  | _, _, .T_Varz, h => by cases h
  | _, _, .T_VarPack _, h => by cases h
  | _, _, .T_VarUnpack _, h => by cases h
  | _, _, .T_Obj _, h => by cases h

/-- **The source types `ℓ.0(ℓ)` at no type.**  The target types it at `⊥` at
every store typing (`appBot_typed`), and it is the erasure of that target term
(`appBot_erase`). -/
theorem app_untypable {T : Ty S1 []} (d : HasType G Ctx.nil srcApp T) : False :=
  app_untypable_aux d rfl

end UncheckedBody

end FCdotR
