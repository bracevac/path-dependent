import Coercions.FCdotR.Inversion
import Coercions.FCdotR.Progress

/-!
# Canonical forms for methods over a machine store

`Preservation` and `Progress` take one hypothesis, `AppInversion` —
canonical forms for methods over an honest machine store — and reduce it to its
evidence-level content `ObsFunInversion` (`AppInversion.ofObs`).  This module
inhabits `ObsFunInversion`, hence `AppInversion`, from `Inversion`'s
`RecordedLit.obsFun`, and states the results of `Preservation` and `Progress`
with the hypothesis gone: `preservation'`, `preservation_steps'`,
`preservation_init'`, `progress'`, `not_stuck'`, `safety'` and
`safety_of_source'`.

The only store-specific step is that an honest machine store records literal
types (`MachineStore.Honest.recordedLit`): its invariant types each stored
definition list with the target's `DefsTy`, so `Inversion.defsLitTy` applies,
and a type-member conjunct of a `DefsTy` type is found by the erased list's
lookup (`defsTy_erase_of_conjunct`), positional labels doing the work.

What this module does **not** contain: anything about the source machine;
`Preservation`'s and `Progress`'s own restrictions (the let-free fragment of the
simulation, the elaborable fragment of source terms) are unchanged.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Dm Dms Ctx Store Subst DmsHasType renameNil)

/-- **A type-member conjunct of a `DefsTy` type is a member of the erased
list**, at the same label and exact type.  The converse direction of
`Preservation.DefsTy.conjunct`, read through erasure. -/
theorem defsTy_erase_of_conjunct {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    {Γ : Ctx σ []} : {ds : Defs σ []} → {T : Ty σ []} → DefsTy G W Γ ds T →
    {a : Lb} → {TX : Ty σ []} → Conjunct T (.TTyp a TX TX) →
    ds.erase.get? a = some (.dty TX)
  | _, _, .dnil, _, _, c => nomatch c
  | _, _, .dty (T := T0) (ds := ds) hds, a, TX, c => by
      cases c with
      | here =>
          show (if ds.length = ds.erase.length then some (Dm.dty T0)
            else ds.erase.get? ds.length) = _
          rw [Defs.erase_length, if_pos rfl]
      | there c =>
          have h := defsTy_erase_of_conjunct hds c
          have hlt := dmsTyp_label_lt _ h
          show (if a = ds.erase.length then some (Dm.dty T0) else ds.erase.get? a) = _
          rw [if_neg (Nat.ne_of_lt hlt)]
          exact h
  | _, _, .dfun (ds := ds) hds _, a, TX, c => by
      cases c with
      | there c =>
          have h := defsTy_erase_of_conjunct hds c
          have hlt := dmsTyp_label_lt _ h
          show (if a = ds.erase.length then some _ else ds.erase.get? a) = _
          rw [if_neg (Nat.ne_of_lt hlt)]
          exact h

/-- **An honest machine store records literal types**, read through erasure:
the invariant's `DefsTy` witness has the skeleton, hence the erasure, of the
stored list. -/
def MachineStore.Honest.recordedLit {σ : Sig} {G : MachineStore σ σ} {W : StoreTy σ}
    (h : MachineStore.Honest G W) : RecordedLit G.erase W := fun l =>
  defsLitTy _ (h.at' l).typed (fun c => by
    rw [← MachineStore.erase_lookup, ← Defs.erase_of_skel (h.at' l).skel]
    exact defsTy_erase_of_conjunct (h.at' l).typed c)

/-- `Inversion.LocBase` is `Preservation.LocType`: the same two location
nodes. -/
def LocBase.toLocType {σ : Sig} {G : Store σ σ} {W : StoreTy σ} {l : BVar σ .var} :
    {B : Ty σ []} → LocBase G W l B → LocType G W l B
  | _, .recorded => .recorded
  | _, .witness hd hs => .witness hd hs

/-- **`Preservation.ObsFunInversion` is inhabited**: canonical forms for method
observations over an honest machine store, by `RecordedLit.obsFun`. -/
def obsFunInversion : ObsFunInversion where
  inv := fun h => fun dv =>
    let o := h.recordedLit.obsFun dv
    { base := o.base, baseTy := o.baseOf.toLocType, S := o.S, U := o.U,
      conj := o.conj, dom := o.dom.ev, domTy := o.dom.typed, cod := o.cod.ev,
      codTy := o.cod.typed }

/-- **`Preservation.AppInversion` is inhabited**, by `AppInversion.ofObs`. -/
def appInversion : AppInversion := AppInversion.ofObs obsFunInversion

/-- **Preservation, with no hypothesis**: `Preservation.preservation` at
`appInversion`. -/
theorem preservation' {σ1 σ2 : Sig} {g : Oopsla16.Grows σ1 σ2} {st : State σ1}
    {st' : State σ2} {W : StoreTy σ1} {T : Ty σ1 []} (h : st.G.Honest W)
    (d : StateTy st W T) (hs : Step g st st') :
    ∃ W', Nonempty (st'.G.Honest W' × StateTy st' W' (Ty.alongGrows g T)) :=
  preservation appInversion h d hs

/-- **Preservation along a run, with no hypothesis**:
`Preservation.preservation_steps` at `appInversion`. -/
theorem preservation_steps' {σ1 σ2 : Sig} {g : Oopsla16.Grows σ1 σ2} {st : State σ1}
    {st' : State σ2} {W : StoreTy σ1} {T : Ty σ1 []} (h : MachineStore.Honest st.G W)
    (d : StateTy st W T) (hs : Steps g st st') :
    ∃ W', Nonempty (MachineStore.Honest st'.G W' × StateTy st' W' (Ty.alongGrows g T)) :=
  preservation_steps appInversion h d hs

/-- **A closed typed term stays typed along a run, with no hypothesis**:
`Preservation.preservation_init` at `appInversion`. -/
theorem preservation_init' {W : StoreTy []} {t : Tm [] []} {T : Ty [] []}
    (d : TmTy Store.nil W Ctx.nil t T) {σ : Sig} {g : Oopsla16.Grows [] σ}
    {st' : State σ} (hs : Steps g ⟨MachineStore.nil, .nil, t⟩ st') :
    ∃ W', Nonempty (MachineStore.Honest st'.G W' × StateTy st' W' (Ty.alongGrows g T)) :=
  preservation_init appInversion d hs

/-- **Progress, with no hypothesis**: `Progress.progress` at `appInversion`. -/
theorem progress' {σ : Sig} {st : State σ} {W : StoreTy σ} {U : Ty σ []}
    (h : MachineStore.Honest st.G W) (d : StateTy st W U) : st.Final ∨ st.CanStep :=
  progress appInversion h d

/-- **A typed state over an honest machine store is not stuck, with no
hypothesis**: `Progress.not_stuck` at `appInversion`. -/
theorem not_stuck' {σ : Sig} {st : State σ} {W : StoreTy σ} {U : Ty σ []}
    (h : MachineStore.Honest st.G W) (d : StateTy st W U) : ¬ st.Stuck :=
  not_stuck appInversion h d

/-- **Type safety of the FCdotR machine, with no hypothesis**: a closed term
typed over the empty store never reaches a stuck state.  `Progress.safety` at
`appInversion`. -/
theorem safety' {W : StoreTy []} {t : Tm [] []} {T : Ty [] []}
    (d : TmTy Store.nil W Ctx.nil t T) {σ : Sig} {g : Oopsla16.Grows [] σ}
    {st' : State σ} (hs : Steps g ⟨MachineStore.nil, .nil, t⟩ st') : ¬ st'.Stuck :=
  safety appInversion d hs

/-- **Type safety from an elaborable source configuration, with no
hypothesis**: `Progress.safety_of_source` at `appInversion`.  A source term
typed over an honest source store, the term and every stored witness in the
elaborable fragment (`TmFrag`/`DmsFrag`), starts a machine run that never
reaches a stuck *target* state.  This is not yet safety of `Oopsla16`'s own
semantics: that needs `Erasure`'s simulation beyond the let-free fragment. -/
theorem safety_of_source' {σ : Sig} {G : Store σ σ} {W : StoreTy σ}
    (h : Store.Honest G W) (hf : ∀ l, DmsFrag (h.at' l).defs)
    {t : Oopsla16.Tm σ []} {T : Ty σ []} (ht : Oopsla16.HasType G Ctx.nil t T)
    (ft : TmFrag t) {σ' : Sig} {g : Oopsla16.Grows σ σ'} {st' : State σ'}
    (hs : Steps g (StateTy.ofSource h hf ht ft).1 st') : ¬ st'.Stuck :=
  safety_of_source appInversion h hf ht ft hs

end FCdotR
