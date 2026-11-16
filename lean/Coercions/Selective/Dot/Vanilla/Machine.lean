import Coercions.DotMNF.Machine
import Coercions.Selective.Dot.Vanilla.Exact
import Coercions.Selective.Dot.Safety

/-!
# Selective DOT and DOT-MNF: the machines

The machine of DOT-MNF and the machine of `SelDot` agree on states translated
by `ofDot`: every step of one is a step of the other, and a translated state is
final or stuck exactly when the source state is. Type safety of DOT-MNF then
follows from the safety of `SelDot`, through the elaboration of a typing
derivation, whose erasure is the source term.
-/

namespace SelDot

open FCdot (Kind Sig BVar Rename Label)

/-! ## Translations of terms commute with renaming -/

mutual

theorem Tm.ofDot_rename : ∀ {s1 s2 : Sig} (t : DotMNF.Tm s1) (ρ : Rename s1 s2),
    Tm.ofDot (t.rename ρ) = (Tm.ofDot t).rename ρ
  | _, _, .path (.var _), _ => rfl
  | _, _, .val v, ρ => by
      simp only [DotMNF.Tm.rename, Tm.ofDot, Tm.rename, Value.ofDot_rename v ρ]
  | _, _, .app _ _, _ => rfl
  | _, _, .proj _ _, _ => rfl
  | _, _, .let t u, ρ => by
      simp only [DotMNF.Tm.rename, Tm.ofDot, Tm.rename, Tm.ofDot_rename t ρ,
        Tm.ofDot_rename u ρ.lift]

theorem Value.ofDot_rename : ∀ {s1 s2 : Sig} (v : DotMNF.Value s1) (ρ : Rename s1 s2),
    Value.ofDot (v.rename ρ) = (Value.ofDot v).rename ρ
  | _, _, .obj d, ρ => by
      simp only [DotMNF.Value.rename, Value.ofDot, Value.rename, Defs.ofDot_rename d ρ.lift]
  | _, _, .lam S t, ρ => by
      simp only [DotMNF.Value.rename, Value.ofDot, Value.rename, Ty.ofDot_rename,
        Tm.ofDot_rename t ρ.lift]

theorem Defs.ofDot_rename : ∀ {s1 s2 : Sig} (d : DotMNF.Defs s1) (ρ : Rename s1 s2),
    Defs.ofDot (d.rename ρ) = (Defs.ofDot d).rename ρ
  | _, _, .typ _ _, ρ => by
      simp only [DotMNF.Defs.rename, Defs.ofDot, Defs.rename, Ty.ofDot_rename]
  | _, _, .trm _ t, ρ => by
      simp only [DotMNF.Defs.rename, Defs.ofDot, Defs.rename, Tm.ofDot_rename t ρ]
  | _, _, .and d1 d2, ρ => by
      simp only [DotMNF.Defs.rename, Defs.ofDot, Defs.rename, Defs.ofDot_rename d1 ρ,
        Defs.ofDot_rename d2 ρ]

end

theorem Tm.ofDot_weaken (t : DotMNF.Tm s) :
    Tm.ofDot (t.weaken : DotMNF.Tm (s,x)) = (Tm.ofDot t).weaken := Tm.ofDot_rename t _

theorem Value.ofDot_weaken (v : DotMNF.Value s) :
    Value.ofDot (v.weaken : DotMNF.Value (s,x)) = (Value.ofDot v).weaken :=
  Value.ofDot_rename v _

theorem Defs.ofDot_weaken (d : DotMNF.Defs s) :
    Defs.ofDot (d.weaken : DotMNF.Defs (s,x)) = (Defs.ofDot d).weaken := Defs.ofDot_rename d _

theorem Tm.ofDot_substVar (t : DotMNF.Tm (s,x)) (y : BVar s .var) :
    Tm.ofDot (t.substVar y) = (Tm.ofDot t).substVar y := Tm.ofDot_rename t _

/-- Term lookup commutes with the translation of definitions. -/
theorem Defs.ofDot_lookupTrm : ∀ {s : Sig} (d : DotMNF.Defs s) (a : Label),
    (Defs.ofDot d).lookupTrm a = (d.lookupTrm a).map Tm.ofDot
  | _, .typ _ _, _ => rfl
  | _, .trm b t, a => by
      simp only [Defs.ofDot, Defs.lookupTrm, DotMNF.Defs.lookupTrm]
      split <;> rfl
  | _, .and d1 d2, a => by
      simp only [Defs.ofDot, Defs.lookupTrm, DotMNF.Defs.lookupTrm,
        Defs.ofDot_lookupTrm d1 a, Defs.ofDot_lookupTrm d2 a]
      cases DotMNF.Defs.lookupTrm d2 a <;> rfl

/-! ## Translations of machine states -/

/-- Stores from DOT-MNF. -/
def Store.ofDot : DotMNF.Store s → Store s
  | .nil => .nil
  | .cons σ v => .cons (Store.ofDot σ) (Value.ofDot v)

/-- Continuations from DOT-MNF. -/
def Cont.ofDot : DotMNF.Cont s → Cont s
  | .nil => .nil
  | .cons K u => .cons (Cont.ofDot K) (Tm.ofDot u)

/-- States from DOT-MNF. -/
def State.ofDot (st : DotMNF.State s) : State s :=
  ⟨Store.ofDot st.σ, Cont.ofDot st.K, Tm.ofDot st.t⟩

/-- Store lookup commutes with the translation of stores. -/
theorem Store.ofDot_lookup : ∀ {s : Sig} (σ : DotMNF.Store s) (x : BVar s .var),
    (Store.ofDot σ).lookup x = Value.ofDot (σ.lookup x)
  | _, .cons _ v, .here => (Value.ofDot_weaken v).symm
  | _, .cons σ _, .there y => by
      change ((Store.ofDot σ).lookup y).weaken = Value.ofDot ((σ.lookup y).weaken)
      rw [Store.ofDot_lookup σ y, Value.ofDot_weaken]

theorem Cont.ofDot_rename : ∀ {s1 s2 : Sig} (K : DotMNF.Cont s1) (ρ : Rename s1 s2),
    Cont.ofDot (K.rename ρ) = (Cont.ofDot K).rename ρ
  | _, _, .nil, _ => rfl
  | _, _, .cons K u, ρ => by
      simp only [DotMNF.Cont.rename, Cont.ofDot, Cont.rename, Cont.ofDot_rename K ρ,
        Tm.ofDot_rename]

theorem Cont.ofDot_weaken (K : DotMNF.Cont s) :
    Cont.ofDot (K.weaken : DotMNF.Cont (s,x)) = (Cont.ofDot K).weaken := Cont.ofDot_rename K _

end SelDot

namespace SelDot.Vanilla

open FCdot (Kind Sig BVar Rename Label)

/-! ## The machines agree -/

/-- A step of DOT-MNF is a step of `SelDot` on the translated states. -/
theorem step_ofDot {s s' : Sig} {st : DotMNF.State s} {st' : DotMNF.State s'}
    (h : DotMNF.Step st st') : SelDot.Step (State.ofDot st) (State.ofDot st') := by
  cases h with
  | «let» => exact .let
  | alloc =>
      simp only [State.ofDot, Store.ofDot, Cont.ofDot, Tm.ofDot, Cont.ofDot_weaken]
      exact .alloc
  | rename =>
      simp only [State.ofDot, Cont.ofDot, Tm.ofDot, Tm.ofDot_substVar]
      exact .rename
  | app hx =>
      simp only [State.ofDot, Tm.ofDot, Tm.ofDot_substVar]
      exact .app ((Store.ofDot_lookup _ _).trans (congrArg Value.ofDot hx))
  | proj hx ha =>
      simp only [State.ofDot, Tm.ofDot, Tm.ofDot_substVar]
      exact .proj ((Store.ofDot_lookup _ _).trans (congrArg Value.ofDot hx))
        ((Defs.ofDot_lookupTrm _ _).trans (congrArg (Option.map Tm.ofDot) ha))

/-- A step of `SelDot` from a translated state is the translation of a step of DOT-MNF. -/
theorem step_of_ofDot {s s' : Sig} {st : DotMNF.State s} {st2 : SelDot.State s'}
    (h : SelDot.Step (State.ofDot st) st2) :
    ∃ st' : DotMNF.State s', st2 = State.ofDot st' ∧ DotMNF.Step st st' := by
  obtain ⟨σ, K, t⟩ := st
  cases t with
  | path p =>
      cases p with
      | var y =>
          cases K with
          | nil => cases h
          | cons K u =>
              cases h
              exact ⟨⟨σ, K, u.substVar y⟩, by simp only [State.ofDot, Tm.ofDot_substVar],
                .rename⟩
  | val v =>
      cases K with
      | nil => cases h
      | cons K u =>
          cases h
          exact ⟨⟨.cons σ v, K.weaken, u⟩, by simp only [State.ofDot, Store.ofDot,
            Cont.ofDot_weaken], .alloc⟩
  | app x y =>
      simp only [State.ofDot, Tm.ofDot] at h
      generalize hK : Cont.ofDot K = K' at h
      cases h with
      | app hx =>
          subst hK
          rw [Store.ofDot_lookup] at hx
          generalize hv : σ.lookup x = v at hx
          cases v with
          | obj _ => cases hx
          | lam S t =>
              cases hx
              exact ⟨⟨σ, K, t.substVar y⟩, by simp only [State.ofDot, Tm.ofDot_substVar],
                .app hv⟩
  | proj x a =>
      simp only [State.ofDot, Tm.ofDot] at h
      generalize hK : Cont.ofDot K = K' at h
      cases h with
      | proj hx ha =>
          subst hK
          rw [Store.ofDot_lookup] at hx
          generalize hv : σ.lookup x = v at hx
          cases v with
          | lam _ _ => cases hx
          | obj d =>
              cases hx
              rw [Defs.ofDot_lookupTrm] at ha
              generalize hu : d.lookupTrm a = o at ha
              cases o with
              | none => cases ha
              | some t =>
                  cases ha
                  exact ⟨⟨σ, K, t.substVar x⟩, by simp only [State.ofDot, Tm.ofDot_substVar],
                    .proj hv hu⟩
  | «let» t u =>
      simp only [State.ofDot, Tm.ofDot] at h
      generalize hK : Cont.ofDot K = K' at h
      cases h
      subst hK
      exact ⟨⟨σ, .cons K u, t⟩, rfl, .let⟩

/-- Runs of DOT-MNF are runs of `SelDot` on the translated states. -/
theorem steps_ofDot {s s' : Sig} {st : DotMNF.State s} {st' : DotMNF.State s'}
    (h : DotMNF.Steps st st') : SelDot.Steps (State.ofDot st) (State.ofDot st') := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact .tail ih (step_ofDot hstep)

/-- A translated state is final exactly when the source state is. -/
theorem final_ofDot {s : Sig} {st : DotMNF.State s} : (State.ofDot st).Final ↔ st.Final := by
  obtain ⟨σ, K, t⟩ := st
  cases K with
  | cons K u =>
      constructor
      · rintro ⟨h, _⟩; cases h
      · rintro ⟨h, _⟩; cases h
  | nil =>
      cases t with
      | path p =>
          cases p with
          | var y =>
              exact ⟨fun _ => ⟨rfl, .inr ⟨.var y, rfl⟩⟩, fun _ => ⟨rfl, .inr ⟨y, rfl⟩⟩⟩
      | val v =>
          exact ⟨fun _ => ⟨rfl, .inl ⟨v, rfl⟩⟩, fun _ => ⟨rfl, .inl ⟨Value.ofDot v, rfl⟩⟩⟩
      | app x y =>
          constructor
          · rintro ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩ <;> cases h
          · rintro ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩ <;> cases h
      | proj x a =>
          constructor
          · rintro ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩ <;> cases h
          · rintro ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩ <;> cases h
      | «let» t u =>
          constructor
          · rintro ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩ <;> cases h
          · rintro ⟨_, ⟨_, h⟩ | ⟨_, h⟩⟩ <;> cases h

/-- A stuck state of DOT-MNF translates to a stuck state of `SelDot`. -/
theorem stuck_ofDot {s : Sig} {st : DotMNF.State s} (h : st.Stuck) : (State.ofDot st).Stuck := by
  obtain ⟨hnf, hns⟩ := h
  refine ⟨fun hf => hnf (final_ofDot.mp hf), ?_⟩
  rintro ⟨s', st2, hstep⟩
  obtain ⟨st', _, hst'⟩ := step_of_ofDot hstep
  exact hns ⟨s', st', hst'⟩

/-! ## Type safety of DOT-MNF -/

/-- A closed typed DOT-MNF program never reaches a stuck state. The proof
elaborates the program into `SelDot` and runs the translated machine. -/
theorem dot_safety_direct {t : DotMNF.Tm []} {T : DotMNF.Ty []} (h : DotMNF.HasTy .nil t T)
    {s : Sig} {st : DotMNF.State s} (hs : DotMNF.Steps ⟨.nil, .nil, t⟩ st) : ¬ st.Stuck := by
  intro hst
  have hrun : SelDot.Steps ⟨.nil, .nil, h.elab.erase⟩ (State.ofDot st) := by
    rw [h.elab_erase]
    exact steps_ofDot hs
  have ht : SelDot.HasTy .nil h.elab (Ty.ofDot T) := h.elab_typed
  exact SelDot.safety ht hrun (stuck_ofDot hst)

end SelDot.Vanilla
