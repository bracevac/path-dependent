import Coercions.DotMNF.WadlerFest.Machine
import Coercions.DotMNF.Machine

/-!
# Annotation erasure for the annotated store machine

Removing object annotations preserves and reflects individual steps, finite
executions, finality, and stuckness between the annotated store machine and
DOT-MNF. These results have no typing premises. They concern the two store
machines, not the published retained-let evaluation-context semantics.
-/

namespace WadlerFest

open FCdot (Sig BVar Rename Label)

def Store.eraseAnnotations : Store s → DotMNF.Store s
  | .nil => .nil
  | .cons σ v => .cons σ.eraseAnnotations v.eraseAnnotations

def Cont.eraseAnnotations : Cont s → DotMNF.Cont s
  | .nil => .nil
  | .cons K u => .cons K.eraseAnnotations u.eraseAnnotations

def State.eraseAnnotations (st : State s) : DotMNF.State s :=
  ⟨st.σ.eraseAnnotations, st.K.eraseAnnotations, st.t.eraseAnnotations⟩

@[simp] theorem Value.eraseAnnotations_weaken (v : Value s) :
    v.weaken.eraseAnnotations = v.eraseAnnotations.weaken :=
  v.eraseAnnotations_rename Rename.succ

@[simp] theorem Cont.eraseAnnotations_rename (K : Cont s₁) (ρ : Rename s₁ s₂) :
    (K.rename ρ).eraseAnnotations = K.eraseAnnotations.rename ρ := by
  induction K with
  | nil => rfl
  | cons K u ih =>
      simp only [Cont.rename, Cont.eraseAnnotations, DotMNF.Cont.rename,
        ih, Tm.eraseAnnotations_rename]

@[simp] theorem Cont.eraseAnnotations_weaken (K : Cont s) :
    K.weaken.eraseAnnotations = K.eraseAnnotations.weaken :=
  K.eraseAnnotations_rename Rename.succ

@[simp] theorem Store.lookup_eraseAnnotations (σ : Store s) (x : BVar s .var) :
    σ.eraseAnnotations.lookup x = (σ.lookup x).eraseAnnotations := by
  match σ, x with
  | .cons _ v, .here =>
      simp only [Store.eraseAnnotations, Store.lookup, DotMNF.Store.lookup,
        Value.eraseAnnotations_weaken]
  | .cons σ _, .there x =>
      simp only [Store.eraseAnnotations, Store.lookup, DotMNF.Store.lookup,
        Value.eraseAnnotations_weaken, Store.lookup_eraseAnnotations σ x]

@[simp] theorem Defs.lookupTrm_eraseAnnotations (d : Defs s) (ℓ : Label) :
    d.eraseAnnotations.lookupTrm ℓ = (d.lookupTrm ℓ).map Tm.eraseAnnotations := by
  match d with
  | .typ _ _ => rfl
  | .trm a t =>
      simp only [Defs.eraseAnnotations, Defs.lookupTrm, DotMNF.Defs.lookupTrm]
      split <;> rfl
  | .and d₁ d₂ =>
      simp only [Defs.eraseAnnotations, Defs.lookupTrm, DotMNF.Defs.lookupTrm,
        Defs.lookupTrm_eraseAnnotations d₁ ℓ, Defs.lookupTrm_eraseAnnotations d₂ ℓ]
      cases d₂.lookupTrm ℓ <;> rfl

/-- Annotation erasure preserves each machine step. -/
theorem eraseAnnotations_step {st : State s} {st' : State s'} (h : Step st st') :
    DotMNF.Step st.eraseAnnotations st'.eraseAnnotations := by
  cases h with
  | «let» => exact .let
  | alloc =>
      simpa only [State.eraseAnnotations, Store.eraseAnnotations, Cont.eraseAnnotations,
        Tm.eraseAnnotations, Cont.eraseAnnotations_weaken] using
        (DotMNF.Step.alloc (σ := _) (K := _) (u := _) (v := _))
  | rename =>
      simpa only [State.eraseAnnotations, Cont.eraseAnnotations, Tm.eraseAnnotations,
        Tm.eraseAnnotations_substVar] using
        (DotMNF.Step.rename (σ := _) (K := _) (u := _) (y := _))
  | app hl =>
      simp only [State.eraseAnnotations, Tm.eraseAnnotations, Tm.eraseAnnotations_substVar]
      exact .app (by rw [Store.lookup_eraseAnnotations, hl]; rfl)
  | proj hl hd =>
      simp only [State.eraseAnnotations, Tm.eraseAnnotations, Tm.eraseAnnotations_substVar]
      exact .proj (by rw [Store.lookup_eraseAnnotations, hl]; rfl)
        (by rw [Defs.lookupTrm_eraseAnnotations, hd]; rfl)

private theorem reflect_app {σ : Store s} {K : Cont s} {x y : BVar s .var}
    {S : DotMNF.Ty s} {t₀ : DotMNF.Tm (s,x)}
    (hl : σ.eraseAnnotations.lookup x = .lam S t₀) :
    ∃ st' : State s, Step ⟨σ, K, .app x y⟩ st' ∧
      st'.eraseAnnotations = ⟨σ.eraseAnnotations, K.eraseAnnotations, t₀.substVar y⟩ := by
  rw [Store.lookup_eraseAnnotations] at hl
  cases hv : σ.lookup x with
  | obj T d => rw [hv] at hl; cases hl
  | lam S' t =>
      rw [hv] at hl
      cases hl
      exact ⟨⟨σ, K, t.substVar y⟩, .app hv, by
        simp only [State.eraseAnnotations, Tm.eraseAnnotations_substVar]⟩

private theorem reflect_proj {σ : Store s} {K : Cont s} {x : BVar s .var} {ℓ : Label}
    {d₀ : DotMNF.Defs (s,x)} {t₀ : DotMNF.Tm (s,x)}
    (hl : σ.eraseAnnotations.lookup x = .obj d₀) (hf : d₀.lookupTrm ℓ = some t₀) :
    ∃ st' : State s, Step ⟨σ, K, .proj x ℓ⟩ st' ∧
      st'.eraseAnnotations = ⟨σ.eraseAnnotations, K.eraseAnnotations, t₀.substVar x⟩ := by
  rw [Store.lookup_eraseAnnotations] at hl
  cases hv : σ.lookup x with
  | lam S t => rw [hv] at hl; cases hl
  | obj T d =>
      rw [hv] at hl
      cases hl
      rw [Defs.lookupTrm_eraseAnnotations] at hf
      cases hd : d.lookupTrm ℓ with
      | none => rw [hd] at hf; cases hf
      | some t =>
          rw [hd] at hf
          cases hf
          exact ⟨⟨σ, K, t.substVar x⟩, .proj hv hd, by
            simp only [State.eraseAnnotations, Tm.eraseAnnotations_substVar]⟩

/-- Every DOT-MNF step from an erased state lifts to an annotated step with
exactly that erased successor. -/
theorem eraseAnnotations_reflect {st : State s} {r : DotMNF.State s'}
    (h : DotMNF.Step st.eraseAnnotations r) :
    ∃ st' : State s', Step st st' ∧ st'.eraseAnnotations = r := by
  obtain ⟨σ, K, t⟩ := st
  cases t with
  | path p =>
      cases p with
      | var x =>
          cases K with
          | nil => cases h
          | cons K u =>
              cases h
              exact ⟨⟨σ, K, u.substVar x⟩, .rename, by
                simp only [State.eraseAnnotations, Tm.eraseAnnotations_substVar]⟩
  | val v =>
      cases K with
      | nil => cases h
      | cons K u =>
          cases h
          exact ⟨⟨.cons σ v, K.weaken, u⟩, .alloc, by
            simp only [State.eraseAnnotations, Store.eraseAnnotations, Cont.eraseAnnotations_weaken]⟩
  | app x y =>
      cases K <;>
        simp only [State.eraseAnnotations, Cont.eraseAnnotations, Tm.eraseAnnotations] at h
      all_goals
        cases h with
        | app hl => exact reflect_app hl
  | proj x ℓ =>
      cases K <;>
        simp only [State.eraseAnnotations, Cont.eraseAnnotations, Tm.eraseAnnotations] at h
      all_goals
        cases h with
        | proj hl hf => exact reflect_proj hl hf
  | «let» t u =>
      cases K with
      | nil =>
          cases h
          exact ⟨⟨σ, .cons .nil u, t⟩, .let, rfl⟩
      | cons K v =>
          cases h
          exact ⟨⟨σ, .cons (.cons K v) u, t⟩, .let, rfl⟩

/-- Annotation erasure preserves finite executions. -/
theorem eraseAnnotations_steps {st : State s} {st' : State s'} (h : Steps st st') :
    DotMNF.Steps st.eraseAnnotations st'.eraseAnnotations := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (eraseAnnotations_step h)

/-- Finite DOT-MNF executions lift to annotated executions. -/
theorem eraseAnnotations_steps_reflect {st : State s} {r : DotMNF.State s'}
    (h : DotMNF.Steps st.eraseAnnotations r) :
    ∃ st' : State s', Steps st st' ∧ st'.eraseAnnotations = r := by
  generalize he : st.eraseAnnotations = r₀ at h
  induction h generalizing st with
  | refl => exact ⟨st, .refl, he⟩
  | tail _ h ih =>
      obtain ⟨mid, hm, heMid⟩ := ih he
      rw [← heMid] at h
      obtain ⟨out, ho, heOut⟩ := eraseAnnotations_reflect h
      exact ⟨out, .tail hm ho, heOut⟩

/-- Finality is unchanged by annotation erasure. -/
theorem State.eraseAnnotations_final_iff (st : State s) :
    st.eraseAnnotations.Final ↔ st.Final := by
  obtain ⟨σ, K, t⟩ := st
  cases K <;> cases t <;>
    simp [State.eraseAnnotations, State.Final, DotMNF.State.Final,
      Cont.eraseAnnotations, Tm.eraseAnnotations]

/-- A state is stuck exactly when its annotation erasure is stuck. -/
theorem State.eraseAnnotations_stuck_iff (st : State s) :
    st.eraseAnnotations.Stuck ↔ st.Stuck := by
  constructor
  · rintro ⟨hnf, hns⟩
    refine ⟨fun hf => hnf ((State.eraseAnnotations_final_iff st).mpr hf), ?_⟩
    rintro ⟨s', st', h⟩
    exact hns ⟨s', st'.eraseAnnotations, eraseAnnotations_step h⟩
  · rintro ⟨hnf, hns⟩
    refine ⟨fun hf => hnf ((State.eraseAnnotations_final_iff st).mp hf), ?_⟩
    rintro ⟨s', r, h⟩
    obtain ⟨st', hs, _⟩ := eraseAnnotations_reflect h
    exact hns ⟨s', st', hs⟩

end WadlerFest
