import Coercions.DotMNF.WadlerFest.Reduction

/-!
# Reading machine states back into retained lets

A continuation supplies the pending let contexts, and the store supplies
their enclosing value bindings. Machine steps become finite retained-let
reductions: pushing a frame changes no term, while allocation reassociates
the newly retained value binding across the remaining continuation.
-/

namespace WadlerFest

open FCdot (Sig BVar Rename Label)

/-- Fill the pending right-hand-side contexts from the innermost frame out. -/
def Cont.plug : Cont s → Tm s → Tm s
  | .nil, t => t
  | .cons K u, t => K.plug (.let t u)

/-- Turn the store into the enclosing retained value bindings. -/
def Store.close : (σ : Store s) → Tm s → Tm []
  | .nil, t => t
  | .cons σ v, t => σ.close (.let (.val v) t)

/-- The closed retained-let term represented by a machine state. -/
def State.readback (st : State s) : Tm [] := st.σ.close (st.K.plug st.t)

/-- Deterministic lookup always selects an occurring definition. No label
disjointness assumption is required in this direction. -/
theorem Defs.lookupTrm_hasField {d : Defs s}
    (h : d.lookupTrm a = some t) : d.HasField a t := by
  cases d with
  | typ => simp [lookupTrm] at h
  | trm b u =>
      simp only [lookupTrm] at h
      split at h
      next heq =>
        cases heq
        cases h
        exact .trm
      next => contradiction
  | and d₁ d₂ =>
      cases h₂ : d₂.lookupTrm a with
      | none =>
          apply Defs.HasField.andLeft
          apply lookupTrm_hasField
          simpa [lookupTrm, h₂] using h
      | some u =>
          have heq : u = t := by simpa [lookupTrm, h₂] using h
          cases heq
          exact .andRight (lookupTrm_hasField h₂)

/-- An occurring field guarantees that lookup finds some field, even when
several definitions share its label. -/
theorem Defs.HasField.lookupTrm_some {d : Defs s} (h : d.HasField a t) :
    ∃ u, d.lookupTrm a = some u := by
  induction h with
  | @trm a t => exact ⟨t, by simp [Defs.lookupTrm]⟩
  | @andLeft d₁ a t d₂ _ ih =>
      cases h₂ : d₂.lookupTrm a with
      | none =>
          obtain ⟨u, hu⟩ := ih
          exact ⟨u, by simp [Defs.lookupTrm, h₂, hu]⟩
      | some u => exact ⟨u, by simp [Defs.lookupTrm, h₂]⟩
  | andRight _ ih =>
      obtain ⟨u, hu⟩ := ih
      exact ⟨u, by simp [Defs.lookupTrm, hu]⟩

namespace Retained

/-- A continuation is an iterated right-hand-side evaluation context. -/
theorem Red.plug {σ : Store s} {t t' : Tm s}
    (h : Red σ t t') (K : Cont s) :
    Red σ (K.plug t) (K.plug t') := by
  induction K generalizing t t' with
  | nil => exact h
  | cons K u ih => exact ih (.letRHS h)

theorem Steps.plug {σ : Store s} {t t' : Tm s}
    (h : Steps σ t t') (K : Cont s) :
    Steps σ (K.plug t) (K.plug t') := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (h.plug K)

/-- Closing the ambient store retains each binding around the reduction. -/
theorem Red.close {σ : Store s} (h : Red σ t t') :
    Red .nil (σ.close t) (σ.close t') := by
  induction σ with
  | nil => exact h
  | cons σ v ih => exact ih (.letValue h)

theorem Steps.close {σ : Store s} (h : Steps σ t t') :
    Steps .nil (σ.close t) (σ.close t') := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih h.close

theorem Answer.close {t : Tm s} (h : Answer t) (σ : Store s) :
    Answer (σ.close t) := by
  induction σ with
  | nil => exact h
  | cons σ v ih => exact ih (.letValue h)

/-- Enclosing a stuck term in its ambient value bindings preserves stuckness. -/
theorem Stuck.close {σ : Store s} {t : Tm s} (h : Stuck σ t) :
    Stuck .nil (σ.close t) := by
  induction σ with
  | nil => exact h
  | cons σ v ih =>
      apply ih
      constructor
      · intro ha
        cases ha with
        | letValue ha => exact h.1 ha
      · rintro ⟨u, hr⟩
        cases hr with
        | letRHS hr => cases hr
        | letValue hr => exact h.2 ⟨_, hr⟩

end Retained

/-- Move a let binding outward through the continuation. Each pending frame
contributes one retained-let reassociation. -/
theorem Cont.plug_let (K : Cont s) (σ : Store s) (t : Tm s)
    (u : Tm (s,x)) :
    Retained.Steps σ (K.plug (.let t u))
      (.let t (K.weaken.plug u)) := by
  induction K generalizing u with
  | nil => exact .refl
  | cons K w ih =>
      exact (Retained.Steps.single (Retained.Red.assoc.plug K)).trans
        (ih (.let u (w.rename Rename.succ.lift)))

/-- Allocation retains the new value binding around the remaining frames. -/
theorem Cont.plug_alloc (K : Cont s) (σ : Store s) (v : Value s)
    (u : Tm (s,x)) :
    Retained.Steps σ (K.plug (.let (.val v) u))
      (.let (.val v) (K.weaken.plug u)) := K.plug_let σ (.val v) u

/-- Reassociate pending frames so the current term is the outermost RHS. -/
def Cont.focus : Cont s → Tm s → Tm s
  | .nil, t => t
  | .cons K u, t => .let t (K.weaken.plug u)

theorem Cont.plug_focus (K : Cont s) (σ : Store s) (t : Tm s) :
    Retained.Steps σ (K.plug t) (K.focus t) := by
  cases K with
  | nil => exact .refl
  | cons K u => exact K.plug_let σ t u

/-- One machine transition is represented by finitely many retained-let
steps, including zero steps for pushing a continuation frame. -/
theorem Step.readback (h : Step st st') :
    Retained.Steps .nil st.readback st'.readback := by
  cases h with
  | «let» => exact .refl
  | alloc => exact (Cont.plug_alloc _ _ _ _).close
  | rename => exact (Retained.Steps.single (Retained.Red.alias.plug _)).close
  | app hx => exact (Retained.Steps.single ((Retained.Red.app hx).plug _)).close
  | proj hx hd =>
      exact (Retained.Steps.single
        ((Retained.Red.proj hx (Defs.lookupTrm_hasField hd)).plug _)).close

/-- Finite machine evaluation preserves its retained-let reading. -/
theorem Steps.readback (h : Steps st st') :
    Retained.Steps .nil st.readback st'.readback := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.trans h.readback

/-- Reading back a final machine state yields a retained-let answer. -/
theorem State.Final.readback {st : State s} (h : st.Final) :
    Retained.Answer st.readback := by
  rcases st with ⟨σ, K, t⟩
  rcases h with ⟨rfl, (⟨v, rfl⟩ | ⟨p, rfl⟩)⟩
  · exact Retained.Answer.val.close σ
  · exact Retained.Answer.path.close σ

/-- A stuck machine focus is a blocked application or projection. Once its
pending frames are reassociated, the retained-let term is stuck as well. -/
theorem State.Stuck.focus {σ : Store s} {K : Cont s} {t : Tm s}
    (h : State.Stuck ⟨σ, K, t⟩) : Retained.Stuck σ (K.focus t) := by
  rcases h with ⟨hnf, hstep⟩
  cases t with
  | path p =>
      cases K with
      | nil => exact False.elim (hnf ⟨rfl, .inr ⟨p, rfl⟩⟩)
      | cons K u =>
          cases p with
          | var y => exact False.elim (hstep ⟨_, _, .rename⟩)
  | val v =>
      cases K with
      | nil => exact False.elim (hnf ⟨rfl, .inl ⟨v, rfl⟩⟩)
      | cons K u => exact False.elim (hstep ⟨_, _, .alloc⟩)
  | «let» t u => exact False.elim (hstep ⟨_, _, .let⟩)
  | app x y =>
      have hr : ¬ ∃ u, Retained.Red σ (.app x y) u := by
        rintro ⟨u, hu⟩
        cases hu with
        | app hx => exact hstep ⟨_, _, .app hx⟩
      cases K with
      | nil =>
          constructor
          · intro ha; cases ha
          · exact hr
      | cons K u =>
          constructor
          · intro ha; cases ha
          · rintro ⟨u', hu⟩
            cases hu with
            | letRHS hu => exact hr ⟨_, hu⟩
  | proj x a =>
      have hr : ¬ ∃ u, Retained.Red σ (.proj x a) u := by
        rintro ⟨u, hu⟩
        cases hu with
        | proj hx hd =>
            obtain ⟨t', ht'⟩ := hd.lookupTrm_some
            exact hstep ⟨_, _, .proj hx ht'⟩
      cases K with
      | nil =>
          constructor
          · intro ha; cases ha
          · exact hr
      | cons K u =>
          constructor
          · intro ha; cases ha
          · rintro ⟨u', hu⟩
            cases hu with
            | letRHS hu => exact hr ⟨_, hu⟩

/-- A stuck state reads back to a term that reduces to a retained-let stuck
term. The intervening steps only reassociate pending continuation frames. -/
theorem State.Stuck.readback {st : State s} (h : st.Stuck) :
    ∃ u, Retained.Steps .nil st.readback u ∧ Retained.Stuck .nil u := by
  exact ⟨st.σ.close (st.K.focus st.t),
    (st.K.plug_focus st.σ st.t).close, h.focus.close⟩

end WadlerFest
