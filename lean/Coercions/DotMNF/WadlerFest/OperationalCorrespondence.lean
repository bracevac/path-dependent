import Coercions.DotMNF.WadlerFest.MachineBehavior
import Coercions.DotMNF.WadlerFest.WellFormed
import Coercions.DotMNF.WadlerFest.Readback

/-!
# Operational correspondence for retained lets

Retained-let reduction and the continuation machine have different
administrative steps. Readback interprets every machine transition by a
finite retained-let reduction. In the other direction, a retained-let step
preserves machine behavior backwards in every continuation. Reassociation
uses continuation fusion; value-body reduction uses allocation followed by
evaluation under the extended store.

Together these facts give finite-answer correspondence and transfer the
machine's no-stuck theorem to the independently defined term reduction.
The only source invariant required by the operational argument is label
distinctness, which reconciles field membership with deterministic lookup.
-/

namespace WadlerFest

open FCdot (Sig BVar Rename)

namespace Retained

/-- Every terminating or stuck machine execution of the reduct also gives
such an execution of the original term, in any continuation. -/
theorem Red.behavior_back {σ : Store s} {t u : Tm s}
    (h : Red σ t u) (hσ : σ.Wf) (ht : t.Wf)
    {o : Outcome} (K : Cont s) (hu : Behavior o ⟨σ, K, u⟩) :
    Behavior o ⟨σ, K, t⟩ := by
  induction h with
  | app hl => exact .step (.app hl) hu
  | proj hl hf =>
      rename_i s d a t σ x T
      have hv := hσ.lookup x
      rw [hl] at hv
      cases hv with
      | obj hd => exact .step (.proj hl (hf.lookupTrm hd.distinct)) hu
  | alias => exact .step .let (.step .rename hu)
  | assoc =>
      have hb := Behavior.let_iff.mp hu
      exact .step .let (.step .let (Cont.Fuses.behavior_back .fuse hb))
  | letRHS _ ih =>
      cases ht with
      | «let» ht _ =>
          exact .step .let (ih hσ ht _ (Behavior.let_iff.mp hu))
  | letValue h ih =>
      cases ht with
      | «let» hv ht =>
          cases hv with
          | val hv =>
              have hb := Behavior.alloc_iff.mp (Behavior.let_iff.mp hu)
              exact .step .let (.step .alloc (ih (.cons hσ hv) ht _ hb))

theorem Steps.behavior_back {σ : Store s} {t u : Tm s}
    (h : Steps σ t u) (hσ : σ.Wf) (ht : t.Wf)
    {o : Outcome} (K : Cont s) (hu : Behavior o ⟨σ, K, u⟩) :
    Behavior o ⟨σ, K, t⟩ := by
  induction h with
  | refl => exact hu
  | tail hs h ih => exact ih (h.behavior_back hσ (hs.wf hσ ht) K hu)

/-- A retained-let answer finishes after administrative machine steps. -/
theorem Answer.behavior {σ : Store s} {t : Tm s} (h : Answer t) :
    Behavior (.answer (σ.close t)) ⟨σ, .nil, t⟩ := by
  induction h with
  | path => exact .answer ⟨rfl, .inr ⟨_, rfl⟩⟩ rfl
  | val => exact .answer ⟨rfl, .inl ⟨_, rfl⟩⟩ rfl
  | letValue h ih =>
      rename_i v
      exact .step .let (.step .alloc (ih (σ := .cons σ v)))

private theorem blocked_app {σ : Store s} {K : Cont s} {x y : BVar s .var}
    (hn : ¬ ∃ u, Red σ (.app x y) u) :
    (⟨σ, K, .app x y⟩ : State s).Stuck := by
  constructor
  · rintro ⟨_, hf⟩
    rcases hf with ⟨v, hv⟩ | ⟨p, hp⟩
    · cases hv
    · cases hp
  · rintro ⟨s', st', hs⟩
    cases hs with
    | app hl => exact hn ⟨_, .app hl⟩

private theorem blocked_proj {σ : Store s} {K : Cont s} {x : BVar s .var}
    (hn : ¬ ∃ u, Red σ (.proj x a) u) :
    (⟨σ, K, .proj x a⟩ : State s).Stuck := by
  constructor
  · rintro ⟨_, hf⟩
    rcases hf with ⟨v, hv⟩ | ⟨p, hp⟩
    · cases hv
    · cases hp
  · rintro ⟨s', st', hs⟩
    cases hs with
    | proj hl hd => exact hn ⟨_, .proj hl (Defs.lookupTrm_hasField hd)⟩

/-- A stuck retained-let term yields a finite stuck machine execution.
This direction does not require distinct definitions. -/
theorem Stuck.behavior {σ : Store s} {t : Tm s} (h : Stuck σ t) (K : Cont s) :
    Behavior .stuck ⟨σ, K, t⟩ := by
  obtain ⟨ha, hr⟩ := h
  match t with
  | .path _ => exact False.elim (ha .path)
  | .val _ => exact False.elim (ha .val)
  | .app _ _ => exact .stuck (blocked_app hr)
  | .proj _ _ => exact .stuck (blocked_proj hr)
  | .let (.path (.var y)) u => exact False.elim (hr ⟨_, .alias⟩)
  | .let (.val v) u =>
      have hu : Stuck (.cons σ v) u :=
        ⟨fun h => ha (.letValue h), fun ⟨u', h⟩ => hr ⟨_, .letValue h⟩⟩
      exact .step .let (.step .alloc (hu.behavior K.weaken))
  | .let (.app x y) u =>
      have hn : ¬ ∃ t', Red σ (.app x y) t' :=
        fun ⟨t', h⟩ => hr ⟨_, .letRHS h⟩
      exact .step .let (.stuck (blocked_app hn))
  | .let (.proj x a) u =>
      have hn : ¬ ∃ t', Red σ (.proj x a) t' :=
        fun ⟨t', h⟩ => hr ⟨_, .letRHS h⟩
      exact .step .let (.stuck (blocked_proj hn))
  | .let (.let _ _) _ => exact False.elim (hr ⟨_, .assoc⟩)

/-- Exact finite-answer correspondence. A retained-let answer is reached
precisely when a final machine state reads back to that same annotated term. -/
theorem answer_iff_machine {t u : Tm []} (ht : t.Wf) (hu : Answer u) :
    Steps .nil t u ↔
      ∃ (s : Sig) (st : State s),
        WadlerFest.Steps (⟨.nil, .nil, t⟩ : State []) st ∧
          st.Final ∧ st.readback = u := by
  constructor
  · intro hr
    exact (hr.behavior_back .nil ht .nil hu.behavior).answer_run
  · rintro ⟨s, st, hr, _, he⟩
    simpa only [State.readback, Cont.plug, Store.close] using he ▸ hr.readback

/-- Finite stuckness agrees between the two semantics. Pending machine
frames may require reassociation before their readback is itself stuck. -/
theorem stuck_iff_machine {t : Tm []} (ht : t.Wf) :
    (∃ u, Steps .nil t u ∧ Stuck .nil u) ↔
      ∃ (s : Sig) (st : State s),
        WadlerFest.Steps (⟨.nil, .nil, t⟩ : State []) st ∧ st.Stuck := by
  constructor
  · rintro ⟨u, hr, hs⟩
    exact (hr.behavior_back .nil ht .nil (hs.behavior .nil)).stuck_run
  · rintro ⟨s, st, hr, hs⟩
    obtain ⟨u, hu, hs⟩ := hs.readback
    exact ⟨u, hr.readback.trans hu, hs⟩

end Retained

end WadlerFest
