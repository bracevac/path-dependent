import Coercions.DotMNF.WadlerFest.Renaming
import Coercions.DotMNF.WadlerFest.Readback

/-!
# Finite machine behavior and continuation fusion

Finite behavior records termination at an exact retained-let answer or at a stuck state. The
fusion lemma compares two administrative representations of the same nested
let: two continuation frames, or one frame whose body contains a let.
-/

namespace WadlerFest

open FCdot (Sig BVar Rename)

inductive Outcome where
  | answer : Tm [] → Outcome
  | stuck

inductive Behavior : Outcome → {s : Sig} → State s → Prop where
  | answer : st.Final → st.readback = result → Behavior (.answer result) st
  | stuck : st.Stuck → Behavior .stuck st
  | step : Step st st' → Behavior o st' → Behavior o st

def Outcome.Holds (o : Outcome) (st : State s) : Prop :=
  match o with
  | .answer result => st.Final ∧ st.readback = result
  | .stuck => st.Stuck

theorem Steps.prepend (h : Step st st') (hs : Steps st' st'') : Steps st st'' := by
  induction hs with
  | refl => exact .tail .refl h
  | tail _ hs ih => exact .tail (ih h) hs

theorem Behavior.run (h : Behavior o st) :
    ∃ s', ∃ st' : State s', Steps st st' ∧ o.Holds st' := by
  induction h with
  | answer hf he => exact ⟨_, _, .refl, hf, he⟩
  | stuck hs => exact ⟨_, _, .refl, hs⟩
  | step hs _ ih =>
      obtain ⟨s', st', hr, ht⟩ := ih
      exact ⟨s', st', hr.prepend hs, ht⟩

theorem Behavior.stuck_run (h : Behavior .stuck st) :
    ∃ s', ∃ st' : State s', Steps st st' ∧ st'.Stuck := h.run

theorem Behavior.answer_run (h : Behavior (.answer result) st) :
    ∃ s', ∃ st' : State s', Steps st st' ∧ st'.Final ∧ st'.readback = result := h.run

theorem Behavior.from_steps (hs : Steps st st') (hb : Behavior o st') :
    Behavior o st := by
  induction hs with
  | refl => exact hb
  | tail _ hs ih => exact ih (.step hs hb)

theorem Behavior.from_run {o : Outcome} (hs : Steps st st') (ht : o.Holds st') : Behavior o st := by
  cases o with
  | answer _ => exact Behavior.from_steps hs (.answer ht.1 ht.2)
  | stuck => exact Behavior.from_steps hs (.stuck ht)

theorem Behavior.let_inv (h : Behavior o (⟨σ, K, .let t u⟩ : State s)) :
    Behavior o ⟨σ, .cons K u, t⟩ := by
  cases h with
  | answer hf _ =>
      obtain ⟨_, hv | hp⟩ := hf
      · obtain ⟨v, hv⟩ := hv; cases hv
      · obtain ⟨p, hp⟩ := hp; cases hp
  | stuck hs => exact False.elim (hs.2 ⟨_, _, .let⟩)
  | step hs hb => cases hs; exact hb

theorem Behavior.let_iff :
    Behavior o (⟨σ, K, .let t u⟩ : State s) ↔ Behavior o ⟨σ, .cons K u, t⟩ :=
  ⟨Behavior.let_inv, fun h => .step .let h⟩

theorem Behavior.alloc_inv (h : Behavior o (⟨σ, .cons K u, .val v⟩ : State s)) :
    Behavior o ⟨.cons σ v, K.weaken, u⟩ := by
  cases h with
  | answer hf _ => cases hf.1
  | stuck hs => exact False.elim (hs.2 ⟨_, _, .alloc⟩)
  | step hs hb => cases hs; exact hb

theorem Behavior.alloc_iff :
    Behavior o (⟨σ, .cons K u, .val v⟩ : State s) ↔
      Behavior o ⟨.cons σ v, K.weaken, u⟩ :=
  ⟨Behavior.alloc_inv, fun h => .step .alloc h⟩

theorem Behavior.rename_inv (h : Behavior o (⟨σ, .cons K u, .path (.var y)⟩ : State s)) :
    Behavior o ⟨σ, K, u.substVar y⟩ := by
  cases h with
  | answer hf _ => cases hf.1
  | stuck hs => exact False.elim (hs.2 ⟨_, _, .rename⟩)
  | step hs hb => cases hs; exact hb

theorem Behavior.rename_iff :
    Behavior o (⟨σ, .cons K u, .path (.var y)⟩ : State s) ↔
      Behavior o ⟨σ, K, u.substVar y⟩ :=
  ⟨Behavior.rename_inv, fun h => .step .rename h⟩

/-- One pair of consecutive frames is fused, possibly below other frames. -/
inductive Cont.Fuses : Cont s → Cont s → Prop where
  | fuse : Fuses (.cons (.cons K v) u)
      (.cons K (.let u (v.rename Rename.succ.lift)))
  | cons : Fuses K L → Fuses (.cons K w) (.cons L w)

theorem Cont.Fuses.rename {K L : Cont s₁} (h : Fuses K L) (ρ : Rename s₁ s₂) :
    Fuses (K.rename ρ) (L.rename ρ) := by
  induction h with
  | @fuse K₀ v u =>
      simpa only [Cont.rename, Tm.rename, Tm.insertBinder_rename] using
        (Fuses.fuse (K := K₀.rename ρ) (v := v.rename ρ.lift) (u := u.rename ρ.lift))
  | cons _ ih => exact .cons ih

theorem Cont.Fuses.weaken (h : Fuses K L) : Fuses K.weaken L.weaken :=
  h.rename Rename.succ

theorem Cont.Fuses.left_ne_nil (h : Fuses K L) : K ≠ .nil := by
  cases h <;> intro he <;> cases he

theorem Cont.Fuses.right_ne_nil (h : Fuses K L) : L ≠ .nil := by
  cases h <;> intro he <;> cases he

theorem Cont.Fuses.stuck_back {σ : Store s} {K L : Cont s} {t : Tm s} (h : Fuses K L)
    (hs : (⟨σ, L, t⟩ : State s).Stuck) : (⟨σ, K, t⟩ : State s).Stuck := by
  refine ⟨fun hf => h.left_ne_nil hf.1, ?_⟩
  intro ⟨s', st', hr⟩
  cases hr with
  | «let» => exact hs.2 ⟨_, _, .let⟩
  | alloc => cases h <;> exact hs.2 ⟨_, _, .alloc⟩
  | rename => cases h <;> exact hs.2 ⟨_, _, .rename⟩
  | app he => exact hs.2 ⟨_, _, .app he⟩
  | proj hv ht => exact hs.2 ⟨_, _, .proj hv ht⟩

private theorem Behavior.fusion_back {st : State s} (hb : Behavior o st) :
    ∀ K, Cont.Fuses K st.K → Behavior o ⟨st.σ, K, st.t⟩ := by
  induction hb with
  | answer hf _ =>
      intro K hF
      exact False.elim (hF.right_ne_nil hf.1)
  | stuck hs =>
      intro K hF
      exact .stuck (hF.stuck_back hs)
  | step hs hb ih =>
      intro K hF
      cases hs with
      | «let» => exact .step .let (ih _ (.cons hF))
      | app he => exact .step (.app he) (ih _ hF)
      | proj hv ht => exact .step (.proj hv ht) (ih _ hF)
      | alloc =>
          cases hF with
          | fuse => exact .step .alloc hb.let_inv
          | cons hF => exact .step .alloc (ih _ hF.weaken)
      | rename =>
          cases hF with
          | fuse =>
              apply Behavior.step .rename
              apply Behavior.let_inv
              simpa only [Tm.substVar, Tm.rename, Tm.insertBinder_substLift] using hb
          | cons hF => exact .step .rename (ih _ hF)

/-- A fused continuation cannot gain a finite answer or stuck behavior. -/
theorem Cont.Fuses.behavior_back {σ : Store s} {K L : Cont s} {t : Tm s} (h : Fuses K L)
    (hb : Behavior o (⟨σ, L, t⟩ : State s)) : Behavior o ⟨σ, K, t⟩ :=
  hb.fusion_back K h

end WadlerFest
