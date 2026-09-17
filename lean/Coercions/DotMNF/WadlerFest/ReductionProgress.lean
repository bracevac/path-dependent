import Coercions.DotMNF.WadlerFest.WellFormed
import Coercions.DotMNF.WadlerFest.Readback

/-!
# Constructive decomposition of retained-let terms

Every term is an answer, takes a step, or is stuck. This is a syntactic
decomposition for arbitrary stores and terms, independent of typing or
distinct labels. Although duplicate fields may make reduction ambiguous,
lookup finds a field exactly when some field occurs.
-/

namespace WadlerFest

open FCdot (Sig BVar Label)

theorem Defs.lookupTrm_none_iff (d : Defs s) (a : Label) :
    d.lookupTrm a = none ↔ ¬ ∃ t, d.HasField a t := by
  constructor
  · intro hn ⟨t, ht⟩
    obtain ⟨u, hu⟩ := ht.lookupTrm_some
    rw [hn] at hu
    cases hu
  · intro hn
    cases h : d.lookupTrm a with
    | none => rfl
    | some t => exact False.elim (hn ⟨t, Defs.lookupTrm_hasField h⟩)

namespace Retained

theorem app_step_or_stuck (σ : Store s) (x y : BVar s .var) :
    (∃ u, Red σ (.app x y) u) ∨ Stuck σ (.app x y) := by
  cases hv : σ.lookup x with
  | lam S t => exact .inl ⟨_, .app hv⟩
  | obj T d =>
      apply Or.inr
      constructor
      · intro ha; cases ha
      · intro ⟨u, hr⟩
        cases hr with
        | app hl => rw [hv] at hl; cases hl

theorem proj_step_or_stuck (σ : Store s) (x : BVar s .var) (a : Label) :
    (∃ u, Red σ (.proj x a) u) ∨ Stuck σ (.proj x a) := by
  cases hv : σ.lookup x with
  | lam S t =>
      apply Or.inr
      constructor
      · intro ha; cases ha
      · intro ⟨u, hr⟩
        cases hr with
        | proj hl _ => rw [hv] at hl; cases hl
  | obj T d =>
      cases hd : d.lookupTrm a with
      | some t => exact .inl ⟨_, .proj hv (Defs.lookupTrm_hasField hd)⟩
      | none =>
          apply Or.inr
          constructor
          · intro ha; cases ha
          · intro ⟨u, hr⟩
            cases hr with
            | proj hl hf =>
                rw [hv] at hl
                cases hl
                exact (Defs.lookupTrm_none_iff d a).mp hd ⟨_, hf⟩

theorem Stuck.letValue (h : Stuck (.cons σ v) t) : Stuck σ (.let (.val v) t) := by
  constructor
  · intro ha
    cases ha with
    | letValue ha => exact h.1 ha
  · intro ⟨u, hr⟩
    cases hr with
    | letRHS hr => cases hr
    | letValue hr => exact h.2 ⟨_, hr⟩

theorem Stuck.letApp {σ : Store s} {x y : BVar s .var}
    (h : Stuck σ (.app x y)) (u : Tm (s,x)) :
    Stuck σ (.let (.app x y) u) := by
  constructor
  · intro ha; cases ha
  · intro ⟨u, hr⟩
    cases hr with
    | letRHS hr => exact h.2 ⟨_, hr⟩

theorem Stuck.letProj {σ : Store s} {x : BVar s .var} {a : Label}
    (h : Stuck σ (.proj x a)) (u : Tm (s,x)) :
    Stuck σ (.let (.proj x a) u) := by
  constructor
  · intro ha; cases ha
  · intro ⟨u, hr⟩
    cases hr with
    | letRHS hr => exact h.2 ⟨_, hr⟩

/-- Syntactic decomposition; this theorem uses no classical choice. -/
theorem trichotomy : ∀ {s : Sig} (σ : Store s) (t : Tm s),
    Answer t ∨ (∃ u, Red σ t u) ∨ Stuck σ t
  | _, _, .path _ => .inl .path
  | _, _, .val _ => .inl .val
  | _, σ, .app x y => .inr (app_step_or_stuck σ x y)
  | _, σ, .proj x a => .inr (proj_step_or_stuck σ x a)
  | _, _, .let (.path (.var _)) _ => .inr (.inl ⟨_, .alias⟩)
  | _, σ, .let (.val v) t => by
      rcases trichotomy (.cons σ v) t with ha | ⟨u, hr⟩ | hs
      · exact .inl (.letValue ha)
      · exact .inr (.inl ⟨_, .letValue hr⟩)
      · exact .inr (.inr hs.letValue)
  | _, _, .let (.let _ _) _ => .inr (.inl ⟨_, .assoc⟩)
  | _, σ, .let (.app x y) u => by
      rcases app_step_or_stuck σ x y with ⟨t, hr⟩ | hs
      · exact .inr (.inl ⟨_, .letRHS hr⟩)
      · exact .inr (.inr (hs.letApp u))
  | _, σ, .let (.proj x a) u => by
      rcases proj_step_or_stuck σ x a with ⟨t, hr⟩ | hs
      · exact .inr (.inl ⟨_, .letRHS hr⟩)
      · exact .inr (.inr (hs.letProj u))

end Retained
end WadlerFest
