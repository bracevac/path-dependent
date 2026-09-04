import Coercions.FCdot.Canonical

/-!
# Fuel monotonicity and determinism of the normalizer

Every function of the normalizer is monotone in its fuel: a result at fuel
`n` is the result at every larger fuel.  Hence two successful runs agree.
-/

namespace FCdot

section
variable (σ : Store s)

theorem normalizer_succ : ∀ n : Nat,
    (∀ (e : LeCo s) (F : Form s), hnf σ n e = some F → hnf σ (n + 1) e = some F) ∧
    (∀ (m : Morphism s) (Es : List (Entry s)), entries σ n m = some Es → entries σ (n + 1) m = some Es) ∧
    (∀ (a : Atom s) (V : View s), view σ n a = some V → view σ (n + 1) a = some V) ∧
    (∀ (F : Form s) (a : Atom s) (V : View s),
      viewThrough σ n F a = some V → viewThrough σ (n + 1) F a = some V) ∧
    (∀ (x : BVar s .var) (h : Has s) (p : BVar s .var × Label),
      hasView σ n x h = some p → hasView σ (n + 1) x h = some p)
  | 0 => by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro e F h; rw [hnf] at h; cases h
      · intro m Es h; rw [entries] at h; cases h
      · intro a V h; rw [view] at h; cases h
      · intro F a V h; rw [viewThrough] at h; cases h
      · intro x hh p h; rw [hasView] at h; cases h
  | n + 1 => by
      obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := normalizer_succ n
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro e F h
        cases e with
        | refl T => rw [hnf] at h; rw [hnf]; exact h
        | top T => rw [hnf] at h; rw [hnf]; exact h
        | bot T => rw [hnf] at h; rw [hnf]; exact h
        | eqToLe φ => rw [hnf] at h; rw [hnf]; exact h
        | pi d c => rw [hnf] at h; rw [hnf]; exact h
        | obj Tel m =>
            cases hm : entries σ n m with
            | none => simp [hnf, hm] at h
            | some Es => simpa [hnf, hm, ih2 m Es hm] using h
        | trans e f =>
            cases he : hnf σ n e with
            | none => simp [hnf, he] at h
            | some F₁ =>
                cases hf : hnf σ n f with
                | none => simp [hnf, he, hf] at h
                | some G => simpa [hnf, he, hf, ih1 e F₁ he, ih1 f G hf] using h
        | member a e i =>
            cases he : hnf σ n e with
            | none => simp [hnf, he] at h
            | some F₁ =>
                cases hv : viewThrough σ n F₁ a with
                | none => simp [hnf, he, hv] at h
                | some V => simpa [hnf, he, hv, ih1 e F₁ he, ih4 F₁ a V hv] using h
      · intro m Es h
        cases m with
        | nil => rw [entries] at h; rw [entries]; exact h
        | le m e =>
            cases hm : entries σ n m with
            | none => simp [entries, hm] at h
            | some Es₀ =>
                cases he : hnf σ n e with
                | none => simp [entries, hm, he] at h
                | some F => simpa [entries, hm, he, ih2 m Es₀ hm, ih1 e F he] using h
        | eq m φ =>
            cases hm : entries σ n m with
            | none => simp [entries, hm] at h
            | some Es₀ => simpa [entries, hm, ih2 m Es₀ hm] using h
        | has m j =>
            cases hm : entries σ n m with
            | none => simp [entries, hm] at h
            | some Es₀ => simpa [entries, hm, ih2 m Es₀ hm] using h
      · intro a V h
        cases a with
        | var x => rw [view] at h; rw [view]; exact h
        | cast a e =>
            cases he : hnf σ n e with
            | none => simp [view, he] at h
            | some F => simpa [view, he, ih1 e F he, ih4 F a V (by simpa [view, he] using h)] using h
        | foldSelf Tel a => simp only [view] at h ⊢; exact ih3 a V h
        | unfoldSelf a => simp only [view] at h ⊢; exact ih3 a V h
      · intro F a V h
        cases F with
        | id => simp only [viewThrough] at h ⊢; exact ih3 a V h
        | eqv φ => simp only [viewThrough] at h ⊢; exact ih3 a V h
        | obj Es =>
            cases hv : view σ n a with
            | none => simp [viewThrough, hv] at h
            | some V₀ => simpa [viewThrough, hv, ih3 a V₀ hv] using h
        | pi d c => rw [viewThrough] at h; rw [viewThrough]; exact h
        | top => rw [viewThrough] at h; rw [viewThrough]; exact h
        | bot => rw [viewThrough] at h; rw [viewThrough]; exact h
      · intro x hh p hp
        cases hh with
        | field ℓ => rw [hasView] at hp; rw [hasView]; exact hp
        | member a e i =>
            cases he : hnf σ n e with
            | none => simp [hasView, he] at hp
            | some F =>
                cases hv : viewThrough σ n F a with
                | none => simp [hasView, he, hv] at hp
                | some V => simpa [hasView, he, hv, ih1 e F he, ih4 F a V hv] using hp

variable {σ}

theorem hnf_le {n n' : Nat} {e : LeCo s} {F : Form s} (h : n ≤ n') (hF : hnf σ n e = some F) :
    hnf σ n' e = some F := by
  induction h with
  | refl => exact hF
  | step _ ih => exact (normalizer_succ σ _).1 e F ih

theorem entries_le {n n' : Nat} {m : Morphism s} {Es : List (Entry s)} (h : n ≤ n')
    (hE : entries σ n m = some Es) : entries σ n' m = some Es := by
  induction h with
  | refl => exact hE
  | step _ ih => exact (normalizer_succ σ _).2.1 m Es ih

theorem view_le {n n' : Nat} {a : Atom s} {V : View s} (h : n ≤ n') (hV : view σ n a = some V) :
    view σ n' a = some V := by
  induction h with
  | refl => exact hV
  | step _ ih => exact (normalizer_succ σ _).2.2.1 a V ih

theorem viewThrough_le {n n' : Nat} {F : Form s} {a : Atom s} {V : View s} (h : n ≤ n')
    (hV : viewThrough σ n F a = some V) : viewThrough σ n' F a = some V := by
  induction h with
  | refl => exact hV
  | step _ ih => exact (normalizer_succ σ _).2.2.2.1 F a V ih

theorem hasView_le {n n' : Nat} {x : BVar s .var} {hh : Has s} {p : BVar s .var × Label}
    (h : n ≤ n') (hp : hasView σ n x hh = some p) : hasView σ n' x hh = some p := by
  induction h with
  | refl => exact hp
  | step _ ih => exact (normalizer_succ σ _).2.2.2.2 x hh p ih

theorem closedAtomForm_succ : ∀ (n : Nat) (a : Atom s) (r : Atom s × Form s),
    closedAtomForm σ n a = some r → closedAtomForm σ (n + 1) a = some r
  | 0, _, _, h => by simp [closedAtomForm] at h
  | n + 1, a, r, h => by
      cases a with
      | var x => rw [closedAtomForm] at h; rw [closedAtomForm]; exact h
      | cast a e =>
          cases hc : closedAtomForm σ n a with
          | none => simp [closedAtomForm, hc] at h
          | some p =>
              obtain ⟨a', F⟩ := p
              cases he : hnf σ n e with
              | none => simp [closedAtomForm, hc, he] at h
              | some G =>
                  simpa [closedAtomForm, hc, he, closedAtomForm_succ n a _ hc,
                    hnf_le (Nat.le_succ n) he] using h
      | foldSelf Tel a =>
          cases hc : closedAtomForm σ n a with
          | none => simp [closedAtomForm, hc] at h
          | some p =>
              obtain ⟨a', F⟩ := p
              simpa [closedAtomForm, hc, closedAtomForm_succ n a _ hc] using h
      | unfoldSelf a =>
          cases hc : closedAtomForm σ n a with
          | none => simp [closedAtomForm, hc] at h
          | some p =>
              obtain ⟨a', F⟩ := p
              simpa [closedAtomForm, hc, closedAtomForm_succ n a _ hc] using h

theorem closedAtomForm_le {n n' : Nat} {a : Atom s} {r : Atom s × Form s} (h : n ≤ n')
    (hr : closedAtomForm σ n a = some r) : closedAtomForm σ n' a = some r := by
  induction h with
  | refl => exact hr
  | step _ ih => exact closedAtomForm_succ _ a r ih

/-! ## Determinism -/

theorem hnf_det {n₁ n₂ : Nat} {e : LeCo s} {F₁ F₂ : Form s}
    (h₁ : hnf σ n₁ e = some F₁) (h₂ : hnf σ n₂ e = some F₂) : F₁ = F₂ :=
  Option.some.inj ((hnf_le (Nat.le_max_left n₁ n₂) h₁).symm.trans (hnf_le (Nat.le_max_right n₁ n₂) h₂))

theorem view_det {n₁ n₂ : Nat} {a : Atom s} {V₁ V₂ : View s}
    (h₁ : view σ n₁ a = some V₁) (h₂ : view σ n₂ a = some V₂) : V₁ = V₂ :=
  Option.some.inj ((view_le (Nat.le_max_left n₁ n₂) h₁).symm.trans (view_le (Nat.le_max_right n₁ n₂) h₂))

theorem closedAtomForm_det {n₁ n₂ : Nat} {a : Atom s} {r₁ r₂ : Atom s × Form s}
    (h₁ : closedAtomForm σ n₁ a = some r₁) (h₂ : closedAtomForm σ n₂ a = some r₂) : r₁ = r₂ :=
  Option.some.inj ((closedAtomForm_le (Nat.le_max_left n₁ n₂) h₁).symm.trans
    (closedAtomForm_le (Nat.le_max_right n₁ n₂) h₂))

end

end FCdot
