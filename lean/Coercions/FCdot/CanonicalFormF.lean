import Coercions.FCdot.CanonicalDepth

/-!
# Form typedness with a witness function: monotonicity
-/

namespace FCdot

section
variable (σ : Store s) (Γ : Ctx s)

/-- Downward closure in the depth, with the same witness function. -/
theorem FormTypedF_mono {f : Atom s → View s → Nat × Nat} {k k' : Nat} {F : Form s} {S T : Ty s}
    (hk : k' ≤ k) (h : FormTypedF σ Γ f k F S T) : FormTypedF σ Γ f k' F S T := by
  cases F with
  | obj cs =>
      cases k' with
      | zero =>
          rw [FormTypedF_zero σ Γ]
          exact FormTyped_mono (Nat.zero_le _) h.toFormTyped
      | succ j' =>
          cases k with
          | zero => omega
          | succ j =>
              simp only [FormTypedF] at h ⊢
              obtain ⟨Tel₁, Tel₂, h₁, h₂, hc, hcl⟩ := h
              exact ⟨Tel₁, Tel₂, h₁, h₂, hc, fun a ha V j'' ht hj => hcl a ha V j'' ht (by omega)⟩
  | bot => rw [FormTypedF_nonObj σ Γ (by intro cs h; cases h)] at h ⊢; exact FormTyped_mono hk h
  | top => rw [FormTypedF_nonObj σ Γ (by intro cs h; cases h)] at h ⊢; exact FormTyped_mono hk h
  | id => rw [FormTypedF_nonObj σ Γ (by intro cs h; cases h)] at h ⊢; exact FormTyped_mono hk h
  | eqv φ => rw [FormTypedF_nonObj σ Γ (by intro cs h; cases h)] at h ⊢; exact FormTyped_mono hk h
  | pi d c => rw [FormTypedF_nonObj σ Γ (by intro cs h; cases h)] at h ⊢; exact FormTyped_mono hk h

end

end FCdot
