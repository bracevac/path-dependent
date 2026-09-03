import Coercions.FCdot.CanonicalCombine
import Coercions.FCdot.CanonicalFormF

/-!
# Composition with a witness function

`Form.fcomb` combines the per-input threshold/loss functions of two forms
into one for their composite.  For two object chains the second chain's
witness is evaluated at the first chain's output, which is chosen
classically; typedness of the composite follows the proof of
`Form.combine_typed` with the witnesses made explicit.
-/

namespace FCdot

section

variable {σ : Store s} {Γ : Ctx s}

open Classical in
/-- Witness function of a composite form. -/
noncomputable def Form.fcomb (σ : Store s) : Form s → Form s →
    (Atom s → View s → Nat × Nat) → (Atom s → View s → Nat × Nat) → Atom s → View s → Nat × Nat
  | .id, _, _, f₂ => f₂
  | _, .id, f₁, _ => f₁
  | .eqv φ, .obj _, _, f₂ => fun a V => f₂ (.cast a (.eqToLe φ)) V
  | .obj _, .eqv _, f₁, _ => f₁
  | .obj cs₁, .obj _, f₁, f₂ => fun a V =>
      if h : ∃ n V₁, applyChain σ n cs₁ a V = some V₁ then
        let V₁ := Classical.choose (Classical.choose_spec h)
        (max (f₁ a V).1 ((f₂ (ChainStep.chainAtom cs₁ a) V₁).1 + (f₁ a V).2),
          (f₁ a V).2 + (f₂ (ChainStep.chainAtom cs₁ a) V₁).2)
      else f₁ a V
  | _, _, f₁, _ => f₁

theorem combine_typedF_of_nonObj {f₁ f₂ f : Atom s → View s → Nat × Nat} {k : Nat}
    {F G : Form s} {S M T : Ty s}
    (hne : ∀ cs, F.combine G ≠ .obj cs)
    (hF : FormTypedF σ Γ f₁ k F S M) (hG : FormTypedF σ Γ f₂ k G M T) :
    FormTypedF σ Γ f k (F.combine G) S T :=
  (FormTypedF_nonObj σ Γ hne).mpr (Form.combine_typed hF.toFormTyped hG.toFormTyped)

/-- Composition of head forms with an explicit witness function. -/
theorem Form.combine_typedF {f₁ f₂ : Atom s → View s → Nat × Nat} {k : Nat} {F G : Form s}
    {S M T : Ty s}
    (hF : FormTypedF σ Γ f₁ k F S M) (hG : FormTypedF σ Γ f₂ k G M T) :
    FormTypedF σ Γ (Form.fcomb σ F G f₁ f₂) k (F.combine G) S T := by
  cases k with
  | zero =>
      rw [FormTypedF_zero σ Γ]
      exact Form.combine_typed hF.toFormTyped hG.toFormTyped
  | succ j =>
  cases F with
  | id =>
      have hSM : S = M := (FormTyped_id σ Γ).mp ((FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp hF)
      subst hSM
      rw [Form.combine_id_left]
      cases G <;> simpa [Form.fcomb] using hG
  | bot => exact combine_typedF_of_nonObj (by intro cs; cases G <;> simp [Form.combine]) hF hG
  | top =>
      cases G with
      | id =>
          have hMT : M = T := (FormTyped_id σ Γ).mp ((FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp hG)
          subst hMT
          rw [Form.combine_id_right]
          simpa [Form.fcomb] using hF
      | _ => exact combine_typedF_of_nonObj (by intro cs; simp [Form.combine]) hF hG
  | pi d c =>
      cases G with
      | id =>
          have hMT : M = T := (FormTyped_id σ Γ).mp ((FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp hG)
          subst hMT
          rw [Form.combine_id_right]
          simpa [Form.fcomb] using hF
      | _ => exact combine_typedF_of_nonObj (by intro cs; simp [Form.combine]) hF hG
  | eqv φ =>
      cases G with
      | id =>
          have hMT : M = T := (FormTyped_id σ Γ).mp ((FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp hG)
          subst hMT
          rw [Form.combine_id_right]
          simpa [Form.fcomb] using hF
      | obj cs =>
          simp only [FormTypedF] at hG ⊢
          have hF' := (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp hF
          rw [FormTyped_eqv] at hF'
          obtain ⟨hφ, hres⟩ := hF'
          obtain ⟨Tel₁, Tel₂, hM, hT, hchain, hcl⟩ := hG
          rw [Form.combine_eqv_obj]
          refine ⟨Tel₁, Tel₂, hres.trans hM, hT, ⟨M, hφ, hres, hchain⟩, fun a ha V j' ht hj hV => ?_⟩
          have ha' : Atom.HasType Γ (.cast a (.eqToLe φ)) M := Atom.HasType.cast ha (.eqToLe hφ)
          simp only [Form.fcomb] at ht ⊢
          obtain ⟨n, V', happ, hV'⟩ := hcl _ ha' V j' ht hj (ViewTypedWith_cast hV)
          refine ⟨n + 1, V', ?_, ViewTypedWith_root rfl hV'⟩
          rw [applyChain_cons_conv]
          exact happ
      | _ => exact combine_typedF_of_nonObj (by intro cs; simp [Form.combine]) hF hG
  | obj cs =>
      cases G with
      | id =>
          have hMT : M = T := (FormTyped_id σ Γ).mp ((FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp hG)
          subst hMT
          rw [Form.combine_id_right]
          simpa [Form.fcomb] using hF
      | bot =>
          simp only [FormTypedF] at hF
          have hG' := (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp hG
          rw [FormTyped_bot] at hG'
          obtain ⟨_, _, _, hM, _, _⟩ := hF
          rw [hM] at hG'
          exact absurd hG' (by simp)
      | top => exact combine_typedF_of_nonObj (by intro cs; simp [Form.combine]) hF hG
      | pi d c =>
          simp only [FormTypedF] at hF
          have hG' := (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp hG
          rw [FormTyped_pi] at hG'
          obtain ⟨_, _, _, hM, _, _⟩ := hF
          obtain ⟨_, _, _, _, hM', _, _, _⟩ := hG'
          rw [hM] at hM'
          exact absurd hM' (by simp)
      | eqv ψ =>
          simp only [FormTypedF] at hF ⊢
          have hG' := (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp hG
          rw [FormTyped_eqv] at hG'
          obtain ⟨hψ, hres⟩ := hG'
          obtain ⟨Tel₁, Tel₂, hS, hM, hchain, hcl⟩ := hF
          rw [Form.combine_obj_eqv]
          refine ⟨Tel₁, Tel₂, hS, hres.symm.trans hM,
            ChainWellTyped_append cs hchain ⟨T, hψ, hres, rfl⟩, fun a ha V j' ht hj hV => ?_⟩
          simp only [Form.fcomb] at ht ⊢
          obtain ⟨n, V', happ, hV'⟩ := hcl a ha V j' ht hj hV
          have h2 : applyChain σ 2 [ChainStep.conv ψ] (ChainStep.chainAtom cs a) V' = some V' := rfl
          exact ⟨n + 2 + cs.length, V', applyChain_append_of cs happ h2, hV'⟩
      | obj cs₂ =>
          simp only [FormTypedF] at hF hG ⊢
          obtain ⟨Tel₁, TelM, hS, hM, hchain₁, hcl₁⟩ := hF
          obtain ⟨TelM', Tel₂, hM', hT, hchain₂, hcl₂⟩ := hG
          injection hM.symm.trans hM' with _ hTel
          subst hTel
          rw [Form.combine_obj_obj]
          refine ⟨Tel₁, Tel₂, hS, hT, ChainWellTyped_append cs hchain₁ hchain₂,
            fun a ha V j' ht hj hV => ?_⟩
          have hb : Atom.HasType Γ (ChainStep.chainAtom cs a) M := by
            rw [ChainStep.chainAtom_eq_chainAtom']
            exact ChainWellTyped_chainAtom cs hchain₁ ha
          by_cases hex : ∃ n V₁, applyChain σ n cs a V = some V₁
          · simp only [Form.fcomb, dif_pos hex] at ht ⊢
            have hspec := Classical.choose_spec (Classical.choose_spec hex)
            have ht₁ : (f₁ a V).1 ≤ j' := Nat.le_trans (Nat.le_max_left _ _) ht
            have ht₂ : (f₂ (ChainStep.chainAtom cs a) (Classical.choose (Classical.choose_spec hex))).1
                + (f₁ a V).2 ≤ j' :=
              Nat.le_trans (Nat.le_max_right _ _) ht
            obtain ⟨n₁, V₁', happ₁, hV₁'⟩ := hcl₁ a ha V j' ht₁ hj hV
            have hV₁eq : V₁' = Classical.choose (Classical.choose_spec hex) := by
              have h₁ := applyChain_le (Nat.le_max_left n₁ (Classical.choose hex)) happ₁
              have h₂ := applyChain_le (Nat.le_max_right n₁ (Classical.choose hex)) hspec
              exact Option.some.inj (h₁.symm.trans h₂)
            rw [← hV₁eq] at ht₂ ⊢
            obtain ⟨n₂, V'', happ₂, hV''⟩ :=
              hcl₂ _ hb V₁' (j' - (f₁ a V).2) (by omega) (by omega)
                (ViewTypedWith_root (ChainStep.chainAtom_root cs a).symm hV₁')
            refine ⟨n₁ + n₂ + cs.length, V'', applyChain_append_of cs happ₁ happ₂, ?_⟩
            have hdepth : j' - (f₁ a V).2 - (f₂ (ChainStep.chainAtom cs a) V₁').2 =
                j' - ((f₁ a V).2 + (f₂ (ChainStep.chainAtom cs a) V₁').2) := by omega
            rw [hdepth] at hV''
            exact ViewTypedWith_root (ChainStep.chainAtom_root cs a) hV''
          · simp only [Form.fcomb, dif_neg hex] at ht
            obtain ⟨n, V', happ, _⟩ := hcl₁ a ha V j' ht hj hV
            exact absurd ⟨n, V', happ⟩ hex

end

end FCdot
