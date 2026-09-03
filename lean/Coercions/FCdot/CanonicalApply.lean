import Coercions.FCdot.CanonicalDepth
import Coercions.FCdot.CanonicalMono
import Coercions.FCdot.CanonicalFormF

/-!
# Applying a typed form to a typed view

Elimination at an atom (`member`) normalizes an inclusion to a head form
and applies it to the atom's view.  This is the one place the object clause
of `FormTyped` is consumed: applying a form whose source and target resolve
to object types sends a typed input view to a typed output view of the
target telescope.  Forms whose source resolves to an object type are `id`,
`eqv`, or `obj`; `bot` is excluded because the atom's type is not absurd,
and `top`/`pi` cannot have an object target.
-/

namespace FCdot

section
variable {σ : Store s} {Γ : Ctx s}

theorem applyForm_viewF {F : Form s} {f : Atom s → View s → Nat × Nat}
    {S T : Ty s} {a : Atom s} {V : View s} {Tel₁ Tel₂ : Telescope (s,x)} {j : Nat}
    (hF : FormTypedF σ Γ f (j + 1) F S T)
    (hS : Γ.resolve S = .obj Tel₁) (hT : Γ.resolve T = .obj Tel₂)
    (ha : Atom.HasType Γ a S) :
    ∀ j', (f a V).1 ≤ j' → j' ≤ j →
      ViewTypedWith σ Γ (FormTyped σ Γ j') V Tel₁ a →
      ∃ n V', applyForm σ n F a V = some V' ∧
        ViewTypedWith σ Γ (FormTyped σ Γ (j' - (f a V).2)) V' Tel₂ a := by
  cases F with
  | bot =>
      have := (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp hF
      rw [FormTyped] at this; rw [this] at hS; exact absurd hS (by simp)
  | top =>
      have := (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp hF
      rw [FormTyped] at this; rw [this] at hT; exact absurd hT (by simp)
  | pi d c =>
      have := (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp hF
      rw [FormTyped] at this
      obtain ⟨_, _, _, _, hS', _, _, _⟩ := this
      rw [hS'] at hS; exact absurd hS (by simp)
  | id =>
      have hST : S = T := by
        have := (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp hF
        rw [FormTyped] at this; exact this
      subst hST
      have hTel : Tel₁ = Tel₂ := by rw [hS] at hT; exact (Ty.obj.injEq _ _).mp hT
      subst hTel
      exact fun j' _ _ hV => ⟨1, V, rfl, ViewTypedWith_mono (fun _ _ _ h => FormTyped_mono (Nat.sub_le _ _) h) (by simpa using hV)⟩
  | eqv φ =>
      have hres : Γ.resolve S = Γ.resolve T := by
        have := (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp hF
        rw [FormTyped] at this; exact this.2
      have hTel : Tel₁ = Tel₂ := by rw [hS, hT] at hres; exact (Ty.obj.injEq _ _).mp hres
      subst hTel
      exact fun j' _ _ hV => ⟨1, V, rfl, ViewTypedWith_mono (fun _ _ _ h => FormTyped_mono (Nat.sub_le _ _) h) (by simpa using hV)⟩
  | obj cs =>
      simp only [FormTypedF] at hF
      obtain ⟨Tel₁', Tel₂', hS', hT', hchain, hcl⟩ := hF
      have e₁ : Tel₁' = Tel₁ := by rw [hS'] at hS; exact (Ty.obj.injEq _ _).mp hS
      have e₂ : Tel₂' = Tel₂ := by rw [hT'] at hT; exact (Ty.obj.injEq _ _).mp hT
      subst e₁; subst e₂
      intro j' ht hj hV
      obtain ⟨n, V', happ, hV'⟩ := hcl a ha V j' ht hj hV
      exact ⟨n + 1, V', by simpa [applyForm] using happ, hV'⟩

/-- A head form whose source and target both resolve to object types is `id`,
`eqv`, or `obj`; if in addition the source does not resolve to `⊥`, its
source telescope is determined. -/
theorem FormTyped_obj_source {F : Form s} {S T : Ty s} {Tel₂ : Telescope (s,x)} {k : Nat}
    (hF : FormTyped σ Γ k F S T) (hT : Γ.resolve T = .obj Tel₂)
    (hnb : Γ.resolve S ≠ .bot) :
    ∃ Tel₁, Γ.resolve S = .obj Tel₁ := by
  cases F with
  | bot => rw [FormTyped] at hF; exact absurd hF hnb
  | top => rw [FormTyped] at hF; rw [hF] at hT; exact absurd hT (by simp)
  | pi d c =>
      rw [FormTyped] at hF; obtain ⟨_, _, _, _, _, hT', _, _⟩ := hF
      rw [hT'] at hT; exact absurd hT (by simp)
  | id => rw [FormTyped] at hF; subst hF; exact ⟨Tel₂, hT⟩
  | eqv φ => rw [FormTyped] at hF; exact ⟨Tel₂, hF.2.trans hT⟩
  | obj cs =>
      cases k with
      | zero => rw [FormTyped] at hF; obtain ⟨Tel₁, _, hS', _, _⟩ := hF; exact ⟨Tel₁, hS'⟩
      | succ j => rw [FormTyped] at hF; obtain ⟨Tel₁, _, hS', _, _, _⟩ := hF; exact ⟨Tel₁, hS'⟩

end

end FCdot
