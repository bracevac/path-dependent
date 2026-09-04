import Coercions.FCdot.CanonicalForms

/-!
# Progress

A typed state is final or steps.  The two places where typing has to say
something about the store are application and projection: a function atom
is rooted at a closure (`closed_pi_inversion`), and presence evidence names
a field that the object at the root actually has (`has_canon`).  Both are
consequences of the canonical-forms theorem.
-/

namespace FCdot

section
variable {σ : Store s} {Γ : Ctx s}

/-- A function atom is rooted at a closure. -/
theorem closed_pi_inversion (hσ : ⊢ σ : Γ) {a : Atom s} {S : Ty s} {T : Ty (s,x)}
    (h : Γ ⊢ₐ a : .pi S T) : ∃ S₀ t₀, σ.lookup a.root = .lam S₀ t₀ := by
  obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed hσ h
  have hlk : ∃ S₀ T₀, Γ.lookupTy a.root = .pi S₀ T₀ := by
    rcases hσ.lookupTy_shape a.root with hp | ⟨Tel, ho⟩
    · exact hp
    · exfalso
      cases hFt with
      | bot hb => rw [ho] at hb; simp at hb
      | top ht => simp at ht
      | id hres => rw [ho] at hres; simp [Ctx.resolveAt, Ty.unfoldAt] at hres
      | eqv hres => rw [ho] at hres; simp [Ctx.resolveAt, Ty.unfoldAt] at hres
      | pi hp _ _ _ => rw [ho] at hp; simp at hp
      | obj _ ho' _ => simp [Ctx.resolveAt, Ty.unfoldAt] at ho'
  obtain ⟨S₀, T₀, hlk⟩ := hlk
  have hv := hσ.lookup a.root
  have hlit := hσ.lookup_isLiteral a.root
  cases hl : σ.lookup a.root with
  | lam S₁ t₁ => exact ⟨_, _, rfl⟩
  | obj W F =>
      rw [hl] at hv
      obtain ⟨hT, _, _⟩ := hv.obj_inv
      rw [hlk] at hT; simp at hT
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

/-- Presence evidence at a location names a field of the object stored there. -/
theorem closed_has_field (hσ : ⊢ σ : Γ) {h : Has s} {x : BVar s .var} {ℓ : Label}
    (hh : Has.HasType Γ h x ℓ) : ∃ W F t, σ.lookup x = .obj W F ∧ F.get? ℓ = some t := by
  obtain ⟨_, _, W, F, hl, hget⟩ := has_canon hσ hh
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hget
  exact ⟨W, F, t, hl, ht⟩

end

/-- A typed state is final or steps. -/
theorem progress {s : Sig} {st : State s} {U : Ty s} (hT : State.Typed st U) :
    st.Final ∨ ∃ (s' : Sig) (st' : State s'), Step st st' := by
  obtain ⟨Γ, T, hσ, ht, hK⟩ := hT
  obtain ⟨σ, K, t⟩ := st
  simp only at hσ ht hK
  cases t with
  | atom a =>
      cases K with
      | nil => exact Or.inl (Or.inr ⟨rfl, a, rfl⟩)
      | cons K f =>
          cases f with
          | «let» u => exact Or.inr ⟨_, _, .rename⟩
          | cast e => exact Or.inr ⟨_, _, .castAtom⟩
  | val v =>
      cases K with
      | nil => exact Or.inl (Or.inl ⟨rfl, v, rfl⟩)
      | cons K f =>
          cases f with
          | «let» u => exact Or.inr ⟨_, _, .alloc⟩
          | cast e => exact Or.inr ⟨_, _, .castVal⟩
  | app a b =>
      cases ht with
      | app ha hb =>
          obtain ⟨S₀, t₀, hl⟩ := closed_pi_inversion hσ ha
          by_cases hne : a = .var a.root
          · obtain ⟨x, rfl⟩ : ∃ x, a = .var x := ⟨_, hne⟩
            exact Or.inr ⟨_, _, Step.appVar hl⟩
          · obtain ⟨n, a', F, hF, hFs⟩ := closedAtomForm_pi hσ ha
            rcases hFs with hid | ⟨φ, hφ⟩ | ⟨d, c, hpi⟩
            · exact Or.inr ⟨_, _, Step.appCastRefl hl hne hF (Or.inl hid)⟩
            · exact Or.inr ⟨_, _, Step.appCastRefl hl hne hF (Or.inr ⟨φ, hφ⟩)⟩
            · subst hpi; exact Or.inr ⟨_, _, Step.appCast hl hne hF⟩
  | proj a ℓ h =>
      cases ht with
      | proj _ hh =>
          obtain ⟨W, F, t, hl, hget⟩ := closed_has_field hσ hh
          exact Or.inr ⟨_, _, Step.proj hl hget⟩
  | «let» t u => exact Or.inr ⟨_, _, .let⟩
  | cast t e => exact Or.inr ⟨_, _, .castPush⟩

/-- A typed state is never stuck. -/
theorem not_stuck {s : Sig} {st : State s} {U : Ty s} (hT : State.Typed st U) : ¬ st.Stuck := by
  intro ⟨hnf, hns⟩
  rcases progress hT with hf | hs
  · exact hnf hf
  · exact hns hs

end FCdot
