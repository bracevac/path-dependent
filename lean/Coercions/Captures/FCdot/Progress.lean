import Coercions.Captures.FCdot.CanonicalForms

namespace Captures

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
    {C : CaptureSet s} (h : Γ ⊢ₐ a : (Π(S) T) ^ C) :
    ∃ A S₀ t₀ g, σ.lookup a.root = .lam A S₀ t₀ g := by
  obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed hσ h
  rw [Ty.shape_capt] at hFt
  have hlk : ∃ S₀ T₀, (Γ.lookupTy a.root).shape = Π(S₀) T₀ := by
    rcases hσ.lookupTy_shape a.root with hp | ⟨Tel, ho⟩ | ⟨X, hx⟩
    · exact hp
    · exfalso
      cases hFt with
      | bot hb => simp [Ctx.resolveAt, ho] at hb
      | top ht => simp [Ctx.resolveAt] at ht
      | id hres => simp [Ctx.resolveAt, ho] at hres
      | eqv hres => simp [Ctx.resolveAt, ho] at hres
      | pi hp _ _ _ => simp [Ctx.resolveAt, ho] at hp
      | obj _ ho' _ => simp [Ctx.resolveAt] at ho'
      | into ho' _ => simp [Ctx.resolveAt] at ho'
      | boxed _ hb _ => simp at hb
      | bnd hS hAt _ => exact hσ.root_no_bnd a.root hS hAt
    · exfalso
      cases hFt with
      | bot hb => simp [Ctx.resolveAt, hx] at hb
      | top ht => simp [Ctx.resolveAt] at ht
      | id hres => simp [Ctx.resolveAt, hx] at hres
      | eqv hres => simp [Ctx.resolveAt, hx] at hres
      | pi hp _ _ _ => simp [Ctx.resolveAt, hx] at hp
      | obj _ ho' _ => simp [Ctx.resolveAt] at ho'
      | into ho' _ => simp [Ctx.resolveAt] at ho'
      | boxed _ hb _ => simp at hb
      | bnd hS hAt _ => exact hσ.root_no_bnd a.root hS hAt
  obtain ⟨S₀, T₀, hlk⟩ := hlk
  have hv := hσ.lookup a.root
  have hlit := hσ.lookup_isLiteral a.root
  cases hl : σ.lookup a.root with
  | lam A S₁ t₁ g => exact ⟨_, _, _, _, rfl⟩
  | obj A W Wc F =>
      rw [hl] at hv
      obtain ⟨hT, _⟩ := hv.obj_inv
      rw [hT] at hlk; simp at hlk
  | box b =>
      rw [hl] at hv
      obtain ⟨X, hT, _⟩ := hv.box_inv
      rw [hT] at hlk; simp at hlk
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

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
          | «let» u U' f => exact Or.inr ⟨_, _, .rename⟩
          | cast e => exact Or.inr ⟨_, _, .castAtom⟩
  | val v =>
      cases K with
      | nil => exact Or.inl (Or.inl ⟨rfl, v, rfl⟩)
      | cons K f =>
          cases f with
          | «let» u U' f => exact Or.inr ⟨_, _, .alloc⟩
          | cast e => exact Or.inr ⟨_, _, .castVal⟩
  | app a b =>
      cases ht with
      | app ha hb =>
          obtain ⟨A, S₀, t₀, g, hl⟩ := closed_pi_inversion hσ ha
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
          obtain ⟨A, W, Wc, F, t, hl, hget⟩ := closed_has_field hσ hh
          exact Or.inr ⟨_, _, Step.proj hl hget⟩
  | «let» t u U' f => exact Or.inr ⟨_, _, .let⟩
  | cast t e => exact Or.inr ⟨_, _, .castPush⟩
  -- An `unbox` is a term now: its atom is rooted at a stored box, and the
  -- head form of its casts is one of the three the two steps consume.
  | unbox a U f =>
      cases ht with
      | unbox ha _ =>
          obtain ⟨b, a', n, F, hl, hform, hFs⟩ := closed_box_inversion hσ ha
          rcases hFs with rfl | ⟨φ, rfl⟩ | ⟨d, rfl⟩
          · exact Or.inr ⟨_, _, Step.unboxRefl hl hform (Or.inl rfl)⟩
          · exact Or.inr ⟨_, _, Step.unboxRefl hl hform (Or.inr ⟨φ, rfl⟩)⟩
          · exact Or.inr ⟨_, _, Step.unboxCast hl hform⟩

/-- A typed state is never stuck. -/
theorem not_stuck {s : Sig} {st : State s} {U : Ty s} (hT : State.Typed st U) : ¬ st.Stuck := by
  intro ⟨hnf, hns⟩
  rcases progress hT with hf | hs
  · exact hnf hf
  · exact hns hs

end FCdot

end Captures
