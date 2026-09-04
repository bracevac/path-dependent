import Coercions.FCdot.CanonicalForms

/-!
# Consistency of typed stores (Plan III §8.3, the target side of M5)

Over a typed store, closed inclusion evidence relates types of compatible
shapes only; in particular there is no closed `⊤ ≤ ⊥`, no closed inclusion
of an object type into a function type or conversely, and every block name
of a store binder is defined by the stored literal's witness.  Bad bounds
remain expressible under a lambda; they never reach the store.  Along a
run of the machine the store stays typed (`Steps.typed`), so these hold at
every reachable state.
-/

namespace FCdot

section
variable {σ : Store s} {Γ : Ctx s}

/-- Closed inclusion evidence relates types of compatible shapes: the source
resolves to `⊥`, or the target to `⊤`, or both resolve equally, or both are
function types, or both are object types. -/
theorem closed_le_shapes (hσ : ⊢ σ : Γ) {e : LeCo s} {S T : Ty s} (h : Γ ⊢ e : S ≤ T) :
    Γ.resolve S = ⊥ ∨ Γ.resolve T = ⊤ ∨ Γ.resolve S = Γ.resolve T ∨
    (∃ S₁ T₁ S₂ T₂, Γ.resolve S = Π(S₁) T₁ ∧ Γ.resolve T = Π(S₂) T₂) ∨
    (∃ Tel₁ Tel₂, Γ.resolve S = μ Tel₁ ∧ Γ.resolve T = μ Tel₂) := by
  obtain ⟨_, F, _, hF⟩ := le_canon hσ h
  cases hF with
  | bot hS => exact Or.inl hS
  | top hT => exact Or.inr (Or.inl hT)
  | id hres => exact Or.inr (Or.inr (Or.inl hres))
  | eqv hres => exact Or.inr (Or.inr (Or.inl hres))
  | pi hS hT _ _ => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, hS, hT⟩)))
  | obj hS hT _ => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, hS, hT⟩)))

/-- No closed evidence for `⊤ ≤ ⊥`. -/
theorem Store.Typed.no_top_le_bot (hσ : ⊢ σ : Γ) : ¬ ∃ e : LeCo s, Γ ⊢ e : ⊤ ≤ ⊥ := by
  rintro ⟨e, h⟩
  rcases closed_le_shapes hσ h with h | h | h | ⟨_, _, _, _, h, _⟩ | ⟨_, _, _, h⟩ <;> simp at h

/-- No closed evidence from an object type into a function type. -/
theorem Store.Typed.no_obj_le_pi (hσ : ⊢ σ : Γ) {Tel : Telescope (s,x)} {S : Ty s}
    {T : Ty (s,x)} : ¬ ∃ e : LeCo s, Γ ⊢ e : μ Tel ≤ Π(S) T := by
  rintro ⟨e, h⟩
  rcases closed_le_shapes hσ h with h | h | h | ⟨_, _, _, _, h, _⟩ | ⟨_, _, _, h⟩ <;> simp at h

/-- No closed evidence from a function type into a nonempty object type. -/
theorem Store.Typed.no_pi_le_obj (hσ : ⊢ σ : Γ) {Tel : Telescope (s,x)} {S : Ty s}
    {T : Ty (s,x)} (hne : Tel ≠ .nil) : ¬ ∃ e : LeCo s, Γ ⊢ e : Π(S) T ≤ μ Tel := by
  rintro ⟨e, h⟩
  rcases closed_le_shapes hσ h with h | h | h | ⟨_, _, _, _, _, h⟩ | ⟨_, _, h, _⟩
  · simp at h
  · exact hne (Ty.obj.inj (by simpa using h))
  · simp at h
  · simp at h
  · simp at h

/-- Every block name of a store binder is defined by the stored literal's
witness, and the definition is closed equality evidence. -/
theorem Store.Typed.realized (hσ : ⊢ σ : Γ) (x : BVar s .var) (ℓ : Label) :
    ∃ W, Γ.lookupDef x ℓ = some W ∧ Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W :=
  ⟨_, hσ.lookupDef x ℓ, .def (hσ.lookupDef x ℓ)⟩

end

/-- Along a run, states stay typed (at a renamed result type). -/
theorem Steps.typed {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hT : State.Typed st U) (run : st ⟶* st') : ∃ U', State.Typed st' U' := by
  induction run with
  | refl => exact ⟨U, hT⟩
  | tail _ step ih =>
      obtain ⟨U', hT'⟩ := ih hT
      obtain ⟨ρ, hT''⟩ := preservation' hT' step
      exact ⟨_, hT''⟩

/-- Every store reachable from a typed state is typed, hence consistent: no
closed `⊤ ≤ ⊥` in its context, and every block name is defined. -/
theorem reachable_consistent {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hT : State.Typed st U) (run : st ⟶* st') :
    ∃ Γ : Ctx s', ⊢ st'.σ : Γ ∧ (¬ ∃ e : LeCo s', Γ ⊢ e : ⊤ ≤ ⊥) ∧
      ∀ x ℓ, ∃ W, Γ.lookupDef x ℓ = some W ∧ Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W := by
  obtain ⟨U', Γ, T, hσ, _, _⟩ := Steps.typed hT run
  exact ⟨Γ, hσ, hσ.no_top_le_bot, hσ.realized⟩

end FCdot
