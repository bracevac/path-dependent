import Coercions.FCdot.CanonicalForms

/-!
# Consistency of typed stores (Plan III §8.3, the target side of M5)

Over a typed store, closed inclusion evidence relates types of compatible
shapes only; in particular there is no closed `⊤ ≤ ⊥`, no closed inclusion
of an object type *without bounds* into a function type, no closed inclusion
of a function type into an object type with a proposition that is not a
bound, and every block name of a store binder is defined by the stored
literal's witness.  Bad bounds remain expressible under a lambda; they never
reach the store.  Along a run of the machine the store stays typed
(`Steps.typed`), so these hold at every reachable state.

With self-bound propositions a coercion may also go *through* a bound of the
source object type, or *into* an object type whose propositions are proven
without consulting the source's view; `closed_le_shapes` has one disjunct
for each.
-/

namespace FCdot

section
variable {σ : Store s} {Γ : Ctx s}

/-! ## Telescopes of bounds only -/

/-- A telescope all of whose propositions are bounds. -/
def Telescope.BndsOnly (Tel : Telescope (s,x)) : Prop :=
  ∀ (i : Nat) (P : Proposition (s,x)), Tel ∋ (i ↦ P) → ∃ X : Ty (s,x), P = Proposition.bnd X

theorem Telescope.BndsOnly.nil : (Telescope.nil (s := (s,x))).BndsOnly := by
  intro i P h; cases h

/-- An entry over a bounds-only telescope proves a bound. -/
theorem EntryTyped.bnd_of_bndsOnly {ρ : Option (BVar s .var)} {TelM : Telescope (s,x)}
    {E : Entry s} {P : Proposition (s,x)} (hb : TelM.BndsOnly)
    (hE : EntryTyped Γ ρ TelM E P) : ∃ X : Ty (s,x), P = Proposition.bnd X := by
  cases hE with
  | le hh _ _ =>
      cases hh with
      | le hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
      | eq hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
      | eqSym hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
  | eq hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
  | eqSym hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
  | has hAt => obtain ⟨_, hP⟩ := hb _ _ hAt; exact absurd hP (by simp)
  | bnd _ => exact ⟨_, rfl⟩
  | bndId _ => exact ⟨_, rfl⟩

mutual

/-- View-free entries out of a source that is neither `⊥` nor an object type
can only prove bounds. -/
theorem BndsTyped.bndsOnly {ρ : Option (BVar s .var)} {S : Ty s} {Es : Entries s}
    {Tel : Telescope (s,x)} (hb : Γ.resolveAt? ρ S ≠ ⊥)
    (ho : ∀ Tel₁ : Telescope (s,x), Γ.resolveAt? ρ S ≠ μ Tel₁)
    (h : BndsTyped Γ ρ S Es Tel) : Tel.BndsOnly := by
  match h with
  | .nil => intro i P hP; cases hP
  | .cons h' _ =>
      intro i P hP
      cases hP with
      | here => exact ⟨_, rfl⟩
      | there hP' => exact BndsTyped.bndsOnly hb ho h' _ _ hP'
  | .thru h' hH hM hE =>
      intro i P hP
      cases hP with
      | here => exact EntryTyped.bnd_of_bndsOnly (FormTyped.bndsOnly_target hb ho hH hM) hE
      | there hP' => exact BndsTyped.bndsOnly hb ho h' _ _ hP'

/-- A form out of a source that is neither `⊥` nor an object type reaches
only object types with bounds only. -/
theorem FormTyped.bndsOnly_target {ρ : Option (BVar s .var)} {S M : Ty s} {H : Form s}
    {TelM : Telescope (s,x)} (hb : Γ.resolveAt? ρ S ≠ ⊥)
    (ho : ∀ Tel₁ : Telescope (s,x), Γ.resolveAt? ρ S ≠ μ Tel₁)
    (hH : FormTyped Γ ρ H S M) (hM : Γ.resolveAt? ρ M = μ TelM) : TelM.BndsOnly := by
  match hH with
  | .bot hS => exact absurd hS hb
  | .top hT =>
      rw [hM] at hT
      obtain rfl := Ty.obj.inj (by simpa using hT : (μ TelM : Ty s) = μ .nil)
      exact Telescope.BndsOnly.nil
  | .id hres => exact absurd (hres.trans hM) (ho TelM)
  | .eqv hres => exact absurd (hres.trans hM) (ho TelM)
  | .pi _ hT _ _ => rw [hM] at hT; exact absurd hT (by simp)
  | .obj hS _ _ => exact absurd hS (ho _)
  | .bnd hS _ _ => exact absurd hS (ho _)
  | .into hT hB =>
      rw [hM] at hT
      obtain rfl := Ty.obj.inj hT
      exact BndsTyped.bndsOnly hb ho hB

end

/-- Closed inclusion evidence relates types of compatible shapes: the source
resolves to `⊥`, or the target to `⊤`, or both resolve equally, or both are
function types, or both are object types, or the source resolves to an
object type with a bound whose type is below the target, or the target
resolves to an object type that is bounds-only unless the source is an
object type too. -/
theorem closed_le_shapes (hσ : ⊢ σ : Γ) {e : LeCo s} {S T : Ty s} (h : Γ ⊢ e : S ≤ T) :
    Γ.resolve S = ⊥ ∨ Γ.resolve T = ⊤ ∨ Γ.resolve S = Γ.resolve T ∨
    (∃ S₁ T₁ S₂ T₂, Γ.resolve S = Π(S₁) T₁ ∧ Γ.resolve T = Π(S₂) T₂) ∨
    (∃ Tel₁ Tel₂, Γ.resolve S = μ Tel₁ ∧ Γ.resolve T = μ Tel₂) ∨
    (∃ (Tel₁ : Telescope (s,x)) (i : Nat) (T' : Ty s) (F : Form s),
      Γ.resolve S = μ Tel₁ ∧ Tel₁ ∋ (i ↦ ⊑ T'↑) ∧ Γ ⊨ F : T' ≤ T) ∨
    (∃ Tel₂ : Telescope (s,x), Γ.resolve T = μ Tel₂ ∧
      ((∃ Tel₁ : Telescope (s,x), Γ.resolve S = μ Tel₁) ∨ Tel₂.BndsOnly)) := by
  obtain ⟨_, F, _, hF⟩ := le_canon hσ h
  cases hF with
  | bot hS => exact Or.inl hS
  | top hT => exact Or.inr (Or.inl hT)
  | id hres => exact Or.inr (Or.inr (Or.inl hres))
  | eqv hres => exact Or.inr (Or.inr (Or.inl hres))
  | pi hS hT _ _ => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, hS, hT⟩)))
  | obj hS hT _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, hS, hT⟩))))
  | bnd hS hAt hF' =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, hS, hAt, hF'⟩)))))
  | into hT hB =>
      cases hres : Γ.resolve S with
      | bot => exact Or.inl rfl
      | obj Tel₁ =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hT, Or.inl ⟨Tel₁, rfl⟩⟩)))))
      | sel y ℓ =>
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hT, Or.inr ?_⟩)))))
          exact BndsTyped.bndsOnly (ρ := none) (by rw [Ctx.resolveAt?_none, hres]; simp)
            (fun Tel₁ h' => by rw [Ctx.resolveAt?_none, hres] at h'; simp at h') hB
      | pi S₀ T₀ =>
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hT, Or.inr ?_⟩)))))
          exact BndsTyped.bndsOnly (ρ := none) (by rw [Ctx.resolveAt?_none, hres]; simp)
            (fun Tel₁ h' => by rw [Ctx.resolveAt?_none, hres] at h'; simp at h') hB

/-- No closed evidence for `⊤ ≤ ⊥`. -/
theorem Store.Typed.no_top_le_bot (hσ : ⊢ σ : Γ) : ¬ ∃ e : LeCo s, Γ ⊢ e : ⊤ ≤ ⊥ := by
  rintro ⟨e, h⟩
  rcases closed_le_shapes hσ h with
    h | h | h | ⟨_, _, _, _, h, _⟩ | ⟨_, _, _, h⟩ | ⟨Tel₁, i, T', F, hS, hAt, _⟩ | ⟨_, h, _⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · obtain rfl := Ty.obj.inj (by simpa using hS : (μ .nil : Ty s) = μ Tel₁)
    cases hAt
  · simp at h

/-- No closed evidence from an object type without bounds into a function
type. -/
theorem Store.Typed.no_obj_le_pi (hσ : ⊢ σ : Γ) {Tel : Telescope (s,x)} {S : Ty s}
    {T : Ty (s,x)} (hnb : ∀ (i : Nat) (T' : Ty s), ¬ Tel ∋ (i ↦ ⊑ T'↑)) :
    ¬ ∃ e : LeCo s, Γ ⊢ e : μ Tel ≤ Π(S) T := by
  rintro ⟨e, h⟩
  rcases closed_le_shapes hσ h with
    h | h | h | ⟨_, _, _, _, h, _⟩ | ⟨_, _, _, h⟩ | ⟨Tel₁, i, T', F, hS, hAt, _⟩ | ⟨_, h, _⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · rw [Ctx.resolve_obj] at hS
    obtain rfl := Ty.obj.inj hS
    exact hnb i T' hAt
  · simp at h

/-- No closed evidence from a function type into an object type with a
proposition that is not a bound. -/
theorem Store.Typed.no_pi_le_obj (hσ : ⊢ σ : Γ) {Tel : Telescope (s,x)} {S : Ty s}
    {T : Ty (s,x)} {i : Nat} {P : Proposition (s,x)} (hAt : Tel ∋ (i ↦ P))
    (hP : ∀ X : Ty (s,x), P ≠ Proposition.bnd X) :
    ¬ ∃ e : LeCo s, Γ ⊢ e : Π(S) T ≤ μ Tel := by
  rintro ⟨e, h⟩
  rcases closed_le_shapes hσ h with
    h | h | h | ⟨_, _, _, _, _, h⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, _, h, _⟩ | ⟨Tel₂, hT, hd⟩
  · simp at h
  · rw [Ctx.resolve_obj] at h
    obtain rfl := Ty.obj.inj (by simpa using h : (μ Tel : Ty s) = μ .nil)
    cases hAt
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · rw [Ctx.resolve_obj] at hT
    obtain rfl := Ty.obj.inj hT
    rcases hd with ⟨Tel₁, h₁⟩ | hbo
    · simp at h₁
    · obtain ⟨X, hX⟩ := hbo _ _ hAt
      exact hP X hX

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
