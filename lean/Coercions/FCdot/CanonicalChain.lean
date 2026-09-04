import Coercions.FCdot.CanonicalMetatheory
import Coercions.FCdot.Preservation

/-!
# The chain of casts of a closed atom

Over a typed store, the head form of a closed atom's wrappers is typed from
the root's type to the atom's type, at the atom's root: opening the self
block at the root is invisible to `foldSelf` and `unfoldSelf`, and a
coercion form (typed with plain shapes) is typed at any root.  This
discharges the canonical-forms obligations of preservation and of the
backward erasure simulation.
-/

namespace FCdot

section
variable {σ : Store s} {Γ : Ctx s}

/-- The root of an atom under wrappers. -/
@[simp] theorem Atom.root_cast (a : Atom s) (e : LeCo s) : (Atom.cast a e).root = a.root := rfl
@[simp] theorem Atom.root_foldSelf (Tel : Telescope (s,x)) (a : Atom s) :
    (Atom.foldSelf Tel a).root = a.root := rfl
@[simp] theorem Atom.root_unfoldSelf (a : Atom s) : (Atom.unfoldSelf a).root = a.root := rfl

/-- Opening the self block at the root is invisible to `foldSelf`. -/
theorem Ctx.resolveAt_fold (Γ : Ctx s) (r : BVar s .var) (Tel : Telescope (s,x)) :
    Γ.resolveAt (some r) (.obj Tel) = Γ.resolveAt (some r) (.obj ((Tel⟦r⟧)↑)) := by
  simp [Ctx.resolveAt, Ty.unfoldAt, Telescope.weaken_substVar]

/-- The chain of casts of a closed atom normalizes to a form typed from the
root's type to the atom's type, at the root. -/
theorem closedAtomForm_typed (hσ : ⊢ σ : Γ) {a : Atom s} {S : Ty s}
    (h : Γ ⊢ₐ a : S) :
    ∃ n a' F, closedAtomForm σ n a = some (a', F) ∧
      Γ ⊨[a.root] F : (Γ.lookupTy a.root) ≤ S := by
  match h with
  | .var => exact ⟨1, _, .id, rfl, .id rfl⟩
  | @Atom.HasType.cast _ _ a S₀ e T ha he =>
      obtain ⟨n₁, a', F, hF, hFt⟩ := closedAtomForm_typed hσ ha
      obtain ⟨n₂, G, hG, hGt⟩ := le_canon hσ he
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hFt (hGt.atRoot _)
      refine ⟨max n₁ n₂ + 1, .cast a' e, H, ?_, ?_⟩
      · simp [closedAtomForm, closedAtomForm_le (Nat.le_max_left n₁ n₂) hF,
          hnf_le (Nat.le_max_right n₁ n₂) hG, hH]
      · simp only [Atom.root_cast]; exact hHt
  | @Atom.HasType.unfoldSelf _ _ a Tel ha =>
      obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed hσ ha
      refine ⟨n + 1, .unfoldSelf a', F, by simp [closedAtomForm, hF], ?_⟩
      simp only [Atom.root_unfoldSelf]
      exact hFt.tgtRes (Ctx.resolveAt_fold Γ a.root Tel)
  | @Atom.HasType.foldSelf _ _ a Tel ha =>
      obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed hσ ha
      refine ⟨n + 1, .foldSelf Tel a', F, by simp [closedAtomForm, hF], ?_⟩
      simp only [Atom.root_foldSelf]
      exact hFt.tgtRes (Ctx.resolveAt_fold Γ a.root Tel).symm

/-- The type recorded for a location is a function or an object type. -/
theorem Store.Typed.lookupTy_shape (hσ : ⊢ σ : Γ) (x : BVar s .var) :
    (∃ S T, Γ.lookupTy x = .pi S T) ∨ ∃ Tel, Γ.lookupTy x = .obj Tel := by
  have hv := hσ.lookup x
  have hlit := hσ.lookup_isLiteral x
  cases hl : σ.lookup x with
  | lam S t =>
      rw [hl] at hv
      obtain ⟨T₀, hT, _⟩ := hv.lam_inv
      exact Or.inl ⟨_, _, hT⟩
  | obj W F =>
      rw [hl] at hv
      obtain ⟨hT, _, _⟩ := hv.obj_inv
      exact Or.inr ⟨_, hT⟩
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

/-- The head form of a function atom's casts is the identity, an equality, or
a `pi` form. -/
theorem closedAtomForm_pi (hσ : ⊢ σ : Γ) {a : Atom s} {S : Ty s} {T : Ty (s,x)}
    (h : Γ ⊢ₐ a : (.pi S T)) :
    ∃ n a' F, closedAtomForm σ n a = some (a', F) ∧
      (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d c, F = .pi d c) := by
  obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed hσ h
  refine ⟨n, a', F, hF, ?_⟩
  cases hFt with
  | bot hb =>
      rcases hσ.lookupTy_shape a.root with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩
      · rw [hp] at hb; simp at hb
      · rw [ho] at hb; simp at hb
  | top ht => simp at ht
  | id _ => exact Or.inl rfl
  | eqv _ => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | pi _ _ _ _ => exact Or.inr (Or.inr ⟨_, _, rfl⟩)
  | obj _ ho _ => simp [Ctx.resolveAt, Ty.unfoldAt] at ho

/-- The canonical-forms obligation of preservation. -/
theorem Store.Typed.formsTyped (hσ : ⊢ σ : Γ) : FormsTyped σ Γ where
  pi := by
    intro a S T n a' d c S₀ T₀ ha hF hlk
    obtain ⟨n', a'', F', hF', hFt⟩ := closedAtomForm_typed hσ ha
    have hd := closedAtomForm_det hF hF'
    have hFe : F' = .pi d c := ((Prod.mk.injEq _ _ _ _).mp hd).2.symm
    subst hFe
    cases hFt with
    | pi hS hT hd hc =>
        rw [hlk, Ctx.resolve_pi] at hS
        rw [Ctx.resolve_pi] at hT
        obtain ⟨rfl, rfl⟩ := (Ty.pi.injEq _ _ _ _).mp hS
        obtain ⟨rfl, rfl⟩ := (Ty.pi.injEq _ _ _ _).mp hT
        exact ⟨hd, hc⟩
  refl := by
    intro a S T n a' F ha hF hid
    obtain ⟨n', a'', F', hF', hFt⟩ := closedAtomForm_typed hσ ha
    have hd := closedAtomForm_det hF hF'
    have hFe : F' = F := ((Prod.mk.injEq _ _ _ _).mp hd).2.symm
    subst hFe
    have hres : Γ.resolveAt (some a.root) (Γ.lookupTy a.root) = Γ.resolveAt (some a.root) (.pi S T) := by
      rcases hid with rfl | ⟨φ, rfl⟩
      · cases hFt with | id h => exact h
      · cases hFt with | eqv h => exact h
    rw [show Γ.resolveAt (some a.root) (.pi S T) = .pi S T by simp [Ctx.resolveAt, Ty.unfoldAt]] at hres
    have hres' := (Ctx.resolveAt_pi_iff Γ _ _ _ _).mp hres
    rcases hσ.lookupTy_shape a.root with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩
    · rw [hp, Ctx.resolve_pi] at hres'
      obtain ⟨rfl, rfl⟩ := (Ty.pi.injEq _ _ _ _).mp hres'
      exact hp
    · rw [ho, Ctx.resolve_obj] at hres'; simp at hres'

/-! ## Corollaries without obligations -/

/-- Preservation over typed states. -/
theorem preservation' {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hT : State.Typed st U) (step : Step st st') :
    ∃ ρ : Rename s s', State.Typed st' (U.rename ρ) :=
  preservation (fun _ hσ => hσ.formsTyped) hT step

/-- Backward simulation over typed stores. -/
theorem erase_reflect' {s s' : Sig} {st : State s} {Γ : Ctx s} {r : Runtime.State s'}
    (hσ : ⊢ st.σ : Γ) (hty : ∃ T, Γ ⊢ st.t : T)
    (h : Runtime.Step st.erase r) :
    ∃ st' : State s', Steps st st' ∧ st'.erase = r :=
  erase_reflect hσ (fun _ _ _ ha _ => closedAtomForm_pi hσ ha) hty h

end

end FCdot
