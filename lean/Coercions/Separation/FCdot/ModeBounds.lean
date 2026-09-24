import Coercions.Separation.FCdot.Typing

namespace Separation

/-!
# Capture evidence and mode bounds

Closed capture evidence `C ⊑ D` keeps every mode bound of names: every bound
of `D` in the mode reading is a bound of `C` (`Ctx.ModeLe`, `Names.lean`).
That is false in an open context, where a telescope assumption of a
parameter types `{y} ⊑ {ro y}` by `member`.  It holds for every other rule in
every context whose term variables are no parameters.  This module proves it
by one mutual induction over capture evidence, equality evidence and atoms,
with the two `member` rules as hypotheses.  Canonical forms discharge them in
a store context (`Ctx.modeSound_store`, `CanonicalForms.lean`), which is the
second half of T0.4 of plan-5h.

`Ctx.ModeSound Γ` is the statement for all closed evidence of `Γ`.  It is a
field of `FormsTyped` (`Retyping.lean`), read at the let-like steps of
the machine, where a binder is instantiated by a closed atom of its type.
-/

namespace FCdot

/-- Closed capture evidence keeps every mode bound. -/
def Ctx.ModeSound (Γ : Ctx s) : Prop :=
  ∀ (f : CapCo s) (C D : CaptureSet s), Γ ⊢ᶜ f : C ⊑ D → Γ.ModeLe C D

section
variable {s : Sig} {Γ : Ctx s}
  (hvar : ∀ x, Γ.isFormalVar x = false)
  (hmem : ∀ (a : Atom s) (S : Shape s) (D : CaptureSet s) (e : ShapeCo s)
    (Tel : Telescope (s,x)) (i : Nat) (C₁ C₂ : CaptureSet (s,x)),
    Γ ⊢ₐ a : S ^ D → Γ ⊢ˢ e : S ≤ μ Tel → Tel ∋ (i ↦ C₁ ⊑ᶜ C₂) →
    Γ.ModeLe (C₁⟦a.root⟧) (C₂⟦a.root⟧))
  (hmemEq : ∀ (a : Atom s) (S : Shape s) (D : CaptureSet s) (e : ShapeCo s)
    (Tel : Telescope (s,x)) (i : Nat) (C₁ C₂ : CaptureSet (s,x)),
    Γ ⊢ₐ a : S ^ D → Γ ⊢ˢ e : S ≤ μ Tel → Tel ∋ (i ↦ C₁ ≐ᶜ C₂) →
    Γ.ModeEq (C₁⟦a.root⟧) (C₂⟦a.root⟧))

include hvar hmem hmemEq

set_option linter.unusedSectionVars false

mutual

/-- **Capture evidence keeps every mode bound**, provided the two `member`
rules do and no term variable is a parameter.  `level` reads its premise,
`ownLe` reads its premise, `modeLe` and `roMap` are the algebra of
`EMode.thr`, `defC` is `Ctx.modeEq_defC`, and `var` reads that the variable is
no parameter. -/
theorem CapCo.HasType.namesModeLe {f : CapCo s} {C D : CaptureSet s} (h : Γ ⊢ᶜ f : C ⊑ D) :
    Γ.ModeLe C D := by
  match h with
  | .refl => exact Ctx.ModeLe.refl _ _
  | .trans hf hg =>
      exact (CapCo.HasType.namesModeLe hf).trans (CapCo.HasType.namesModeLe hg)
  | .elem hsub => exact Ctx.ModeLe.of_subset hsub
  | .union hf hg => exact (CapCo.HasType.namesModeLe hf).union (CapCo.HasType.namesModeLe hg)
  | .capvar ha => exact Atom.HasType.namesModeLe ha
  | .member ha he hAt => exact hmem _ _ _ _ _ _ _ _ ha he hAt
  | .eqToLe hφ => exact (CapEq.HasType.namesModeEq hφ).1
  | .level hr _ he => exact Ctx.modeLe_level hr he
  | .modeLe hm => exact Ctx.modeLe_modeLe _ hm
  | .roMap _ => exact Ctx.modeLe_roMap _ _ _
  | .ownLe hO hW => exact Ctx.modeLe_ownLe hO hW

theorem CapEq.HasType.namesModeEq {φ : CapEq s} {C D : CaptureSet s} (h : Γ ⊢ᶜ φ : C ≡ D) :
    Γ.ModeEq C D := by
  match h with
  | .refl => exact Ctx.ModeEq.refl _ _
  | .symm hφ => exact (CapEq.HasType.namesModeEq hφ).symm
  | .trans h₁ h₂ => exact (CapEq.HasType.namesModeEq h₁).trans (CapEq.HasType.namesModeEq h₂)
  | .defC hd => exact Ctx.modeEq_defC _ _ _ _ hd
  | .instC hI => exact Ctx.modeEq_instC hI
  | .member ha he hAt => exact hmemEq _ _ _ _ _ _ _ _ ha he hAt

/-- The root of a typed atom has the bounds of the atom's capture set. -/
theorem Atom.HasType.namesModeLe {a : Atom s} {T : Ty s} (h : Γ ⊢ₐ a : T) :
    Γ.ModeLe [CapAtom.var a.root] T.captureSet := by
  match h with
  | @Atom.HasType.var _ _ x =>
      intro m hD
      rw [Ctx.setBound_singleton]
      exact (Γ.modeBound_var x (hvar x) m).mpr hD
  | .cast hb (.capt _ hg) =>
      exact (Atom.HasType.namesModeLe hb).trans (CapCo.HasType.namesModeLe hg)
  | .recap _ hg => exact CapCo.HasType.namesModeLe hg
  | .unfoldSelf hb => have := Atom.HasType.namesModeLe hb; exact this
  | .foldSelf hb => have := Atom.HasType.namesModeLe hb; exact this
  | .both hb _ _ => have := Atom.HasType.namesModeLe hb; exact this

end

end

/-- The root of a typed atom is bounded by the atom's type, in a sound
context whose variables are no parameters. -/
theorem Ctx.ModeSound.atom {Γ : Ctx s} (hms : Γ.ModeSound) {a : Atom s} {T : Ty s}
    (ha : Γ ⊢ₐ a : T) (m : EMode) (hT : Γ.SetBound T.captureSet m) :
    Γ.ModeBound (.var a.root) m := by
  cases T with
  | capt C S =>
      have := hms _ _ _ (CapCo.HasType.capvar ha) m hT
      rwa [Ctx.setBound_singleton] at this

/-! ## Closed evidence over a store with no term binder

A signature without a term binder has no atom, so neither `member` nor
`capvar` nor `defC` can fire.  Over a single location, no evidence types
`{y} ⊑ {ro y}` (`Γs_no_ro_widen`, `ModeExamples.lean`). -/

theorem BVar.no_var_cap : BVar ([] ,c) .var → False := by
  intro x
  cases x with
  | there y => cases y

end FCdot

end Separation
