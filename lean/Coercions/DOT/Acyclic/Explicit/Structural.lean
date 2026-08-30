import Coercions.DOT.Acyclic.Explicit.Typing

/-!
# Structural scope facts for proof-only and local binders

These equations justify the nonescape side conditions used by the structural
target rules and by derivation-directed elaboration.
-/

namespace DotFC.Explicit.ScopedTy

open DotFC

/-- Renaming a type and then applying a stable-path renaming cancels when the
two variable maps cancel.  The statement is general enough to commute below
dependent term binders. -/
theorem rename_cancel (type : Source.Ty s₁) (rho : Rename s₁ s₂)
    (tau : TermRename s₂ s₁)
    (cancel : ∀ path, tau.var (rho.var path) = path) :
    rename (type.rename rho) tau = type := by
  induction type generalizing s₂ with
  | top => rfl
  | bot => rfl
  | all domain codomain ihDomain ihCodomain =>
      simp only [Source.Ty.rename_all, rename]
      congr
      · exact ihDomain rho tau cancel
      · apply ihCodomain rho.lift tau.lift
        intro path
        cases path with
        | here => rfl
        | there path => simp [TermRename.lift, cancel]
  | member label lower upper ihLower ihUpper =>
      simp only [Source.Ty.rename_member, rename]
      congr
      · exact ihLower rho tau cancel
      · exact ihUpper rho tau cancel
  | sel path label =>
      simp only [Source.Ty.rename_sel, rename, cancel]

/-- Partial strengthening succeeds after a renaming when every renamed path
maps back to its origin. -/
theorem rename?_cancel (type : Source.Ty s₁) (rho : Rename s₁ s₂)
    (tau : PartialTermRename s₂ s₁)
    (cancel : ∀ path, tau.var (rho.var path) = some path) :
    rename? (type.rename rho) tau = some type := by
  induction type generalizing s₂ with
  | top => rfl
  | bot => rfl
  | all domain codomain ihDomain ihCodomain =>
      simp only [Source.Ty.rename_all, rename?]
      rw [ihDomain rho tau cancel]
      rw [ihCodomain rho.lift tau.lift]
      · rfl
      · intro path
        cases path with
        | here => rfl
        | there path => simp [PartialTermRename.lift, cancel]
  | member label lower upper ihLower ihUpper =>
      simp only [Source.Ty.rename_member, rename?]
      rw [ihLower rho tau cancel, ihUpper rho tau cancel]
      rfl
  | sel path label =>
      simp only [Source.Ty.rename_sel, rename?, cancel]
      rfl

/-- Weakening below a reusable-handle binder and then erasing that binder is
the identity on source types. -/
@[simp]
theorem dropMember_weaken (type : Source.Ty s) :
    dropMember (type.weaken (kind := .member)) = type := by
  apply rename_cancel type Rename.succ TermRename.dropMember
  intro path
  rfl

/-- The same cancellation fact for an erased equality or inclusion binder. -/
@[simp]
theorem dropEvidence_weaken {relation : Relation} (type : Source.Ty s) :
    dropEvidence (type.weaken (kind := .evidence relation)) = type := by
  apply rename_cancel type Rename.succ TermRename.dropEvidence
  intro path
  rfl

/-- A weakened type never mentions the newest local term variable, so
strengthening succeeds with the original type. -/
@[simp]
theorem strengthenTerm_weaken (type : Source.Ty s) :
    strengthenTerm (type.weaken (kind := .term)) = some type := by
  apply rename?_cancel type Rename.succ PartialTermRename.strengthenTerm
  intro path
  rfl

end DotFC.Explicit.ScopedTy
