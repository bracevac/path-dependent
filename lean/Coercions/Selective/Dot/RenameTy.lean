import Coercions.Selective.Dot.Syntax

/-!
# Selective DOT: renaming of types

The equations of `Ty.rename` that every later module uses.
-/

namespace SelDot

open FCdot (Kind Sig BVar Rename Label)

@[simp] theorem Ty.rename_id (T : Ty s) : T.rename Rename.id = T := by
  induction T with
  | top | bot => rfl
  | typ _ _ _ ih1 ih2 => simp [Ty.rename, ih1, ih2]
  | fld _ _ ih => simp [Ty.rename, ih]
  | sel => simp [Ty.rename]
  | mu _ ih => simp [Ty.rename, Rename.lift_id, ih]
  | all _ _ ih1 ih2 => simp [Ty.rename, Rename.lift_id, ih1, ih2]
  | and _ _ ih1 ih2 => simp [Ty.rename, ih1, ih2]

theorem Ty.rename_comp (T : Ty s1) (ρ : Rename s1 s2) (τ : Rename s2 s3) :
    (T.rename ρ).rename τ = T.rename (ρ.comp τ) := by
  induction T generalizing s2 s3 with
  | top | bot => rfl
  | typ _ _ _ ih1 ih2 => simp [Ty.rename, ih1, ih2]
  | fld _ _ ih => simp [Ty.rename, ih]
  | sel => simp [Ty.rename]
  | mu _ ih => simp [Ty.rename, Rename.lift_comp, ih]
  | all _ _ ih1 ih2 => simp [Ty.rename, Rename.lift_comp, ih1, ih2]
  | and _ _ ih1 ih2 => simp [Ty.rename, ih1, ih2]

theorem Ty.weaken_rename (T : Ty s1) (ρ : Rename s1 s2) :
    T.weaken.rename (ρ.lift (k := .var)) = (T.rename ρ).weaken := by
  simp only [Ty.weaken, Ty.rename_comp, Rename.succ_lift]

theorem Ty.substVar_rename (T : Ty (s1,x)) (y : BVar s1 .var) (ρ : Rename s1 s2) :
    (T.substVar y).rename ρ = (T.rename ρ.lift).substVar (ρ.var y) := by
  simp only [Ty.substVar, Ty.rename_comp]
  congr 1
  apply Rename.funext'
  intro k z
  cases z <;> rfl

@[simp] theorem Ty.weaken_substVar (T : Ty s) (y : BVar s .var) :
    T.weaken.substVar y = T := by
  simp [Ty.weaken, Ty.substVar, Ty.rename_comp, Rename.succ_subst]

/-- Unfolding a weakened recursive type at the new self recovers its body. -/
@[simp] theorem Ty.open_self (T : Ty (s,x)) :
    (T.rename Rename.succ.lift).substVar .here = T := by
  simp only [Ty.substVar, Ty.rename_comp]
  have h : (Rename.succ.lift : Rename (s,x) ((s,x),x)).comp
      (Rename.subst .here) = Rename.id := by
    apply Rename.funext'
    intro k z
    cases z <;> rfl
  rw [h, Ty.rename_id]

end SelDot
