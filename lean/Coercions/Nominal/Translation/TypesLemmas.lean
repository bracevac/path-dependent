import Coercions.Nominal.Translation.Types
import Coercions.Nominal.Source.Programs
import Coercions.Nominal.Source.Examples

/-!
# Laws of the type translation (plan X, Part TR.2, stage X6 group g1)

The translation commutes with renaming and with path substitution, at every variable.  `⟦·⟧` reads
no variable as a self.  Only `tel` does, and `Ty.telAt_subst` moves a substitution that sends the
self to a variable.  `Ty.translate_subst` and its four companions are one mutual block, structural
on the type.  `Ty.translate_rename`, `Ty.translate_weaken` and `Ty.translate_substPath` are its
corollaries.

The fold.  `Ty.tel_fold` is the plan's `tel_fold`, `(tel⁺ (T⟨p⟩))⟨p⟩ = (tel T)⟨p⟩` for
`T : Ty (s,z)`.  It is `Ty.telP_subst_substPath` at `PathSubst.one p` with the self `.here`.  It is
the equation the fold after unfold of `ty_rec_intro` and `ty_rec_elim` reads, as in the Paths line
(`Paths/DotToFCdot/Evidence.lean:286-288`).  The equation `tel (T⟨p⟩) = (tel T)⟨p⟩` of
`design-d3.md:637` is false.  `tel_open_ne` restates it at `{A : ⊤..⊤}` and refutes it by `decide`.

The examples run the translation in the kernel on E3's types (`Source/Programs.lean:251-307`).
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-- A tel-like type translates to the object type over its `tel⁺`. -/
theorem Ty.translate_of_telLike : ∀ {T : Ty s}, T.telLike = true → T.translate = .mu T.telP
  | .top, _ => rfl
  | .rcd _, _ => rfl
  | .and _ _, _ => rfl

/-- Any other type contributes the one proposition `is ⟦T⟧↑` under a fresh self. -/
theorem Ty.telP_of_not_telLike : ∀ {T : Ty s}, T.telLike = false → T.telP = .cons .nil (.is T.translate.weaken)
  | .bot, _ => rfl
  | .sel _ _, _ => rfl
  | .mu _, _ => rfl
  | .all _ _, _ => rfl
  | .sngl _, _ => rfl

/-- Any other type contributes the one proposition `is ⟦T⟧` at any self. -/
theorem Ty.telAt_of_not_telLike (self : BVar s .var) : ∀ {T : Ty s}, T.telLike = false → T.telAt self = .cons .nil (.is T.translate)
  | .bot, _ => rfl
  | .sel _ _, _ => rfl
  | .mu _, _ => rfl
  | .all _ _, _ => rfl
  | .sngl _, _ => rfl

/-- Path substitution keeps the head constructor, so it keeps tel-likeness. -/
theorem Ty.telLike_subst : ∀ (T : Ty s₁) (σ : PathSubst s₁ s₂), (T.subst σ).telLike = T.telLike
  | .top, _ => rfl | .bot, _ => rfl | .rcd _, _ => rfl | .and _ _, _ => rfl
  | .sel _ _, _ => rfl | .mu _, _ => rfl | .all _ _, _ => rfl | .sngl _, _ => rfl

/-- Renaming keeps the head constructor, so it keeps tel-likeness. -/
theorem Ty.telLike_rename : ∀ (T : Ty s₁) (ρ : Rename s₁ s₂), (T.rename ρ).telLike = T.telLike
  | .top, _ => rfl | .bot, _ => rfl | .rcd _, _ => rfl | .and _ _, _ => rfl
  | .sel _ _, _ => rfl | .mu _, _ => rfl | .all _ _, _ => rfl | .sngl _, _ => rfl

-- one mutual block, structural on the type
mutual
/-- The translation commutes with path substitution, at every variable. -/
theorem Ty.translate_subst : ∀ (T : Ty s₁) (σ : PathSubst s₁ s₂), (T.subst σ).translate = T.translate.subst σ
  | .top, _ => rfl
  | .bot, _ => rfl
  | .rcd D, σ => by
      show FCn.Ty.mu (D.subst σ).telP = FCn.Ty.mu (D.telP.subst σ.lift)
      rw [Dec.telP_subst D σ]
  | .and T U, σ => by
      show FCn.Ty.mu ((T.subst σ).telP ++ (U.subst σ).telP) = FCn.Ty.mu ((T.telP ++ U.telP).subst σ.lift)
      rw [Ty.telP_subst T σ, Ty.telP_subst U σ, FCn.Telescope.append_subst]
  | .sel p A, σ => rfl
  | .mu T, σ => by
      show FCn.Ty.mu ((T.subst σ.lift).telAt .here) = FCn.Ty.mu ((T.telAt .here).subst σ.lift)
      rw [Ty.telAt_subst T σ.lift .here .here rfl]
  | .all S T, σ => by
      show FCn.Ty.pi (S.subst σ).translate (T.subst σ.lift).translate = FCn.Ty.pi (S.translate.subst σ) (T.translate.subst σ.lift)
      rw [Ty.translate_subst S σ, Ty.translate_subst T σ.lift]
  | .sngl p, σ => (FCn.Ty.sngl_subst p σ).symm
/-- `tel⁺ {D}` commutes with path substitution, lifted over the fresh self. -/
theorem Dec.telP_subst : ∀ (D : Dec s₁) (σ : PathSubst s₁ s₂), (D.subst σ).telP = D.telP.subst σ.lift
  | .typ A S U, σ => by
      simp only [Dec.subst, Dec.telP, Ty.translate_subst S σ, Ty.translate_subst U σ, FCn.Telescope.subst,
        FCn.Pr.subst, FCn.Ty.subst, FCn.Ty.weaken_subst_lift]
      rfl
  | .trm a T, σ => by
      simp only [Dec.subst, Dec.telP, Ty.translate_subst T σ, FCn.Telescope.subst, FCn.Pr.subst,
        FCn.Ty.weaken_subst_lift]
/-- `tel⁺ T` commutes with path substitution, lifted over the fresh self. -/
theorem Ty.telP_subst : ∀ (T : Ty s₁) (σ : PathSubst s₁ s₂), (T.subst σ).telP = T.telP.subst σ.lift
  | .top, _ => rfl
  | .rcd D, σ => Dec.telP_subst D σ
  | .and T U, σ => by
      show (T.subst σ).telP ++ (U.subst σ).telP = (T.telP ++ U.telP).subst σ.lift
      rw [Ty.telP_subst T σ, Ty.telP_subst U σ, FCn.Telescope.append_subst]
  | .bot, σ => rfl
  | .sel p A, σ => by
      simp only [Ty.subst, Ty.telP, FCn.Telescope.subst, FCn.Pr.subst, FCn.Ty.weaken_subst_lift, FCn.Ty.subst]
  | .mu T, σ => by
      simp only [Ty.subst, Ty.telP, FCn.Telescope.subst, FCn.Pr.subst, FCn.Ty.weaken_subst_lift, FCn.Ty.subst,
        Ty.telAt_subst T σ.lift .here .here rfl]
  | .all S T, σ => by
      simp only [Ty.subst, Ty.telP, FCn.Telescope.subst, FCn.Pr.subst, FCn.Ty.weaken_subst_lift, FCn.Ty.subst,
        Ty.translate_subst S σ, Ty.translate_subst T σ.lift]
  | .sngl p, σ => by
      simp only [Ty.subst, Ty.telP, FCn.Telescope.subst, FCn.Pr.subst, FCn.Ty.weaken_subst_lift, FCn.Ty.sngl_subst]
/-- `tel {D}` at the self `self` commutes with a path substitution that sends `self` to the variable
`self'`. -/
theorem Dec.telAt_subst : ∀ (D : Dec s₁) (σ : PathSubst s₁ s₂) (self : BVar s₁ .var) (self' : BVar s₂ .var),
    σ.var self = .var self' → (D.subst σ).telAt self' = (D.telAt self).subst σ
  | .typ A S U, σ, self, self', h => by
      simp only [Dec.subst, Dec.telAt, Ty.translate_subst S σ, Ty.translate_subst U σ, FCn.Telescope.subst,
        FCn.Pr.subst, FCn.Ty.subst, Path.subst, h]
  | .trm a T, σ, _, _, _ => by
      show FCn.Telescope.cons .nil (.fld a (T.subst σ).translate) = _
      rw [Ty.translate_subst T σ]; rfl
/-- `tel T` at the self `self` commutes with a path substitution that sends `self` to the variable
`self'`. -/
theorem Ty.telAt_subst : ∀ (T : Ty s₁) (σ : PathSubst s₁ s₂) (self : BVar s₁ .var) (self' : BVar s₂ .var),
    σ.var self = .var self' → (T.subst σ).telAt self' = (T.telAt self).subst σ
  | .top, _, _, _, _ => rfl
  | .rcd D, σ, self, self', h => Dec.telAt_subst D σ self self' h
  | .and T U, σ, self, self', h => by
      show (T.subst σ).telAt self' ++ (U.subst σ).telAt self' = (T.telAt self ++ U.telAt self).subst σ
      rw [Ty.telAt_subst T σ self self' h, Ty.telAt_subst U σ self self' h, FCn.Telescope.append_subst]
  | .bot, _, _, _, _ => rfl
  | .sel p A, _, _, _, _ => rfl
  | .mu T, σ, _, _, _ => by
      simp only [Ty.subst, Ty.telAt, FCn.Telescope.subst, FCn.Pr.subst, FCn.Ty.subst, Ty.telAt_subst T σ.lift .here .here rfl]
  | .all S T, σ, _, _, _ => by
      simp only [Ty.subst, Ty.telAt, FCn.Telescope.subst, FCn.Pr.subst, FCn.Ty.subst, Ty.translate_subst S σ,
        Ty.translate_subst T σ.lift]
  | .sngl p, σ, _, _, _ => by
      simp only [Ty.subst, Ty.telAt, FCn.Telescope.subst, FCn.Pr.subst, FCn.Ty.sngl_subst]
end
-- end of the block

/-- The plan's `translate_rename`: the translation commutes with renaming. -/
theorem Ty.translate_rename (T : Ty s₁) (ρ : Rename s₁ s₂) : (T.rename ρ).translate = T.translate.rename ρ := by
  rw [← Ty.subst_ofRename, Ty.translate_subst, FCn.Ty.subst_ofRename]

/-- `tel⁺ T` commutes with renaming, lifted over the fresh self. -/
theorem Ty.telP_rename (T : Ty s₁) (ρ : Rename s₁ s₂) : (T.rename ρ).telP = T.telP.rename ρ.lift := by
  rw [← Ty.subst_ofRename, Ty.telP_subst, PathSubst.lift_ofRename, FCn.Telescope.subst_ofRename]

/-- `tel T` commutes with renaming, with the self renamed too. -/
theorem Ty.telAt_rename (T : Ty s₁) (ρ : Rename s₁ s₂) (self : BVar s₁ .var) :
    (T.rename ρ).telAt (ρ.var self) = (T.telAt self).rename ρ := by
  rw [← Ty.subst_ofRename, Ty.telAt_subst T _ self (ρ.var self) rfl, FCn.Telescope.subst_ofRename]

/-- The translation commutes with weakening. -/
theorem Ty.translate_weaken (T : Ty s) : T.weaken.translate = T.translate.weaken := Ty.translate_rename T Rename.succ

/-- The plan's `translate_substPath`, `⟦T⟨p⟩⟧ = ⟦T⟧⟨p⟩`. -/
theorem Ty.translate_substPath (T : Ty (s,x)) (p : Path s) : (T.substPath p).translate = T.translate.substPath p :=
  Ty.translate_subst T (PathSubst.one p)

/-- Weakening under the newest variable, then opening at that variable, is the identity on a
telescope. -/
theorem _root_.Nominal.Translation.rename_succ_lift_substPath_here (Tel : FCn.Telescope (s,x)) :
    (Tel.rename (Rename.succ (k := .var)).lift).substPath (.var .here) = Tel := by
  rw [FCn.Telescope.substPath, FCn.Telescope.rename_subst]
  have : (Rename.succ (s := s) (k := .var)).lift.pathComp (PathSubst.one (.var .here)) = PathSubst.ofRename Rename.id := by
    apply PathSubst.funext'; intro y; rcases y with _ | y <;> rfl
  rw [this, FCn.Telescope.subst_ofRename, FCn.Telescope.rename_id]

-- two theorems, not a mutual block, Dec's first and Ty's calling it at .rcd:
-- the fold, every self read at the path it is opened at

/-- The fold at a declaration: `tel⁺` of a substituted declaration, opened at the path `q` that the
self is sent to, is the substituted `tel` at that self. -/
theorem Dec.telP_subst_substPath : ∀ (D : Dec s₁) (σ : PathSubst s₁ s₂) (self : BVar s₁ .var) (q : Path s₂),
    σ.var self = q → (D.subst σ).telP.substPath q = (D.telAt self).subst σ
  | .typ A S U, σ, self, q, h => by
      simp only [Dec.subst, Dec.telP, Dec.telAt, FCn.Telescope.substPath, FCn.Telescope.subst, FCn.Pr.subst,
        FCn.Ty.subst, Path.subst, h, Ty.translate_subst S σ, Ty.translate_subst U σ]
      rw [← FCn.Ty.substPath, FCn.Ty.weaken_substPath, ← FCn.Ty.substPath, FCn.Ty.weaken_substPath]
      rfl
  | .trm a T, σ, self, q, h => by
      simp only [Dec.subst, Dec.telP, Dec.telAt, FCn.Telescope.substPath, FCn.Telescope.subst, FCn.Pr.subst,
        Ty.translate_subst T σ]
      rw [← FCn.Ty.substPath, FCn.Ty.weaken_substPath]

/-- The fold at a type: `tel⁺` of a substituted type, opened at the path `q` that the self is sent
to, is the substituted `tel` at that self.  Every self is read at the path it is opened at. -/
theorem Ty.telP_subst_substPath : ∀ (T : Ty s₁) (σ : PathSubst s₁ s₂) (self : BVar s₁ .var) (q : Path s₂),
    σ.var self = q → (T.subst σ).telP.substPath q = (T.telAt self).subst σ
  | .top, _, _, _, _ => rfl
  | .rcd D, σ, self, q, h => Dec.telP_subst_substPath D σ self q h
  | .and T U, σ, self, q, h => by
      show ((T.subst σ).telP ++ (U.subst σ).telP).subst (PathSubst.one q) = (T.telAt self ++ U.telAt self).subst σ
      rw [FCn.Telescope.append_subst, FCn.Telescope.append_subst, ← FCn.Telescope.substPath, ← FCn.Telescope.substPath,
        Ty.telP_subst_substPath T σ self q h, Ty.telP_subst_substPath U σ self q h]
  | .bot, _, _, _, _ => rfl
  | .sel p A, σ, self, q, h => by
      simp only [Ty.subst, Ty.telP, Ty.telAt, FCn.Telescope.substPath, FCn.Telescope.subst, FCn.Pr.subst]
      rw [← FCn.Ty.substPath, FCn.Ty.weaken_substPath]; rfl
  | .mu T, σ, self, q, h => by
      have e := Ty.translate_subst (.mu T) σ
      simp only [Ty.subst, Ty.telP, Ty.telAt, FCn.Telescope.substPath, FCn.Telescope.subst, FCn.Pr.subst]
      rw [← FCn.Ty.substPath, FCn.Ty.weaken_substPath]
      exact congrArg (fun X => FCn.Telescope.cons .nil (.is X)) e
  | .all S T, σ, self, q, h => by
      have e := Ty.translate_subst (.all S T) σ
      simp only [Ty.subst, Ty.telP, Ty.telAt, FCn.Telescope.substPath, FCn.Telescope.subst, FCn.Pr.subst]
      rw [← FCn.Ty.substPath, FCn.Ty.weaken_substPath]
      exact congrArg (fun X => FCn.Telescope.cons .nil (.is X)) e
  | .sngl p, σ, self, q, h => by
      have e := Ty.translate_subst (.sngl p) σ
      simp only [Ty.subst, Ty.telP, Ty.telAt, FCn.Telescope.substPath, FCn.Telescope.subst, FCn.Pr.subst]
      rw [← FCn.Ty.substPath, FCn.Ty.weaken_substPath]
      exact congrArg (fun X => FCn.Telescope.cons .nil (.is X)) e

/-- The plan's `tel_fold`: `(tel⁺ (T⟨p⟩))⟨p⟩ = (tel T)⟨p⟩` for `T : Ty (s,z)`.  It is the equation
the fold after unfold needs. -/
theorem Ty.tel_fold (T : Ty (s,x)) (p : Path s) : (T.substPath p).telP.substPath p = T.tel.substPath p :=
  Ty.telP_subst_substPath T (PathSubst.one p) .here p rfl

/-- `tel T` commutes with a substitution lifted over its self. -/
theorem Ty.tel_subst_lift (T : Ty (s₁,x)) (σ : PathSubst s₁ s₂) : (T.subst σ.lift).tel = T.tel.subst σ.lift :=
  Ty.telAt_subst T σ.lift .here .here rfl

/-- The plan's definition of `tel⁺`, `tel⁺ T = tel (T↑)`, as a theorem. -/
theorem Ty.telP_eq_tel_weaken (T : Ty s) : T.telP = T.weaken.tel := by
  have h := Ty.telP_subst_substPath T.weaken (PathSubst.ofRename Rename.id) .here (.var .here) rfl
  rw [Ty.subst_ofRename, Ty.rename_id, FCn.Telescope.subst_ofRename, FCn.Telescope.rename_id, Ty.weaken,
    Ty.telP_rename, Translation.rename_succ_lift_substPath_here] at h
  exact h

/-- E3: the kernel translates the type of `TpeImpl`, a recursive type whose body is a record. -/
theorem E3_tpeImpl_translate :
    (cp_TpeImpl (s := [])).translate = FCn.Ty.mu (.cons .nil (.fld cp_denotation (.pi (.mu .nil) (.mu .nil)))) := by
  decide +kernel

/-- E3: the kernel translates the compiler's type to the object type over `tel` of its body. -/
theorem E3_translate_kernel : compiler_T.translate = FCn.Ty.mu (cp_rT (s := [])).tel := by decide +kernel

/-- E3: `translate_substPath` at the tight `DottyCore` package, evaluated by the kernel. -/
theorem E3_translate_substPath_kernel :
    ((cp_DottyCoreTight (s := ([],x))).substPath (.var .here)).translate =
      (cp_DottyCoreTight (s := ([],x))).translate.substPath (.var .here) := by decide +kernel

/-- E3: `tel_fold` at the tight `DottyCore` package, evaluated by the kernel. -/
theorem E3_tel_fold_kernel :
    ((cp_DottyCoreTight (s := ([],x))).substPath (.var .here)).telP.substPath (.var .here) =
      (cp_DottyCoreTight (s := ([],x))).tel.substPath (.var .here) := by decide +kernel

-- g1: the equation of design-d3.md:637 (RefuteD2.lean:1430-1436) is false at {A : ⊤..⊤}

/-- The type label `A` of the counterexample. -/
abbrev j2_A : Label := .typ 0

/-- `{A : ⊤..⊤}`, under `([],z)` then the self `w`. -/
abbrev j2_T : Ty (([],x),x) := .rcd (.typ j2_A .top .top)                       -- {A : ⊤..⊤}, under ([],z) then w

/-- The path `z` the counterexample opens at. -/
abbrev j2_p : Path ([],x) := .var .here                                         -- z

/-- The equation `tel (T⟨p⟩) = (tel T)⟨p⟩` of `design-d3.md:637`, read under a fresh self, is false
at `{A : ⊤..⊤}`.  `Ty.tel_fold` is the true equation. -/
theorem tel_open_ne : (j2_T.tel.substPath j2_p).weaken ≠ (j2_T.substPath j2_p).telP := by decide

end Nominal.Source
