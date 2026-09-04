import Coercions.DotToFCdot.Terms
import Coercions.DotToFCdot.EvidenceTyped
import Coercions.FCdot.Erasure
import Coercions.DotMNF.Erasure

/-!
# Erasure of the term translation (Plan III §8.2, M4)

`HasTy.translate` erases (into the shared runtime) to the same term as the
source DOT-MNF typing derivation: types, evidence, and cast frames vanish
under `FCdot.Tm.erase`, and what is left is exactly the source term with
paths reduced to their root variable, which is what `DotMNF.Tm.erase`
produces directly.  The two typing derivations of the same term therefore
translate to observationally identical target terms (`coherence`).
-/

namespace FCdot

open scoped FCdot

/-- Appending fields commutes with erasure, with the arguments swapped:
`FCdot.Fields.append` recurses on its *first* argument, which ends up
outermost, while `DotMNF.appendFields` recurses on its *second*. -/
theorem Fields.append_erase {s : Sig} (F G : FCdot.Fields s) :
    (F.append G).erase = DotMNF.appendFields G.erase F.erase := by
  match F with
  | .nil => rfl
  | .cons F ℓ t => simp only [FCdot.Fields.append, Fields.erase, DotMNF.appendFields,
      Fields.append_erase F G]

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)
open scoped FCdot

mutual

/-- Erasure of the translation of a typing derivation is the source term's
own erasure. -/
theorem HasTy.translate_erase : {Γ : Ctx s} → {t : Tm s} → {T : Ty s} →
    (h : HasTy Γ t T) → ⌊h.translate⌋ = Tm.erase t
  | Γ, _, _, @HasTy.var _ _ x => by
      simp only [HasTy.translate, FCdot.Tm.erase, Ctx.varAtom_root Γ x, Tm.erase, Path.root]
  | _, .val (.lam S _), _, .lam h _ => by
      simp only [HasTy.translate, FCdot.Tm.erase, FCdot.Value.erase, Tm.erase, Value.erase,
        HasTy.translate_erase h]
  | _, _, _, .app h₁ h₂ => by
      simp only [HasTy.translate, FCdot.Tm.erase, Tm.erase,
        HasTy.translateAtom_root h₁, HasTy.translateAtom_root h₂]
  | _, _, _, @HasTy.obj _ _ _ _ h _ _ _ => by
      simp only [HasTy.translate, FCdot.Tm.erase, FCdot.Value.erase, Tm.erase, Value.erase,
        DefsTy.translateFields_erase h]
  | _, .proj _ a, T, .proj h => by
      simp only [HasTy.translate, FCdot.Tm.erase, Tm.erase, HasTy.translateAtom_root h]
  | _, _, _, .let h₁ h₂ _ => by
      simp only [HasTy.translate, FCdot.Tm.erase, Tm.erase,
        HasTy.translate_erase h₁, HasTy.translate_erase h₂]
  | _, _, _, .recI h₁ h₂ => by
      simp only [HasTy.translate, FCdot.Tm.erase, Tm.erase, Path.root,
        HasTy.translateAtom_root (.recI h₁ h₂)]
  | _, _, _, .recE h₁ h₂ => by
      simp only [HasTy.translate, FCdot.Tm.erase, Tm.erase, Path.root,
        HasTy.translateAtom_root (.recE h₁ h₂)]
  | _, _, _, .andI h₁ h₂ h₃ h₄ => by
      simp only [HasTy.translate, FCdot.Tm.erase, Tm.erase, Path.root,
        HasTy.translateAtom_root (.andI h₁ h₂ h₃ h₄)]
  | _, _, _, .sub h _ => by
      simp only [HasTy.translate, FCdot.Tm.erase, HasTy.translate_erase h]

/-- Erasure of the translated fields of a literal is the source definition
list's own erasure. -/
theorem DefsTy.translateFields_erase : {Γ : Ctx (s,x)} → {d : Defs (s,x)} → {T : Ty (s,x)} →
    (h : DefsTy Γ d T) → h.translateFields.erase = Defs.erase d
  | _, _, _, .typ => by simp only [DefsTy.translateFields, FCdot.Fields.erase, Defs.erase]
  | _, .trm a _, _, .trm h => by
      simp only [DefsTy.translateFields, FCdot.Fields.erase, FCdot.Tm.erase, Defs.erase,
        HasTy.translate_erase h]
  | _, _, _, .and h₁ h₂ => by
      simp only [DefsTy.translateFields, FCdot.Fields.append_erase, Defs.erase,
        DefsTy.translateFields_erase h₁, DefsTy.translateFields_erase h₂]

end

/-- The two typing derivations of the same term translate to target terms
with the same runtime observation. -/
theorem coherence {Γ : Ctx s} {t : Tm s} {T₁ T₂ : Ty s} (d₁ : HasTy Γ t T₁) (d₂ : HasTy Γ t T₂) :
    ⌊d₁.translate⌋ = ⌊d₂.translate⌋ := by
  rw [HasTy.translate_erase d₁, HasTy.translate_erase d₂]

end DotMNF
