import Coercions.CapturesCC.DotToFCdot.Terms
import Coercions.CapturesCC.DotToFCdot.EvidenceTyped
import Coercions.CapturesCC.FCdot.Erasure
import Coercions.CapturesCC.DotMNF.Erasure

namespace CapturesCC

/-!
# Erasure of the term translation (Plan III §8.2, M4; stage A3a)

`HasTy.translate` erases (into the shared runtime) to the same term as the
source DOT-MNF typing derivation: types, evidence, annotations, use sets and
cast frames vanish under `FCdot.Tm.erase`, and what is left is exactly the
source term with paths reduced to their root variable, which is what
`DotMNF.Tm.erase` produces directly.  The two typing derivations of the same
term therefore translate to observationally identical target terms
(`coherence`).

Stage A3a adds two clauses.  A source box `□ x` erases to the runtime's own
inert box at `x`, and so does the target box its translation is; a source
unboxing `C ⊸ x` erases to the runtime's unboxing at `x`, and so does the
target unboxing.  Both clauses close once the atom's root is read
(`HasTy.translateAtom_root`).
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
  | .cons F ℓ t g => simp only [FCdot.Fields.append, Fields.erase, DotMNF.appendFields,
      Fields.append_erase F G]

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)
open scoped FCdot

mutual

/-- Erasure of the translation of a typing derivation is the source term's
own erasure. -/
theorem HasTy.translate_erase : {U : CaptureSet s} → {Γ : Ctx s} → {t : Tm s} → {E : ETy s} →
    (h : HasTy U Γ t E) → ⌊h.translate⌋ = Tm.erase t
  | _, Γ, _, _, @HasTy.var _ _ x => by
      simp only [HasTy.translate, FCdot.Tm.erase, FCdot.PAtom.root_plain, FCdot.Atom.root,
        Ctx.varAtom_root Γ x, Tm.erase, Path.root]
  | _, _, .val (.lam S _), _, .lam h _ => by
      simp only [HasTy.translate, FCdot.Tm.erase, FCdot.Value.erase, Tm.erase, Value.erase,
        HasTy.translate_erase h]
  | _, _, _, _, .app h₁ h₂ => by
      simp only [HasTy.translate, FCdot.Tm.erase, Tm.erase,
        HasTy.translateAtom_root h₁, HasTy.translateAtom_root h₂]
  | _, _, _, _, @HasTy.obj _ _ _ _ _ h _ => by
      simp only [HasTy.translate, FCdot.Tm.erase, FCdot.Value.erase, Tm.erase, Value.erase,
        DefsTy.translateFields_erase h]
  | _, _, _, _, .box h => by
      simp only [HasTy.translate, FCdot.Tm.erase, FCdot.Value.erase, Tm.erase, Value.erase,
        HasTy.translateAtom_root h]
  | _, _, .proj _ a, _, .proj h => by
      simp only [HasTy.translate, FCdot.Tm.erase, Tm.erase, HasTy.translateAtom_root h]
  | _, _, _, _, .let h₁ h₂ _ => by
      simp only [HasTy.translate, FCdot.Tm.erase, Tm.erase,
        HasTy.translate_erase h₁, HasTy.translate_erase h₂]
  | _, _, _, _, .unbox h _ => by
      simp only [HasTy.translate, FCdot.Tm.erase, Tm.erase,
        HasTy.translateAtom_root h]
  | _, _, _, _, .recI h₁ h₂ => by
      simp only [HasTy.translate, FCdot.Tm.erase, Tm.erase, Path.root,
        FCdot.PAtom.root_plain, HasTy.translateAtom_root (.recI h₁ h₂)]
  | _, _, _, _, .recE h₁ h₂ => by
      simp only [HasTy.translate, FCdot.Tm.erase, Tm.erase, Path.root,
        FCdot.PAtom.root_plain, HasTy.translateAtom_root (.recE h₁ h₂)]
  | _, _, _, _, .andI h₁ h₂ => by
      simp only [HasTy.translate, FCdot.Tm.erase, Tm.erase, Path.root,
        FCdot.PAtom.root_plain, HasTy.translateAtom_root (.andI h₁ h₂)]
  | _, _, _, _, .letex h₁ _ h₂ => by
      simp only [HasTy.translate, FCdot.Tm.erase, Tm.erase,
        HasTy.translate_erase h₁, HasTy.translate_erase h₂]
  | _, _, _, _, .sub h _ _ => by
      simp only [HasTy.translate, FCdot.Tm.erase, HasTy.translate_erase h]

/-- Erasure of the translated fields of a literal is the source definition
list's own erasure.  A capture member contributes no field, as a type member
does not. -/
theorem DefsTy.translateFields_erase : {U : CaptureSet (s,x)} → {Γ : Ctx (s,x)} →
    {d : Defs (s,x)} → {S : Shape (s,x)} →
    (h : DefsTy U Γ d S) → h.translateFields.erase = Defs.erase d
  | _, _, _, _, .typ => by simp only [DefsTy.translateFields, FCdot.Fields.erase, Defs.erase]
  | _, _, _, _, .cap => by simp only [DefsTy.translateFields, FCdot.Fields.erase, Defs.erase]
  | _, _, .trm a _, _, .trm h => by
      simp only [DefsTy.translateFields, FCdot.Fields.erase, fieldBody, FCdot.Tm.erase,
        Defs.erase, HasTy.translate_erase h]
  | _, _, _, _, .and h₁ h₂ => by
      simp only [DefsTy.translateFields, FCdot.Fields.append_erase, Defs.erase,
        DefsTy.translateFields_erase h₁, DefsTy.translateFields_erase h₂]

end

/-- The two typing derivations of the same term translate to target terms
with the same runtime observation. -/
theorem coherence {U₁ U₂ : CaptureSet s} {Γ : Ctx s} {t : Tm s} {E₁ E₂ : ETy s}
    (d₁ : HasTy U₁ Γ t E₁) (d₂ : HasTy U₂ Γ t E₂) :
    ⌊d₁.translate⌋ = ⌊d₂.translate⌋ := by
  rw [HasTy.translate_erase d₁, HasTy.translate_erase d₂]

end DotMNF

end CapturesCC
