import Coercions.DotToFCdot.Evidence

/-!
# Translation of terms (Plan III §8.2, M4)

A typing derivation becomes an FCdot term with the same erasure.  Variables
become atoms (`HasTy.translateAtom`), subsumption becomes a cast, a
projection carries the presence evidence read off the receiver's
declaration and is cast from its block name to the declared field type by
the declaration's bound, and an object literal becomes a literal with the witnesses of
its declaration type, each field cast from its translated type to its block
name by the literal's own definition equality, the whole cast from the
precise type to `⟦μ(x. T)⟧`.
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-- Concatenation of fields.  The first argument is the outermost one: its
fields shadow, and `FCdot.Fields.labels` lists them first.  An intersection
is therefore translated with its *right* conjunct's fields first — the right
conjunct shadows in DOT, and that is also the order of `Ty.fieldLabels` (and
hence of the `has` entries of the literal's telescope) and of
`DotMNF.Defs.erase`. -/
def _root_.FCdot.Fields.append : FCdot.Fields s → FCdot.Fields s → FCdot.Fields s
  | .nil, F' => F'
  | .cons F ℓ t, F' => .cons (F.append F') ℓ t

mutual

/-- `⟦h⟧ : ⟦T⟧`. -/
def HasTy.translate : {Γ : Ctx s} → {t : Tm s} → {T : Ty s} → HasTy Γ t T → FCdot.Tm s
  | Γ, _, _, @HasTy.var _ _ x => .atom (Γ.varAtom x)
  | _, .val (.lam S _), _, .lam h _ => .val (.lam S.translate h.translate)
  | _, _, _, .app h₁ h₂ => .app h₁.translateAtom h₂.translateAtom
  | _, _, _, @HasTy.obj _ _ T _ h _ =>
      .cast (.val (.obj T.witnesses h.translateFields)) (litCo T)
  | _, .proj _ a, T, .proj h =>
      .cast (.proj h.translateAtom a (.member h.translateAtom (.refl (Ty.translate (.fld a T))) 0))
        (.member h.translateAtom (.refl (Ty.translate (.fld a T))) 1)
  | _, _, _, .let h₁ h₂ _ => .let h₁.translate h₂.translate
  | _, _, _, h@(.recI _ _) => .atom h.translateAtom
  | _, _, _, h@(.recE _ _) => .atom h.translateAtom
  | _, _, _, h@(.andI _ _ _ _) => .atom h.translateAtom
  | _, _, _, .sub h d => .cast h.translate d.translate

/-- The fields of a literal, typed under its self binder: each field body is
cast to its block name by the literal's definition equality. -/
def DefsTy.translateFields : {Γ : Ctx (s,x)} → {d : Defs (s,x)} → {T : Ty (s,x)} →
    DefsTy Γ d T → FCdot.Fields (s,x)
  | _, _, _, .typ => .nil
  | _, .trm a _, _, .trm h =>
      .cons .nil a (.cast h.translate (.eqToLe (.symm (.def .here a))))
  | _, _, _, .and h₁ h₂ => h₂.translateFields.append h₁.translateFields

end

end DotMNF
