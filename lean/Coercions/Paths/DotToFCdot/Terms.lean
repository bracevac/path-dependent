import Coercions.Paths.DotToFCdot.Evidence

namespace Paths

/-!
# Translation of terms (Plan III §8.2, M4, and P2.4)

A typing derivation becomes an FCdot term with the same erasure.  Variables
become atoms (`HasTy.translateAtom`), subsumption becomes a cast, a
projection carries the presence evidence read off the receiver's
declaration and is cast from its block name to the declared field type by
the declaration's bound, and an object literal becomes a literal with the witnesses of
its declaration type, each field cast from its translated type to its block
name by the literal's own definition equality, the whole cast from the
precise type to `⟦μ(x. T)⟧`.

P2 adds three clauses and changes one.  `HasTy.sngl` gives the variable's
own atom under `Atom.sngl`.  `HasTy.projP` reads the presence and the bound
by `memberP` at the path image of the receiver, as `HasTy.proj` reads them
by `member` at its atom (decision 33).  A `let` at a singleton is the opaque
`let` (decision 32).  `DefsTy.translateFields` takes the self binder, the
self's type and the equality counter `e` as arguments, so that it is
structural (decision 31).  A `trm` field is cast by `EqCo.member` at `e`,
which eliminates, so the field is plain.  A `trmObj` field is the inner
literal under `litCo` and `EqCo.def`, both table-only, so the field is
stable (decision 26).
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-- Concatenation of fields.  The first argument is the outermost one: its
fields shadow, and `FCdot.Fields.labels` lists them first.  An intersection
is therefore translated with its *right* conjunct's fields first — the right
conjunct shadows in DOT, and that is also the order of `Ty.fieldLabels` (and
hence of the `has` entries of the literal's telescope) and of
`DotMNF.Defs.erase`. -/
def _root_.Paths.FCdot.Fields.append : FCdot.Fields s → FCdot.Fields s → FCdot.Fields s
  | .nil, F' => F'
  | .cons F ℓ t, F' => .cons (F.append F') ℓ t

mutual

/-- `⟦h⟧ : ⟦T⟧`. -/
def HasTy.translate : {Γ : Ctx s} → {t : Tm s} → {T : Ty s} → HasTy Γ t T → FCdot.Tm s
  | Γ, _, _, @HasTy.var _ _ x => .atom (Γ.varAtom x)
  | _, _, _, h@(.recI _ _) => .atom h.translateAtom
  | _, _, _, h@(.recE _ _) => .atom h.translateAtom
  | _, _, _, h@(.andI _ _) => .atom h.translateAtom
  | _, _, _, h@(.sngl _) => .atom h.translateAtom
  | _, .val (.lam S _), _, .lam h _ => .val (.lam S.translate h.translate)
  | _, _, _, .app h₁ h₂ => .app h₁.translateAtom h₂.translateAtom
  | _, _, _, HasTy.obj (T := T) h _ =>
      .cast (.val (.obj T.witnesses (h.translateFields .here T.literalTy.weaken 0))) (litCo T)
  | _, .proj _ a, T, .proj h =>
      .cast (.proj h.translateAtom a (.member h.translateAtom (.refl (Ty.translate (.fld a T))) 0))
        (.member h.translateAtom (.refl (Ty.translate (.fld a T))) 1)
  | Γ, .proj x a, T, .projP h =>
      .cast (.proj (Γ.varAtom x) a
          (.memberP h.translatePath (.refl (Ty.translate (.fld a T))) 0))
        (.memberP h.translatePath (.refl (Ty.translate (.fld a T))) 1)
  | _, _, _, .let h₁ h₂ _ => .let h₁.translate h₂.translate
  | _, _, _, .sub h d => .cast h.translate d.translate

/-- The fields of a literal under its self binder `self`.  `Tself` is the
self's type in the translated context, `T.literalTy.weaken` of the enclosing
literal.  `e` is the equality counter of decision 26: the position of the
field's `≐` entry in the self's precise telescope.  A `trm` field is cast by
`member` at `e`, which eliminates, so the field is plain.  A `trmObj` field
keeps `def`, which is table-only, so the field is stable. -/
def DefsTy.translateFields : {Γ : Ctx s} → {d : Defs s} → {T : Ty s} →
    DefsTy Γ d T → BVar s .var → FCdot.Ty s → Nat → FCdot.Fields s
  | _, _, _, .typ, _, _, _ => .nil
  | _, .trm a _, _, .trm h, self, Tself, e =>
      .cons .nil a (.cast h.translate
        (.eqToLe (.symm (.member (.var self) (.refl Tself) e))))
  | _, .trm a _, _, DefsTy.trmObj (T' := T') h _, self, _, _ =>
      .cons .nil a (.cast (.cast (.val (.obj T'.witnesses
          (h.translateFields .here T'.literalTy.weaken 0)))
        (litCo T')) (.eqToLe (.symm (.def self a))))
  | _, _, _, DefsTy.and (T1 := T₁) h₁ h₂, self, Tself, e =>
      FCdot.Fields.append (h₂.translateFields self Tself (e + T₁.witnesses.length))
        (h₁.translateFields self Tself e)

end

end DotMNF

end Paths
