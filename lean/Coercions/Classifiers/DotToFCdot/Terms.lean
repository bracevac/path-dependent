import Coercions.Classifiers.DotToFCdot.Evidence

namespace Classifiers

/-!
# Translation of terms (Plan III §8.2, M4; stage A3a)

A typing derivation becomes an FCdot term with the same erasure.  Variables
become atoms (`HasTy.translateAtom`), subsumption becomes a cast, a
projection carries the presence evidence read off the receiver's
declaration and is cast from its block name to the declared field type by
the declaration's bound, and an object literal becomes a literal with the
witnesses of its declaration shape, each field cast from its translated type
to its block name by the literal's own definition equality, the whole cast
from the precise type to `⟦μ(x. S)⟧`.

A projection also carries a capture set: `proj` concludes `(x ∙ ℓ) ^ {x∙ℓ}`,
and the translation brings it to the field's *declared* set by the capture
entry `{self∙ℓ} ⊑ᶜ ⟦C⟧` of the declared telescope of a field, read at the
receiver by `member` in the capture sort.

Use sets are the other half of the stage.  The source now carries a use set
of its own, so a second function on derivations, `HasTy.translateUses`,
produces the capture evidence that the target's binders ask for.  It is typed
at `uses ⟦h⟧ ⊑ ⟦U⟧`.  A translated lambda declares the assigned set `⟦U⟧` of
its type and takes the body's evidence as its closing evidence, a translated
literal declares `⟦U⟧` and each field takes its body's evidence, a translated
let declares `⟦U⟧` and takes the body's evidence as its avoidance evidence,
and a translated unboxing declares `⟦U⟧` and takes the translated
subcapturing premise.  The stage A2 stand-ins `pureEvidence` and
`closingEvidence` are gone with the purity they assumed.
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-- Concatenation of fields.  The first argument is the outermost one: its
fields shadow, and `FCdot.Fields.labels` lists them first.  An intersection
is therefore translated with its *right* conjunct's fields first.  The right
conjunct shadows in DOT, and that is also the order of `Shape.fieldLabels`
and hence of the `has` entries of the literal's telescope, and of
`DotMNF.Defs.erase`. -/
def _root_.Classifiers.FCdot.Fields.append : FCdot.Fields s → FCdot.Fields s → FCdot.Fields s
  | .nil, F' => F'
  | .cons F ℓ t g, F' => .cons (F.append F') ℓ t g

/-- The body of a translated field: the translated term of the definition,
cast from its declared shape to the block name of its label by the literal's
own definition equality, and from its declared capture set to the capture
name of the same label by the literal's own capture definition.  This is what
the field rule of the target asks for, since a field is typed at
`(self ∙ a) ^ {self ∙ a}`. -/
def fieldBody (a : Label) (t : FCdot.Tm (s,x)) : FCdot.Tm (s,x) :=
  .cast t (.capt (.eqToLe (.symm (.def .here a))) (.eqToLe (.symm (.defC .here a))))

mutual

/-- `⟦h⟧ : ⟦T⟧`. -/
def HasTy.translate : {U : CaptureSet s} → {Γ : Ctx s} → {t : Tm s} → {E : ETy s} →
    HasTy U Γ t E → FCdot.Tm s
  | _, Γ, _, _, @HasTy.var _ _ x =>
      .atom (.plain (.recap (Γ.varAtom x) (.refl [FCdot.CapAtom.var x])))
  | _, _, _, _, @HasTy.lam _ _ U T1 _ _ h _ =>
      .val (.lam U.translate T1.translate h.translate h.translateUses)
  | _, _, _, _, .app h₁ h₂ => .app h₁.translateAtom h₂.translateAtom
  | _, _, _, _, @HasTy.obj _ _ U _ S hd _ =>
      .cast (.val (.obj U.translate S.witnesses S.capWitnesses hd.translateFields))
        ((litCo S).atC U.translate)
  | _, _, _, _, .box h => .val (.box h.translateAtom)
  | _, _, _, _, @HasTy.proj _ _ _ _ a T _ h =>
      .cast
        (.proj h.translateAtom a
          (.member h.translateAtom (.refl (Shape.fld a T).translate) 0))
        (.capt
          (.member h.translateAtom (.refl (Shape.fld a T).translate) 1)
          (.member h.translateAtom (.refl (Shape.fld a T).translate) 2))
  | _, _, _, _, @HasTy.let _ _ U _ _ _ _ h₁ h₂ _ =>
      .let h₁.translate h₂.translate U.translate h₂.translateUses
  | _, _, _, _, @HasTy.unbox _ _ U _ _ _ _ h f =>
      .unbox h.translateAtom U.translate f.translate
  | _, _, _, _, h@(.recI _ _) => .atom (.plain h.translateAtom)
  | _, _, _, _, h@(.recE _ _) => .atom (.plain h.translateAtom)
  | _, _, _, _, h@(.andI _ _) => .atom (.plain h.translateAtom)
  | _, _, _, _, @HasTy.letex _ _ _ U₂ _ _ _ _ _ h₁ f h₂ =>
      .letex h₁.translate h₂.translate U₂.translate f.translate h₂.translateUses
  | _, _, _, _, .sub h d _ => .castE h.translate d.translate

/-- `⟦h⟧ᵤ`, the source's own use-set evidence, read in the target: it puts the
use set of `⟦h⟧` below `⟦U⟧`.  On a derivation of a variable it puts `{x}`
below `⟦U⟧`, which is the same statement, since the use set of a translated
variable term is `{x}`. -/
def HasTy.translateUses : {U : CaptureSet s} → {Γ : Ctx s} → {t : Tm s} → {E : ETy s} →
    HasTy U Γ t E → FCdot.CapCo s
  | _, _, _, _, @HasTy.var _ _ x => .refl [FCdot.CapAtom.var x]
  | _, _, _, _, .lam _ _ => .refl []
  | _, _, _, _, .app h₁ h₂ => .union h₁.translateUses h₂.translateUses
  | _, _, _, _, .obj _ _ => .refl []
  | _, _, _, _, .box _ => .refl []
  | _, _, _, _, .proj h => h.translateUses
  | _, _, _, _, @HasTy.let _ _ U _ _ _ _ h₁ _ _ =>
      .union h₁.translateUses (.refl U.translate)
  | _, _, _, _, @HasTy.unbox _ _ U _ _ _ _ h _ =>
      .union h.translateUses (.refl U.translate)
  | _, _, _, _, .recI h _ => h.translateUses
  | _, _, _, _, .recE h _ => h.translateUses
  | _, _, _, _, .andI h₁ _ => h₁.translateUses
  | _, _, _, _, @HasTy.letex _ _ U₁ U₂ _ _ _ _ _ h₁ _ _ =>
      .union (.trans h₁.translateUses (.elem U₁.translate (U₁ ∪ U₂).translate))
        (.elem U₂.translate (U₁ ∪ U₂).translate)
  | _, _, _, _, .sub h _ f => .trans h.translateUses f.translate

/-- The fields of a literal, typed under its self binder: each field body is
cast to its block name and capture name by the literal's own definitions, and
its closing evidence is the body's own use-set evidence. -/
def DefsTy.translateFields : {U : CaptureSet (s,x)} → {Γ : Ctx (s,x)} → {d : Defs (s,x)} →
    {S : Shape (s,x)} → DefsTy U Γ d S → FCdot.Fields (s,x)
  | _, _, _, _, .typ => .nil
  | _, _, _, _, .cap => .nil
  | _, _, .trm a _, _, .trm h =>
      .cons .nil a (fieldBody a h.translate) h.translateUses
  | _, _, _, _, .and h₁ h₂ => h₂.translateFields.append h₁.translateFields

end

end DotMNF

end Classifiers
