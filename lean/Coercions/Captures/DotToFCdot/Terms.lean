import Coercions.Captures.DotToFCdot.Evidence

namespace Captures

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

Since stage A2 a projection also carries a capture set: `proj` concludes
`(x ∙ ℓ) ^ {x∙ℓ}`, and the translation brings it back to the pure `⟦T⟧ ^ {}`
by the capture entry `{self∙ℓ} ⊑ᶜ {}` that the declared telescope of a field
now has, read at the receiver by `member` in the capture sort.

Use sets and annotations are the other half of the stage.  Every binder of a
translated context is pure, so a translated term uses only term variables of
pure type: a translated let declares the use set `[]` with the avoidance
evidence `pureEvidence`, and a translated lambda and a translated literal
carry the assigned set `[]` with the closing evidence `closingEvidence`.  No
translated term unboxes.
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-- Concatenation of fields.  The first argument is the outermost one: its
fields shadow, and `FCdot.Fields.labels` lists them first.  An intersection
is therefore translated with its *right* conjunct's fields first — the right
conjunct shadows in DOT, and that is also the order of `Ty.fieldLabels` (and
hence of the `has` entries of the literal's telescope) and of
`DotMNF.Defs.erase`. -/
def _root_.Captures.FCdot.Fields.append : FCdot.Fields s → FCdot.Fields s → FCdot.Fields s
  | .nil, F' => F'
  | .cons F ℓ t g, F' => .cons (F.append F') ℓ t g

/-! ## Use sets of translated terms -/

/-- A capture set of term variables only.  The use set of a translated term
is one: `Tm.uses` reads roots of atoms, and the only other source of atoms is
a let's declared set, which the translation takes empty. -/
def _root_.Captures.FCdot.CaptureSet.AllVar : FCdot.CaptureSet s → Prop
  | [] => True
  | .var _ :: C => FCdot.CaptureSet.AllVar C
  | _ :: _ => False

/-- Evidence that a capture set of term variables is below the empty set.
Every binder of a translated context has a pure type, so each variable's own
capture set is empty (`capvar`), and the union of those inclusions is the
whole set.  A non-variable atom gets a syntactic inclusion that no context
accepts; `pureEvidence_typed` asks for `AllVar`. -/
def pureEvidence : FCdot.CaptureSet s → FCdot.CapCo s
  | [] => .refl []
  | .var x :: C => .union (.capvar (.var x)) (pureEvidence C)
  | a :: C => .union (.elem [a] []) (pureEvidence C)

/-- The closing evidence of a translated lambda body or of a translated
field: the body's use set is below the empty set, which is inside the
closing set of any assigned set. -/
def closingEvidence (A : FCdot.CaptureSet s) (t : FCdot.Tm (s,x)) : FCdot.CapCo (s,x) :=
  .trans (pureEvidence t.uses)
    (.elem [] (FCdot.CaptureSet.weaken A ∪ [FCdot.CapAtom.var .here]))

/-- The body of a translated field: the translated term of the definition,
cast from its declared type to the block name of its label by the literal's
own definition equality, and from the empty capture set to the capture name
of the same label, which is what the field rule of stage A2 asks for. -/
def fieldBody (a : Label) (t : FCdot.Tm (s,x)) : FCdot.Tm (s,x) :=
  .cast t (.capt (.eqToLe (.symm (.def .here a))) (.elem [] [FCdot.CapAtom.name .here a]))

mutual

/-- `⟦h⟧ : ⟦T⟧`. -/
def HasTy.translate : {Γ : Ctx s} → {t : Tm s} → {T : Ty s} → HasTy Γ t T → FCdot.Tm s
  | Γ, _, _, @HasTy.var _ _ x => .atom (Γ.varAtom x)
  | _, .val (.lam S _), _, .lam h _ =>
      .val (.lam [] S.translate h.translate (closingEvidence [] h.translate))
  | _, _, _, .app h₁ h₂ => .app h₁.translateAtom h₂.translateAtom
  | _, _, _, @HasTy.obj _ _ T _ h _ =>
      .cast (.val (.obj [] T.witnesses T.capWitnesses h.translateFields)) (litCo T).pure
  | _, .proj _ a, T, .proj h =>
      .cast
        (.proj h.translateAtom a
          (.member h.translateAtom (.refl (Ty.translateShape (.fld a T))) 0))
        (.capt
          (.member h.translateAtom (.refl (Ty.translateShape (.fld a T))) 1)
          (.member h.translateAtom (.refl (Ty.translateShape (.fld a T))) 2))
  | _, _, _, .let h₁ h₂ _ =>
      .let h₁.translate h₂.translate [] (pureEvidence h₂.translate.uses)
  | _, _, _, h@(.recI _ _) => .atom h.translateAtom
  | _, _, _, h@(.recE _ _) => .atom h.translateAtom
  | _, _, _, h@(.andI _ _) => .atom h.translateAtom
  | _, _, _, .sub h d => .cast h.translate d.translate

/-- The fields of a literal, typed under its self binder: each field body is
cast to its block name by the literal's definition equality. -/
def DefsTy.translateFields : {Γ : Ctx (s,x)} → {d : Defs (s,x)} → {T : Ty (s,x)} →
    DefsTy Γ d T → FCdot.Fields (s,x)
  | _, _, _, .typ => .nil
  | _, .trm a _, _, .trm h =>
      .cons .nil a (fieldBody a h.translate) (closingEvidence [] (fieldBody a h.translate))
  | _, _, _, .and h₁ h₂ => h₂.translateFields.append h₁.translateFields

end

end DotMNF

end Captures
