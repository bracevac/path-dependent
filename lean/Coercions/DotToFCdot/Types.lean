import Coercions.DotMNF.Typing
import Coercions.FCdot.Context

/-!
# Translation of types (Plan III §8.1, M3)

Types translate homomorphically.  Declaration-shaped types become object
types over a fresh self block: a type member `{A : S..T}` is the pair of
propositions `⟦S⟧ ⊑ self∙A`, `self∙A ⊑ ⟦T⟧`; a field `{a : T}` is presence of
`a` together with `self∙a ⊑ ⟦T⟧`; an intersection concatenates; a recursive
type `μ(x. T)` binds its own self, identified with the block of the object.
`⊤` is the empty object type, so every declaration-shaped type, `⊤`
included, is `μ (tel T)`.

Two telescope functions: `tel T` reads a type over `s` as propositions about
a fresh self, `telSelf T` reads a type over `(s,x)` whose self is already the
innermost binder.  They agree on weakened types (`tel_eq_telSelf_weaken`).
-/

namespace FCdot

/-- Concatenation of witnesses (second appended after the first). -/
def Witnesses.append : Witnesses s → Witnesses s → Witnesses s
  | W, .nil => W
  | W, .cons W' ℓ T => .cons (W.append W') ℓ T

def Witnesses.length : Witnesses s → Nat
  | .nil => 0
  | .cons W _ _ => W.length + 1

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

mutual

/-- `⟦T⟧`. -/
def Ty.translate : Ty s → FCdot.Ty s
  | .top => FCdot.Ty.obj .nil
  | .bot => .bot
  | .sel (.var x) A => .sel x A
  | .all S T => .pi (Ty.translate S) (Ty.translate T)
  | .typ A S T => .obj (Ty.tel (.typ A S T))
  | .fld a T => .obj (Ty.tel (.fld a T))
  | .and S T => .obj (Ty.tel (.and S T))
  | .mu T => .obj (Ty.telSelf T)

/-- A type over `s` as propositions about a fresh self block. -/
def Ty.tel : Ty s → FCdot.Telescope (s,x)
  | .typ A S T =>
      .cons (.cons .nil (.le (Ty.translate S).weaken (.sel .here A)))
        (.le (.sel .here A) (Ty.translate T).weaken)
  | .fld a T => .cons (.cons .nil (.has a)) (.le (.sel .here a) (Ty.translate T).weaken)
  | .and S T => (Ty.tel S).append (Ty.tel T)
  | .mu T => Ty.telSelf T
  | _ => .nil

/-- A type over `(s,x)` whose self is the innermost binder, as propositions
about that binder. -/
def Ty.telSelf : Ty (s,x) → FCdot.Telescope (s,x)
  | .typ A S T =>
      .cons (.cons .nil (.le (Ty.translate S) (.sel .here A)))
        (.le (.sel .here A) (Ty.translate T))
  | .fld a T => .cons (.cons .nil (.has a)) (.le (.sel .here a) (Ty.translate T))
  | .and S T => (Ty.telSelf S).append (Ty.telSelf T)
  | .mu T => (Ty.telSelf T).substVar .here
  | _ => .nil

end

/-- The witnesses of a literal, read off its declaration type: the exact
bound of each type member and the declared type of each field. -/
def Ty.witnesses : Ty (s,x) → FCdot.Witnesses (s,x)
  | .typ A S _ => .cons .nil A S.translate
  | .fld a T => .cons .nil a T.translate
  | .and S T => S.witnesses.append T.witnesses
  | _ => .nil

/-- The field labels of a declaration type, newest (outermost) first.
`FCdot.Fields.labels` lists the outermost field first and `FCdot.Fields.get?`
lets the outermost field win, and in DOT the *right* conjunct of an
intersection shadows; so the right conjunct's fields are the outermost ones
of the translated literal and come first here.  This is the same convention
as `Ty.witnesses`, where `FCdot.Witnesses.append` puts the second argument's
witnesses outermost and `Witnesses.get` gives them priority. -/
def Ty.fieldLabels : Ty s → List Label
  | .fld a _ => [a]
  | .and S T => T.fieldLabels ++ S.fieldLabels
  | _ => []

/-- The precise target type of a literal whose declaration type is `T`. -/
def Ty.literalTy (T : Ty (s,x)) : FCdot.Ty s :=
  .obj (FCdot.Telescope.ofLiteral T.witnesses T.fieldLabels)

/-- Contexts translate binder by binder: an ordinary binder is opaque at its
translated type; a literal's self binder is transparent at the literal's
precise type. -/
def Ctx.translate : Ctx s → FCdot.Ctx s
  | .nil => .nil
  | .cons Γ T => .cons Γ.translate (.opaque T.translate)
  | .consSelf Γ _ T =>
      .cons Γ.translate (.transparent T.literalTy T.witnesses T.fieldLabels)

end DotMNF
