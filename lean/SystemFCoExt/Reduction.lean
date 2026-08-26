import SystemFCoExt.Typing

/-!
# Call-by-value dynamics for explicit directed coercions

Coercions and casts are explicit administrative syntax in this target.
Reduction inspects coercion constructors and pushes structural casts through
their matching eliminators. A separate operational-correspondence theorem is
therefore required before claiming that this syntax can be erased.
-/

namespace SystemFCoExt
namespace Exp

/-- Values and coercion wrappers waiting for the matching eliminator. -/
inductive IsValue : Exp sig -> Prop where
| abs : IsValue (.abs parameter body)
| tabs : IsValue (.tabs body)
| cabs : IsValue (.cabs source target body)
| castTop : IsValue expression -> IsValue (.cast expression (.top source))
| castArrow : IsValue expression ->
    IsValue (.cast expression (.arrow parameter result))
| castPoly : IsValue expression -> IsValue (.cast expression (.poly body))
| castQual : IsValue expression ->
    IsValue (.cast expression (.qual argument result))

/-- Weak left-to-right call-by-value reduction. -/
inductive Step : Exp sig -> Exp sig -> Prop where
| appFunction : Step function function' ->
    Step (.app function argument) (.app function' argument)
| appArgument : IsValue function -> Step argument argument' ->
    Step (.app function argument) (.app function argument')
| beta : IsValue argument ->
    Step (.app (.abs parameter body) argument)
      (body.subst (Subst.openVar argument))
| tappFunction : Step function function' ->
    Step (.tapp function argument) (.tapp function' argument)
| typeBeta :
    Step (.tapp (.tabs body) argument)
      (body.subst (Subst.openTVar argument))
| cappFunction : Step function function' ->
    Step (.capp function argument) (.capp function' argument)
| coercionBeta :
    Step (.capp (.cabs source target body) argument)
      (body.subst (Subst.openCVar argument))
| castExpression : Step expression expression' ->
    Step (.cast expression coercion) (.cast expression' coercion)
| castRefl : IsValue expression ->
    Step (.cast expression (.refl ty)) expression
| castTrans : IsValue expression ->
    Step (.cast expression (.trans first second))
      (.cast (.cast expression first) second)
| castBottom : IsValue expression ->
    Step (.cast expression (.bottom target)) (.tapp expression target)
| castAdapter : IsValue expression ->
    Step (.cast expression (.adapter source body))
      (body.subst (Subst.openVar expression))
| castArrowApp : IsValue function -> IsValue argument ->
    Step (.app (.cast function (.arrow parameter result)) argument)
      (.cast (.app function (.cast argument parameter)) result)
| castPolyTapp : IsValue function ->
    Step (.tapp (.cast function (.poly body)) argument)
      (.cast (.tapp function argument)
        (body.subst (Subst.openTVar argument)))
| castQualCapp : IsValue function ->
    Step (.capp (.cast function (.qual evidence result)) argument)
      (.cast
        (.capp function (evidence.subst (Subst.openCVar argument)))
        (result.subst (Subst.openCVar argument)))

inductive Steps : Exp sig -> Exp sig -> Prop where
| refl : Steps expression expression
| tail : Step first middle -> Steps middle last -> Steps first last

def IsStuck (expression : Exp sig) : Prop :=
  Not (IsValue expression) /\ Not (Exists fun next => Step expression next)

end Exp
end SystemFCoExt
