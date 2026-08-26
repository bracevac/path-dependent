import LambdaPToFCo.StaticExactLookup

namespace LambdaPToFCo
namespace StaticTranslation

open SystemFCo
open LambdaPFC

namespace Scope

theorem lookupMemberAux_spec
    {n : Nat} {memberContext sourceContext : LambdaPFC.Ctx n}
    {package first : Fin n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty n}
    {targetSig : Sig} {targetContext : Ctx targetSig}
    (member : Fragment.BoundMember memberContext package label lower upper
      first)
    (scope : Scope sourceContext targetContext)
    (contextEq : memberContext = sourceContext) :
    TypedInterfaceSlot.exact (lookupMemberAux member scope contextEq) =
      scope.lookup package := by
  induction member generalizing targetSig targetContext with
  | @here n memberParent memberFirst memberLabel memberLower memberUpper =>
      cases scope with
      | ordinary scopeParent sourceType shape targetType =>
          have bindingEq := (LambdaPFC.Ctx.snoc.inj contextEq).2
          exact Empty.elim (shape.notMember
            { first := memberFirst
              label := memberLabel
              lower := memberLower
              upper := memberUpper
              equality := bindingEq.symm })
      | member scopeParent newFirst newLabel newLower newUpper newLowerWf
          newUpperWf newNonempty targetLower targetUpper targetFirst =>
          rfl
  | @there n memberParent package first label lower upper boundType member ih =>
      cases scope with
      | @ordinary _ _ baseSig baseTarget scopeParent sourceType shape
          targetType =>
          have parentEq := (LambdaPFC.Ctx.snoc.inj contextEq).1
          have induction := ih scopeParent parentEq
          exact congrArg
            (TypedInterfaceSlot.rename ·
              ((Interface.BinderPlan.ordinary targetType).weakenTyped
                baseTarget))
            induction
      | @member _ _ baseSig baseTarget scopeParent newFirst newLabel
          newLower newUpper newLowerWf newUpperWf newNonempty targetLower
          targetUpper targetFirst =>
          have parentEq := (LambdaPFC.Ctx.snoc.inj contextEq).1
          have induction := ih scopeParent parentEq
          exact congrArg
            (TypedInterfaceSlot.rename ·
              ((Interface.BinderPlan.exact targetLower targetUpper
                (payloadFamily targetFirst)).weakenTyped baseTarget))
            induction

theorem lookupMember_spec
    (scope : Scope sourceContext targetContext)
    (member : Fragment.BoundMember sourceContext package label lower upper
      first) :
    TypedInterfaceSlot.exact (lookupMember scope member) =
      scope.lookup package :=
  lookupMemberAux_spec member scope rfl

/-- Member-slot lookup depends only on the package position. -/
theorem lookupMember_irrel
    (scope : Scope sourceContext targetContext)
    (left : Fragment.BoundMember sourceContext package leftLabel
      leftLower leftUpper leftFirst)
    (right : Fragment.BoundMember sourceContext package rightLabel
      rightLower rightUpper rightFirst) :
    lookupMember scope left = lookupMember scope right := by
  apply TypedInterfaceSlot.exact.inj
  exact (lookupMember_spec scope left).trans
    (lookupMember_spec scope right).symm

end Scope

end StaticTranslation
end LambdaPToFCo
