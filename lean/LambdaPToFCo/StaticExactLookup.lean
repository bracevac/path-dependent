import LambdaPToFCo.StaticScopeBase

namespace LambdaPToFCo
namespace StaticTranslation

open SystemFCo
open LambdaPFC

namespace Scope

noncomputable def lookupMemberAux
    {n : Nat} {memberContext sourceContext : LambdaPFC.Ctx n}
    {package first : Fin n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty n}
    {targetSig : Sig} {targetContext : Ctx targetSig}
    (member : Fragment.BoundMember memberContext package label lower upper
      first)
    (scope : Scope sourceContext targetContext)
    (contextEq : memberContext = sourceContext) :
    TypedExactSlot targetContext := by
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
          exact newestExact _ targetLower targetUpper
            (payloadFamily targetFirst)
  | @there n memberParent package first label lower upper boundType member ih =>
      cases scope with
      | @ordinary _ _ baseSig baseTarget scopeParent sourceType shape
          targetType =>
          have parentEq := (LambdaPFC.Ctx.snoc.inj contextEq).1
          have older : TypedExactSlot baseTarget := ih scopeParent parentEq
          exact older.rename
            ((Interface.BinderPlan.ordinary targetType).weakenTyped _)
      | @member _ _ baseSig baseTarget scopeParent newFirst newLabel
          newLower newUpper newLowerWf newUpperWf newNonempty targetLower
          targetUpper targetFirst =>
          have parentEq := (LambdaPFC.Ctx.snoc.inj contextEq).1
          have older : TypedExactSlot baseTarget := ih scopeParent parentEq
          exact older.rename
            ((Interface.BinderPlan.exact targetLower targetUpper
              (payloadFamily targetFirst)).weakenTyped _)

/-- Resolve a source member package to the five typed lexical projections
created for its binder. -/
noncomputable def lookupMember
    (scope : Scope sourceContext targetContext)
    (member : Fragment.BoundMember sourceContext package label lower upper
      first) : TypedExactSlot targetContext :=
  lookupMemberAux member scope rfl

@[simp] theorem lookupMember_here
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    (lower upper : LambdaPFC.Ty n)
    (lowerWf : Fragment.Wf sourceContext lower)
    (upperWf : Fragment.Wf sourceContext upper)
    (nonempty : Fragment.Sub sourceContext lower upper)
    (targetLower targetUpper targetFirst : Ty sig) :
    lookupMember
        (.member scope first label lower upper lowerWf upperWf nonempty
          targetLower targetUpper targetFirst)
        (Fragment.BoundMember.here
          (Γ := sourceContext) (first := first) (label := label)
          (lower := lower) (upper := upper)) =
      newestExact targetContext targetLower targetUpper
        (payloadFamily targetFirst) := rfl

@[simp] theorem lookupMember_there_ordinary
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {package first : Fin n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty n}
    (scope : Scope sourceContext targetContext)
    (sourceType : LambdaPFC.Ty n) (shape : OrdinaryShape sourceType)
    (targetType : Ty sig)
    (member : Fragment.BoundMember sourceContext package label lower upper
      first) :
    lookupMember (.ordinary scope sourceType shape targetType) (.there member) =
      (lookupMember scope member).rename
        ((Interface.BinderPlan.ordinary targetType).weakenTyped
          targetContext) := rfl

@[simp] theorem lookupMember_there_member
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {package first : Fin n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty n}
    (scope : Scope sourceContext targetContext)
    (newFirst : Fin n) (newLabel : LambdaPFC.Name)
    (newLower newUpper : LambdaPFC.Ty n)
    (newLowerWf : Fragment.Wf sourceContext newLower)
    (newUpperWf : Fragment.Wf sourceContext newUpper)
    (newNonempty : Fragment.Sub sourceContext newLower newUpper)
    (targetLower targetUpper targetFirst : Ty sig)
    (member : Fragment.BoundMember sourceContext package label lower upper
      first) :
    lookupMember
        (.member scope newFirst newLabel newLower newUpper newLowerWf
          newUpperWf newNonempty targetLower targetUpper targetFirst)
        (.there member) =
      (lookupMember scope member).rename
        ((Interface.BinderPlan.exact targetLower targetUpper
          (payloadFamily targetFirst)).weakenTyped targetContext) := rfl

/-- Compatibility name for the exact specialization. -/
noncomputable def lookupExact
    (scope : Scope sourceContext targetContext)
    (member : Fragment.BoundExactMember sourceContext package label witness
      first) : TypedExactSlot targetContext :=
  lookupMember scope member

end Scope

end StaticTranslation
end LambdaPToFCo
