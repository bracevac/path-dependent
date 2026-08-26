import LambdaPToFCo.StaticCoherenceBase

namespace LambdaPToFCo
namespace StaticTranslation

open SystemFCo

theorem translatePath_type_weaken_ordinary
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (scope : Scope sourceContext targetContext)
    (boundType : LambdaPFC.Ty n) (shape : OrdinaryShape boundType)
    (targetType : Ty sig)
    (typing : Fragment.PathTy sourceContext path sourceType) :
    (translatePath (.ordinary scope boundType shape targetType)
      (typing.weaken boundType)).targetType =
    (translatePath scope typing).targetType.rename
      (Interface.BinderPlan.ordinary targetType).weaken := by
  cases typing with
  | var =>
      simp only [Fragment.PathTy.weaken, LambdaPFC.FinFun.weaken_apply,
        translatePath]
      rw [Scope.lookup_there_ordinary]
      cases scope.lookup _ <;> rfl
  | exactFst member =>
      simp only [Fragment.PathTy.weaken, translatePath]
      unfold TypedExactSlot.payloadPath
      change ((Scope.lookupMember (.ordinary scope boundType shape targetType)
        member.there).payloadType) =
        (Scope.lookupMember scope member).payloadType.rename
          (Interface.BinderPlan.ordinary targetType).weaken
      rw [Scope.lookupMember_there_ordinary]
      rfl

theorem translatePath_type_weaken_member
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (scope : Scope sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    (lower upper : LambdaPFC.Ty n)
    (lowerWf : Fragment.Wf sourceContext lower)
    (upperWf : Fragment.Wf sourceContext upper)
    (nonempty : Fragment.Sub sourceContext lower upper)
    (targetLower targetUpper targetFirst : Ty sig)
    (typing : Fragment.PathTy sourceContext path sourceType) :
    (translatePath
      (.member scope first label lower upper lowerWf upperWf nonempty
        targetLower targetUpper targetFirst)
      (typing.weaken
        (Fragment.memberPackageTy first label lower upper))).targetType =
    (translatePath scope typing).targetType.rename
      (Interface.BinderPlan.exact targetLower targetUpper
        (payloadFamily targetFirst)).weaken := by
  cases typing with
  | var =>
      simp only [Fragment.PathTy.weaken, LambdaPFC.FinFun.weaken_apply,
        translatePath]
      rw [Scope.lookup_there_member]
      cases scope.lookup _ <;> rfl
  | exactFst member =>
      simp only [Fragment.PathTy.weaken, translatePath]
      unfold TypedExactSlot.payloadPath
      change ((Scope.lookupMember
        (.member scope first label lower upper lowerWf upperWf nonempty
          targetLower targetUpper targetFirst)
        member.there).payloadType) =
        (Scope.lookupMember scope member).payloadType.rename
          (Interface.BinderPlan.exact targetLower targetUpper
            (payloadFamily targetFirst)).weaken
      rw [Scope.lookupMember_there_member]
      rfl

end StaticTranslation
end LambdaPToFCo
