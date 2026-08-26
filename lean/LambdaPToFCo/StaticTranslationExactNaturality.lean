import LambdaPToFCo.StaticTranslationOrdinaryNaturality

namespace LambdaPToFCo
namespace StaticTranslation

open SystemFCo

/-- Translating a type after crossing an interval-package source binder is
the same as translating it first and weakening through the full interface. -/
noncomputable def translateType_weaken_member
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (scope : Scope sourceContext targetContext)
    (newFirst : Fin n) (newLabel : LambdaPFC.Name)
    (newLower newUpper : LambdaPFC.Ty n)
    (newLowerWf : Fragment.Wf sourceContext newLower)
    (newUpperWf : Fragment.Wf sourceContext newUpper)
    (newNonempty : Fragment.Sub sourceContext newLower newUpper)
    (targetLower targetUpper targetFirst : Ty sig)
    (wf : Fragment.Wf sourceContext sourceType) :
    let boundType :=
      Fragment.memberPackageTy newFirst newLabel newLower newUpper
    let plan := Interface.BinderPlan.exact targetLower targetUpper
      (payloadFamily targetFirst)
    translateType
        (.member scope newFirst newLabel newLower newUpper newLowerWf
          newUpperWf newNonempty targetLower targetUpper targetFirst)
        (wf.weaken boundType) =
      (translateType scope wf).rename plan.weaken := by
  dsimp only
  cases wf with
  | top => rfl
  | singleton typing =>
      change (translatePath
          (.member scope newFirst newLabel newLower newUpper newLowerWf
            newUpperWf newNonempty targetLower targetUpper targetFirst)
          (typing.weaken
            (Fragment.memberPackageTy newFirst newLabel newLower
              newUpper))).targetType =
        (translatePath scope typing).targetType.rename
          (Interface.BinderPlan.exact targetLower targetUpper
            (payloadFamily targetFirst)).weaken
      exact translatePath_type_weaken_member scope newFirst newLabel
        newLower newUpper newLowerWf newUpperWf newNonempty targetLower
        targetUpper targetFirst typing
  | selection member nonempty =>
      change
        ((Scope.lookupMember
          (.member scope newFirst newLabel newLower newUpper newLowerWf
            newUpperWf newNonempty targetLower targetUpper targetFirst)
          member.there).interface.witness) =
        (Scope.lookupMember scope member).interface.witness.rename
          (Interface.BinderPlan.exact targetLower targetUpper
            (payloadFamily targetFirst)).weaken
      rw [Scope.lookupMember_there_member]
      rfl
  | @memberPackage first label lower upper lowerWf upperWf nonempty =>
      let boundType :=
        Fragment.memberPackageTy newFirst newLabel newLower newUpper
      let extended := Scope.member scope newFirst newLabel newLower newUpper
        newLowerWf newUpperWf newNonempty targetLower targetUpper targetFirst
      let canonical : Fragment.Wf (sourceContext.snoc boundType)
          (Fragment.memberPackageTy first.succ label
            lower.weaken upper.weaken) :=
        .memberPackage (lowerWf.weaken boundType) (upperWf.weaken boundType)
          (nonempty.weaken boundType)
      have sourceEq :
          (Fragment.memberPackageTy first label lower upper).weaken =
            Fragment.memberPackageTy first.succ label
              lower.weaken upper.weaken := by
        exact Fragment.memberPackageTy_rename first label lower upper
          LambdaPFC.FinFun.weaken
      have replace := translateType_irrel_of_type_eq extended
        ((Fragment.Wf.memberPackage lowerWf upperWf nonempty).weaken
          boundType)
        canonical sourceEq
      rw [replace]
      dsimp [extended, canonical]
      rw [translateType_weaken_member scope newFirst newLabel newLower
          newUpper newLowerWf newUpperWf newNonempty targetLower targetUpper
          targetFirst lowerWf,
        translateType_weaken_member scope newFirst newLabel newLower
          newUpper newLowerWf newUpperWf newNonempty targetLower targetUpper
          targetFirst upperWf]
      let plan := Interface.BinderPlan.exact targetLower targetUpper
        (payloadFamily targetFirst)
      have firstEq :
          (((scope.lookup first).rename
            (plan.weakenTyped targetContext)).path.targetType) =
            (scope.lookup first).path.targetType.rename plan.weaken := by
        cases scope.lookup first <;> rfl
      dsimp [plan] at firstEq ⊢
      change _ = (Ty.member _ _ _).rename _
      rw [firstEq, Interface.member_rename]
      unfold payloadFamily
      rw [Ty.weaken_rename_comm]
  | @arrow domain codomain domainWf codomainWf =>
      let boundType :=
        Fragment.memberPackageTy newFirst newLabel newLower newUpper
      let extended := Scope.member scope newFirst newLabel newLower newUpper
        newLowerWf newUpperWf newNonempty targetLower targetUpper targetFirst
      let canonical : Fragment.Wf (sourceContext.snoc boundType)
          (.Fun domain.weaken codomain.weaken.weaken) :=
        .arrow (domainWf.weaken boundType) (codomainWf.weaken boundType)
      have sourceEq :
          (LambdaPFC.Ty.Fun domain codomain.weaken).weaken =
            .Fun domain.weaken codomain.weaken.weaken := by
        change LambdaPFC.Ty.Fun domain.weaken
          (codomain.weaken.rename LambdaPFC.FinFun.weaken.ext) = _
        apply congrArg (LambdaPFC.Ty.Fun domain.weaken)
        exact (LambdaPFC.Ty.weaken_rename codomain
          LambdaPFC.FinFun.weaken).symm
      have replace := translateType_irrel_of_type_eq extended
        ((Fragment.Wf.arrow domainWf codomainWf).weaken boundType)
        canonical sourceEq
      rw [replace]
      dsimp [extended, canonical]
      simp only [SystemFCo.Ty.rename]
      rw [translateType_weaken_member scope newFirst newLabel newLower
          newUpper newLowerWf newUpperWf newNonempty targetLower targetUpper
          targetFirst domainWf,
        translateType_weaken_member scope newFirst newLabel newLower
          newUpper newLowerWf newUpperWf newNonempty targetLower targetUpper
          targetFirst codomainWf]

end StaticTranslation
end LambdaPToFCo
