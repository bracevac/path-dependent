import LambdaPToFCo.StaticTranslationPathNaturality

namespace LambdaPToFCo
namespace StaticTranslation

open SystemFCo

/-- Translating a type after crossing an ordinary source binder is the same
as translating it first and weakening through the corresponding target plan. -/
noncomputable def translateType_weaken_ordinary
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {sourceType boundType : LambdaPFC.Ty n}
    (scope : Scope sourceContext targetContext)
    (shape : OrdinaryShape boundType) (targetType : Ty sig)
    (wf : Fragment.Wf sourceContext sourceType) :
    translateType (.ordinary scope boundType shape targetType)
        (wf.weaken boundType) =
      (translateType scope wf).rename
        (Interface.BinderPlan.ordinary targetType).weaken := by
  cases wf with
  | top => rfl
  | singleton typing =>
      change (translatePath (.ordinary scope boundType shape targetType)
          (typing.weaken boundType)).targetType =
        (translatePath scope typing).targetType.rename
          (Interface.BinderPlan.ordinary targetType).weaken
      exact translatePath_type_weaken_ordinary scope boundType shape
        targetType typing
  | selection member nonempty =>
      change
        ((Scope.lookupMember (.ordinary scope boundType shape targetType)
          member.there).interface.witness) =
        (Scope.lookupMember scope member).interface.witness.rename
          (Interface.BinderPlan.ordinary targetType).weaken
      rw [Scope.lookupMember_there_ordinary]
      rfl
  | @memberPackage first label lower upper lowerWf upperWf nonempty =>
      let extended := Scope.ordinary scope boundType shape targetType
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
        ((Fragment.Wf.memberPackage lowerWf upperWf nonempty).weaken boundType)
        canonical sourceEq
      rw [replace]
      dsimp [extended, canonical]
      rw [translateType_weaken_ordinary scope shape targetType lowerWf,
        translateType_weaken_ordinary scope shape targetType upperWf]
      have firstEq :
          ((scope.lookup first).rename
            ((Interface.BinderPlan.ordinary targetType).weakenTyped
              targetContext)).path.targetType =
            (scope.lookup first).path.targetType.rename
              (Interface.BinderPlan.ordinary targetType).weaken := by
        cases scope.lookup first <;> rfl
      change _ = (Ty.member _ _ _).rename _
      rw [firstEq, Interface.member_rename]
      unfold payloadFamily
      rw [Ty.weaken_rename_comm]
  | @arrow domain codomain domainWf codomainWf =>
      let extended := Scope.ordinary scope boundType shape targetType
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
      rw [translateType_weaken_ordinary scope shape targetType domainWf,
        translateType_weaken_ordinary scope shape targetType codomainWf]

end StaticTranslation
end LambdaPToFCo
