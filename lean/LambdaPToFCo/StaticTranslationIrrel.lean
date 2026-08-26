import LambdaPToFCo.StaticSourceLaws

namespace LambdaPToFCo
namespace StaticTranslation

open SystemFCo

theorem Fragment.memberPackageTy_injective
    {first second : Fin n} {leftLabel rightLabel : LambdaPFC.Name}
    {leftLower leftUpper rightLower rightUpper : LambdaPFC.Ty n}
    (equality :
      Fragment.memberPackageTy first leftLabel leftLower leftUpper =
      Fragment.memberPackageTy second rightLabel rightLower rightUpper) :
    first = second ∧ leftLabel = rightLabel ∧
      leftLower = rightLower ∧ leftUpper = rightUpper := by
  unfold Fragment.memberPackageTy at equality
  have parts := LambdaPFC.Ty.Pair.inj equality
  have firstTypeEq := parts.2.1
  have labelEq := parts.2.2.1
  have memberEq := eq_of_heq parts.2.2.2
  have firstEq := LambdaPFC.Path.var.inj
    (LambdaPFC.Ty.Single.inj firstTypeEq)
  have intervalEq := LambdaPFC.Tau.intv.inj memberEq
  exact ⟨firstEq, labelEq,
    LambdaPFC.Ty.weaken_injective intervalEq.1,
    LambdaPFC.Ty.weaken_injective intervalEq.2⟩

theorem Fragment.exactPackageTy_injective
    {first second : Fin n} {leftLabel rightLabel : LambdaPFC.Name}
    {leftWitness rightWitness : LambdaPFC.Ty n}
    (equality : Fragment.exactPackageTy first leftLabel leftWitness =
      Fragment.exactPackageTy second rightLabel rightWitness) :
    first = second ∧ leftLabel = rightLabel ∧ leftWitness = rightWitness := by
  have parts := Fragment.memberPackageTy_injective equality
  exact ⟨parts.1, parts.2.1, parts.2.2.1⟩

theorem translatePath_type_irrel_of_path_eq
    (scope : Scope sourceContext targetContext)
    (left : Fragment.PathTy sourceContext leftPath leftType)
    (right : Fragment.PathTy sourceContext rightPath rightType)
    (pathEq : leftPath = rightPath) :
    (translatePath scope left).targetType =
      (translatePath scope right).targetType := by
  cases left with
  | var =>
      cases right with
      | var =>
          have indexEq := LambdaPFC.Path.var.inj pathEq
          cases indexEq
          rfl
      | exactFst member => cases pathEq
  | exactFst leftMember =>
      cases right with
      | var => cases pathEq
      | exactFst rightMember =>
          have packageEq := LambdaPFC.Path.fst.inj pathEq |>
            LambdaPFC.Path.var.inj
          cases packageEq
          apply congrArg TypedExactSlot.payloadType
          exact Scope.lookupMember_irrel scope leftMember rightMember

theorem translatePath_type_irrel
    (scope : Scope sourceContext targetContext)
    (left right : Fragment.PathTy sourceContext path sourceType) :
    (translatePath scope left).targetType =
      (translatePath scope right).targetType :=
  translatePath_type_irrel_of_path_eq scope left right rfl

noncomputable def translateType_irrel_of_type_eq
    (scope : Scope sourceContext targetContext)
    (left : Fragment.Wf sourceContext leftType)
    (right : Fragment.Wf sourceContext rightType)
    (typeEq : leftType = rightType) :
    translateType scope left = translateType scope right := by
  cases left with
  | top =>
      cases right <;> cases typeEq
      rfl
  | singleton leftPath =>
      cases right with
      | top | selection _ _ | memberPackage _ _ _ | arrow _ _ =>
          cases typeEq
      | singleton rightPath =>
          have pathEq := LambdaPFC.Ty.Single.inj typeEq
          change (translatePath scope leftPath).targetType =
            (translatePath scope rightPath).targetType
          exact translatePath_type_irrel_of_path_eq scope _ _ pathEq
  | selection leftMember leftNonempty =>
      cases right with
      | top | singleton _ | memberPackage _ _ _ | arrow _ _ =>
          cases typeEq
      | selection rightMember rightNonempty =>
          have pathEq := (LambdaPFC.Ty.TSel.inj typeEq).1
          have packageEq := LambdaPFC.Path.var.inj pathEq
          cases packageEq
          change (scope.lookupMember leftMember).interface.witness =
            (scope.lookupMember rightMember).interface.witness
          exact congrArg (fun slot : TypedExactSlot targetContext =>
            slot.interface.witness)
            (Scope.lookupMember_irrel scope leftMember rightMember)
  | @memberPackage first label lower upper leftLowerWf leftUpperWf
      leftNonempty =>
      cases right with
      | top | singleton _ | selection _ _ | arrow _ _ => cases typeEq
      | @memberPackage rightFirst rightLabel rightLower rightUpper
          rightLowerWf rightUpperWf rightNonempty =>
          have parts := Fragment.memberPackageTy_injective typeEq
          cases parts.1
          cases parts.2.1
          cases parts.2.2.1
          cases parts.2.2.2
          simp only [translateType_memberPackage]
          rw [translateType_irrel_of_type_eq scope leftLowerWf rightLowerWf rfl,
            translateType_irrel_of_type_eq scope leftUpperWf rightUpperWf rfl]
  | arrow leftDomainWf leftCodomainWf =>
      cases right with
      | top | singleton _ | selection _ _ | memberPackage _ _ _ =>
          cases typeEq
      | arrow rightDomainWf rightCodomainWf =>
          have outer := LambdaPFC.Ty.Fun.inj typeEq
          have domainEq := outer.1
          have codomainEq := LambdaPFC.Ty.weaken_injective outer.2
          simp only [translateType_arrow]
          rw [translateType_irrel_of_type_eq scope leftDomainWf
                rightDomainWf domainEq,
            translateType_irrel_of_type_eq scope leftCodomainWf
                rightCodomainWf codomainEq]

/-- The target type depends only on the source type, not on which fragment
well-formedness derivation was chosen. -/
theorem translateType_irrel
    (scope : Scope sourceContext targetContext)
    (left right : Fragment.Wf sourceContext sourceType) :
    translateType scope left = translateType scope right :=
  translateType_irrel_of_type_eq scope left right rfl

end StaticTranslation
end LambdaPToFCo
