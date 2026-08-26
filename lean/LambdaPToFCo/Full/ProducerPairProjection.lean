import LambdaPToFCo.Full.ProducerPairHead
import LambdaPToFCo.Full.ModelInstantiationCoherence

/-!
# Sealed positive pair projection

This leaf normalizes retained `ProducerPairHead` history to the current pair
shape and exposes the exact closed binder-exchange certificate required by a
dependent right selection.  The certificate target is determined by
`ModelInstantiation.exchangeUnderBinding`; callers cannot supply a replacement
member model.

This is one stage of `sel_r`, not a total path rule.  Consuming the receiver's
actual first-field arguments and opening the exchanged member requires a
separate action-specific `openAt` certificate and package construction.
-/

namespace LambdaPToFCo.Full

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

noncomputable def ProperPairCapability.targetRename
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx source}
    {targetTargetContext : SystemFCoExt.Ctx target}
    {sourceView : ScopeView n sourceTargetContext}
    {sourceType : LambdaPFC.Ty n} {sourcePlan : ValuePlan source}
    (model : ProducerPlanModel sourceContext sourceTargetContext sourceView
      sourceType sourcePlan)
    (older : ProperPairCapability model)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    ProperPairCapability (.targetRename model mapping typed) where
  firstType := older.firstType
  label := older.label
  memberType := older.memberType
  source_eq := older.source_eq
  firstPlan := older.firstPlan.rename mapping
  memberPlan := Pair.Proper.renameMember older.firstPlan older.memberPlan
    mapping
  plan_eq := by
    calc
      sourcePlan.rename mapping =
          (Pair.Proper.plan older.firstPlan older.memberPlan).rename mapping :=
        congrArg (fun plan => plan.rename mapping) older.plan_eq
      _ = Pair.Proper.plan (older.firstPlan.rename mapping)
          (Pair.Proper.renameMember older.firstPlan older.memberPlan
            mapping) :=
        Pair.Proper.plan_rename older.firstPlan older.memberPlan mapping
  firstModel := .targetRename older.firstModel mapping typed
  history := .targetRename model older.history mapping typed

noncomputable def IntervalPairCapability.underBinding
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext}
    {boundType olderType : LambdaPFC.Ty n}
    {boundPlan olderPlan : ValuePlan sig}
    (boundModel : ProducerPlanModel sourceContext targetContext view
      boundType boundPlan)
    (olderModel : ProducerPlanModel sourceContext targetContext view
      olderType olderPlan)
    (older : IntervalPairCapability olderModel) :
    IntervalPairCapability (.underBinding boundModel olderModel) where
  firstType := older.firstType.weaken
  label := older.label
  lower := older.lower.rename FinFun.weaken.ext
  upper := older.upper.rename FinFun.weaken.ext
  source_eq := by
    calc
      olderType.weaken =
          (LambdaPFC.Ty.Pair older.firstType older.label
            (.intv older.lower older.upper)).weaken :=
        congrArg LambdaPFC.Ty.weaken older.source_eq
      _ = LambdaPFC.Ty.Pair older.firstType.weaken older.label
          (.intv (older.lower.rename FinFun.weaken.ext)
            (older.upper.rename FinFun.weaken.ext)) := rfl
  firstPlan := older.firstPlan.rename boundPlan.telescope.weaken
  lowerPlan := older.lowerPlan.rename
    (older.firstPlan.telescope.liftRename boundPlan.telescope.weaken)
  upperPlan := older.upperPlan.rename
    (older.firstPlan.telescope.liftRename boundPlan.telescope.weaken)
  plan_eq := by
    calc
      olderPlan.rename boundPlan.telescope.weaken =
          (Pair.Interval.plan older.firstPlan older.lowerPlan.inputTy
            older.upperPlan.inputTy).rename boundPlan.telescope.weaken :=
        congrArg (fun plan => plan.rename boundPlan.telescope.weaken)
          older.plan_eq
      _ = _ := by
        rw [Pair.Interval.plan_rename, ValuePlan.inputTy_rename,
          ValuePlan.inputTy_rename]
        rfl
  firstModel := .underBinding boundModel older.firstModel
  history := .underBinding boundModel olderModel older.history

noncomputable def IntervalPairCapability.bound
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : ProducerPlanModel sourceContext targetContext view sourceType
      plan)
    (older : IntervalPairCapability model) :
    IntervalPairCapability (.bound model) where
  firstType := older.firstType.weaken
  label := older.label
  lower := older.lower.rename FinFun.weaken.ext
  upper := older.upper.rename FinFun.weaken.ext
  source_eq := by
    calc
      sourceType.weaken =
          (LambdaPFC.Ty.Pair older.firstType older.label
            (.intv older.lower older.upper)).weaken :=
        congrArg LambdaPFC.Ty.weaken older.source_eq
      _ = LambdaPFC.Ty.Pair older.firstType.weaken older.label
          (.intv (older.lower.rename FinFun.weaken.ext)
            (older.upper.rename FinFun.weaken.ext)) := rfl
  firstPlan := older.firstPlan.rename plan.telescope.weaken
  lowerPlan := older.lowerPlan.rename
    (older.firstPlan.telescope.liftRename plan.telescope.weaken)
  upperPlan := older.upperPlan.rename
    (older.firstPlan.telescope.liftRename plan.telescope.weaken)
  plan_eq := by
    calc
      plan.rename plan.telescope.weaken =
          (Pair.Interval.plan older.firstPlan older.lowerPlan.inputTy
            older.upperPlan.inputTy).rename plan.telescope.weaken :=
        congrArg (fun current => current.rename plan.telescope.weaken)
          older.plan_eq
      _ = _ := by
        rw [Pair.Interval.plan_rename, ValuePlan.inputTy_rename,
          ValuePlan.inputTy_rename]
        rfl
  firstModel := .underBinding model older.firstModel
  history := .bound model older.history

noncomputable def IntervalPairCapability.targetRename
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx source}
    {targetTargetContext : SystemFCoExt.Ctx target}
    {sourceView : ScopeView n sourceTargetContext}
    {sourceType : LambdaPFC.Ty n} {sourcePlan : ValuePlan source}
    (model : ProducerPlanModel sourceContext sourceTargetContext sourceView
      sourceType sourcePlan)
    (older : IntervalPairCapability model)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    IntervalPairCapability (.targetRename model mapping typed) where
  firstType := older.firstType
  label := older.label
  lower := older.lower
  upper := older.upper
  source_eq := older.source_eq
  firstPlan := older.firstPlan.rename mapping
  lowerPlan := older.lowerPlan.rename
    (older.firstPlan.telescope.liftRename mapping)
  upperPlan := older.upperPlan.rename
    (older.firstPlan.telescope.liftRename mapping)
  plan_eq := by
    calc
      sourcePlan.rename mapping =
          (Pair.Interval.plan older.firstPlan older.lowerPlan.inputTy
            older.upperPlan.inputTy).rename mapping :=
        congrArg (fun plan => plan.rename mapping) older.plan_eq
      _ = _ := by
        rw [Pair.Interval.plan_rename, ValuePlan.inputTy_rename,
          ValuePlan.inputTy_rename]
  firstModel := .targetRename older.firstModel mapping typed
  history := .targetRename model older.history mapping typed

/-- Normalize retained pair-head history to its current source, plan, and
first-field shape.  This recursion intentionally does not synthesize a
dependent member model. -/
noncomputable def ProducerPairHead.projection
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext targetContext view sourceType
      plan}
    (history : ProducerPairHead model) : ProducerPairProjection model :=
  match history with
  | .proper first member =>
      ProducerPairProjection.proper (ProperPairCapability.direct first member)
  | .interval first member =>
      ProducerPairProjection.interval
        (IntervalPairCapability.direct first member)
  | .bound model previous =>
      match ProducerPairHead.projection previous with
      | .proper capability =>
          .proper (ProperPairCapability.bound model capability)
      | .interval capability =>
          .interval (IntervalPairCapability.bound model capability)
  | .underBinding boundModel olderModel previous =>
      match ProducerPairHead.projection previous with
      | .proper capability =>
          .proper (ProperPairCapability.underBinding boundModel olderModel
            capability)
      | .interval capability =>
          .interval (IntervalPairCapability.underBinding boundModel olderModel
            capability)
  | .targetRename model previous mapping typed =>
      match ProducerPairHead.projection previous with
      | .proper capability =>
          .proper (ProperPairCapability.targetRename model capability mapping
            typed)
      | .interval capability =>
          .interval (IntervalPairCapability.targetRename model capability
            mapping typed)

/-! ## Action-specific dependent-member exchange -/

/-- Exact additional certificate required to move a proper dependent member
past one modeled source binding.  Its target is determined by the closed
exchange action, not supplied by the caller. -/
abbrev ProperMemberExchangeCertificate
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (constructed : ConstructedScope scope)
    {boundType firstType : LambdaPFC.Ty n}
    {boundPlan firstPlan : ValuePlan sig}
    (bound : ProducerPlanModel sourceContext targetContext scope.view
      boundType boundPlan)
    (first : ProducerPlanModel sourceContext targetContext scope.view
      firstType firstPlan)
    {memberType : LambdaPFC.Ty (n + 1)}
    {memberPlan : ValuePlan firstPlan.scope}
    (member : ProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context targetContext) (ScopeView.bindPlan scope.view
        firstPlan) memberType memberPlan) :=
  ProducerInstantiationCoherence.Result
    (ModelInstantiation.exchangeUnderBinding scope constructed bound first)
    member

/-- Eliminate an action-specific proper certificate to the uniquely
determined exchanged member model. -/
noncomputable def ProperMemberExchangeCertificate.instantiated
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (constructed : ConstructedScope scope)
    {boundType firstType : LambdaPFC.Ty n}
    {boundPlan firstPlan : ValuePlan sig}
    (bound : ProducerPlanModel sourceContext targetContext scope.view
      boundType boundPlan)
    (first : ProducerPlanModel sourceContext targetContext scope.view
      firstType firstPlan)
    {memberType : LambdaPFC.Ty (n + 1)}
    {memberPlan : ValuePlan firstPlan.scope}
    (member : ProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context targetContext) (ScopeView.bindPlan scope.view
        firstPlan) memberType memberPlan)
    (certificate : ProperMemberExchangeCertificate scope constructed bound
      first member) :
    ModelInstantiation.ProducerTarget
      (ModelInstantiation.exchangeUnderBinding scope constructed bound first)
      memberType memberPlan :=
  ProducerInstantiationCoherence.Result.instantiated certificate

/-- Interval analogue.  It retains lower-negative and upper-positive evidence
as one certificate-determined target. -/
abbrev IntervalMemberExchangeCertificate
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (constructed : ConstructedScope scope)
    {boundType firstType : LambdaPFC.Ty n}
    {boundPlan firstPlan : ValuePlan sig}
    (bound : ProducerPlanModel sourceContext targetContext scope.view
      boundType boundPlan)
    (first : ProducerPlanModel sourceContext targetContext scope.view
      firstType firstPlan)
    {lower upper : LambdaPFC.Ty (n + 1)}
    {lowerPlan upperPlan : ValuePlan firstPlan.scope}
    (member : IntervalProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context targetContext) (ScopeView.bindPlan scope.view
        firstPlan) lower upper lowerPlan upperPlan) :=
  IntervalProducerInstantiationCoherence.Result
    (ModelInstantiation.exchangeUnderBinding scope constructed bound first)
    member

/-- Eliminate an action-specific interval certificate to its inseparable,
uniquely determined exchanged endpoint models. -/
noncomputable def IntervalMemberExchangeCertificate.instantiated
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (constructed : ConstructedScope scope)
    {boundType firstType : LambdaPFC.Ty n}
    {boundPlan firstPlan : ValuePlan sig}
    (bound : ProducerPlanModel sourceContext targetContext scope.view
      boundType boundPlan)
    (first : ProducerPlanModel sourceContext targetContext scope.view
      firstType firstPlan)
    {lower upper : LambdaPFC.Ty (n + 1)}
    {lowerPlan upperPlan : ValuePlan firstPlan.scope}
    (member : IntervalProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context targetContext) (ScopeView.bindPlan scope.view
        firstPlan) lower upper lowerPlan upperPlan)
    (certificate : IntervalMemberExchangeCertificate scope constructed bound
      first member) :
    ModelInstantiation.IntervalProducerTarget
      (ModelInstantiation.exchangeUnderBinding scope constructed bound first)
      lower upper lowerPlan upperPlan :=
  IntervalProducerInstantiationCoherence.Result.instantiated certificate

end LambdaPToFCo.Full
