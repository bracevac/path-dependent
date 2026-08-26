import LambdaPToFCo.Full.ConstructedScopeInstantiation
import LambdaPToFCo.Full.InterfaceArgumentCancellation
import LambdaPToFCo.Full.ScopeModelBinding
import LambdaPToFCo.Full.StableIdentitySubstitution

/-!
# Closed coherence for synchronized model instantiation

Dependent path selection opens one precisely typed source binding together
with the actual argument spine of its target value plan. `ModelInstantiation`
records that opening, target-renamed opening, closed scope renaming and
source/target binder insertion, together with their binder lifts. The seven
mutual coherence relations mirror the sealed plan-model constructors and
determine substituted targets without accepting an arbitrary model callback.

`ProducerInstantiationCoherence.Result` is the high-boundary seam for models
stored through dependent equality transports, notably `ScopeModel.bind.slot`.
Its eliminator recovers exact coherence only after checking the retained type,
plan, and model equalities.

There is intentionally no function which certifies an arbitrary
`ProperPathPackage`. Its low-level constructor stores a raw plan model but no
construction provenance. A total path compiler must return a high result that
retains the appropriate coherence result; `WfPlan.Resolver` path and selection
cases must delegate to that certified path layer.

There is likewise no total exchange certificate for an arbitrary member
headed by `targetRename`. Such a member may retain an unrelated target
mapping, while binder exchange retains no preimage of its inserted bound or
first model along that mapping. Only an outer rename whose exact factorization
is retained by construction can be commuted. High pair projection must retain
per-member coherence (or stronger constructed-model history) rather than
inventing that factorization here.
-/

namespace LambdaPToFCo.Full

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

namespace PairedInstantiation

/-- Exact opening of one source binding and the matching compiled target
plan. The source path and replacement model are fixed, and the target
substitution is forced to be the supplied plan's actual argument spine. -/
noncomputable def openAt
    {arity : Nat} {sourceContext : LambdaPFC.Ctx arity}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {boundType : LambdaPFC.Ty arity} {path : LambdaPFC.Path arity}
    (precise : LambdaPFC.Path.Ty sourceContext path (.ty boundType))
    {plan : ValuePlan sig}
    (replacement : ProducerPlanModel sourceContext targetContext scope.view
      boundType plan)
    (arguments : Telescope.Args targetContext plan.telescope) :
    PairedInstantiation (sourceContext.snoc boundType) sourceContext
      (plan.context targetContext) targetContext
      (TranslationInterfaces.ScopeView.bindPlan scope.view plan) scope.view
      (PathSubst.openAt path) arguments.substitution := by
  let substitutedView := ScopeView.subst
    (TranslationInterfaces.ScopeView.bindPlan scope.view plan)
    arguments.substitution arguments.substitution_typed
  refine
    { sourceTyped := TypedPathSubstitution.openAt precise
      targetTyped := arguments.substitution_typed
      image := substitutedView
      alignment := ScopeAlignment.identity substitutedView
      image_plan := fun index => ValueInterface.subst_plan _ _ _
      slotModel := ?_ }
  intro index
  refine Fin.cases ?_ (fun older => ?_) index
  · simp only [LambdaPFC.Ctx.lookup, Fin.cases_zero,
      TranslationInterfaces.ScopeView.bindPlan_here,
      TranslationInterfaces.ValueInterface.ofArguments_plan]
    have sourceCancel :
        boundType.weaken.subst (PathSubst.openAt path) = boundType :=
      LambdaPFC.Ty.weaken_open boundType path
    have targetCancel := ValuePlan.rename_subst_cancel plan
      plan.telescope.weaken
      arguments.substitution
      (TargetArguments.weaken_comp_substitution arguments)
    exact sourceCancel.symm ▸ targetCancel.symm ▸ replacement
  · simp only [LambdaPFC.Ctx.lookup, Fin.cases_succ,
      TranslationInterfaces.ScopeView.bindPlan_there,
      ValueInterface.rename]
    have sourceCancel :
        (sourceContext.lookup older).weaken.subst
            (PathSubst.openAt path) = sourceContext.lookup older :=
      LambdaPFC.Ty.weaken_open (sourceContext.lookup older) path
    have targetCancel := ValuePlan.rename_subst_cancel
      (scope.view older).plan
      plan.telescope.weaken arguments.substitution
      (TargetArguments.weaken_comp_substitution arguments)
    exact sourceCancel.symm ▸ targetCancel.symm ▸ scope.slot older

end PairedInstantiation

/-- Closed provenance for synchronized instantiations used by dependent path
selection. Every root is one exact construction action; there is no
constructor from an arbitrary `PairedInstantiation`. -/
inductive ModelInstantiation :
    {sourceArity targetArity : Nat} ->
    (sourceContext : LambdaPFC.Ctx sourceArity) ->
    (targetSourceContext : LambdaPFC.Ctx targetArity) ->
    {sourceSig targetSig : Sig} ->
    (sourceTargetContext : SystemFCoExt.Ctx sourceSig) ->
    (targetTargetContext : SystemFCoExt.Ctx targetSig) ->
    (sourceView : ScopeView sourceArity sourceTargetContext) ->
    (targetView : ScopeView targetArity targetTargetContext) ->
    (sourceSubstitution : PathSubst sourceArity targetArity) ->
    (targetSubstitution : Subst sourceSig targetSig) -> Type where
  | preTargetRename
      (mapping : Rename preSig sourceSig)
      (typed : Rename.Typed preTargetContext sourceTargetContext mapping)
      (next : ModelInstantiation sourceContext targetSourceContext
        sourceTargetContext targetTargetContext
        (preView.rename mapping typed) targetView sourceSubstitution
        targetSubstitution) :
      ModelInstantiation sourceContext targetSourceContext preTargetContext
        targetTargetContext preView targetView sourceSubstitution
        (mapping.asSubst.comp targetSubstitution)
  | openAt
      (scope : ScopeModel sourceContext targetContext)
      (precise : LambdaPFC.Path.Ty sourceContext path (.ty boundType))
      (replacement : ProducerPlanModel sourceContext targetContext scope.view
        boundType plan)
      (arguments : Telescope.Args targetContext plan.telescope) :
      ModelInstantiation (sourceContext.snoc boundType) sourceContext
        (plan.context targetContext) targetContext
        (TranslationInterfaces.ScopeView.bindPlan scope.view plan) scope.view
        (PathSubst.openAt path) arguments.substitution
  | targetRenameScope
      {sourceArity : Nat}
      {sourceContext : LambdaPFC.Ctx sourceArity}
      {sourceSig targetSig : Sig}
      {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
      {targetTargetContext : SystemFCoExt.Ctx targetSig}
      (scope : ScopeModel sourceContext sourceTargetContext)
      (_constructed : ConstructedScope scope)
      (mapping : Rename sourceSig targetSig)
      (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
      ModelInstantiation (sourceArity := sourceArity)
        (targetArity := sourceArity) (sourceSig := sourceSig)
        (targetSig := targetSig) sourceContext sourceContext
        sourceTargetContext targetTargetContext scope.view
        (TranslationInterfaces.ScopeModel.targetRename
          (source := sourceSig) (target := targetSig) scope mapping typed).view
        (PathSubst.id : PathSubst sourceArity sourceArity)
        (mapping.asSubst : Subst sourceSig targetSig)
  | weakenUnderBinding
      {sourceArity : Nat}
      {sourceContext : LambdaPFC.Ctx sourceArity}
      {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
      {boundType : LambdaPFC.Ty sourceArity}
      {boundPlan : ValuePlan sig}
      (scope : ScopeModel sourceContext targetContext)
      (_constructed : ConstructedScope scope)
      (bound : ProducerPlanModel sourceContext targetContext scope.view
        boundType boundPlan) :
      ModelInstantiation sourceContext (sourceContext.snoc boundType)
        targetContext (boundPlan.context targetContext) scope.view
        (scope.bind bound).view FinFun.weaken.asSubst
        boundPlan.telescope.weaken.asSubst
  | openAtTargetRename
      {sourceArity : Nat}
      {sourceContext : LambdaPFC.Ctx sourceArity}
      {sourceSig targetSig : Sig}
      {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
      {targetTargetContext : SystemFCoExt.Ctx targetSig}
      {boundType : LambdaPFC.Ty sourceArity}
      {path : LambdaPFC.Path sourceArity}
      {plan : ValuePlan sourceSig}
      (scope : ScopeModel sourceContext sourceTargetContext)
      (_constructed : ConstructedScope scope)
      (mapping : Rename sourceSig targetSig)
      (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
      (precise : LambdaPFC.Path.Ty sourceContext path (.ty boundType))
      (replacement : ProducerPlanModel sourceContext sourceTargetContext
        scope.view boundType plan)
      (arguments : Telescope.Args targetTargetContext
        (plan.rename mapping).telescope) :
      ModelInstantiation (sourceContext.snoc boundType) sourceContext
        (plan.context sourceTargetContext) targetTargetContext
        (TranslationInterfaces.ScopeView.bindPlan scope.view plan)
        (scope.targetRename mapping typed).view (PathSubst.openAt path)
        ((plan.telescope.liftRename mapping).asSubst.comp
          arguments.substitution)
  | lift
      (previous : ModelInstantiation sourceContext targetSourceContext
        sourceTargetContext targetTargetContext sourceView targetView
        sourceSubstitution targetSubstitution)
      (newBound : ProducerPlanModel targetSourceContext targetTargetContext
        targetView (boundType.subst sourceSubstitution)
        (boundPlan.subst targetSubstitution)) :
      ModelInstantiation (sourceContext.snoc boundType)
        (targetSourceContext.snoc (boundType.subst sourceSubstitution))
        (boundPlan.context sourceTargetContext)
        ((boundPlan.subst targetSubstitution).context targetTargetContext)
        (TranslationInterfaces.ScopeView.bindPlan sourceView boundPlan)
        (TranslationInterfaces.ScopeView.bindPlan targetView
          (boundPlan.subst targetSubstitution))
        sourceSubstitution.lift
        (ValuePlan.telescope_subst boundPlan targetSubstitution ▸
          boundPlan.telescope.liftSubst targetSubstitution)

namespace ModelInstantiation

/-- Forget the closed provenance to the reusable synchronized carrier. -/
noncomputable def pairing :
    ModelInstantiation sourceContext targetSourceContext sourceTargetContext
      targetTargetContext sourceView targetView sourceSubstitution
      targetSubstitution ->
    PairedInstantiation sourceContext targetSourceContext sourceTargetContext
      targetTargetContext sourceView targetView sourceSubstitution
      targetSubstitution
  | .openAt scope precise replacement arguments =>
      PairedInstantiation.openAt scope precise replacement arguments
  | .targetRenameScope scope _ mapping typed =>
      PairedInstantiation.targetRenameScope scope mapping typed
  | .weakenUnderBinding scope _ bound =>
      PairedInstantiation.weakenUnderBinding scope bound
  | .openAtTargetRename scope _ mapping typed precise replacement arguments =>
      PairedInstantiation.openAtTargetRename scope mapping typed precise
        replacement arguments
  | .lift previous newBound => previous.pairing.liftWith newBound
  | .preTargetRename mapping typed next =>
      next.pairing.preTargetRename mapping typed

end ModelInstantiation

namespace SelectionOrigin

noncomputable def subst
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetContext : LambdaPFC.Ctx targetArity}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    (typed : TypedPathSubstitution sourceContext targetContext
      sourceSubstitution)
    (origin : SelectionOrigin sourceContext path label) :
    SelectionOrigin targetContext (path.subst sourceSubstitution) label where
  lower := origin.lower.subst sourceSubstitution
  upper := origin.upper.subst sourceSubstitution
  precise := by
    simpa only [LambdaPFC.Path.subst] using
      PathTyping.subst typed origin.precise
  nonempty := Subtyping.subst typed origin.nonempty

end SelectionOrigin

namespace ModelInstantiation

/-- Opening the exact outer binder cancels weakening of every positive model
from its retained predecessor scope. -/
noncomputable def openWeakenedProducer
    {sourceArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {sourceSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {sourceType : LambdaPFC.Ty sourceArity}
    {sourcePlan binderPlan : ValuePlan sourceSig}
    (model : ProducerPlanModel sourceContext sourceTargetContext sourceView
      sourceType sourcePlan)
    (path : LambdaPFC.Path sourceArity)
    (arguments : Telescope.Args sourceTargetContext binderPlan.telescope) :
    ProducerPlanModel sourceContext sourceTargetContext sourceView
      (sourceType.weaken.subst (PathSubst.openAt path))
      ((sourcePlan.rename binderPlan.telescope.weaken).subst
        arguments.substitution) := by
  have sourceCancel :
      sourceType.weaken.subst (PathSubst.openAt path) = sourceType :=
    LambdaPFC.Ty.weaken_open sourceType path
  have targetCancel := ValuePlan.rename_subst_cancel sourcePlan
    binderPlan.telescope.weaken arguments.substitution
    (TargetArguments.weaken_comp_substitution arguments)
  exact sourceCancel.symm ▸ targetCancel.symm ▸ model

/-- Negative analogue of `openWeakenedProducer`, available now that demand
models retain their exact positive binder. -/
noncomputable def openWeakenedDemand
    {sourceArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {sourceSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {sourceType : LambdaPFC.Ty sourceArity}
    {sourcePlan binderPlan : ValuePlan sourceSig}
    (model : DemandPlanModel sourceContext sourceTargetContext sourceView
      sourceType sourcePlan)
    (path : LambdaPFC.Path sourceArity)
    (arguments : Telescope.Args sourceTargetContext binderPlan.telescope) :
    DemandPlanModel sourceContext sourceTargetContext sourceView
      (sourceType.weaken.subst (PathSubst.openAt path))
      ((sourcePlan.rename binderPlan.telescope.weaken).subst
        arguments.substitution) := by
  have sourceCancel :
      sourceType.weaken.subst (PathSubst.openAt path) = sourceType :=
    LambdaPFC.Ty.weaken_open sourceType path
  have targetCancel := ValuePlan.rename_subst_cancel sourcePlan
    binderPlan.telescope.weaken arguments.substitution
    (TargetArguments.weaken_comp_substitution arguments)
  exact sourceCancel.symm ▸ targetCancel.symm ▸ model

end ModelInstantiation

/-! ## Model-indexed targets for sealed coherence certificates -/

namespace ModelInstantiation

abbrev ProducerTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (_action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    (sourceType : LambdaPFC.Ty sourceArity) (plan : ValuePlan sourceSig) :=
  ProducerPlanModel targetSourceContext targetTargetContext targetView
    (sourceType.subst sourceSubstitution) (plan.subst targetSubstitution)

abbrev DemandTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (_action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    (sourceType : LambdaPFC.Ty sourceArity) (plan : ValuePlan sourceSig) :=
  DemandPlanModel targetSourceContext targetTargetContext targetView
    (sourceType.subst sourceSubstitution) (plan.subst targetSubstitution)

abbrev BidirectionalTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (_action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    (sourceType : LambdaPFC.Ty sourceArity) (plan : ValuePlan sourceSig) :=
  BidirectionalPlanModel targetSourceContext targetTargetContext targetView
    (sourceType.subst sourceSubstitution) (plan.subst targetSubstitution)

abbrev SelectionTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {path : LambdaPFC.Path sourceArity} {label : LambdaPFC.Name}
    (origin : SelectionOrigin sourceContext path label)
    (plan : ValuePlan sourceSig) :=
  SelectionPlanModel targetSourceContext targetTargetContext targetView
    (SelectionOrigin.subst action.pairing.sourceTyped origin)
    (plan.subst targetSubstitution)

abbrev IntervalProducerTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (_action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    (lower upper : LambdaPFC.Ty sourceArity)
    (lowerPlan upperPlan : ValuePlan sourceSig) :=
  IntervalProducerPlanModel targetSourceContext targetTargetContext targetView
    (lower.subst sourceSubstitution) (upper.subst sourceSubstitution)
    (lowerPlan.subst targetSubstitution) (upperPlan.subst targetSubstitution)

abbrev IntervalDemandTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (_action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    (lower upper : LambdaPFC.Ty sourceArity)
    (lowerPlan upperPlan : ValuePlan sourceSig) :=
  IntervalDemandPlanModel targetSourceContext targetTargetContext targetView
    (lower.subst sourceSubstitution) (upper.subst sourceSubstitution)
    (lowerPlan.subst targetSubstitution) (upperPlan.subst targetSubstitution)

abbrev IntervalBidirectionalTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (_action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    (lower upper : LambdaPFC.Ty sourceArity)
    (lowerPlan upperPlan : ValuePlan sourceSig) :=
  IntervalBidirectionalPlanModel targetSourceContext targetTargetContext
    targetView (lower.subst sourceSubstitution)
    (upper.subst sourceSubstitution) (lowerPlan.subst targetSubstitution)
    (upperPlan.subst targetSubstitution)

/-- Reassociate the composed target substitution after recursively
instantiating the predecessor of a proof-relevant positive target rename. -/
noncomputable def targetRenameProducerTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {preSig sourceSig targetSig : Sig}
    {preTargetContext : SystemFCoExt.Ctx preSig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {preView : ScopeView sourceArity preTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (mapping : Rename preSig sourceSig)
    (typed : Rename.Typed preTargetContext sourceTargetContext mapping)
    {next : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext
      (preView.rename mapping typed) targetView sourceSubstitution
      targetSubstitution}
    {sourceType : LambdaPFC.Ty sourceArity}
    {plan : ValuePlan preSig}
    (target : ProducerTarget
      (.preTargetRename mapping typed next) sourceType plan) :
    ProducerTarget next sourceType (plan.rename mapping) := by
  simpa only [ProducerTarget, TargetModelRenaming.plan_rename_asSubst,
    ValuePlan.subst_comp] using target

/-- Negative analogue of `targetRenameProducerTarget`. -/
noncomputable def targetRenameDemandTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {preSig sourceSig targetSig : Sig}
    {preTargetContext : SystemFCoExt.Ctx preSig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {preView : ScopeView sourceArity preTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (mapping : Rename preSig sourceSig)
    (typed : Rename.Typed preTargetContext sourceTargetContext mapping)
    {next : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext
      (preView.rename mapping typed) targetView sourceSubstitution
      targetSubstitution}
    {sourceType : LambdaPFC.Ty sourceArity}
    {plan : ValuePlan preSig}
    (target : DemandTarget
      (.preTargetRename mapping typed next) sourceType plan) :
    DemandTarget next sourceType (plan.rename mapping) := by
  simpa only [DemandTarget, TargetModelRenaming.plan_rename_asSubst,
    ValuePlan.subst_comp] using target

/-- The exact positive target of the closed target-only scope action. -/
noncomputable def targetRenameScopeProducerTarget
    {sourceArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {source target : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx source}
    {targetTargetContext : SystemFCoExt.Ctx target}
    (scope : ScopeModel sourceContext sourceTargetContext)
    (constructed : ConstructedScope scope)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
    {sourceType : LambdaPFC.Ty sourceArity}
    {plan : ValuePlan source}
    (model : ProducerPlanModel sourceContext sourceTargetContext scope.view
      sourceType plan) :
    ProducerTarget (.targetRenameScope scope constructed mapping typed)
      sourceType plan := by
  have sourceEq : sourceType.subst PathSubst.id = sourceType :=
    LambdaPFC.Ty.subst_id sourceType
  have targetEq : plan.subst mapping.asSubst = plan.rename mapping := by
    rw [TargetModelRenaming.plan_rename_asSubst]
  change ProducerPlanModel sourceContext targetTargetContext
    (scope.targetRename mapping typed).view
    (sourceType.subst PathSubst.id) (plan.subst mapping.asSubst)
  rw [targetEq, sourceEq]
  exact TargetModelRenaming.producer model mapping typed

/-- The exact negative target of the closed target-only scope action. -/
noncomputable def targetRenameScopeDemandTarget
    {sourceArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {source target : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx source}
    {targetTargetContext : SystemFCoExt.Ctx target}
    (scope : ScopeModel sourceContext sourceTargetContext)
    (constructed : ConstructedScope scope)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
    {sourceType : LambdaPFC.Ty sourceArity}
    {plan : ValuePlan source}
    (model : DemandPlanModel sourceContext sourceTargetContext scope.view
      sourceType plan) :
    DemandTarget (.targetRenameScope scope constructed mapping typed)
      sourceType plan := by
  have sourceEq : sourceType.subst PathSubst.id = sourceType :=
    LambdaPFC.Ty.subst_id sourceType
  have targetEq : plan.subst mapping.asSubst = plan.rename mapping := by
    rw [TargetModelRenaming.plan_rename_asSubst]
  change DemandPlanModel sourceContext targetTargetContext
    (scope.targetRename mapping typed).view
    (sourceType.subst PathSubst.id) (plan.subst mapping.asSubst)
  rw [targetEq, sourceEq]
  exact TargetModelRenaming.demand model mapping typed

/-- Adding one retained scope binder weakens an arbitrary positive model by
the exact source and target substitutions of `weakenUnderBinding`. -/
noncomputable def weakenUnderBindingProducerTarget
    {sourceArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (constructed : ConstructedScope scope)
    {boundType sourceType : LambdaPFC.Ty sourceArity}
    {boundPlan sourcePlan : ValuePlan sig}
    (bound : ProducerPlanModel sourceContext targetContext scope.view
      boundType boundPlan)
    (model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType sourcePlan) :
    ProducerTarget (.weakenUnderBinding scope constructed bound)
      sourceType sourcePlan := by
  have sourceEq : sourceType.subst FinFun.weaken.asSubst =
      sourceType.weaken := by
    simpa only [LambdaPFC.Ty.weaken] using
      LambdaPFC.Ty.subst_asSubst sourceType FinFun.weaken
  change ProducerPlanModel (sourceContext.snoc boundType)
    (boundPlan.context targetContext) (scope.bind bound).view
    (sourceType.subst FinFun.weaken.asSubst)
    (sourcePlan.subst boundPlan.telescope.weaken.asSubst)
  rw [sourceEq]
  simpa only [TargetModelRenaming.plan_rename_asSubst] using
    ProducerPlanModel.underBinding bound model

/-- Negative analogue of `weakenUnderBindingProducerTarget`. -/
noncomputable def weakenUnderBindingDemandTarget
    {sourceArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (constructed : ConstructedScope scope)
    {boundType sourceType : LambdaPFC.Ty sourceArity}
    {boundPlan sourcePlan : ValuePlan sig}
    (bound : ProducerPlanModel sourceContext targetContext scope.view
      boundType boundPlan)
    (model : DemandPlanModel sourceContext targetContext scope.view
      sourceType sourcePlan) :
    DemandTarget (.weakenUnderBinding scope constructed bound)
      sourceType sourcePlan := by
  have sourceEq : sourceType.subst FinFun.weaken.asSubst =
      sourceType.weaken := by
    simpa only [LambdaPFC.Ty.weaken] using
      LambdaPFC.Ty.subst_asSubst sourceType FinFun.weaken
  change DemandPlanModel (sourceContext.snoc boundType)
    (boundPlan.context targetContext) (scope.bind bound).view
    (sourceType.subst FinFun.weaken.asSubst)
    (sourcePlan.subst boundPlan.telescope.weaken.asSubst)
  rw [sourceEq]
  simpa only [TargetModelRenaming.plan_rename_asSubst] using
    DemandPlanModel.underBinding bound model

/-- The named closed binder-exchange action used by dependent pair members.
Its predecessor is exactly `weakenUnderBinding`; its lifted bound is the
factorization-safe weakening of the retained first model. -/
noncomputable def exchangeUnderBinding
    {sourceArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (constructed : ConstructedScope scope)
    {boundType firstType : LambdaPFC.Ty sourceArity}
    {boundPlan firstPlan : ValuePlan sig}
    (bound : ProducerPlanModel sourceContext targetContext scope.view
      boundType boundPlan)
    (first : ProducerPlanModel sourceContext targetContext scope.view
      firstType firstPlan) :=
  ModelInstantiation.lift (.weakenUnderBinding scope constructed bound)
    (weakenUnderBindingProducerTarget scope constructed bound first)

/-- Opening after a typed target rename cancels an older positive model's
source weakening and retains its exact target-renamed structure. -/
noncomputable def openAtTargetRenameWeakenedProducerTarget
    {sourceArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {source target : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx source}
    {targetTargetContext : SystemFCoExt.Ctx target}
    (scope : ScopeModel sourceContext sourceTargetContext)
    (constructed : ConstructedScope scope)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
    {boundType : LambdaPFC.Ty sourceArity}
    {path : LambdaPFC.Path sourceArity}
    (precise : LambdaPFC.Path.Ty sourceContext path (.ty boundType))
    {boundPlan : ValuePlan source}
    (replacement : ProducerPlanModel sourceContext sourceTargetContext
      scope.view boundType boundPlan)
    (arguments : Telescope.Args targetTargetContext
      (boundPlan.rename mapping).telescope)
    {olderType : LambdaPFC.Ty sourceArity}
    {olderPlan : ValuePlan source}
    (older : ProducerPlanModel sourceContext sourceTargetContext scope.view
      olderType olderPlan) :
    ProducerTarget (.openAtTargetRename scope constructed mapping typed
      precise replacement arguments) olderType.weaken
      (olderPlan.rename boundPlan.telescope.weaken) := by
  have sourceCancel :
      olderType.weaken.subst (PathSubst.openAt path) = olderType :=
    LambdaPFC.Ty.weaken_open olderType path
  have targetCancel := ValuePlan.rename_weaken_openAfterRename_cancel
    olderPlan boundPlan mapping arguments
  change ProducerPlanModel sourceContext targetTargetContext
    (scope.targetRename mapping typed).view
    (olderType.weaken.subst (PathSubst.openAt path))
    ((olderPlan.rename boundPlan.telescope.weaken).subst
      ((boundPlan.telescope.liftRename mapping).asSubst.comp
        arguments.substitution))
  rw [sourceCancel, targetCancel]
  exact TargetModelRenaming.producer older mapping typed

/-- Negative analogue of
`openAtTargetRenameWeakenedProducerTarget`. -/
noncomputable def openAtTargetRenameWeakenedDemandTarget
    {sourceArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {source target : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx source}
    {targetTargetContext : SystemFCoExt.Ctx target}
    (scope : ScopeModel sourceContext sourceTargetContext)
    (constructed : ConstructedScope scope)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
    {boundType : LambdaPFC.Ty sourceArity}
    {path : LambdaPFC.Path sourceArity}
    (precise : LambdaPFC.Path.Ty sourceContext path (.ty boundType))
    {boundPlan : ValuePlan source}
    (replacement : ProducerPlanModel sourceContext sourceTargetContext
      scope.view boundType boundPlan)
    (arguments : Telescope.Args targetTargetContext
      (boundPlan.rename mapping).telescope)
    {olderType : LambdaPFC.Ty sourceArity}
    {olderPlan : ValuePlan source}
    (older : DemandPlanModel sourceContext sourceTargetContext scope.view
      olderType olderPlan) :
    DemandTarget (.openAtTargetRename scope constructed mapping typed precise
      replacement arguments) olderType.weaken
      (olderPlan.rename boundPlan.telescope.weaken) := by
  have sourceCancel :
      olderType.weaken.subst (PathSubst.openAt path) = olderType :=
    LambdaPFC.Ty.weaken_open olderType path
  have targetCancel := ValuePlan.rename_weaken_openAfterRename_cancel
    olderPlan boundPlan mapping arguments
  change DemandPlanModel sourceContext targetTargetContext
    (scope.targetRename mapping typed).view
    (olderType.weaken.subst (PathSubst.openAt path))
    ((olderPlan.rename boundPlan.telescope.weaken).subst
      ((boundPlan.telescope.liftRename mapping).asSubst.comp
        arguments.substitution))
  rw [sourceCancel, targetCancel]
  exact TargetModelRenaming.demand older mapping typed

section AtomicTargets

variable {sourceArity targetArity : Nat}
variable {sourceContext : LambdaPFC.Ctx sourceArity}
variable {targetSourceContext : LambdaPFC.Ctx targetArity}
variable {sourceSig targetSig : Sig}
variable {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
variable {targetTargetContext : SystemFCoExt.Ctx targetSig}
variable {sourceView : ScopeView sourceArity sourceTargetContext}
variable {targetView : ScopeView targetArity targetTargetContext}
variable {sourceSubstitution : PathSubst sourceArity targetArity}
variable {targetSubstitution : Subst sourceSig targetSig}
variable (action : ModelInstantiation sourceContext targetSourceContext
  sourceTargetContext targetTargetContext sourceView targetView
  sourceSubstitution targetSubstitution)

noncomputable def bottomProducerTarget :
    ProducerTarget action .Bot (Bot.plan sourceSig) := by
  exact .bottom

noncomputable def topProducerTarget :
    ProducerTarget action .Top (Top.plan sourceSig) := by
  exact .top

noncomputable def bottomDemandTarget :
    DemandTarget action .Bot (Bot.plan sourceSig) := by
  exact .bottom

noncomputable def opaqueDemandTarget (sourceType : LambdaPFC.Ty sourceArity) :
    DemandTarget action sourceType (Top.plan sourceSig) := by
  exact .opaque _

end AtomicTargets

noncomputable def functionProducerTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {domain : LambdaPFC.Ty sourceArity}
    {domainPlan : ValuePlan sourceSig}
    {codomain : LambdaPFC.Ty (sourceArity + 1)}
    {codomainPlan : ValuePlan domainPlan.scope}
    (domainTarget : BidirectionalTarget action domain domainPlan)
    (codomainTarget : ProducerTarget
      (.lift action domainTarget.producer) codomain codomainPlan) :
    ProducerTarget (sourceArity := sourceArity)
      (targetArity := targetArity) (sourceSig := sourceSig)
      (targetSig := targetSig) (sourceContext := sourceContext)
      (targetSourceContext := targetSourceContext)
      (sourceTargetContext := sourceTargetContext)
      (targetTargetContext := targetTargetContext)
      (sourceView := sourceView) (targetView := targetView)
      (sourceSubstitution := sourceSubstitution)
      (targetSubstitution := targetSubstitution) action
      (.Fun domain codomain)
      (@Function.plan sourceSig domainPlan codomainPlan) := by
  have result := ProducerPlanModel.function domainTarget codomainTarget
  change ProducerPlanModel targetSourceContext targetTargetContext targetView
    ((LambdaPFC.Ty.Fun domain codomain).subst sourceSubstitution)
    ((Function.plan domainPlan codomainPlan).subst targetSubstitution)
  exact (Function.plan_subst domainPlan codomainPlan
    targetSubstitution).symm ▸ result

noncomputable def selectionProducerTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {path : LambdaPFC.Path sourceArity} {label : LambdaPFC.Name}
    {origin : SelectionOrigin sourceContext path label}
    {plan : ValuePlan sourceSig}
    (selected : SelectionTarget action origin plan) :
    ProducerTarget action (.TSel path label) plan := by
  exact .selection selected

noncomputable def singletonProducerTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {path : LambdaPFC.Path sourceArity}
    {referent : LambdaPFC.Ty sourceArity} {plan : ValuePlan sourceSig}
    (precise : LambdaPFC.Path.Ty sourceContext path (.ty referent))
    (targetReferent : ProducerTarget action referent plan) :
    ProducerTarget action (.Single path) plan := by
  exact .singleton (PathTyping.subst action.pairing.sourceTyped precise)
    targetReferent

noncomputable def selectionDemandTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {path : LambdaPFC.Path sourceArity} {label : LambdaPFC.Name}
    {origin : SelectionOrigin sourceContext path label}
    {plan : ValuePlan sourceSig}
    (selected : SelectionTarget action origin plan) :
    DemandTarget action (.TSel path label) plan := by
  exact .selection selected

noncomputable def singletonDemandTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {path : LambdaPFC.Path sourceArity}
    {referent : LambdaPFC.Ty sourceArity} {plan : ValuePlan sourceSig}
    (precise : LambdaPFC.Path.Ty sourceContext path (.ty referent))
    (targetReferent : ProducerTarget action referent plan) :
    DemandTarget action (.Single path) plan := by
  exact .singleton (PathTyping.subst action.pairing.sourceTyped precise)
    targetReferent

noncomputable def selectionBetweenTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {path : LambdaPFC.Path sourceArity} {label : LambdaPFC.Name}
    {origin : SelectionOrigin sourceContext path label}
    {lowerPlan upperPlan selectedPlan : ValuePlan sourceSig}
    (targetBounds : IntervalDemandTarget action origin.lower origin.upper
      lowerPlan upperPlan)
    (lowerToSelected : StableIdentity.Adapter sourceTargetContext lowerPlan
      selectedPlan)
    (selectedToUpper : StableIdentity.Adapter sourceTargetContext selectedPlan
      upperPlan) : SelectionTarget action origin selectedPlan := by
  exact .between targetBounds
    (StableIdentity.Adapter.subst lowerToSelected targetSubstitution
      action.pairing.targetTyped)
    (StableIdentity.Adapter.subst selectedToUpper targetSubstitution
      action.pairing.targetTyped)

noncomputable def properPairProducerTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {first : LambdaPFC.Ty sourceArity} {firstPlan : ValuePlan sourceSig}
    {member : LambdaPFC.Ty (sourceArity + 1)}
    {memberPlan : ValuePlan firstPlan.scope} {label : LambdaPFC.Name}
    (firstTarget : ProducerTarget action first firstPlan)
    (memberTarget : ProducerTarget (.lift action firstTarget) member
      memberPlan) :
    ProducerTarget (sourceArity := sourceArity)
      (targetArity := targetArity) (sourceSig := sourceSig)
      (targetSig := targetSig) (sourceContext := sourceContext)
      (targetSourceContext := targetSourceContext)
      (sourceTargetContext := sourceTargetContext)
      (targetTargetContext := targetTargetContext)
      (sourceView := sourceView) (targetView := targetView)
      (sourceSubstitution := sourceSubstitution)
      (targetSubstitution := targetSubstitution) action
      (.Pair first label (.ty member))
      (@Pair.Proper.plan sourceSig firstPlan memberPlan) := by
  have result := ProducerPlanModel.properPair (label := label) firstTarget
    memberTarget
  change ProducerPlanModel targetSourceContext targetTargetContext targetView
    ((LambdaPFC.Ty.Pair first label (.ty member)).subst sourceSubstitution)
    ((Pair.Proper.plan firstPlan memberPlan).subst targetSubstitution)
  exact (Pair.Proper.plan_subst firstPlan memberPlan
    targetSubstitution).symm ▸ result

noncomputable def intervalPairProducerTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {first : LambdaPFC.Ty sourceArity} {firstPlan : ValuePlan sourceSig}
    {lower upper : LambdaPFC.Ty (sourceArity + 1)}
    {lowerPlan upperPlan : ValuePlan firstPlan.scope}
    {label : LambdaPFC.Name}
    (firstTarget : ProducerTarget action first firstPlan)
    (memberTarget : IntervalProducerTarget (.lift action firstTarget)
      lower upper lowerPlan upperPlan) :
    ProducerTarget action (.Pair first label (.intv lower upper))
      (Pair.Interval.plan firstPlan lowerPlan.inputTy upperPlan.inputTy) := by
  have result := ProducerPlanModel.intervalPair (label := label) firstTarget
    memberTarget
  have planEq := Pair.Interval.plan_subst firstPlan lowerPlan.inputTy
    upperPlan.inputTy targetSubstitution
  rw [ValuePlan.inputTy_subst, ValuePlan.inputTy_subst] at planEq
  change ProducerPlanModel targetSourceContext targetTargetContext targetView
    ((LambdaPFC.Ty.Pair first label (.intv lower upper)).subst
      sourceSubstitution)
    ((Pair.Interval.plan firstPlan lowerPlan.inputTy upperPlan.inputTy).subst
      targetSubstitution)
  exact planEq.symm ▸ result

noncomputable def functionDemandTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {domain : LambdaPFC.Ty sourceArity} {domainPlan : ValuePlan sourceSig}
    {codomain : LambdaPFC.Ty (sourceArity + 1)}
    {codomainPlan : ValuePlan domainPlan.scope}
    (domainTarget : ProducerTarget action domain domainPlan)
    (codomainTarget : DemandTarget (.lift action domainTarget) codomain
      codomainPlan) :
    DemandTarget action (.Fun domain codomain)
      (Function.plan domainPlan codomainPlan) := by
  have result := DemandPlanModel.function domainTarget codomainTarget
  change DemandPlanModel targetSourceContext targetTargetContext targetView
    ((LambdaPFC.Ty.Fun domain codomain).subst sourceSubstitution)
    ((Function.plan domainPlan codomainPlan).subst targetSubstitution)
  exact (Function.plan_subst domainPlan codomainPlan
    targetSubstitution).symm ▸ result

noncomputable def properPairDemandTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {first : LambdaPFC.Ty sourceArity} {firstPlan : ValuePlan sourceSig}
    {member : LambdaPFC.Ty (sourceArity + 1)}
    {memberPlan : ValuePlan firstPlan.scope} {label : LambdaPFC.Name}
    (firstTarget : BidirectionalTarget action first firstPlan)
    (memberTarget : BidirectionalTarget (.lift action firstTarget.producer)
      member memberPlan) :
    DemandTarget action (.Pair first label (.ty member))
      (Pair.Proper.plan firstPlan memberPlan) := by
  have result := DemandPlanModel.properPair (label := label) firstTarget
    memberTarget
  change DemandPlanModel targetSourceContext targetTargetContext targetView
    ((LambdaPFC.Ty.Pair first label (.ty member)).subst sourceSubstitution)
    ((Pair.Proper.plan firstPlan memberPlan).subst targetSubstitution)
  exact (Pair.Proper.plan_subst firstPlan memberPlan
    targetSubstitution).symm ▸ result

noncomputable def intervalPairDemandTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {first : LambdaPFC.Ty sourceArity} {firstPlan : ValuePlan sourceSig}
    {lower upper : LambdaPFC.Ty (sourceArity + 1)}
    {lowerPlan upperPlan : ValuePlan firstPlan.scope}
    {label : LambdaPFC.Name}
    (firstTarget : BidirectionalTarget action first firstPlan)
    (memberTarget : IntervalBidirectionalTarget
      (.lift action firstTarget.producer) lower upper lowerPlan upperPlan) :
    DemandTarget action (.Pair first label (.intv lower upper))
      (Pair.Interval.plan firstPlan lowerPlan.inputTy upperPlan.inputTy) := by
  have result := DemandPlanModel.intervalPair (label := label) firstTarget
    memberTarget
  have planEq := Pair.Interval.plan_subst firstPlan lowerPlan.inputTy
    upperPlan.inputTy targetSubstitution
  rw [ValuePlan.inputTy_subst, ValuePlan.inputTy_subst] at planEq
  change DemandPlanModel targetSourceContext targetTargetContext targetView
    ((LambdaPFC.Ty.Pair first label (.intv lower upper)).subst
      sourceSubstitution)
    ((Pair.Interval.plan firstPlan lowerPlan.inputTy upperPlan.inputTy).subst
      targetSubstitution)
  exact planEq.symm ▸ result

noncomputable def boundTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {boundType : LambdaPFC.Ty sourceArity}
    {boundPlan : ValuePlan sourceSig}
    {sourceSubstitution : PathSubst (sourceArity + 1) targetArity}
    {targetSubstitution : Subst boundPlan.scope targetSig}
    (action : ModelInstantiation (sourceContext.snoc boundType)
      targetSourceContext (boundPlan.context sourceTargetContext)
      targetTargetContext (ScopeView.bindPlan sourceView boundPlan) targetView
      sourceSubstitution targetSubstitution) :
    ProducerTarget action boundType.weaken
      (boundPlan.rename boundPlan.telescope.weaken) := by
  simpa only [LambdaPFC.Ctx.lookup, Fin.cases_zero,
    TranslationInterfaces.ScopeView.bindPlan_here,
    TranslationInterfaces.ValueInterface.ofArguments_plan] using
    action.pairing.slotModel 0

noncomputable def underLiftTarget
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (previous : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {boundType : LambdaPFC.Ty sourceArity}
    {boundPlan : ValuePlan sourceSig}
    (newBound : ProducerPlanModel targetSourceContext targetTargetContext
      targetView (boundType.subst sourceSubstitution)
      (boundPlan.subst targetSubstitution))
    {olderType : LambdaPFC.Ty sourceArity}
    {olderPlan : ValuePlan sourceSig}
    (newOlder : ProducerPlanModel targetSourceContext targetTargetContext
      targetView (olderType.subst sourceSubstitution)
      (olderPlan.subst targetSubstitution)) :
    ProducerTarget (sourceArity := sourceArity + 1)
      (targetArity := targetArity + 1) (sourceSig := boundPlan.scope)
      (targetSig := (boundPlan.subst targetSubstitution).scope)
      (sourceContext := sourceContext.snoc boundType)
      (targetSourceContext := targetSourceContext.snoc
        (boundType.subst sourceSubstitution))
      (sourceTargetContext := boundPlan.context sourceTargetContext)
      (targetTargetContext :=
        (boundPlan.subst targetSubstitution).context targetTargetContext)
      (sourceView := ScopeView.bindPlan sourceView boundPlan)
      (targetView := ScopeView.bindPlan targetView
        (boundPlan.subst targetSubstitution))
      (sourceSubstitution := sourceSubstitution.lift)
      (ModelInstantiation.lift (boundType := boundType)
        (boundPlan := boundPlan) (sourceContext := sourceContext)
        (targetSourceContext := targetSourceContext)
        (sourceTargetContext := sourceTargetContext)
        (targetTargetContext := targetTargetContext)
        (sourceView := sourceView) (targetView := targetView)
        (sourceSubstitution := sourceSubstitution)
        (targetSubstitution := targetSubstitution) previous newBound)
      olderType.weaken
      (olderPlan.rename boundPlan.telescope.weaken) := by
  cases boundPlan with
  | mk observations =>
      simp only [ProducerTarget]
      rw [Ty.weaken_subst_lift]
      exact (ValuePlan.rename_weaken_subst_lift olderPlan
        { observations := observations } targetSubstitution).symm ▸
          ProducerPlanModel.underBinding newBound newOlder

end ModelInstantiation

/-! ## Closed model/action coherence -/

mutual

inductive ProducerInstantiationCoherence :
    {sourceArity targetArity : Nat} ->
    {sourceContext : LambdaPFC.Ctx sourceArity} ->
    {targetSourceContext : LambdaPFC.Ctx targetArity} ->
    {sourceSig targetSig : Sig} ->
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig} ->
    {targetTargetContext : SystemFCoExt.Ctx targetSig} ->
    {sourceView : ScopeView sourceArity sourceTargetContext} ->
    {targetView : ScopeView targetArity targetTargetContext} ->
    {sourceSubstitution : PathSubst sourceArity targetArity} ->
    {targetSubstitution : Subst sourceSig targetSig} ->
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution) ->
    {sourceType : LambdaPFC.Ty sourceArity} ->
    {plan : ValuePlan sourceSig} ->
    ProducerPlanModel sourceContext sourceTargetContext sourceView sourceType
      plan -> ModelInstantiation.ProducerTarget action sourceType plan ->
    Type where
  | bottom : ProducerInstantiationCoherence action .bottom
      (ModelInstantiation.bottomProducerTarget action)
  | top : ProducerInstantiationCoherence action .top
      (ModelInstantiation.topProducerTarget action)
  | singleton
      (precise : LambdaPFC.Path.Ty sourceContext path (.ty referent))
      (referent : ProducerInstantiationCoherence action sourceReferent
        targetReferent) :
      ProducerInstantiationCoherence action
        (.singleton precise sourceReferent)
        (ModelInstantiation.singletonProducerTarget action precise
          targetReferent)
  | selection
      (selected : SelectionInstantiationCoherence action sourceSelection
        targetSelection) :
      ProducerInstantiationCoherence action (.selection sourceSelection)
        (ModelInstantiation.selectionProducerTarget action targetSelection)
  | function
      (domain : BidirectionalInstantiationCoherence action sourceDomain
        targetDomain)
      (codomain : ProducerInstantiationCoherence
        (.lift action targetDomain.producer) sourceCodomain targetCodomain) :
      ProducerInstantiationCoherence action
        (.function sourceDomain sourceCodomain)
        (ModelInstantiation.functionProducerTarget action targetDomain
          targetCodomain)
  | properPair
      (first : ProducerInstantiationCoherence action sourceFirst targetFirst)
      (member : ProducerInstantiationCoherence (.lift action targetFirst)
        sourceMember targetMember) :
      ProducerInstantiationCoherence action
        (.properPair (label := label) sourceFirst sourceMember)
        (ModelInstantiation.properPairProducerTarget action targetFirst
          targetMember)
  | intervalPair
      (first : ProducerInstantiationCoherence action sourceFirst targetFirst)
      (member : IntervalProducerInstantiationCoherence
        (.lift action targetFirst) sourceMember targetMember) :
      ProducerInstantiationCoherence action
        (.intervalPair (label := label) sourceFirst sourceMember)
        (ModelInstantiation.intervalPairProducerTarget action targetFirst
          targetMember)
  | targetRename
      (mapping : Rename preSig sourceSig)
      (typed : Rename.Typed preTargetContext sourceTargetContext mapping)
      (action : ModelInstantiation sourceContext targetSourceContext
        sourceTargetContext targetTargetContext
        (preView.rename mapping typed) targetView sourceSubstitution
        targetSubstitution)
      (sourceModel : ProducerPlanModel sourceContext preTargetContext preView
        sourceType sourcePlan)
      (targetModel : ModelInstantiation.ProducerTarget
        (.preTargetRename mapping typed action) sourceType sourcePlan)
      (previous : ProducerInstantiationCoherence
        (.preTargetRename mapping typed action) sourceModel targetModel) :
      ProducerInstantiationCoherence action
        (.targetRename sourceModel mapping typed)
        (ModelInstantiation.targetRenameProducerTarget (mapping := mapping)
          (typed := typed) targetModel)
  | targetRenameScope
      {sourceArity : Nat}
      {sourceContext : LambdaPFC.Ctx sourceArity}
      {sourceSig targetSig : Sig}
      {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
      {targetTargetContext : SystemFCoExt.Ctx targetSig}
      {sourceType : LambdaPFC.Ty sourceArity}
      {sourcePlan : ValuePlan sourceSig}
      (scope : ScopeModel sourceContext sourceTargetContext)
      (constructed : ConstructedScope scope)
      (mapping : Rename sourceSig targetSig)
      (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
      (sourceModel : ProducerPlanModel sourceContext sourceTargetContext
        scope.view sourceType sourcePlan) :
      ProducerInstantiationCoherence
        (.targetRenameScope scope constructed mapping typed) sourceModel
        (ModelInstantiation.targetRenameScopeProducerTarget
          (source := sourceSig) (target := targetSig)
          (sourceTargetContext := sourceTargetContext)
          (targetTargetContext := targetTargetContext) scope constructed
          mapping typed sourceModel)
  | weakenUnderBinding
      {sourceArity : Nat}
      {sourceContext : LambdaPFC.Ctx sourceArity}
      {sourceSig : Sig}
      {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
      {boundType sourceType : LambdaPFC.Ty sourceArity}
      {boundPlan sourcePlan : ValuePlan sourceSig}
      (scope : ScopeModel sourceContext sourceTargetContext)
      (constructed : ConstructedScope scope)
      (bound : ProducerPlanModel sourceContext sourceTargetContext scope.view
        boundType boundPlan)
      (sourceModel : ProducerPlanModel sourceContext sourceTargetContext
        scope.view sourceType sourcePlan) :
      ProducerInstantiationCoherence
        (.weakenUnderBinding scope constructed bound) sourceModel
        (ModelInstantiation.weakenUnderBindingProducerTarget scope constructed
          bound sourceModel)
  | boundOpen
      (scope : ScopeModel sourceContext targetTargetContext)
      (precise : LambdaPFC.Path.Ty sourceContext path (.ty boundType))
      (replacement : ProducerPlanModel sourceContext targetTargetContext
        scope.view boundType boundPlan)
      (arguments : Telescope.Args targetTargetContext boundPlan.telescope) :
      ProducerInstantiationCoherence
        (.openAt scope precise replacement arguments) (.bound replacement)
        (ModelInstantiation.boundTarget
          (.openAt scope precise replacement arguments))
  | boundLift
      (bound : ProducerInstantiationCoherence previous sourceBound
        targetBound) :
      ProducerInstantiationCoherence (.lift previous targetBound)
        (.bound sourceBound)
        (ModelInstantiation.boundTarget (.lift previous targetBound))
  | underBindingOpen
      (scope : ScopeModel sourceContext targetTargetContext)
      (precise : LambdaPFC.Path.Ty sourceContext path (.ty boundType))
      (replacement : ProducerPlanModel sourceContext targetTargetContext
        scope.view boundType boundPlan)
      (arguments : Telescope.Args targetTargetContext boundPlan.telescope)
      (older : ProducerPlanModel sourceContext targetTargetContext scope.view
        olderType olderPlan) :
      ProducerInstantiationCoherence
        (.openAt scope precise replacement arguments)
        (.underBinding replacement older)
        (ModelInstantiation.openWeakenedProducer older path arguments)
  | boundOpenAtTargetRename
      {sourceArity : Nat}
      {sourceContext : LambdaPFC.Ctx sourceArity}
      {sourceSig targetSig : Sig}
      {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
      {targetTargetContext : SystemFCoExt.Ctx targetSig}
      {boundType : LambdaPFC.Ty sourceArity}
      {path : LambdaPFC.Path sourceArity}
      {boundPlan : ValuePlan sourceSig}
      (scope : ScopeModel sourceContext sourceTargetContext)
      (constructed : ConstructedScope scope)
      (mapping : Rename sourceSig targetSig)
      (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
      (precise : LambdaPFC.Path.Ty sourceContext path (.ty boundType))
      (replacement : ProducerPlanModel sourceContext sourceTargetContext
        scope.view boundType boundPlan)
      (arguments : Telescope.Args targetTargetContext
        (boundPlan.rename mapping).telescope) :
      ProducerInstantiationCoherence
        (.openAtTargetRename scope constructed mapping typed precise
          replacement arguments)
        (.bound replacement)
        (ModelInstantiation.boundTarget
          (.openAtTargetRename scope constructed mapping typed precise
            replacement arguments))
  | underBindingOpenAtTargetRename
      {sourceArity : Nat}
      {sourceContext : LambdaPFC.Ctx sourceArity}
      {sourceSig targetSig : Sig}
      {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
      {targetTargetContext : SystemFCoExt.Ctx targetSig}
      {boundType olderType : LambdaPFC.Ty sourceArity}
      {path : LambdaPFC.Path sourceArity}
      {boundPlan olderPlan : ValuePlan sourceSig}
      (scope : ScopeModel sourceContext sourceTargetContext)
      (constructed : ConstructedScope scope)
      (mapping : Rename sourceSig targetSig)
      (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
      (precise : LambdaPFC.Path.Ty sourceContext path (.ty boundType))
      (replacement : ProducerPlanModel sourceContext sourceTargetContext
        scope.view boundType boundPlan)
      (arguments : Telescope.Args targetTargetContext
        (boundPlan.rename mapping).telescope)
      (older : ProducerPlanModel sourceContext sourceTargetContext scope.view
        olderType olderPlan) :
      ProducerInstantiationCoherence
        (.openAtTargetRename scope constructed mapping typed precise
          replacement arguments)
        (.underBinding replacement older)
        (ModelInstantiation.openAtTargetRenameWeakenedProducerTarget
          (source := sourceSig) (target := targetSig)
          (sourceTargetContext := sourceTargetContext)
          (targetTargetContext := targetTargetContext) scope constructed
          mapping typed precise replacement arguments older)
  | underBindingLift
      (bound : ProducerInstantiationCoherence previous sourceBound
        targetBound)
      (older : ProducerInstantiationCoherence previous sourceOlder
        targetOlder) :
      ProducerInstantiationCoherence (.lift previous targetBound)
        (.underBinding sourceBound sourceOlder)
        (ModelInstantiation.underLiftTarget previous targetBound targetOlder)

inductive DemandInstantiationCoherence :
    {sourceArity targetArity : Nat} ->
    {sourceContext : LambdaPFC.Ctx sourceArity} ->
    {targetSourceContext : LambdaPFC.Ctx targetArity} ->
    {sourceSig targetSig : Sig} ->
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig} ->
    {targetTargetContext : SystemFCoExt.Ctx targetSig} ->
    {sourceView : ScopeView sourceArity sourceTargetContext} ->
    {targetView : ScopeView targetArity targetTargetContext} ->
    {sourceSubstitution : PathSubst sourceArity targetArity} ->
    {targetSubstitution : Subst sourceSig targetSig} ->
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution) ->
    {sourceType : LambdaPFC.Ty sourceArity} ->
    {plan : ValuePlan sourceSig} ->
    DemandPlanModel sourceContext sourceTargetContext sourceView sourceType
      plan -> ModelInstantiation.DemandTarget action sourceType plan ->
    Type where
  | opaque : DemandInstantiationCoherence action (.opaque sourceType)
      (ModelInstantiation.opaqueDemandTarget action sourceType)
  | bottom : DemandInstantiationCoherence action .bottom
      (ModelInstantiation.bottomDemandTarget action)
  | singleton
      (precise : LambdaPFC.Path.Ty sourceContext path (.ty referent))
      (referent : ProducerInstantiationCoherence action sourceReferent
        targetReferent) :
      DemandInstantiationCoherence action
        (.singleton precise sourceReferent)
        (ModelInstantiation.singletonDemandTarget action precise
          targetReferent)
  | selection
      (selected : SelectionInstantiationCoherence action sourceSelection
        targetSelection) :
      DemandInstantiationCoherence action (.selection sourceSelection)
        (ModelInstantiation.selectionDemandTarget action targetSelection)
  | function
      (domain : ProducerInstantiationCoherence action sourceDomain
        targetDomain)
      (codomain : DemandInstantiationCoherence (.lift action targetDomain)
        sourceCodomain targetCodomain) :
      DemandInstantiationCoherence action
        (.function sourceDomain sourceCodomain)
        (ModelInstantiation.functionDemandTarget action targetDomain
          targetCodomain)
  | properPair
      (first : BidirectionalInstantiationCoherence action sourceFirst
        targetFirst)
      (member : BidirectionalInstantiationCoherence
        (.lift action targetFirst.producer) sourceMember targetMember) :
      DemandInstantiationCoherence action
        (.properPair (label := label) sourceFirst sourceMember)
        (ModelInstantiation.properPairDemandTarget action targetFirst
          targetMember)
  | intervalPair
      (first : BidirectionalInstantiationCoherence action sourceFirst
        targetFirst)
      (member : IntervalBidirectionalInstantiationCoherence
        (.lift action targetFirst.producer) sourceMember targetMember) :
      DemandInstantiationCoherence action
        (.intervalPair (label := label) sourceFirst sourceMember)
        (ModelInstantiation.intervalPairDemandTarget action targetFirst
          targetMember)
  | targetRename
      (mapping : Rename preSig sourceSig)
      (typed : Rename.Typed preTargetContext sourceTargetContext mapping)
      (action : ModelInstantiation sourceContext targetSourceContext
        sourceTargetContext targetTargetContext
        (preView.rename mapping typed) targetView sourceSubstitution
        targetSubstitution)
      (sourceModel : DemandPlanModel sourceContext preTargetContext preView
        sourceType sourcePlan)
      (targetModel : ModelInstantiation.DemandTarget
        (.preTargetRename mapping typed action) sourceType sourcePlan)
      (previous : DemandInstantiationCoherence
        (.preTargetRename mapping typed action) sourceModel targetModel) :
      DemandInstantiationCoherence action
        (.targetRename sourceModel mapping typed)
        (ModelInstantiation.targetRenameDemandTarget (mapping := mapping)
          (typed := typed) targetModel)
  | targetRenameScope
      {sourceArity : Nat}
      {sourceContext : LambdaPFC.Ctx sourceArity}
      {sourceSig targetSig : Sig}
      {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
      {targetTargetContext : SystemFCoExt.Ctx targetSig}
      {sourceType : LambdaPFC.Ty sourceArity}
      {sourcePlan : ValuePlan sourceSig}
      (scope : ScopeModel sourceContext sourceTargetContext)
      (constructed : ConstructedScope scope)
      (mapping : Rename sourceSig targetSig)
      (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
      (sourceModel : DemandPlanModel sourceContext sourceTargetContext
        scope.view sourceType sourcePlan) :
      DemandInstantiationCoherence
        (.targetRenameScope scope constructed mapping typed) sourceModel
        (ModelInstantiation.targetRenameScopeDemandTarget
          (source := sourceSig) (target := targetSig)
          (sourceTargetContext := sourceTargetContext)
          (targetTargetContext := targetTargetContext) scope constructed
          mapping typed sourceModel)
  | weakenUnderBinding
      {sourceArity : Nat}
      {sourceContext : LambdaPFC.Ctx sourceArity}
      {sourceSig : Sig}
      {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
      {boundType sourceType : LambdaPFC.Ty sourceArity}
      {boundPlan sourcePlan : ValuePlan sourceSig}
      (scope : ScopeModel sourceContext sourceTargetContext)
      (constructed : ConstructedScope scope)
      (bound : ProducerPlanModel sourceContext sourceTargetContext scope.view
        boundType boundPlan)
      (sourceModel : DemandPlanModel sourceContext sourceTargetContext
        scope.view sourceType sourcePlan) :
      DemandInstantiationCoherence
        (.weakenUnderBinding scope constructed bound) sourceModel
        (ModelInstantiation.weakenUnderBindingDemandTarget scope constructed
          bound sourceModel)
  | underBindingOpen
      {sourceArity : Nat}
      {sourceContext : LambdaPFC.Ctx sourceArity}
      {targetSig : Sig}
      {targetTargetContext : SystemFCoExt.Ctx targetSig}
      {boundType olderType : LambdaPFC.Ty sourceArity}
      {path : LambdaPFC.Path sourceArity}
      {boundPlan olderPlan : ValuePlan targetSig}
      (scope : ScopeModel sourceContext targetTargetContext)
      (precise : LambdaPFC.Path.Ty sourceContext path (.ty boundType))
      (replacement : ProducerPlanModel sourceContext targetTargetContext
        scope.view boundType boundPlan)
      (arguments : Telescope.Args targetTargetContext boundPlan.telescope)
      (older : DemandPlanModel sourceContext targetTargetContext scope.view
        olderType olderPlan) :
      DemandInstantiationCoherence
        (.openAt scope precise replacement arguments)
        (.underBinding replacement older)
        (ModelInstantiation.openWeakenedDemand older path arguments)
  | underBindingOpenAtTargetRename
      {sourceArity : Nat}
      {sourceContext : LambdaPFC.Ctx sourceArity}
      {sourceSig targetSig : Sig}
      {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
      {targetTargetContext : SystemFCoExt.Ctx targetSig}
      {boundType olderType : LambdaPFC.Ty sourceArity}
      {path : LambdaPFC.Path sourceArity}
      {boundPlan olderPlan : ValuePlan sourceSig}
      (scope : ScopeModel sourceContext sourceTargetContext)
      (constructed : ConstructedScope scope)
      (mapping : Rename sourceSig targetSig)
      (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
      (precise : LambdaPFC.Path.Ty sourceContext path (.ty boundType))
      (replacement : ProducerPlanModel sourceContext sourceTargetContext
        scope.view boundType boundPlan)
      (arguments : Telescope.Args targetTargetContext
        (boundPlan.rename mapping).telescope)
      (older : DemandPlanModel sourceContext sourceTargetContext scope.view
        olderType olderPlan) :
      DemandInstantiationCoherence
        (.openAtTargetRename scope constructed mapping typed precise
          replacement arguments)
        (.underBinding replacement older)
        (ModelInstantiation.openAtTargetRenameWeakenedDemandTarget
          (source := sourceSig) (target := targetSig)
          (sourceTargetContext := sourceTargetContext)
          (targetTargetContext := targetTargetContext) scope constructed
          mapping typed precise replacement arguments older)

inductive BidirectionalInstantiationCoherence :
    {sourceArity targetArity : Nat} ->
    {sourceContext : LambdaPFC.Ctx sourceArity} ->
    {targetSourceContext : LambdaPFC.Ctx targetArity} ->
    {sourceSig targetSig : Sig} ->
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig} ->
    {targetTargetContext : SystemFCoExt.Ctx targetSig} ->
    {sourceView : ScopeView sourceArity sourceTargetContext} ->
    {targetView : ScopeView targetArity targetTargetContext} ->
    {sourceSubstitution : PathSubst sourceArity targetArity} ->
    {targetSubstitution : Subst sourceSig targetSig} ->
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution) ->
    {sourceType : LambdaPFC.Ty sourceArity} ->
    {plan : ValuePlan sourceSig} ->
    BidirectionalPlanModel sourceContext sourceTargetContext sourceView
      sourceType plan ->
    ModelInstantiation.BidirectionalTarget action sourceType plan -> Type where
  | both
      (positive : ProducerInstantiationCoherence action sourcePositive
        targetPositive)
      (negative : DemandInstantiationCoherence action sourceNegative
        targetNegative) :
      BidirectionalInstantiationCoherence action
        (.both sourcePositive sourceNegative) (.both targetPositive targetNegative)

inductive SelectionInstantiationCoherence :
    {sourceArity targetArity : Nat} ->
    {sourceContext : LambdaPFC.Ctx sourceArity} ->
    {targetSourceContext : LambdaPFC.Ctx targetArity} ->
    {sourceSig targetSig : Sig} ->
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig} ->
    {targetTargetContext : SystemFCoExt.Ctx targetSig} ->
    {sourceView : ScopeView sourceArity sourceTargetContext} ->
    {targetView : ScopeView targetArity targetTargetContext} ->
    {sourceSubstitution : PathSubst sourceArity targetArity} ->
    {targetSubstitution : Subst sourceSig targetSig} ->
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution) ->
    {path : LambdaPFC.Path sourceArity} -> {label : LambdaPFC.Name} ->
    {origin : SelectionOrigin sourceContext path label} ->
    {plan : ValuePlan sourceSig} ->
    SelectionPlanModel sourceContext sourceTargetContext sourceView origin
      plan -> ModelInstantiation.SelectionTarget action origin plan -> Type where
  | between
      (bounds : IntervalDemandInstantiationCoherence action sourceBounds
        targetBounds) :
      SelectionInstantiationCoherence action
        (.between sourceBounds lowerToSelected selectedToUpper)
        (ModelInstantiation.selectionBetweenTarget action targetBounds
          lowerToSelected selectedToUpper)

inductive IntervalProducerInstantiationCoherence :
    {sourceArity targetArity : Nat} ->
    {sourceContext : LambdaPFC.Ctx sourceArity} ->
    {targetSourceContext : LambdaPFC.Ctx targetArity} ->
    {sourceSig targetSig : Sig} ->
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig} ->
    {targetTargetContext : SystemFCoExt.Ctx targetSig} ->
    {sourceView : ScopeView sourceArity sourceTargetContext} ->
    {targetView : ScopeView targetArity targetTargetContext} ->
    {sourceSubstitution : PathSubst sourceArity targetArity} ->
    {targetSubstitution : Subst sourceSig targetSig} ->
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution) ->
    {lower upper : LambdaPFC.Ty sourceArity} ->
    {lowerPlan upperPlan : ValuePlan sourceSig} ->
    IntervalProducerPlanModel sourceContext sourceTargetContext sourceView
      lower upper lowerPlan upperPlan ->
    ModelInstantiation.IntervalProducerTarget action lower upper lowerPlan
      upperPlan -> Type where
  | bounds
      (lower : DemandInstantiationCoherence action sourceLower targetLower)
      (upper : ProducerInstantiationCoherence action sourceUpper targetUpper) :
      IntervalProducerInstantiationCoherence action
        (.bounds sourceLower sourceUpper) (.bounds targetLower targetUpper)

inductive IntervalDemandInstantiationCoherence :
    {sourceArity targetArity : Nat} ->
    {sourceContext : LambdaPFC.Ctx sourceArity} ->
    {targetSourceContext : LambdaPFC.Ctx targetArity} ->
    {sourceSig targetSig : Sig} ->
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig} ->
    {targetTargetContext : SystemFCoExt.Ctx targetSig} ->
    {sourceView : ScopeView sourceArity sourceTargetContext} ->
    {targetView : ScopeView targetArity targetTargetContext} ->
    {sourceSubstitution : PathSubst sourceArity targetArity} ->
    {targetSubstitution : Subst sourceSig targetSig} ->
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution) ->
    {lower upper : LambdaPFC.Ty sourceArity} ->
    {lowerPlan upperPlan : ValuePlan sourceSig} ->
    IntervalDemandPlanModel sourceContext sourceTargetContext sourceView lower
      upper lowerPlan upperPlan ->
    ModelInstantiation.IntervalDemandTarget action lower upper lowerPlan
      upperPlan -> Type where
  | bounds
      (lower : ProducerInstantiationCoherence action sourceLower targetLower)
      (upper : DemandInstantiationCoherence action sourceUpper targetUpper) :
      IntervalDemandInstantiationCoherence action
        (.bounds sourceLower sourceUpper) (.bounds targetLower targetUpper)

inductive IntervalBidirectionalInstantiationCoherence :
    {sourceArity targetArity : Nat} ->
    {sourceContext : LambdaPFC.Ctx sourceArity} ->
    {targetSourceContext : LambdaPFC.Ctx targetArity} ->
    {sourceSig targetSig : Sig} ->
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig} ->
    {targetTargetContext : SystemFCoExt.Ctx targetSig} ->
    {sourceView : ScopeView sourceArity sourceTargetContext} ->
    {targetView : ScopeView targetArity targetTargetContext} ->
    {sourceSubstitution : PathSubst sourceArity targetArity} ->
    {targetSubstitution : Subst sourceSig targetSig} ->
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution) ->
    {lower upper : LambdaPFC.Ty sourceArity} ->
    {lowerPlan upperPlan : ValuePlan sourceSig} ->
    IntervalBidirectionalPlanModel sourceContext sourceTargetContext sourceView
      lower upper lowerPlan upperPlan ->
    ModelInstantiation.IntervalBidirectionalTarget action lower upper lowerPlan
      upperPlan -> Type where
  | both
      (positive : IntervalProducerInstantiationCoherence action sourcePositive
        targetPositive)
      (negative : IntervalDemandInstantiationCoherence action sourceNegative
        targetNegative) :
      IntervalBidirectionalInstantiationCoherence action
        (.both sourcePositive sourceNegative) (.both targetPositive targetNegative)

end

namespace ProducerInstantiationCoherence

/-- An exact structural certificate together with the explicit index and
model transports needed when a frozen producer was stored through a dependent
`simpa`.  The target remains determined by the closed certificate; this
wrapper does not accept a target-model callback. -/
structure Result
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {sourceType : LambdaPFC.Ty sourceArity}
    {sourcePlan : ValuePlan sourceSig}
    (source : ProducerPlanModel sourceContext sourceTargetContext sourceView
      sourceType sourcePlan) : Type where
  canonicalType : LambdaPFC.Ty sourceArity
  canonicalPlan : ValuePlan sourceSig
  sourceType_eq : sourceType = canonicalType
  sourcePlan_eq : sourcePlan = canonicalPlan
  canonicalSource : ProducerPlanModel sourceContext sourceTargetContext
    sourceView canonicalType canonicalPlan
  source_heq : HEq source canonicalSource
  target : ModelInstantiation.ProducerTarget action canonicalType canonicalPlan
  coherence : ProducerInstantiationCoherence action canonicalSource target

/-- Eliminate both explicit index equalities and the stored model `HEq`,
recovering exact coherence for the original frozen source model. -/
noncomputable def Result.transport
    {source : ProducerPlanModel sourceContext sourceTargetContext sourceView
      sourceType sourcePlan}
    (result : Result action source) :
    Sigma fun target : ModelInstantiation.ProducerTarget action sourceType
      sourcePlan => ProducerInstantiationCoherence action source target := by
  rcases result with
    ⟨_, _, rfl, rfl, canonicalSource, sourceHEq, target, coherence⟩
  have sourceEq : source = canonicalSource := eq_of_heq sourceHEq
  cases sourceEq
  exact ⟨target, coherence⟩

/-- The instantiated producer recovered from a sealed aligned certificate. -/
noncomputable def Result.instantiated
    {source : ProducerPlanModel sourceContext sourceTargetContext sourceView
      sourceType sourcePlan}
    (result : Result action source) :
    ModelInstantiation.ProducerTarget action sourceType sourcePlan :=
  result.transport.1

/-- Every canonical slot of an exactly opened `ScopeModel.bind` has a closed
model-instantiation certificate. -/
noncomputable def openSlot
    {sourceArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSig : Sig}
    {targetContext : SystemFCoExt.Ctx targetSig}
    (scope : ScopeModel sourceContext targetContext)
    {boundType : LambdaPFC.Ty sourceArity}
    {boundPlan : ValuePlan targetSig}
    {path : LambdaPFC.Path sourceArity}
    (precise : LambdaPFC.Path.Ty sourceContext path (.ty boundType))
    (replacement : ProducerPlanModel sourceContext targetContext scope.view
      boundType boundPlan)
    (arguments : Telescope.Args targetContext boundPlan.telescope)
    (index : Fin (sourceArity + 1)) :
    let action := ModelInstantiation.openAt scope precise replacement arguments
    Result action ((scope.bind replacement).slot index) := by
  dsimp only
  refine Fin.cases ?_ (fun older => ?_) index
  · let action := ModelInstantiation.openAt scope precise replacement arguments
    refine
      { canonicalType := boundType.weaken
        canonicalPlan := boundPlan.rename boundPlan.telescope.weaken
        sourceType_eq := ?_
        sourcePlan_eq := ?_
        canonicalSource := .bound replacement
        source_heq := ScopeModel.bind_slot_zero_heq scope replacement
        target := ModelInstantiation.boundTarget action
        coherence := ProducerInstantiationCoherence.boundOpen scope precise
          replacement arguments }
    · rfl
    · simpa only [ScopeModel.bind, ScopeView.bindPlan_here] using
        (ValueInterface.ofArguments_plan
          (boundPlan.rename boundPlan.telescope.weaken)
          (Telescope.Args.identity boundPlan.telescope targetContext))
  · let action := ModelInstantiation.openAt scope precise replacement arguments
    refine
      { canonicalType := (sourceContext.lookup older).weaken
        canonicalPlan :=
          (scope.view older).plan.rename boundPlan.telescope.weaken
        sourceType_eq := ?_
        sourcePlan_eq := ?_
        canonicalSource :=
          .underBinding replacement (scope.slot older)
        source_heq := ScopeModel.bind_slot_succ_heq scope replacement older
        target := ModelInstantiation.openWeakenedProducer (scope.slot older)
          path arguments
        coherence := ProducerInstantiationCoherence.underBindingOpen scope
          precise replacement arguments (scope.slot older) }
    · rfl
    · rfl

/-- Slot coherence lifts compositionally through one further modeled source
binder.  Older slots are recovered through their sealed results before the
structural `.underBindingLift` constructor is applied. -/
noncomputable def liftSlot
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    (scope : ScopeModel sourceContext sourceTargetContext)
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (previous : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext scope.view targetView
      sourceSubstitution targetSubstitution)
    {boundType : LambdaPFC.Ty sourceArity}
    {boundPlan : ValuePlan sourceSig}
    (sourceBound : ProducerPlanModel sourceContext sourceTargetContext
      scope.view boundType boundPlan)
    (targetBound : ModelInstantiation.ProducerTarget previous boundType
      boundPlan)
    (boundCoherence : ProducerInstantiationCoherence previous sourceBound
      targetBound)
    (olderCoherence : (index : Fin sourceArity) ->
      Result previous (scope.slot index))
    (index : Fin (sourceArity + 1)) :
    Result (.lift previous targetBound) ((scope.bind sourceBound).slot index) := by
  refine Fin.cases ?_ (fun older => ?_) index
  · let action := ModelInstantiation.lift previous targetBound
    refine
      { canonicalType := boundType.weaken
        canonicalPlan := boundPlan.rename boundPlan.telescope.weaken
        sourceType_eq := ?_
        sourcePlan_eq := ?_
        canonicalSource := .bound sourceBound
        source_heq := ScopeModel.bind_slot_zero_heq scope sourceBound
        target := ModelInstantiation.boundTarget action
        coherence :=
          ProducerInstantiationCoherence.boundLift boundCoherence }
    · rfl
    · simpa only [ScopeModel.bind, ScopeView.bindPlan_here] using
        (ValueInterface.ofArguments_plan
          (boundPlan.rename boundPlan.telescope.weaken)
          (Telescope.Args.identity boundPlan.telescope sourceTargetContext))
  · let action := ModelInstantiation.lift previous targetBound
    let olderExact := (olderCoherence older).transport
    refine
      { canonicalType := (sourceContext.lookup older).weaken
        canonicalPlan :=
          (scope.view older).plan.rename boundPlan.telescope.weaken
        sourceType_eq := ?_
        sourcePlan_eq := ?_
        canonicalSource :=
          .underBinding sourceBound (scope.slot older)
        source_heq := ScopeModel.bind_slot_succ_heq scope sourceBound older
        target := ModelInstantiation.underLiftTarget previous targetBound
          olderExact.1
        coherence := ProducerInstantiationCoherence.underBindingLift
          boundCoherence olderExact.2 }
    · rfl
    · rfl

end ProducerInstantiationCoherence

namespace IntervalProducerInstantiationCoherence

/-- Heterogeneous high-boundary wrapper for a retained positive interval
member. The instantiated interval is determined by its structural coherence
certificate; no endpoint model or transport callback is accepted. -/
structure Result
    {sourceArity targetArity : Nat}
    {sourceContext : LambdaPFC.Ctx sourceArity}
    {targetSourceContext : LambdaPFC.Ctx targetArity}
    {sourceSig targetSig : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
    {targetTargetContext : SystemFCoExt.Ctx targetSig}
    {sourceView : ScopeView sourceArity sourceTargetContext}
    {targetView : ScopeView targetArity targetTargetContext}
    {sourceSubstitution : PathSubst sourceArity targetArity}
    {targetSubstitution : Subst sourceSig targetSig}
    (action : ModelInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {lower upper : LambdaPFC.Ty sourceArity}
    {lowerPlan upperPlan : ValuePlan sourceSig}
    (source : IntervalProducerPlanModel sourceContext sourceTargetContext
      sourceView lower upper lowerPlan upperPlan) : Type where
  canonicalLower : LambdaPFC.Ty sourceArity
  canonicalUpper : LambdaPFC.Ty sourceArity
  canonicalLowerPlan : ValuePlan sourceSig
  canonicalUpperPlan : ValuePlan sourceSig
  lower_eq : lower = canonicalLower
  upper_eq : upper = canonicalUpper
  lowerPlan_eq : lowerPlan = canonicalLowerPlan
  upperPlan_eq : upperPlan = canonicalUpperPlan
  canonicalSource : IntervalProducerPlanModel sourceContext
    sourceTargetContext sourceView canonicalLower canonicalUpper
    canonicalLowerPlan canonicalUpperPlan
  source_heq : HEq source canonicalSource
  target : ModelInstantiation.IntervalProducerTarget action canonicalLower
    canonicalUpper canonicalLowerPlan canonicalUpperPlan
  coherence : IntervalProducerInstantiationCoherence action canonicalSource
    target

/-- Recover exact interval coherence after eliminating the retained endpoint
and model transports. -/
noncomputable def Result.transport
    {source : IntervalProducerPlanModel sourceContext sourceTargetContext
      sourceView lower upper lowerPlan upperPlan}
    (result : Result action source) :
    Sigma fun target : ModelInstantiation.IntervalProducerTarget action lower
      upper lowerPlan upperPlan =>
        IntervalProducerInstantiationCoherence action source target := by
  rcases result with
    ⟨_, _, _, _, rfl, rfl, rfl, rfl, canonicalSource, sourceHEq,
      target, coherence⟩
  have sourceEq : source = canonicalSource := eq_of_heq sourceHEq
  cases sourceEq
  exact ⟨target, coherence⟩

/-- The exact instantiated positive interval recovered from a sealed result. -/
noncomputable def Result.instantiated
    {source : IntervalProducerPlanModel sourceContext sourceTargetContext
      sourceView lower upper lowerPlan upperPlan}
    (result : Result action source) :
    ModelInstantiation.IntervalProducerTarget action lower upper lowerPlan
      upperPlan :=
  result.transport.1

end IntervalProducerInstantiationCoherence


end LambdaPToFCo.Full
