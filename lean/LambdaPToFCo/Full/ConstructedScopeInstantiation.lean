import LambdaPToFCo.Full.InterfaceArgumentCancellation
import LambdaPToFCo.Full.PairedInstantiation

/-!
# Constructed scopes and closed synchronized actions

Dependent pair projection must move structural models through three exact
scope operations: target-only renaming, insertion of a modeled source/target
binder, and opening a modeled binder after a target rename. These operations
cannot be implemented by equating `bindPlan` with a renamed `bindPlan`:
`ValueInterface` deliberately retains proof-relevant typing and argument
evidence.

This module instead rebuilds every substituted source slot from a retained
`ScopeModel`. `ConstructedScope` records the closed scope history admitted by
the high path compiler; it has no constructor for an arbitrary low-level
scope. The paired actions expose no model callback and accept no free target
adapter.
-/

namespace LambdaPToFCo.Full

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

namespace TargetArguments

/-- After lifting a target rename through a value telescope, the actual
renamed argument spine cancels that telescope and leaves exactly the base
rename. -/
theorem weaken_liftRename_comp_substitution
    {source target : Sig} {targetContext : Ctx target}
    (plan : ValuePlan source) (mapping : Rename source target)
    (arguments : Telescope.Args targetContext
      (plan.rename mapping).telescope) :
    plan.telescope.weaken.asSubst.comp
        ((plan.telescope.liftRename mapping).asSubst.comp
          arguments.substitution) =
      mapping.asSubst := by
  have cancel :
      (plan.telescope.rename mapping).weaken.asSubst.comp
          arguments.substitution = Subst.id := by
    simpa only [ValuePlan.telescope_rename] using
      TargetArguments.weaken_comp_substitution arguments
  rw [← Subst.comp_assoc, ← Rename.asSubst_comp,
    plan.telescope.weaken_liftRename, Rename.asSubst_comp,
    Subst.comp_assoc, cancel, Subst.comp_id]

end TargetArguments

namespace ValuePlan

/-- A plan weakened through a binder, then transported by a target rename
and opened with the rename's actual arguments, is the directly renamed
plan. -/
theorem rename_weaken_openAfterRename_cancel
    {source target : Sig} {targetContext : Ctx target}
    (sourcePlan binderPlan : ValuePlan source)
    (mapping : Rename source target)
    (arguments : Telescope.Args targetContext
      (binderPlan.rename mapping).telescope) :
    (sourcePlan.rename binderPlan.telescope.weaken).subst
        ((binderPlan.telescope.liftRename mapping).asSubst.comp
          arguments.substitution) =
      sourcePlan.rename mapping := by
  rw [TargetModelRenaming.plan_rename_asSubst, ValuePlan.subst_comp,
    TargetArguments.weaken_liftRename_comp_substitution,
    ← TargetModelRenaming.plan_rename_asSubst]

end ValuePlan

namespace PairedInstantiation

/-- Direct synchronized opening after an arbitrary typed target rename.

This avoids equating the proof-relevant views
`(bindPlan view plan).rename ...` and
`bindPlan (view.rename ...) (plan.rename ...)`. Every slot is rebuilt from
the exact predecessor scope, replacement model, typed mapping, and actual
arguments. -/
noncomputable def openAtTargetRename
    {arity : Nat} {sourceContext : LambdaPFC.Ctx arity}
    {source target : Sig}
    {sourceTargetContext : Ctx source}
    {targetTargetContext : Ctx target}
    (scope : ScopeModel sourceContext sourceTargetContext)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
    {boundType : LambdaPFC.Ty arity} {path : LambdaPFC.Path arity}
    (precise : LambdaPFC.Path.Ty sourceContext path (.ty boundType))
    {plan : ValuePlan source}
    (replacement : ProducerPlanModel sourceContext sourceTargetContext
      scope.view boundType plan)
    (arguments : Telescope.Args targetTargetContext
      (plan.rename mapping).telescope) :
    PairedInstantiation (sourceContext.snoc boundType) sourceContext
      (plan.context sourceTargetContext) targetTargetContext
      (TranslationInterfaces.ScopeView.bindPlan scope.view plan)
      (scope.targetRename mapping typed).view
      (PathSubst.openAt path)
      ((plan.telescope.liftRename mapping).asSubst.comp
        arguments.substitution) := by
  let targetSubstitution :=
    (plan.telescope.liftRename mapping).asSubst.comp
      arguments.substitution
  let targetTyped : Subst.Typed (plan.context sourceTargetContext)
      targetTargetContext targetSubstitution :=
    (TargetModelRenaming.substTyped
      (plan.telescope.liftRename_typed typed)).comp
        arguments.substitution_typed
  let substitutedView := ScopeView.subst
    (TranslationInterfaces.ScopeView.bindPlan scope.view plan)
    targetSubstitution targetTyped
  refine
    { sourceTyped := TypedPathSubstitution.openAt precise
      targetTyped := targetTyped
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
    have targetCancel := ValuePlan.rename_weaken_openAfterRename_cancel
      plan plan mapping arguments
    exact sourceCancel.symm ▸ targetCancel.symm ▸
      TargetModelRenaming.producer replacement mapping typed
  · simp only [LambdaPFC.Ctx.lookup, Fin.cases_succ,
      TranslationInterfaces.ScopeView.bindPlan_there,
      ValueInterface.rename]
    have sourceCancel :
        (sourceContext.lookup older).weaken.subst
            (PathSubst.openAt path) = sourceContext.lookup older :=
      LambdaPFC.Ty.weaken_open (sourceContext.lookup older) path
    have targetCancel := ValuePlan.rename_weaken_openAfterRename_cancel
      (scope.view older).plan plan mapping arguments
    exact sourceCancel.symm ▸ targetCancel.symm ▸
      TargetModelRenaming.producer (scope.slot older) mapping typed

/-- Typed identity on source paths. -/
private noncomputable def typedPathIdentity
    (context : LambdaPFC.Ctx arity) :
    TypedPathSubstitution context context PathSubst.id where
  lookup index := by
    simpa only [PathSubst.id, LambdaPFC.Ty.subst_id] using
      (LambdaPFC.Path.Ty.var :
        LambdaPFC.Path.Ty context (.var index)
          (.ty (context.lookup index)))

/-- Pure target renaming as a synchronized model action. Unlike
`preTargetRename`, this does not ask for equality with a pre-existing next
view; it rebuilds every target slot from the exact predecessor scope. -/
noncomputable def targetRenameScope
    {arity : Nat} {sourceContext : LambdaPFC.Ctx arity}
    {source target : Sig}
    {sourceTargetContext : Ctx source}
    {targetTargetContext : Ctx target}
    (scope : ScopeModel sourceContext sourceTargetContext)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    PairedInstantiation sourceContext sourceContext sourceTargetContext
      targetTargetContext scope.view (scope.targetRename mapping typed).view
      PathSubst.id mapping.asSubst := by
  let targetTyped := TargetModelRenaming.substTyped typed
  let substitutedView := ScopeView.subst scope.view mapping.asSubst targetTyped
  refine
    { sourceTyped := typedPathIdentity sourceContext
      targetTyped := targetTyped
      image := substitutedView
      alignment := ScopeAlignment.identity substitutedView
      image_plan := fun index => ValueInterface.subst_plan _ _ _
      slotModel := ?_ }
  intro index
  have sourceCancel :
      (sourceContext.lookup index).subst PathSubst.id =
        sourceContext.lookup index :=
    LambdaPFC.Ty.subst_id _
  have targetCancel :
      (scope.view index).plan.subst mapping.asSubst =
        (scope.view index).plan.rename mapping := by
    rw [TargetModelRenaming.plan_rename_asSubst]
  exact sourceCancel.symm ▸ targetCancel.symm ▸
    TargetModelRenaming.producer (scope.slot index) mapping typed

/-- Insert one exact constructed source binder together with its complete
target plan. This is the source/target weakening action whose lift performs
the `Gamma,S -> Gamma,B,S.weaken` binder exchange needed by pair members. -/
noncomputable def weakenUnderBinding
    {arity : Nat} {sourceContext : LambdaPFC.Ctx arity}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {boundType : LambdaPFC.Ty arity} {boundPlan : ValuePlan sig}
    (bound : ProducerPlanModel sourceContext targetContext scope.view
      boundType boundPlan) :
    PairedInstantiation sourceContext (sourceContext.snoc boundType)
      targetContext (boundPlan.context targetContext) scope.view
      (scope.bind bound).view FinFun.weaken.asSubst
      boundPlan.telescope.weaken.asSubst := by
  let targetTyped := TargetModelRenaming.substTyped
    (boundPlan.telescope.weaken_typed targetContext)
  let substitutedView := ScopeView.subst scope.view
    boundPlan.telescope.weaken.asSubst targetTyped
  refine
    { sourceTyped := TypedPathSubstitution.weaken sourceContext boundType
      targetTyped := targetTyped
      image := substitutedView
      alignment := ScopeAlignment.identity substitutedView
      image_plan := fun index => ValueInterface.subst_plan _ _ _
      slotModel := ?_ }
  intro index
  have sourceEq :
      (sourceContext.lookup index).subst FinFun.weaken.asSubst =
        (sourceContext.lookup index).weaken := by
    simpa only [LambdaPFC.Ty.weaken] using
      LambdaPFC.Ty.subst_asSubst (sourceContext.lookup index)
        FinFun.weaken
  have targetEq :
      (scope.view index).plan.subst
          boundPlan.telescope.weaken.asSubst =
        (scope.view index).plan.rename boundPlan.telescope.weaken := by
    rw [TargetModelRenaming.plan_rename_asSubst]
  exact sourceEq.symm ▸ targetEq.symm ▸
    ProducerPlanModel.underBinding bound (scope.slot index)

/-- Lifting closed source/target weakening through a pair's first plan gives
the exact binder exchange `Gamma,S -> Gamma,B,S.weaken`. -/
noncomputable def exchangeUnderBinding
    {arity : Nat} {sourceContext : LambdaPFC.Ctx arity}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {boundType firstType : LambdaPFC.Ty arity}
    {boundPlan firstPlan : ValuePlan sig}
    (bound : ProducerPlanModel sourceContext targetContext scope.view
      boundType boundPlan)
    (first : ProducerPlanModel sourceContext targetContext scope.view
      firstType firstPlan) :
    PairedInstantiation (sourceContext.snoc firstType)
      ((sourceContext.snoc boundType).snoc
        (firstType.subst FinFun.weaken.asSubst))
      (firstPlan.context targetContext)
      ((firstPlan.subst boundPlan.telescope.weaken.asSubst).context
        (boundPlan.context targetContext))
      (TranslationInterfaces.ScopeView.bindPlan scope.view firstPlan)
      (TranslationInterfaces.ScopeView.bindPlan (scope.bind bound).view
        (firstPlan.subst boundPlan.telescope.weaken.asSubst))
      FinFun.weaken.asSubst.lift
      (firstPlan.telescope.liftSubst
        boundPlan.telescope.weaken.asSubst) := by
  let previous := weakenUnderBinding scope bound
  let targetFirst : ProducerPlanModel (sourceContext.snoc boundType)
      (boundPlan.context targetContext) (scope.bind bound).view
      (firstType.subst FinFun.weaken.asSubst)
      (firstPlan.subst boundPlan.telescope.weaken.asSubst) := by
    have sourceEq : firstType.subst FinFun.weaken.asSubst =
        firstType.weaken := by
      simpa only [LambdaPFC.Ty.weaken] using
        LambdaPFC.Ty.subst_asSubst firstType FinFun.weaken
    have targetEq :
        firstPlan.subst boundPlan.telescope.weaken.asSubst =
          firstPlan.rename boundPlan.telescope.weaken := by
      rw [TargetModelRenaming.plan_rename_asSubst]
    exact sourceEq.symm ▸ targetEq.symm ▸
      ProducerPlanModel.underBinding bound first
  exact previous.liftWith targetFirst

/-- Target-renaming a scope and then lifting through the same first model
also reaches the canonical renamed `bindPlan` view without any equality of
proof-relevant interfaces. -/
noncomputable def exchangeTargetRename
    {arity : Nat} {sourceContext : LambdaPFC.Ctx arity}
    {source target : Sig}
    {sourceTargetContext : Ctx source}
    {targetTargetContext : Ctx target}
    (scope : ScopeModel sourceContext sourceTargetContext)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
    {firstType : LambdaPFC.Ty arity} {firstPlan : ValuePlan source}
    (first : ProducerPlanModel sourceContext sourceTargetContext scope.view
      firstType firstPlan) :
    PairedInstantiation (sourceContext.snoc firstType)
      (sourceContext.snoc (firstType.subst PathSubst.id))
      (firstPlan.context sourceTargetContext)
      ((firstPlan.subst mapping.asSubst).context targetTargetContext)
      (TranslationInterfaces.ScopeView.bindPlan scope.view firstPlan)
      (TranslationInterfaces.ScopeView.bindPlan
        (scope.targetRename mapping typed).view
        (firstPlan.subst mapping.asSubst))
      PathSubst.id.lift
      (firstPlan.telescope.liftSubst mapping.asSubst) := by
  let previous := targetRenameScope scope mapping typed
  let targetFirst : ProducerPlanModel sourceContext targetTargetContext
      (scope.targetRename mapping typed).view
      (firstType.subst PathSubst.id)
      (firstPlan.subst mapping.asSubst) := by
    have sourceEq : firstType.subst PathSubst.id = firstType :=
      LambdaPFC.Ty.subst_id firstType
    have targetEq : firstPlan.subst mapping.asSubst =
        firstPlan.rename mapping := by
      rw [TargetModelRenaming.plan_rename_asSubst]
    exact sourceEq.symm ▸ targetEq.symm ▸
      TargetModelRenaming.producer first mapping typed
  exact previous.liftWith targetFirst

end PairedInstantiation

/-- Closed construction provenance for target scopes admitted by the focused
path compiler. An arbitrary low-level `ScopeModel` is deliberately not a
constructor. -/
inductive ConstructedScope :
    {arity : Nat} -> {sourceContext : LambdaPFC.Ctx arity} ->
    {sig : Sig} -> {targetContext : SystemFCoExt.Ctx sig} ->
    (scope : ScopeModel sourceContext targetContext) -> Type where
  | empty (targetContext : SystemFCoExt.Ctx sig) :
      ConstructedScope (ScopeModel.empty targetContext)
  | bind
      {arity : Nat} {sourceContext : LambdaPFC.Ctx arity}
      {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
      {scope : ScopeModel sourceContext targetContext}
      (older : ConstructedScope scope)
      {sourceType : LambdaPFC.Ty arity} {plan : ValuePlan sig}
      (newest : ProducerPlanModel sourceContext targetContext
        scope.view sourceType plan) :
      ConstructedScope (scope.bind newest)
  | targetRename
      {arity : Nat} {sourceContext : LambdaPFC.Ctx arity}
      {source target : Sig}
      {sourceTargetContext : SystemFCoExt.Ctx source}
      {targetTargetContext : SystemFCoExt.Ctx target}
      {scope : ScopeModel sourceContext sourceTargetContext}
      (older : ConstructedScope scope)
      (mapping : Rename source target)
      (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
      ConstructedScope (scope.targetRename mapping typed)

end LambdaPToFCo.Full
