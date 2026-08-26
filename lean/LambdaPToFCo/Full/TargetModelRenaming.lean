import LambdaPToFCo.Full.StableIdentitySubstitution
import LambdaPToFCo.Full.TranslationInterfaces

/-!
# Typed target renaming of sealed plan models

Opening an unrelated compiled package extends only the System FCo target
context.  Source types and source paths remain unchanged, while every target
plan and opened scope slot is renamed through the same typed target mapping.

The positive and negative relations retain this provenance in their sealed
`targetRename` constructors.  The remaining five mutually related model
families are rebuilt structurally here.  In particular, selection adapters
are transported by the stable-identity substitution theorem; no raw target
plan or adapter is accepted.
-/

namespace LambdaPToFCo.Full.TargetModelRenaming

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

/-- A typed target rename, viewed as the corresponding typed substitution. -/
noncomputable def substTyped
    {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {mapping : Rename source target}
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Subst.Typed sourceContext targetContext mapping.asSubst where
  lookup := by
    intro kind index binding lookup
    have renamed := typed.lookup lookup
    cases binding with
    | var type =>
        simpa only [Subst.Realizes, SystemFCoExt.Ty.subst_asSubst] using
          (Exp.HasType.var renamed)
    | tvar => exact PUnit.unit
    | cvar sourceType targetType =>
        simpa only [Subst.Realizes, SystemFCoExt.Ty.subst_asSubst] using
          (Co.HasType.cvar renamed)

/-- Renaming a value plan is its substitution by the rename embedding. -/
theorem plan_rename_asSubst
    (plan : ValuePlan source) (mapping : Rename source target) :
    plan.rename mapping = plan.subst mapping.asSubst := by
  cases plan with
  | mk observations =>
      apply congrArg ValuePlan.mk
      rw [Telescope.rename_asSubst]
      simp only [Rename.asSubst_lift]

/-- A stable package adapter follows a typed target rename. -/
noncomputable def adapter
    {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {sourcePlan targetPlan : ValuePlan source}
    (value : StableIdentity.Adapter sourceContext sourcePlan targetPlan)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    StableIdentity.Adapter targetContext (sourcePlan.rename mapping)
      (targetPlan.rename mapping) := by
  have renamed := value.subst mapping.asSubst (substTyped typed)
  simpa only [plan_rename_asSubst] using renamed

/-- Positive models retain the exact old model and typed target rename. -/
noncomputable def producer
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : Ctx source} {targetTargetContext : Ctx target}
    {view : ScopeView n sourceTargetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan source}
    (model : ProducerPlanModel sourceContext sourceTargetContext view
      sourceType plan)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    ProducerPlanModel sourceContext targetTargetContext
      (view.rename mapping typed) sourceType (plan.rename mapping) :=
  .targetRename model mapping typed

/-- Negative models retain the exact old model and typed target rename. -/
noncomputable def demand
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : Ctx source} {targetTargetContext : Ctx target}
    {view : ScopeView n sourceTargetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan source}
    (model : DemandPlanModel sourceContext sourceTargetContext view sourceType
      plan)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    DemandPlanModel sourceContext targetTargetContext
      (view.rename mapping typed) sourceType (plan.rename mapping) :=
  .targetRename model mapping typed

/-- Both proper polarities follow the same target rename. -/
noncomputable def bidirectional
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : Ctx source} {targetTargetContext : Ctx target}
    {view : ScopeView n sourceTargetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan source}
    (model : BidirectionalPlanModel sourceContext sourceTargetContext view
      sourceType plan)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    BidirectionalPlanModel sourceContext targetTargetContext
      (view.rename mapping typed) sourceType (plan.rename mapping) :=
  match model with
  | .both positive negative =>
      .both (producer positive mapping typed) (demand negative mapping typed)

/-- The positive interval polarity pair follows the same target rename. -/
noncomputable def intervalProducer
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : Ctx source} {targetTargetContext : Ctx target}
    {view : ScopeView n sourceTargetContext}
    {lower upper : LambdaPFC.Ty n}
    {lowerPlan upperPlan : ValuePlan source}
    (model : IntervalProducerPlanModel sourceContext sourceTargetContext view
      lower upper lowerPlan upperPlan)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    IntervalProducerPlanModel sourceContext targetTargetContext
      (view.rename mapping typed) lower upper (lowerPlan.rename mapping)
      (upperPlan.rename mapping) :=
  match model with
  | .bounds lowerModel upperModel =>
      .bounds (demand lowerModel mapping typed)
        (producer upperModel mapping typed)

/-- The negative interval polarity pair follows the same target rename. -/
noncomputable def intervalDemand
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : Ctx source} {targetTargetContext : Ctx target}
    {view : ScopeView n sourceTargetContext}
    {lower upper : LambdaPFC.Ty n}
    {lowerPlan upperPlan : ValuePlan source}
    (model : IntervalDemandPlanModel sourceContext sourceTargetContext view
      lower upper lowerPlan upperPlan)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    IntervalDemandPlanModel sourceContext targetTargetContext
      (view.rename mapping typed) lower upper (lowerPlan.rename mapping)
      (upperPlan.rename mapping) :=
  match model with
  | .bounds lowerModel upperModel =>
      .bounds (producer lowerModel mapping typed)
        (demand upperModel mapping typed)

/-- Both interval views follow the same target rename. -/
noncomputable def intervalBidirectional
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : Ctx source} {targetTargetContext : Ctx target}
    {view : ScopeView n sourceTargetContext}
    {lower upper : LambdaPFC.Ty n}
    {lowerPlan upperPlan : ValuePlan source}
    (model : IntervalBidirectionalPlanModel sourceContext sourceTargetContext
      view lower upper lowerPlan upperPlan)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    IntervalBidirectionalPlanModel sourceContext targetTargetContext
      (view.rename mapping typed) lower upper (lowerPlan.rename mapping)
      (upperPlan.rename mapping) :=
  match model with
  | .both positive negative =>
      .both (intervalProducer positive mapping typed)
        (intervalDemand negative mapping typed)

/-- A selection keeps its sealed origin and transports its exact bounds and
two stable package adapters. -/
noncomputable def selection
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : Ctx source} {targetTargetContext : Ctx target}
    {view : ScopeView n sourceTargetContext}
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {origin : SelectionOrigin sourceContext path label}
    {plan : ValuePlan source}
    (model : SelectionPlanModel sourceContext sourceTargetContext view origin
      plan)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    SelectionPlanModel sourceContext targetTargetContext
      (view.rename mapping typed) origin (plan.rename mapping) :=
  match model with
  | .between bounds lowerToSelected selectedToUpper =>
      .between (intervalDemand bounds mapping typed)
        (adapter lowerToSelected mapping typed)
        (adapter selectedToUpper mapping typed)

end LambdaPToFCo.Full.TargetModelRenaming

namespace LambdaPToFCo.Full.TranslationInterfaces.ScopeModel

open SystemFCoExt

/-- Rename a complete certified target scope without changing its source
context.  Each slot retains its exact predecessor model in `targetRename`. -/
noncomputable def targetRename
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : Ctx source} {targetTargetContext : Ctx target}
    (scope : ScopeModel sourceContext sourceTargetContext)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
    ScopeModel sourceContext targetTargetContext where
  view := scope.view.rename mapping typed
  slot index :=
    TargetModelRenaming.producer (scope.slot index) mapping typed

end LambdaPToFCo.Full.TranslationInterfaces.ScopeModel
