import LambdaPToFCo.Full.ProducerPairProjection
import LambdaPToFCo.Full.ProperMemberTargetRename

/-!
# Provenance-certified interval selection capability

This leaf is the model/action half of interval-member `sel_r`.  A sealed
capability retains one positive interval descriptor together with its exact
lower-negative and upper-positive endpoint models.  The only root accepts a
certified `IntervalProducer`; `underBinding`, `bound`, and `targetRename`
reconstruct the descriptor from its proof-relevant stable-identity laws while
moving the endpoint models through the matching closed instantiation action.

This module intentionally does not turn an arbitrary typed interval-pair
package into a path result.  Opening such a package exposes raw coercion
variables, from which `StableIdentity.Law` cannot be recovered.  The final
rank-2 selection finisher must additionally consume sealed package provenance
that ties the actual representation arguments and hidden witness to this
retained descriptor.  No equality between an unrelated package and the
descriptor is assumed here.
-/

namespace LambdaPToFCo.Full.IntervalSelectionCapability

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

/-- Origin-free positive interval evidence at one exact opened scope.  The
only public root below is a certified `IntervalProducer`; callers cannot
supply the descriptor independently of its endpoint models. -/
structure MemberEvidence
    {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (view : ScopeView n targetContext)
    (lower upper : LambdaPFC.Ty n)
    (lowerPlan upperPlan : ValuePlan sig) : Type where
  private mk ::
  lowerModel : DemandPlanModel sourceContext targetContext view lower
    lowerPlan
  upperModel : ProducerPlanModel sourceContext targetContext view upper
    upperPlan
  descriptor : TranslationModelCore.IntervalDescriptor sourceContext
    targetContext
    (.negative
      ({ plan := lowerPlan } : TranslationModelCore.NegativePlan
        sourceContext targetContext view lower))
    (.positive
      ({ plan := upperPlan } : TranslationModelCore.PositivePlan
        sourceContext targetContext view upper))

namespace MemberEvidence

def modeled
    (evidence : MemberEvidence sourceContext targetContext view lower upper
      lowerPlan upperPlan) :
    IntervalProducerPlanModel sourceContext targetContext view lower upper
      lowerPlan upperPlan :=
  .bounds evidence.lowerModel evidence.upperModel

noncomputable def ofProducer
    (producer : IntervalProducer sourceContext targetContext scope lower upper) :
    MemberEvidence sourceContext targetContext scope.view lower upper
      producer.lower.plan producer.upper.plan where
  lowerModel := producer.lower.modeled
  upperModel := producer.upper.modeled
  descriptor := producer.descriptor

/-- Substitute a certified interval and its hidden descriptor through one
closed synchronized source/target action. -/
noncomputable def subst
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
    (evidence : MemberEvidence sourceContext sourceTargetContext sourceView
      lower upper lowerPlan upperPlan)
    (target : ModelInstantiation.IntervalProducerTarget action lower upper
      lowerPlan upperPlan) :
    MemberEvidence targetSourceContext targetTargetContext targetView
      (lower.subst sourceSubstitution) (upper.subst sourceSubstitution)
      (lowerPlan.subst targetSubstitution)
      (upperPlan.subst targetSubstitution) := by
  cases target with
  | bounds targetLower targetUpper =>
      refine
        { lowerModel := targetLower
          upperModel := targetUpper
          descriptor := ?_ }
      cases evidence.descriptor with
      | selected representation lowerToSelected selectedToUpper =>
          refine .selected (representation.subst targetSubstitution) ?_ ?_
          · simpa only [TranslationModelCore.PlanEndpoint.plan,
              Selection.plan_subst] using
              StableIdentity.Adapter.subst lowerToSelected targetSubstitution
                action.pairing.targetTyped
          · simpa only [TranslationModelCore.PlanEndpoint.plan,
              Selection.plan_subst] using
              StableIdentity.Adapter.subst selectedToUpper targetSubstitution
                action.pairing.targetTyped

end MemberEvidence

/-- Exact interval analogue of `ProperMemberTargetRenameCertificate`. -/
abbrev MemberTargetRenameCertificate
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx source}
    {targetTargetContext : SystemFCoExt.Ctx target}
    (scope : ScopeModel sourceContext sourceTargetContext)
    (constructed : ConstructedScope scope)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
    {firstType : LambdaPFC.Ty n} {firstPlan : ValuePlan source}
    (first : ProducerPlanModel sourceContext sourceTargetContext scope.view
      firstType firstPlan)
    {lower upper : LambdaPFC.Ty (n + 1)}
    {lowerPlan upperPlan : ValuePlan firstPlan.scope}
    (member : IntervalProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context sourceTargetContext)
      (ScopeView.bindPlan scope.view firstPlan) lower upper lowerPlan
      upperPlan) :=
  IntervalProducerInstantiationCoherence.Result
    (ModelInstantiation.exchangeTargetRename scope constructed mapping typed
      first)
    member

/-- Interval pair-head evidence strengthened with the exact positive
descriptor needed by a right type-member selection. -/
structure Capability
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan) : Type where
  private mk ::
  firstType : LambdaPFC.Ty n
  label : LambdaPFC.Name
  lower : LambdaPFC.Ty (n + 1)
  upper : LambdaPFC.Ty (n + 1)
  source_eq : sourceType = .Pair firstType label (.intv lower upper)
  firstPlan : ValuePlan sig
  lowerPlan : ValuePlan firstPlan.scope
  upperPlan : ValuePlan firstPlan.scope
  plan_eq : plan = Pair.Interval.plan firstPlan lowerPlan.inputTy
    upperPlan.inputTy
  first : ProducerPlanModel sourceContext targetContext scope.view firstType
    firstPlan
  member : MemberEvidence (sourceContext.snoc firstType)
    (firstPlan.context targetContext) (ScopeView.bindPlan scope.view firstPlan)
    lower upper lowerPlan upperPlan
  history : ProducerPairHead model

namespace Capability

/-- Direct interval-pair provenance starts only from the high certified
positive interval carrier, never from a raw descriptor. -/
noncomputable def direct
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {firstType : LambdaPFC.Ty n} {label : LambdaPFC.Name}
    {firstPlan : ValuePlan sig}
    (first : ProducerPlanModel sourceContext targetContext scope.view firstType
      firstPlan)
    {lower upper : LambdaPFC.Ty (n + 1)}
    (member : IntervalProducer (sourceContext.snoc firstType)
      (firstPlan.context targetContext) (scope.bind first) lower upper) :
    Capability scope
      (.intervalPair (label := label) first
        (.bounds member.lower.modeled member.upper.modeled)) where
  firstType := firstType
  label := label
  lower := lower
  upper := upper
  source_eq := rfl
  firstPlan := firstPlan
  lowerPlan := member.lower.plan
  upperPlan := member.upper.plan
  plan_eq := rfl
  first := first
  member := MemberEvidence.ofProducer member
  history := .interval first
    (.bounds member.lower.modeled member.upper.modeled)

/-- Move the retained descriptor and its endpoint models through one exact
compiler-constructed source binding. -/
noncomputable def underBinding
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (constructed : ConstructedScope scope)
    {boundType olderType : LambdaPFC.Ty n}
    {boundPlan olderPlan : ValuePlan sig}
    (bound : ProducerPlanModel sourceContext targetContext scope.view
      boundType boundPlan)
    (olderModel : ProducerPlanModel sourceContext targetContext scope.view
      olderType olderPlan)
    (capability : Capability scope olderModel)
    (certificate : IntervalMemberExchangeCertificate scope constructed bound
      capability.first
      (.bounds capability.member.lowerModel capability.member.upperModel)) :
    Capability (scope.bind bound) (.underBinding bound olderModel) := by
  let substitution := boundPlan.telescope.weaken.asSubst
  let first := ModelInstantiation.weakenUnderBindingProducerTarget scope
    constructed bound capability.first
  let action := ModelInstantiation.exchangeUnderBinding scope constructed
    bound capability.first
  let target := certificate.instantiated
  let member := MemberEvidence.subst
    (targetView := ScopeView.bindPlan (scope.bind bound).view
      (capability.firstPlan.subst substitution)) action capability.member target
  refine
    { firstType := capability.firstType.subst FinFun.weaken.asSubst
      label := capability.label
      lower := capability.lower.subst FinFun.weaken.asSubst.lift
      upper := capability.upper.subst FinFun.weaken.asSubst.lift
      source_eq := ?_
      firstPlan := capability.firstPlan.subst substitution
      lowerPlan := Pair.Proper.substMember capability.firstPlan
        capability.lowerPlan substitution
      upperPlan := Pair.Proper.substMember capability.firstPlan
        capability.upperPlan substitution
      plan_eq := ?_
      first := first
      member := member
      history := .underBinding bound olderModel capability.history }
  · calc
      olderType.weaken =
          (LambdaPFC.Ty.Pair capability.firstType capability.label
            (.intv capability.lower capability.upper)).weaken :=
        congrArg LambdaPFC.Ty.weaken capability.source_eq
      _ = (LambdaPFC.Ty.Pair capability.firstType capability.label
            (.intv capability.lower capability.upper)).rename
          FinFun.weaken := rfl
      _ = (LambdaPFC.Ty.Pair capability.firstType capability.label
            (.intv capability.lower capability.upper)).subst
          FinFun.weaken.asSubst :=
        (LambdaPFC.Ty.subst_asSubst _ _).symm
      _ = LambdaPFC.Ty.Pair
          (capability.firstType.subst FinFun.weaken.asSubst)
          capability.label
          (.intv
            (capability.lower.subst FinFun.weaken.asSubst.lift)
            (capability.upper.subst FinFun.weaken.asSubst.lift)) := rfl
  · calc
      olderPlan.rename boundPlan.telescope.weaken =
          (Pair.Interval.plan capability.firstPlan
            capability.lowerPlan.inputTy
            capability.upperPlan.inputTy).rename
              boundPlan.telescope.weaken :=
        congrArg (fun current => current.rename
          boundPlan.telescope.weaken) capability.plan_eq
      _ = (Pair.Interval.plan capability.firstPlan
            capability.lowerPlan.inputTy
            capability.upperPlan.inputTy).subst substitution :=
        TargetModelRenaming.plan_rename_asSubst _ _
      _ = Pair.Interval.plan
          (capability.firstPlan.subst substitution)
          (Pair.Proper.substMember capability.firstPlan capability.lowerPlan
            substitution).inputTy
          (Pair.Proper.substMember capability.firstPlan capability.upperPlan
            substitution).inputTy := by
        rw [Pair.Interval.plan_subst, ValuePlan.inputTy_subst,
          ValuePlan.inputTy_subst]
        rfl

/-- The newly bound interval pair uses the same closed exchange, retaining
the exact `.bound` pair-head history. -/
noncomputable def bound
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (constructed : ConstructedScope scope)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan)
    (capability : Capability scope model)
    (certificate : IntervalMemberExchangeCertificate scope constructed model
      capability.first
      (.bounds capability.member.lowerModel capability.member.upperModel)) :
    Capability (scope.bind model) (.bound model) := by
  let normalized := underBinding scope constructed model model capability
    certificate
  exact
    { firstType := normalized.firstType
      label := normalized.label
      lower := normalized.lower
      upper := normalized.upper
      source_eq := normalized.source_eq
      firstPlan := normalized.firstPlan
      lowerPlan := normalized.lowerPlan
      upperPlan := normalized.upperPlan
      plan_eq := normalized.plan_eq
      first := normalized.first
      member := normalized.member
      history := .bound model capability.history }

/-- Move the descriptor and both endpoint models through the exact retained
target rename. -/
noncomputable def targetRename
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx source}
    {targetTargetContext : SystemFCoExt.Ctx target}
    (scope : ScopeModel sourceContext sourceTargetContext)
    (constructed : ConstructedScope scope)
    {sourceType : LambdaPFC.Ty n} {sourcePlan : ValuePlan source}
    (model : ProducerPlanModel sourceContext sourceTargetContext scope.view
      sourceType sourcePlan)
    (capability : Capability scope model)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
    (certificate : MemberTargetRenameCertificate scope constructed mapping
      typed capability.first
      (.bounds capability.member.lowerModel capability.member.upperModel)) :
    Capability (scope.targetRename mapping typed)
      (.targetRename model mapping typed) := by
  let first : ProducerPlanModel sourceContext targetTargetContext
      (scope.targetRename mapping typed).view capability.firstType
      (capability.firstPlan.subst mapping.asSubst) := by
    simpa only [TargetModelRenaming.plan_rename_asSubst] using
      TargetModelRenaming.producer capability.first mapping typed
  let action := ModelInstantiation.exchangeTargetRename scope constructed
    mapping typed capability.first
  let targetMember := certificate.instantiated
  let substituted := MemberEvidence.subst
    (sourceView := ScopeView.bindPlan scope.view capability.firstPlan)
    (targetView := ScopeView.bindPlan (scope.targetRename mapping typed).view
      (capability.firstPlan.subst mapping.asSubst))
    (action := action) capability.member targetMember
  let member : MemberEvidence (sourceContext.snoc capability.firstType)
      ((capability.firstPlan.subst mapping.asSubst).context
        targetTargetContext)
      (ScopeView.bindPlan (scope.targetRename mapping typed).view
        (capability.firstPlan.subst mapping.asSubst))
      capability.lower capability.upper
      (Pair.Proper.substMember capability.firstPlan capability.lowerPlan
        mapping.asSubst)
      (Pair.Proper.substMember capability.firstPlan capability.upperPlan
        mapping.asSubst) := by
    simpa only [PathSubst.lift_id, LambdaPFC.Ty.subst_id,
      Pair.Proper.substMember] using substituted
  refine
    { firstType := capability.firstType
      label := capability.label
      lower := capability.lower
      upper := capability.upper
      source_eq := capability.source_eq
      firstPlan := capability.firstPlan.subst mapping.asSubst
      lowerPlan := Pair.Proper.substMember capability.firstPlan
        capability.lowerPlan mapping.asSubst
      upperPlan := Pair.Proper.substMember capability.firstPlan
        capability.upperPlan mapping.asSubst
      plan_eq := ?_
      first := first
      member := member
      history := .targetRename model capability.history mapping typed }
  calc
    sourcePlan.rename mapping =
        (Pair.Interval.plan capability.firstPlan
          capability.lowerPlan.inputTy
          capability.upperPlan.inputTy).rename mapping :=
      congrArg (fun current => current.rename mapping) capability.plan_eq
    _ = (Pair.Interval.plan capability.firstPlan
          capability.lowerPlan.inputTy
          capability.upperPlan.inputTy).subst mapping.asSubst :=
      TargetModelRenaming.plan_rename_asSubst _ _
    _ = Pair.Interval.plan
        (capability.firstPlan.subst mapping.asSubst)
        (Pair.Proper.substMember capability.firstPlan capability.lowerPlan
          mapping.asSubst).inputTy
        (Pair.Proper.substMember capability.firstPlan capability.upperPlan
          mapping.asSubst).inputTy := by
      rw [Pair.Interval.plan_subst, ValuePlan.inputTy_subst,
        ValuePlan.inputTy_subst]
      rfl

def typing
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan}
    {path : LambdaPFC.Path n}
    (capability : Capability scope model)
    (receiver : LambdaPFC.Path.Ty sourceContext path (.ty sourceType)) :
    LambdaPFC.Path.Ty sourceContext path
      (.ty (.Pair capability.firstType capability.label
        (.intv capability.lower capability.upper))) :=
  capability.source_eq ▸ receiver

def package
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan}
    (capability : Capability scope model)
    (source : PathPackageZipper.CompiledPackage targetContext plan) :
    PathPackageZipper.CompiledPackage targetContext
      (Pair.Interval.plan capability.firstPlan capability.lowerPlan.inputTy
        capability.upperPlan.inputTy) :=
  capability.plan_eq ▸ source

/-- Forget the stronger descriptor realization to the existing pair-head
boundary. -/
noncomputable def interval
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan}
    (capability : Capability scope model) : IntervalPairCapability model where
  firstType := capability.firstType
  label := capability.label
  lower := capability.lower
  upper := capability.upper
  source_eq := capability.source_eq
  firstPlan := capability.firstPlan
  lowerPlan := capability.lowerPlan
  upperPlan := capability.upperPlan
  plan_eq := capability.plan_eq
  firstModel := capability.first
  history := capability.history

noncomputable def projection
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan}
    (capability : Capability scope model) : ProducerPairProjection model :=
  .interval capability.interval

end Capability

end LambdaPToFCo.Full.IntervalSelectionCapability
