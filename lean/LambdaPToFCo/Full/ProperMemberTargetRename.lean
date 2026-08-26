import LambdaPToFCo.Full.ModelInstantiationCoherence

/-!
# Closed dependent-member target renaming

Moving a proper pair through a target rename also moves its dependent member
through the rename lifted over the retained first-field plan.  The target view
must be the canonical `bindPlan` of the renamed scope, rather than an equality
transport from a separately renamed bound view.

This leaf names that closed action and seals its member-model coherence.  The
eliminator exposes the literal substitution-normalized indices used by
`Pair.Proper.substMember`; it accepts no replacement target model or transport
callback.
-/

namespace LambdaPToFCo.Full

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

/-- Target-rename a constructed scope and lift that exact action through the
retained first model.  Its source is the first-bound member scope and its
target is the canonical `bindPlan` of the renamed scope and substituted first
plan. -/
noncomputable def ModelInstantiation.exchangeTargetRename
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
      firstType firstPlan) :=
  ModelInstantiation.lift
    (.targetRenameScope scope constructed mapping typed)
    (ModelInstantiation.targetRenameScopeProducerTarget scope constructed
      mapping typed first)

/-- Exact certificate for moving one dependent proper member through the
closed target-rename action determined by its retained first model. -/
abbrev ProperMemberTargetRenameCertificate
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
    {memberType : LambdaPFC.Ty (n + 1)}
    {memberPlan : ValuePlan firstPlan.scope}
    (member : ProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context sourceTargetContext)
      (ScopeView.bindPlan scope.view firstPlan) memberType memberPlan) :=
  ProducerInstantiationCoherence.Result
    (ModelInstantiation.exchangeTargetRename scope constructed mapping typed
      first)
    member

/-- Recover the certificate-determined member at the literal
substitution-normalized indices of `Pair.Proper.substMember`. -/
noncomputable def ProperMemberTargetRenameCertificate.instantiated
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
    {memberType : LambdaPFC.Ty (n + 1)}
    {memberPlan : ValuePlan firstPlan.scope}
    (member : ProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context sourceTargetContext)
      (ScopeView.bindPlan scope.view firstPlan) memberType memberPlan)
    (certificate : ProperMemberTargetRenameCertificate scope constructed
      mapping typed first member) :
    ProducerPlanModel (sourceContext.snoc firstType)
      ((firstPlan.subst mapping.asSubst).context targetTargetContext)
      (ScopeView.bindPlan (scope.targetRename mapping typed).view
        (firstPlan.subst mapping.asSubst))
      memberType
      (Pair.Proper.substMember firstPlan memberPlan mapping.asSubst) := by
  have result :=
    ProducerInstantiationCoherence.Result.instantiated certificate
  simpa only [ModelInstantiation.exchangeTargetRename,
    ModelInstantiation.ProducerTarget, PathSubst.lift_id,
    LambdaPFC.Ty.subst_id, Pair.Proper.substMember] using result

end LambdaPToFCo.Full
