import LambdaPToFCo.Full.ContextWellFormed
import LambdaPToFCo.Full.InterfaceSubstitution
import LambdaPToFCo.Full.TargetModelRenaming

/-!
# Synchronized source and target instantiation

Path selection opens a source binding and a compiled target plan at the same
time.  `PairedInstantiation` records those two typed substitutions together,
the exact stable fields obtained after target substitution, and structural
producer evidence for every substituted source slot.  This prevents path
translation from manufacturing a root-context interface for a value whose
hidden fields exist only under an unpack.
-/

namespace LambdaPToFCo.Full

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

/-- One synchronized source-path and target-interface substitution. -/
structure PairedInstantiation
    {sourceArity targetArity : Nat}
    (sourceContext : LambdaPFC.Ctx sourceArity)
    (targetSourceContext : LambdaPFC.Ctx targetArity)
    {sourceSig targetSig : Sig}
    (sourceTargetContext : SystemFCoExt.Ctx sourceSig)
    (targetTargetContext : SystemFCoExt.Ctx targetSig)
    (sourceView : ScopeView sourceArity sourceTargetContext)
    (targetView : ScopeView targetArity targetTargetContext)
    (sourceSubstitution : PathSubst sourceArity targetArity)
    (targetSubstitution : Subst sourceSig targetSig) : Type where
  sourceTyped : TypedPathSubstitution sourceContext targetSourceContext
    sourceSubstitution
  targetTyped : Subst.Typed sourceTargetContext targetTargetContext
    targetSubstitution
  image : ScopeView sourceArity targetTargetContext
  alignment : ScopeAlignment
    (ScopeView.subst sourceView targetSubstitution targetTyped) image
  image_plan : (index : Fin sourceArity) ->
    (image index).plan = (sourceView index).plan.subst targetSubstitution
  slotModel : (index : Fin sourceArity) ->
    ProducerPlanModel targetSourceContext targetTargetContext targetView
      ((sourceContext.lookup index).subst sourceSubstitution)
      ((sourceView index).plan.subst targetSubstitution)

namespace PairedInstantiation

/-- Precompose the target half of a synchronized instantiation with one
proof-relevant target rename.  The source substitution is unchanged; the
target substitution applies the rename embedding and then the retained
instantiation. -/
noncomputable def preTargetRename
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
    (pairing : PairedInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext
      (preView.rename mapping typed) targetView sourceSubstitution
      targetSubstitution) :
    PairedInstantiation sourceContext targetSourceContext preTargetContext
      targetTargetContext preView targetView sourceSubstitution
      (mapping.asSubst.comp targetSubstitution) := by
  let composedTyped :=
    (TargetModelRenaming.substTyped typed).comp pairing.targetTyped
  let substitutedView := ScopeView.subst preView
    (mapping.asSubst.comp targetSubstitution) composedTyped
  refine
    { sourceTyped := pairing.sourceTyped
      targetTyped := composedTyped
      image := substitutedView
      alignment := ScopeAlignment.identity substitutedView
      image_plan := ?_
      slotModel := ?_ }
  · intro index
    exact ValueInterface.subst_plan _ _ _
  · intro index
    have renamed := pairing.slotModel index
    have plan_eq :
        ((preView.rename mapping typed index).plan.subst targetSubstitution) =
          (preView index).plan.subst
            (mapping.asSubst.comp targetSubstitution) := by
      change ((preView index).plan.rename mapping).subst
        targetSubstitution = _
      rw [TargetModelRenaming.plan_rename_asSubst,
        ValuePlan.subst_comp]
    exact plan_eq ▸ renamed

/-- Lift synchronized instantiation through one positive source binding and
its complete target value plan. -/
noncomputable def liftWith
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
    (pairing : PairedInstantiation sourceContext targetSourceContext
      sourceTargetContext targetTargetContext sourceView targetView
      sourceSubstitution targetSubstitution)
    {boundType : LambdaPFC.Ty sourceArity}
    {boundPlan : ValuePlan sourceSig}
    (newBound : ProducerPlanModel targetSourceContext targetTargetContext
      targetView (boundType.subst sourceSubstitution)
      (boundPlan.subst targetSubstitution)) :
    PairedInstantiation (sourceContext.snoc boundType)
      (targetSourceContext.snoc (boundType.subst sourceSubstitution))
      (boundPlan.context sourceTargetContext)
      ((boundPlan.subst targetSubstitution).context targetTargetContext)
      (TranslationInterfaces.ScopeView.bindPlan sourceView boundPlan)
      (TranslationInterfaces.ScopeView.bindPlan targetView
        (boundPlan.subst targetSubstitution))
      sourceSubstitution.lift
      (boundPlan.telescope.liftSubst targetSubstitution) := by
  let liftedTargetTyped := boundPlan.telescope.liftSubst_typed
    pairing.targetTyped
  let substitutedView := ScopeView.subst
    (TranslationInterfaces.ScopeView.bindPlan sourceView boundPlan)
    (boundPlan.telescope.liftSubst targetSubstitution) liftedTargetTyped
  refine
    { sourceTyped := pairing.sourceTyped.lift boundType
      targetTyped := liftedTargetTyped
      image := substitutedView
      alignment := ScopeAlignment.identity substitutedView
      image_plan := ?_
      slotModel := ?_ }
  · intro index
    exact ValueInterface.subst_plan _ _ _
  · intro index
    refine Fin.cases ?_ (fun older => ?_) index
    · simp only [LambdaPFC.Ctx.lookup, Fin.cases_zero,
        TranslationInterfaces.ScopeView.bindPlan_here,
        TranslationInterfaces.ValueInterface.ofArguments_plan,
        Ty.weaken_subst_lift]
      exact (ValuePlan.rename_weaken_subst_lift boundPlan boundPlan
        targetSubstitution).symm ▸ ProducerPlanModel.bound newBound
    · simp only [LambdaPFC.Ctx.lookup, Fin.cases_succ,
        TranslationInterfaces.ScopeView.bindPlan_there,
        ValueInterface.rename, Ty.weaken_subst_lift]
      exact (ValuePlan.rename_weaken_subst_lift
        (sourceView older).plan boundPlan targetSubstitution).symm ▸
          ProducerPlanModel.underBinding newBound
            (pairing.slotModel older)

end PairedInstantiation

end LambdaPToFCo.Full
