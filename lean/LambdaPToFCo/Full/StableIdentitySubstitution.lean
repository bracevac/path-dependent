import LambdaPToFCo.Full.InterfaceSubstitution
import LambdaPToFCo.Full.StableIdentity

/-!
# Substitution of stable-identity adapters

Stable-identity repacks can be transported along any typed System FCo
substitution.  The public adapter operation is reconstructed from its
proof-relevant `StableIdentity.Law`; it does not assert a syntactic equation
between the old body and the reconstructed body.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

namespace StableIdentity

theorem sourceAtBinder_subst
    (plan : ValuePlan source) (substitution : Subst source target) :
    (sourceAtBinder plan).subst (substitution.lift .var) =
      sourceAtBinder (plan.subst substitution) := by
  cases plan with
  | mk observations =>
      apply congrArg ValuePlan.mk
      simp only [sourceAtBinder, ValuePlan.rename, ValuePlan.subst]
      exact (observations.rename_subst_comm
        (((substitution.weakenComm .var).lift .tvar).lift .var)).symm

private theorem ValuePlan.rename_weaken_heq₂
    {first second first' second' : ValuePlan sig}
    (firstEq : first = first') (secondEq : second = second') :
    HEq (first.rename second.telescope.weaken)
      (first'.rename second'.telescope.weaken) := by
  cases firstEq
  cases secondEq
  rfl

theorem targetAtSource_subst
    (sourcePlan targetPlan : ValuePlan source)
    (substitution : Subst source target) :
    HEq ((targetAtSource sourcePlan targetPlan).subst
        ((sourceAtBinder sourcePlan).telescope.liftSubst
          (substitution.lift .var)))
      (targetAtSource (sourcePlan.subst substitution)
        (targetPlan.subst substitution)) := by
  unfold targetAtSource
  have outerEq := ValuePlan.rename_weaken_subst_lift
    (targetPlan.rename (Rename.weaken .var))
    (sourceAtBinder sourcePlan) (substitution.lift .var)
  let left :=
    ((targetPlan.rename (Rename.weaken .var)).rename
      (sourceAtBinder sourcePlan).telescope.weaken).subst
        ((sourceAtBinder sourcePlan).telescope.liftSubst
          (substitution.lift .var))
  let middle :=
    ((targetPlan.rename (Rename.weaken .var)).subst
      (substitution.lift .var)).rename
        ((sourceAtBinder sourcePlan).subst
          (substitution.lift .var)).telescope.weaken
  have first : HEq left middle := heq_of_eq outerEq
  apply HEq.trans first
  have targetEq := sourceAtBinder_subst targetPlan substitution
  have sourceEq := sourceAtBinder_subst sourcePlan substitution
  exact ValuePlan.rename_weaken_heq₂ targetEq sourceEq

private theorem openedObservations_heq
    {firstBinder secondBinder : ValuePlan sig}
    {firstTarget : ValuePlan firstBinder.scope}
    {secondTarget : ValuePlan secondBinder.scope}
    (binderEq : firstBinder = secondBinder)
    (targetEq : HEq firstTarget secondTarget) :
    HEq
      ((firstTarget.observations.subst
        ((Subst.openTVar firstBinder.identityTy).lift .var)).subst
          (Subst.openVar firstBinder.payload))
      ((secondTarget.observations.subst
        ((Subst.openTVar secondBinder.identityTy).lift .var)).subst
          (Subst.openVar secondBinder.payload)) := by
  cases binderEq
  have targetEq' : firstTarget = secondTarget := eq_of_heq targetEq
  cases targetEq'
  rfl

private def openedObservations
    (binder : ValuePlan sig) (target : ValuePlan binder.scope) :
    Telescope binder.scope :=
  ((target.observations.subst
    ((Subst.openTVar binder.identityTy).lift .var)).subst
      (Subst.openVar binder.payload))

private theorem observationTelescope_subst_raw
    (sourcePlan targetPlan : ValuePlan source)
    (substitution : Subst source target) :
    (observationTelescope sourcePlan targetPlan).subst
        ((sourceAtBinder sourcePlan).telescope.liftSubst
          (substitution.lift .var)) =
      openedObservations
        ((sourceAtBinder sourcePlan).subst (substitution.lift .var))
        ((targetAtSource sourcePlan targetPlan).subst
          ((sourceAtBinder sourcePlan).telescope.liftSubst
            (substitution.lift .var))) := by
  let oldBinder := sourceAtBinder sourcePlan
  let lifted := oldBinder.telescope.liftSubst (substitution.lift .var)
  let oldTarget := targetAtSource sourcePlan targetPlan
  unfold observationTelescope openedObservations
  rw [Telescope.subst_comp, Subst.openVar_comp,
    Telescope.subst_comp, ← Subst.comp_assoc,
    ← Subst.comp_lift, Subst.openTVar_comp,
    Subst.comp_lift, Subst.comp_assoc]
  simp only [ValuePlan.subst, Telescope.subst_comp, Subst.comp_assoc,
    ValuePlan.identityTy_subst, ValuePlan.payload_subst]
  rfl

theorem observationTelescope_subst
    (sourcePlan targetPlan : ValuePlan source)
    (substitution : Subst source target) :
    HEq ((observationTelescope sourcePlan targetPlan).subst
        ((sourceAtBinder sourcePlan).telescope.liftSubst
          (substitution.lift .var)))
      (observationTelescope (sourcePlan.subst substitution)
        (targetPlan.subst substitution)) := by
  let oldBinder := sourceAtBinder sourcePlan
  let newBinder := sourceAtBinder (sourcePlan.subst substitution)
  let lifted := oldBinder.telescope.liftSubst (substitution.lift .var)
  let oldTarget := targetAtSource sourcePlan targetPlan
  let newTarget := targetAtSource (sourcePlan.subst substitution)
    (targetPlan.subst substitution)
  have sourceEq : oldBinder.subst (substitution.lift .var) = newBinder :=
    sourceAtBinder_subst sourcePlan substitution
  have targetEq : HEq (oldTarget.subst lifted) newTarget :=
    targetAtSource_subst sourcePlan targetPlan substitution
  rw [observationTelescope_subst_raw]
  unfold observationTelescope
  exact openedObservations_heq sourceEq targetEq

private structure OpenedTarget (sig : Sig) where
  binder : ValuePlan sig
  target : ValuePlan binder.scope

private def OpenedTarget.Arguments
    (base : Ctx sig) (index : OpenedTarget sig) : Type :=
  Telescope.Args (index.binder.context base)
    (openedObservations index.binder index.target)

private theorem OpenedTarget.eq
    {firstBinder secondBinder : ValuePlan sig}
    {firstTarget : ValuePlan firstBinder.scope}
    {secondTarget : ValuePlan secondBinder.scope}
    (binderEq : firstBinder = secondBinder)
    (targetEq : HEq firstTarget secondTarget) :
    (OpenedTarget.mk firstBinder firstTarget) =
      (OpenedTarget.mk secondBinder secondTarget) := by
  cases binderEq
  have targetEq' : firstTarget = secondTarget := eq_of_heq targetEq
  cases targetEq'
  rfl

/-- Substitute a primitive stable-identity repack.  The dependent target
observation spine is transported internally; the public endpoints retain the
standard `ValuePlan.subst` form. -/
noncomputable def Repack.subst
    {sourceSig targetSig : Sig}
    {sourceContext : Ctx sourceSig} {targetContext : Ctx targetSig}
    {sourcePlan targetPlan : ValuePlan sourceSig}
    (repack : Repack sourceContext sourcePlan targetPlan)
    (substitution : Subst sourceSig targetSig)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    Repack targetContext (sourcePlan.subst substitution)
      (targetPlan.subst substitution) := by
  let oldBinder := sourceAtBinder sourcePlan
  let newBinder := sourceAtBinder (sourcePlan.subst substitution)
  let lifted := oldBinder.telescope.liftSubst (substitution.lift .var)
  have boundTyped : Subst.Typed
      (sourceContext.bindVar sourcePlan.inputTy)
      (targetContext.bindVar (sourcePlan.subst substitution).inputTy)
      (substitution.lift .var) := by
    simpa only [← ValuePlan.inputTy_subst] using
      typed.lift (.var sourcePlan.inputTy)
  have liftedTyped := oldBinder.telescope.liftSubst_typed boundTyped
  have binderEq : oldBinder.subst (substitution.lift .var) = newBinder :=
    sourceAtBinder_subst sourcePlan substitution
  have observations := TargetArguments.subst repack.observations lifted
    liftedTyped
  have naturalEq := observationTelescope_subst_raw sourcePlan targetPlan
    substitution
  rw [naturalEq] at observations
  let oldIndex : OpenedTarget (targetSig ,, .var) :=
    ⟨oldBinder.subst (substitution.lift .var),
      (targetAtSource sourcePlan targetPlan).subst lifted⟩
  let newIndex : OpenedTarget (targetSig ,, .var) :=
    ⟨newBinder, targetAtSource (sourcePlan.subst substitution)
      (targetPlan.subst substitution)⟩
  have indexEq : oldIndex = newIndex :=
    OpenedTarget.eq binderEq
      (targetAtSource_subst sourcePlan targetPlan substitution)
  have oldArguments : OpenedTarget.Arguments
      (targetContext.bindVar (sourcePlan.subst substitution).inputTy)
      oldIndex := by
    exact observations
  have newArguments : OpenedTarget.Arguments
      (targetContext.bindVar (sourcePlan.subst substitution).inputTy)
      newIndex := indexEq ▸ oldArguments
  exact ⟨newArguments⟩

private noncomputable def Law.substAdapter
    {sourceSig targetSig : Sig}
    {sourceContext : Ctx sourceSig} {targetContext : Ctx targetSig}
    {sourcePlan targetPlan : ValuePlan sourceSig}
    {body : Exp (sourceSig ,, .var)}
    (law : Law sourceContext sourcePlan targetPlan body)
    (substitution : Subst sourceSig targetSig)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    Adapter targetContext (sourcePlan.subst substitution)
      (targetPlan.subst substitution) := by
  induction law with
  | identity plan =>
      exact Adapter.identity targetContext (plan.subst substitution)
  | repack witness =>
      exact Adapter.ofRepack (witness.subst substitution typed)
  | compose first second firstIH secondIH =>
      exact firstIH.compose secondIH

namespace Adapter

/-- Substitute a stable-identity adapter into a typed target context.
The result is reconstructed from the proof-relevant stable-identity law;
it deliberately makes no claim that its body is syntactically the
substitution of the original body. -/
noncomputable def subst
    {sourceSig targetSig : Sig}
    {sourceContext : Ctx sourceSig} {targetContext : Ctx targetSig}
    {sourcePlan targetPlan : ValuePlan sourceSig}
    (adapter : Adapter sourceContext sourcePlan targetPlan)
    (substitution : Subst sourceSig targetSig)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    Adapter targetContext (sourcePlan.subst substitution)
      (targetPlan.subst substitution) :=
  adapter.law.substAdapter substitution typed

end Adapter

end StableIdentity

end LambdaPToFCo.Full
