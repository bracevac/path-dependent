import LambdaPToFCo.Full.ScopeView

/-!
# Substitution of opened value interfaces

This module supplies the target-side half of synchronized source/target
instantiation.  A typed target substitution acts on complete heterogeneous
argument spines, opened value interfaces, and arbitrary scope views.  The
plan naturality lemma at the end is the binder calculation used when lifting
such an instantiation through a compiled value plan.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

namespace TargetArguments

/-- Substitute every field of a typed heterogeneous argument spine. -/
noncomputable def subst
    {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {tele : Telescope source}
    (arguments : Telescope.Args sourceContext tele)
    (substitution : Subst source target)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    Telescope.Args targetContext (tele.subst substitution) := by
  induction arguments generalizing target targetContext with
  | nil => exact .nil
  | @var type tail argument argumentTyping rest ih =>
      refine .var (argument.subst substitution)
        (argumentTyping.subst typed) ?_
      have result := ih substitution typed
      rw [Telescope.subst_comp, Subst.openVar_comp] at result
      rw [Telescope.subst_comp]
      exact result
  | @tvar tail argument rest ih =>
      refine .tvar (argument.subst substitution) ?_
      have result := ih substitution typed
      rw [Telescope.subst_comp, Subst.openTVar_comp] at result
      rw [Telescope.subst_comp]
      exact result
  | @cvar sourceType targetType tail argument argumentTyping rest ih =>
      refine .cvar (argument.subst substitution)
        (argumentTyping.subst typed) ?_
      have result := ih substitution typed
      rw [Telescope.subst_comp, Subst.openCVar_comp] at result
      rw [Telescope.subst_comp]
      exact result

end TargetArguments

namespace ValueInterface

/-- Substitute an opened interface, including its dependent observations. -/
noncomputable def subst
    {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    (interface : ValueInterface sourceContext)
    (substitution : Subst source target)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    ValueInterface targetContext where
  plan := interface.plan.subst substitution
  identity := interface.identity.subst substitution
  payload := interface.payload.subst substitution
  payloadTyping := interface.payloadTyping.subst typed
  observations := by
    have result := TargetArguments.subst interface.observations
      substitution typed
    rw [Telescope.subst_comp, Subst.openVar_comp,
      Telescope.subst_comp, ← Subst.comp_assoc,
      ← Subst.comp_lift, Subst.openTVar_comp,
      Subst.comp_lift, Subst.comp_assoc] at result
    rw [Telescope.subst_comp]
    change Telescope.Args targetContext
      ((interface.plan.observations.subst
        ((substitution.lift .tvar).lift .var)).subst _)
    rw [Telescope.subst_comp]
    exact result

@[simp] theorem subst_plan
    {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    (interface : ValueInterface sourceContext)
    (substitution : Subst source target)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    (ValueInterface.subst interface substitution typed).plan =
      interface.plan.subst substitution := by
  rfl

end ValueInterface

namespace ScopeView

/-- Pointwise target substitution of an arbitrary opened source scope. -/
noncomputable def subst
    {arity : Nat} {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    (view : ScopeView arity sourceContext)
    (substitution : Subst source target)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    ScopeView arity targetContext :=
  fun index => ValueInterface.subst (view index) substitution typed

@[simp] theorem subst_apply
    {arity : Nat} {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    (view : ScopeView arity sourceContext)
    (substitution : Subst source target)
    (typed : Subst.Typed sourceContext targetContext substitution)
    (index : Fin arity) :
    ScopeView.subst view substitution typed index =
      ValueInterface.subst (view index) substitution typed := by
  rfl

end ScopeView

namespace ValuePlan

/-- Reindexing a plan below a value binder commutes with substituting the
base and lifting that substitution through the same binder. -/
theorem rename_weaken_subst_lift
    (plan binder : ValuePlan source)
    (substitution : Subst source target) :
    (plan.rename binder.telescope.weaken).subst
        (binder.telescope.liftSubst substitution) =
      (plan.subst substitution).rename
        (binder.subst substitution).telescope.weaken := by
  cases binder with
  | mk binderObservations =>
    cases plan with
    | mk observations =>
      apply congrArg ValuePlan.mk
      simp only [ValuePlan.rename, ValuePlan.subst]
      rw [Telescope.rename_asSubst, Telescope.subst_comp,
        Telescope.rename_asSubst, Telescope.subst_comp]
      simp only [Rename.asSubst_lift]
      rw [← Subst.comp_lift, ← Subst.comp_lift]
      rw [((ValuePlan.mk binderObservations).telescope.weaken_liftSubst
        substitution)]
      rw [Subst.comp_lift, Subst.comp_lift]
      rfl

end ValuePlan

end LambdaPToFCo.Full
