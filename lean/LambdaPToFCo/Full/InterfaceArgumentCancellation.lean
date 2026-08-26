import LambdaPToFCo.Full.InterfaceSubstitution

/-!
# Cancellation for opened interface arguments

The actual mixed argument spine of a value plan substitutes every field
introduced by the plan telescope while leaving the ambient signature
unchanged.  Consequently it cancels the telescope weakening.  The plan-level
corollary is the common equality used by direct pair introduction and by
synchronized dependent path selection.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

namespace TargetArguments

/-- Actual telescope arguments cancel the embedding of the ambient signature
below the telescope fields. -/
theorem weaken_comp_substitution
    {sig : Sig} {base : Ctx sig} {tele : Telescope sig}
    (arguments : Telescope.Args base tele) :
    tele.weaken.asSubst.comp arguments.substitution = Subst.id := by
  induction arguments with
  | nil => exact Subst.id_comp Subst.id
  | @var type tail argument argumentTyping rest ih =>
      change
        (((Rename.weaken .var).comp tail.weaken).asSubst).comp
            ((tail.liftSubst (Subst.openVar argument)).comp
              rest.substitution) = Subst.id
      rw [Rename.asSubst_comp]
      rw [Subst.comp_assoc (Rename.weaken .var).asSubst]
      rw [← Subst.comp_assoc tail.weaken.asSubst]
      rw [tail.weaken_liftSubst]
      rw [Subst.comp_assoc (Subst.openVar argument)]
      rw [ih, Subst.comp_id]
      exact Subst.weakenAsSubst_comp_openVar argument
  | @tvar tail argument rest ih =>
      change
        (((Rename.weaken .tvar).comp tail.weaken).asSubst).comp
            ((tail.liftSubst (Subst.openTVar argument)).comp
              rest.substitution) = Subst.id
      rw [Rename.asSubst_comp]
      rw [Subst.comp_assoc (Rename.weaken .tvar).asSubst]
      rw [← Subst.comp_assoc tail.weaken.asSubst]
      rw [tail.weaken_liftSubst]
      rw [Subst.comp_assoc (Subst.openTVar argument)]
      rw [ih, Subst.comp_id]
      exact Subst.weakenAsSubst_comp_openTVar argument
  | @cvar sourceType targetType tail argument argumentTyping rest ih =>
      change
        (((Rename.weaken .cvar).comp tail.weaken).asSubst).comp
            ((tail.liftSubst (Subst.openCVar argument)).comp
              rest.substitution) = Subst.id
      rw [Rename.asSubst_comp]
      rw [Subst.comp_assoc (Rename.weaken .cvar).asSubst]
      rw [← Subst.comp_assoc tail.weaken.asSubst]
      rw [tail.weaken_liftSubst]
      rw [Subst.comp_assoc (Subst.openCVar argument)]
      rw [ih, Subst.comp_id]
      exact Subst.weakenAsSubst_comp_openCVar argument

end TargetArguments

namespace ValuePlan

/-- Plan substitution cancels any renaming whose substitution action is
cancelled by the supplied opening. -/
theorem rename_subst_cancel
    (plan : ValuePlan source)
    (mapping : Rename source target)
    (opening : Subst target source)
    (cancel : mapping.asSubst.comp opening = Subst.id) :
    (plan.rename mapping).subst opening = plan := by
  cases plan with
  | mk observations =>
      apply congrArg ValuePlan.mk
      apply observations.rename_subst_cancel
      simp only [Rename.asSubst_lift]
      rw [← Subst.comp_lift, ← Subst.comp_lift, cancel,
        Subst.lift_id, Subst.lift_id]

end ValuePlan

end LambdaPToFCo.Full
