import LambdaPToFCo.Direct.Shape

/-!
# Cancellation for direct package interfaces

Opening a mixed telescope with a complete argument spine leaves ambient
target variables unchanged.  The resulting cancellation law is the small
piece of dependent substitution needed when an already-open source value is
used as a field of a newly constructed dependent package.
-/

namespace LambdaPToFCo.Direct

open SystemFCo

namespace Telescope.Args

/-- Actual arguments cancel the weakening beneath the telescope fields. -/
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
  | @cvar source target tail argument argumentTyping rest ih =>
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

end Telescope.Args

namespace Package.Plan

/-- A plan is recovered after a renaming is cancelled by an opening. -/
theorem rename_subst_cancel
    (plan : Package.Plan source)
    (mapping : Rename source target)
    (opening : Subst target source)
    (cancel : mapping.asSubst.comp opening = Subst.id) :
    (plan.rename mapping).subst opening = plan := by
  cases plan with
  | mk observations =>
      apply congrArg Package.Plan.mk
      apply observations.rename_subst_cancel
      simp only [Rename.asSubst_lift]
      rw [← Subst.comp_lift, ← Subst.comp_lift, cancel,
        Subst.lift_id, Subst.lift_id]

end Package.Plan

namespace Shape

/-- Shape substitution cancels any target renaming cancelled by the opening. -/
theorem rename_subst_cancel
    (shape : Shape source)
    (mapping : Rename source target)
    (opening : Subst target source)
    (cancel : mapping.asSubst.comp opening = Subst.id) :
    (shape.rename mapping).subst opening = shape := by
  cases shape with
  | stable plan =>
      exact congrArg Shape.stable
        (Package.Plan.rename_subst_cancel plan mapping opening cancel)
  | «opaque» type =>
      apply congrArg Shape.opaque
      rw [Ty.rename_asSubst, Ty.subst_comp, cancel, Ty.subst_id]

end Shape

end LambdaPToFCo.Direct
