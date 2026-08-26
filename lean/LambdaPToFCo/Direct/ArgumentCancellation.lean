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

private theorem liftSubst_congr_heq
    (tele : Telescope source) {first second : Subst source target}
    (equal : first = second) :
    HEq (tele.liftSubst first) (tele.liftSubst second) := by
  cases equal
  rfl

private theorem liftRename_asSubst_heq
    (tele : Telescope source) (mapping : Rename source target) :
    HEq (tele.liftRename mapping).asSubst
      (tele.liftSubst mapping.asSubst) := by
  induction tele generalizing target with
  | nil => rfl
  | var type tail ih =>
      exact HEq.trans (ih (mapping.lift .var))
        (liftSubst_congr_heq tail (Rename.asSubst_lift mapping))
  | tvar tail ih =>
      exact HEq.trans (ih (mapping.lift .tvar))
        (liftSubst_congr_heq tail (Rename.asSubst_lift mapping))
  | cvar source result tail ih =>
      exact HEq.trans (ih (mapping.lift .cvar))
        (liftSubst_congr_heq tail (Rename.asSubst_lift mapping))

private theorem subst_comp_heq
    {source₁ middle₁ target₁ source₂ middle₂ target₂ : Sig}
    {first₁ : Subst source₁ middle₁} {second₁ : Subst middle₁ target₁}
    {first₂ : Subst source₂ middle₂} {second₂ : Subst middle₂ target₂}
    (sourceEqual : source₁ = source₂) (middleEqual : middle₁ = middle₂)
    (targetEqual : target₁ = target₂)
    (firstEqual : HEq first₁ first₂) (secondEqual : HEq second₁ second₂) :
    HEq (first₁.comp second₁) (first₂.comp second₂) := by
  cases sourceEqual
  cases middleEqual
  cases targetEqual
  cases eq_of_heq firstEqual
  cases eq_of_heq secondEqual
  rfl

private theorem renameComm_comp_eq
    {source middle source' target : Sig}
    {substitution : Subst source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {substitution' : Subst source' target}
    (comm : Subst.RenameComm substitution sourceRename targetRename
      substitution') :
    substitution.comp targetRename.asSubst =
      sourceRename.asSubst.comp substitution' := by
  apply Subst.funext
  · intro index
    change (substitution.var index).subst targetRename.asSubst = _
    rw [Exp.subst_asSubst]
    exact comm.var index
  · intro index
    change (substitution.tvar index).subst targetRename.asSubst = _
    rw [Ty.subst_asSubst]
    exact comm.tvar index
  · intro index
    change (substitution.cvar index).subst targetRename.asSubst = _
    rw [Co.subst_asSubst]
    exact comm.cvar index

private theorem liftRename_open_heq
    (tele : Telescope source) (mapping : Rename source middle)
    (opening : Subst middle target) :
    HEq
      ((tele.liftRename mapping).asSubst.comp
        ((tele.rename mapping).liftSubst opening))
      (tele.liftSubst (mapping.asSubst.comp opening)) := by
  have telescopeEqual := tele.rename_asSubst mapping
  have liftSubst_telescope_heq
      (first second : Telescope middle) (equal : first = second) :
      HEq (first.liftSubst opening) (second.liftSubst opening) := by
    cases equal
    rfl
  have openedEqual :
      HEq ((tele.rename mapping).liftSubst opening)
        ((tele.subst mapping.asSubst).liftSubst opening) := by
    exact liftSubst_telescope_heq _ _ telescopeEqual
  have openedTelescopeEqual :
      (tele.rename mapping).subst opening =
        (tele.subst mapping.asSubst).subst opening :=
    congrArg (fun telescope => telescope.subst opening) telescopeEqual
  have composed := subst_comp_heq rfl
    (congrArg Telescope.scope telescopeEqual)
    (congrArg Telescope.scope openedTelescopeEqual)
    (liftRename_asSubst_heq tele mapping) openedEqual
  exact HEq.trans composed
    (tele.liftSubst_comp_heq mapping.asSubst opening).symm

private theorem substitution_cast_heq
    {first second : Telescope sig} (equal : first = second)
    (arguments : Args base first) :
    HEq (cast (congrArg (Args base) equal) arguments).substitution
      arguments.substitution := by
  cases equal
  rfl

private theorem substitution_rename_step
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target} {kind : Kind}
    (tail : Telescope (source ,, kind))
    (mapping : Rename source target)
    (opening : Subst (source ,, kind) source)
    (renamedOpening : Subst (target ,, kind) target)
    (openingComm : Subst.RenameComm opening (mapping.lift kind) mapping
      renamedOpening)
    (rest : Args sourceContext (tail.subst opening))
    (renamedRest : Args targetContext
      ((tail.subst opening).rename mapping))
    (restCast : Args targetContext
      ((tail.rename (mapping.lift kind)).subst renamedOpening))
    (restCast_heq : HEq restCast.substitution renamedRest.substitution)
    (restSquare : rest.substitution.comp mapping.asSubst =
      ((tail.subst opening).liftRename mapping).asSubst.comp
        renamedRest.substitution) :
    ((tail.liftSubst opening).comp rest.substitution).comp
        mapping.asSubst =
      (tail.liftRename (mapping.lift kind)).asSubst.comp
        (((tail.rename (mapping.lift kind)).liftSubst renamedOpening).comp
          restCast.substitution) := by
  let middleRename := (tail.subst opening).liftRename mapping
  let equal := tail.rename_subst_comm openingComm
  have openingSquare := liftRename_open_heq tail
    (mapping.lift kind) renamedOpening
  have openingEqual := renameComm_comp_eq openingComm
  have collapsed := liftSubst_congr_heq tail openingEqual.symm
  have expanded := tail.liftSubst_comp_heq opening mapping.asSubst
  have middleOrdinary := liftRename_asSubst_heq
    (tail.subst opening) mapping
  have firstPair :
      HEq
        ((tail.liftSubst opening).comp middleRename.asSubst)
        ((tail.liftRename (mapping.lift kind)).asSubst.comp
          ((tail.rename (mapping.lift kind)).liftSubst
            renamedOpening)) := by
    have toExpanded :
        HEq
          ((tail.liftSubst opening).comp middleRename.asSubst)
          ((tail.liftSubst opening).comp
            ((tail.subst opening).liftSubst mapping.asSubst)) :=
      subst_comp_heq rfl rfl
        (congrArg Telescope.scope
          ((tail.subst opening).rename_asSubst mapping))
        (HEq.refl _) middleOrdinary
    exact HEq.trans toExpanded
      (HEq.trans expanded.symm
        (HEq.trans collapsed.symm openingSquare.symm))
  have whole := subst_comp_heq rfl
    (congrArg Telescope.scope equal) rfl firstPair restCast_heq.symm
  calc
    ((tail.liftSubst opening).comp rest.substitution).comp
        mapping.asSubst =
      (tail.liftSubst opening).comp
        (rest.substitution.comp mapping.asSubst) :=
      Subst.comp_assoc _ _ _
    _ = (tail.liftSubst opening).comp
        (middleRename.asSubst.comp renamedRest.substitution) := by
      rw [restSquare]
    _ = ((tail.liftSubst opening).comp middleRename.asSubst).comp
        renamedRest.substitution :=
      (Subst.comp_assoc _ _ _).symm
    _ = ((tail.liftRename (mapping.lift kind)).asSubst.comp
          ((tail.rename (mapping.lift kind)).liftSubst
            renamedOpening)).comp restCast.substitution :=
      eq_of_heq whole
    _ = _ := Subst.comp_assoc _ _ _

/-- Renaming a complete argument spine commutes with its simultaneous
substitution. -/
theorem substitution_rename_comp
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target} {tele : Telescope source}
    (arguments : Args sourceContext tele) (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    arguments.substitution.comp mapping.asSubst =
      (tele.liftRename mapping).asSubst.comp
        (arguments.rename mapping typed).substitution := by
  induction arguments generalizing target targetContext with
  | nil => rfl
  | @var type tail argument argumentTyping rest ih =>
      simp only [Args.rename, Args.substitution, eq_mpr_eq_cast,
        Telescope.liftRename]
      apply substitution_rename_step tail mapping (Subst.openVar argument)
        (Subst.openVar (argument.rename mapping))
        (Subst.openVarRenameComm argument mapping) rest
        (rest.rename mapping typed)
      · exact substitution_cast_heq
          (tail.rename_subst_comm
            (Subst.openVarRenameComm argument mapping)) _
      · exact ih mapping typed
  | @tvar tail argument rest ih =>
      simp only [Args.rename, Args.substitution, eq_mpr_eq_cast,
        Telescope.liftRename]
      apply substitution_rename_step tail mapping (Subst.openTVar argument)
        (Subst.openTVar (argument.rename mapping))
        (Subst.openTVarRenameComm argument mapping) rest
        (rest.rename mapping typed)
      · exact substitution_cast_heq
          (tail.rename_subst_comm
            (Subst.openTVarRenameComm argument mapping)) _
      · exact ih mapping typed
  | @cvar source result tail argument argumentTyping rest ih =>
      simp only [Args.rename, Args.substitution, eq_mpr_eq_cast,
        Telescope.liftRename]
      apply substitution_rename_step tail mapping (Subst.openCVar argument)
        (Subst.openCVar (argument.rename mapping))
        (Subst.openCVarRenameComm argument mapping) rest
        (rest.rename mapping typed)
      · exact substitution_cast_heq
          (tail.rename_subst_comm
            (Subst.openCVarRenameComm argument mapping)) _
      · exact ih mapping typed

end Telescope.Args

namespace Package.Plan

private theorem rename_asSubst (plan : Package.Plan source)
    (mapping : Rename source target) :
    plan.rename mapping = plan.subst mapping.asSubst := by
  cases plan with
  | mk observations =>
      apply congrArg Package.Plan.mk
      rw [observations.rename_asSubst]
      simp only [Rename.asSubst_lift]

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

private theorem rename_asSubst (shape : Shape source)
    (mapping : Rename source target) :
    shape.rename mapping = shape.subst mapping.asSubst := by
  cases shape with
  | stable plan =>
      exact congrArg Shape.stable (Package.Plan.rename_asSubst plan mapping)
  | «opaque» type =>
      exact congrArg Shape.opaque (type.rename_asSubst mapping)

/-- Instantiating a dependent shape with renamed arguments is exactly the
renaming of its original instantiation. -/
theorem subst_arguments_rename
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target} {tele : Telescope source}
    (shape : Shape tele.scope)
    (arguments : Telescope.Args sourceContext tele)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    (shape.subst arguments.substitution).rename mapping =
      (shape.rename (tele.liftRename mapping)).subst
        (arguments.rename mapping typed).substitution := by
  rw [Shape.rename_asSubst, Shape.subst_comp,
    Shape.rename_asSubst, Shape.subst_comp,
    Telescope.Args.substitution_rename_comp arguments mapping typed]

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
