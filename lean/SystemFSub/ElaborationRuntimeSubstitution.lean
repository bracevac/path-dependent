import SystemFSub.ElaborationRuntimeLaws

/-! Substitution/opening laws for the common-runtime erasures. -/

namespace SystemFSub.Elaboration

namespace Runtime

theorem Rename.ext {first second : Rename source target}
    (equal : forall index, first.var index = second.var index) :
    first = second := by
  cases first with
  | mk first =>
      cases second with
      | mk second =>
          congr
          funext index
          exact equal index

@[simp]
theorem Rename.lift_id :
    (Rename.id (sig := sig)).lift = Rename.id := by
  apply Rename.ext
  intro index
  cases index <;> rfl

theorem Term.rename_id (term : Term sig) :
    term.rename Rename.id = term := by
  induction term with
  | var => rfl
  | abs body ih => simp only [Term.rename, Rename.lift_id, ih]
  | app function argument functionIH argumentIH =>
      simp only [Term.rename, functionIH, argumentIH]
  | tabs body ih => simp only [Term.rename, ih]
  | tapp function ih => simp only [Term.rename, ih]

theorem Subst.ext {first second : Subst source target}
    (equal : forall index, first.var index = second.var index) :
    first = second := by
  cases first with
  | mk first =>
      cases second with
      | mk second =>
          congr
          funext index
          exact equal index

@[simp]
theorem Subst.lift_id :
    (Subst.id (sig := sig)).lift = Subst.id := by
  apply Subst.ext
  intro index
  cases index <;> rfl

theorem Term.subst_id (term : Term sig) :
    term.subst Subst.id = term := by
  induction term with
  | var => rfl
  | abs body ih => simp only [Term.subst, Subst.lift_id, ih]
  | app function argument functionIH argumentIH =>
      simp only [Term.subst, functionIH, argumentIH]
  | tabs body ih => simp only [Term.subst, ih]
  | tapp function ih => simp only [Term.subst, ih]

end Runtime

def SourceSubstErases
    (substitution : SystemFSub.Subst source target)
    (runtimeSubstitution : Runtime.Subst (sourceRuntimeSig source)
      (sourceRuntimeSig target)) : Prop :=
  forall index : SystemFSub.BVar source .var,
    eraseSource (substitution.var index) =
      runtimeSubstitution.var (eraseSourceVar index)

def TargetSubstErases
    (substitution : SystemFCo.Subst source target)
    (runtimeSubstitution : Runtime.Subst (targetRuntimeSig source)
      (targetRuntimeSig target)) : Prop :=
  forall index : SystemFCo.BVar source .var,
    eraseTarget (substitution.var index) =
      runtimeSubstitution.var (eraseTargetVar index)

theorem SourceSubstErases.liftVar
    (erases : SourceSubstErases substitution runtimeSubstitution) :
    SourceSubstErases (substitution.lift (k := .var))
      runtimeSubstitution.lift := by
  intro index
  cases index with
  | here => rfl
  | there index =>
      change eraseSource ((substitution.var index).rename
          (SystemFSub.Rename.succ (k := .var))) =
        (runtimeSubstitution.var (eraseSourceVar index)).rename
          Runtime.Rename.weaken
      rw [eraseSource_rename _ (sourceRenameWeakenVar _), erases index]
      rfl

theorem SourceSubstErases.liftTVar
    (erases : SourceSubstErases substitution runtimeSubstitution) :
    SourceSubstErases (substitution.lift (k := .tvar))
      runtimeSubstitution := by
  intro index
  cases index with
  | there index =>
      calc
        eraseSource ((substitution.var index).rename
            (SystemFSub.Rename.succ (k := .tvar))) =
            (eraseSource (substitution.var index)).rename Runtime.Rename.id :=
          eraseSource_rename _ (sourceRenameWeakenTVar _)
        _ = eraseSource (substitution.var index) :=
          Runtime.Term.rename_id _
        _ = runtimeSubstitution.var (eraseSourceVar index) := erases index

theorem TargetSubstErases.liftVar
    (erases : TargetSubstErases substitution runtimeSubstitution) :
    TargetSubstErases (substitution.lift .var)
      runtimeSubstitution.lift := by
  intro index
  cases index with
  | here => rfl
  | there index =>
      change eraseTarget ((substitution.var index).rename
          (SystemFCo.Rename.weaken .var)) =
        (runtimeSubstitution.var (eraseTargetVar index)).rename
          Runtime.Rename.weaken
      rw [eraseTarget_rename _ (targetRenameWeakenVar _), erases index]
      rfl

theorem TargetSubstErases.liftTVar
    (erases : TargetSubstErases substitution runtimeSubstitution) :
    TargetSubstErases (substitution.lift .tvar)
      runtimeSubstitution := by
  intro index
  cases index with
  | there index =>
      calc
        eraseTarget ((substitution.var index).rename
            (SystemFCo.Rename.weaken .tvar)) =
            (eraseTarget (substitution.var index)).rename Runtime.Rename.id :=
          eraseTarget_rename _ (targetRenameWeakenTVar _)
        _ = eraseTarget (substitution.var index) := Runtime.Term.rename_id _
        _ = runtimeSubstitution.var (eraseTargetVar index) := erases index

theorem TargetSubstErases.liftCVar
    (erases : TargetSubstErases substitution runtimeSubstitution) :
    TargetSubstErases (substitution.lift .cvar)
      runtimeSubstitution := by
  intro index
  cases index with
  | there index =>
      calc
        eraseTarget ((substitution.var index).rename
            (SystemFCo.Rename.weaken .cvar)) =
            (eraseTarget (substitution.var index)).rename Runtime.Rename.id :=
          eraseTarget_rename _ (targetRenameWeakenCVar _)
        _ = eraseTarget (substitution.var index) := Runtime.Term.rename_id _
        _ = runtimeSubstitution.var (eraseTargetVar index) := erases index

theorem eraseSource_subst {source target : SystemFSub.Sig}
    (term : SystemFSub.Tm source)
    {substitution : SystemFSub.Subst source target}
    {runtimeSubstitution : Runtime.Subst (sourceRuntimeSig source)
      (sourceRuntimeSig target)}
    (erases : SourceSubstErases substitution runtimeSubstitution) :
    eraseSource (term.subst substitution) =
      (eraseSource term).subst runtimeSubstitution := by
  induction term generalizing target with
  | var index => exact erases index
  | abs _ body ih => exact congrArg Runtime.Term.abs (ih erases.liftVar)
  | app function argument functionIH argumentIH =>
      simp only [SystemFSub.Tm.subst, eraseSource, Runtime.Term.subst]
      rw [functionIH erases, argumentIH erases]
  | tabs _ body ih =>
      exact congrArg (fun term => Runtime.Term.tabs (.tabs term))
        (ih erases.liftTVar)
  | tapp function _ ih =>
      exact congrArg (fun term => Runtime.Term.tapp (.tapp term)) (ih erases)

theorem eraseTarget_subst {source target : SystemFCo.Sig}
    (expression : SystemFCo.Exp source)
    {substitution : SystemFCo.Subst source target}
    {runtimeSubstitution : Runtime.Subst (targetRuntimeSig source)
      (targetRuntimeSig target)}
    (erases : TargetSubstErases substitution runtimeSubstitution) :
    eraseTarget (expression.subst substitution) =
      (eraseTarget expression).subst runtimeSubstitution := by
  induction expression generalizing target with
  | var index => exact erases index
  | abs _ body ih => exact congrArg Runtime.Term.abs (ih erases.liftVar)
  | app function argument functionIH argumentIH =>
      simp only [SystemFCo.Exp.subst, eraseTarget, Runtime.Term.subst]
      rw [functionIH erases, argumentIH erases]
  | tabs body ih => exact congrArg Runtime.Term.tabs (ih erases.liftTVar)
  | tapp function _ ih => exact congrArg Runtime.Term.tapp (ih erases)
  | cabs _ _ body ih => exact congrArg Runtime.Term.tabs (ih erases.liftCVar)
  | capp function _ ih => exact congrArg Runtime.Term.tapp (ih erases)
  | cast expression _ ih => exact ih erases

theorem sourceOpenVarErases (argument : SystemFSub.Tm sig) :
    SourceSubstErases (SystemFSub.Subst.openVar argument)
      (Runtime.Subst.openVar (eraseSource argument)) := by
  intro index
  cases index <;> rfl

theorem sourceOpenTVarErases (argument : SystemFSub.Ty sig) :
    SourceSubstErases (SystemFSub.Subst.openTVar argument)
      Runtime.Subst.id := by
  intro index
  cases index with
  | there index => rfl

theorem targetOpenVarErases (argument : SystemFCo.Exp sig) :
    TargetSubstErases (SystemFCo.Subst.openVar argument)
      (Runtime.Subst.openVar (eraseTarget argument)) := by
  intro index
  cases index <;> rfl

theorem targetOpenTVarErases (argument : SystemFCo.Ty sig) :
    TargetSubstErases (SystemFCo.Subst.openTVar argument)
      Runtime.Subst.id := by
  intro index
  cases index with
  | there index => rfl

theorem targetOpenCVarErases (argument : SystemFCo.Co sig) :
    TargetSubstErases (SystemFCo.Subst.openCVar argument)
      Runtime.Subst.id := by
  intro index
  cases index with
  | there index => rfl

theorem eraseSource_open (body : SystemFSub.Tm (sig,x))
    (argument : SystemFSub.Tm sig) :
    eraseSource (body.open argument) =
      (eraseSource body).instantiate (eraseSource argument) :=
  eraseSource_subst body (sourceOpenVarErases argument)

theorem eraseSource_openTy (body : SystemFSub.Tm (sig,X))
    (argument : SystemFSub.Ty sig) :
    eraseSource (body.openTy argument) = eraseSource body := by
  unfold SystemFSub.Tm.openTy
  rw [eraseSource_subst body (sourceOpenTVarErases argument)]
  exact Runtime.Term.subst_id _

theorem eraseTarget_openVar (body : SystemFCo.Exp (sig ,, .var))
    (argument : SystemFCo.Exp sig) :
    eraseTarget (body.subst (SystemFCo.Subst.openVar argument)) =
      (eraseTarget body).instantiate (eraseTarget argument) :=
  eraseTarget_subst body (targetOpenVarErases argument)

theorem eraseTarget_openTVar (body : SystemFCo.Exp (sig ,, .tvar))
    (argument : SystemFCo.Ty sig) :
    eraseTarget (body.subst (SystemFCo.Subst.openTVar argument)) =
      eraseTarget body := by
  rw [eraseTarget_subst body (targetOpenTVarErases argument)]
  exact Runtime.Term.subst_id _

theorem eraseTarget_openCVar (body : SystemFCo.Exp (sig ,, .cvar))
    (argument : SystemFCo.Co sig) :
    eraseTarget (body.subst (SystemFCo.Subst.openCVar argument)) =
      eraseTarget body := by
  rw [eraseTarget_subst body (targetOpenCVarErases argument)]
  exact Runtime.Term.subst_id _

end SystemFSub.Elaboration
