import SystemFSub.ElaborationRuntime

/-! Algebra for the intrinsically scoped common-runtime erasures. -/

namespace SystemFSub.Elaboration

theorem targetRuntimeSig_translateSig (sig : SystemFSub.Sig) :
    targetRuntimeSig (translateSig sig) = sourceRuntimeSig sig := rfl

def SourceRenameErases
    (rename : SystemFSub.Rename source target)
    (runtimeRename : Runtime.Rename (sourceRuntimeSig source)
      (sourceRuntimeSig target)) : Prop :=
  forall index : SystemFSub.BVar source .var,
    eraseSourceVar (rename.var index) =
      runtimeRename.var (eraseSourceVar index)

def TargetRenameErases
    (rename : SystemFCo.Rename source target)
    (runtimeRename : Runtime.Rename (targetRuntimeSig source)
      (targetRuntimeSig target)) : Prop :=
  forall index : SystemFCo.BVar source .var,
    eraseTargetVar (rename.var index) =
      runtimeRename.var (eraseTargetVar index)

theorem SourceRenameErases.liftVar
    (erases : SourceRenameErases rename runtimeRename) :
    SourceRenameErases (rename.lift (k := .var)) runtimeRename.lift := by
  intro index
  cases index with
  | here => rfl
  | there index => exact congrArg Runtime.BVar.there (erases index)

theorem SourceRenameErases.liftTVar
    (erases : SourceRenameErases rename runtimeRename) :
    SourceRenameErases (rename.lift (k := .tvar)) runtimeRename := by
  intro index
  cases index with
  | there index => exact erases index

theorem TargetRenameErases.liftVar
    (erases : TargetRenameErases rename runtimeRename) :
    TargetRenameErases (rename.lift .var) runtimeRename.lift := by
  intro index
  cases index with
  | here => rfl
  | there index => exact congrArg Runtime.BVar.there (erases index)

theorem TargetRenameErases.liftTVar
    (erases : TargetRenameErases rename runtimeRename) :
    TargetRenameErases (rename.lift .tvar) runtimeRename := by
  intro index
  cases index with
  | there index => exact erases index

theorem TargetRenameErases.liftCVar
    (erases : TargetRenameErases rename runtimeRename) :
    TargetRenameErases (rename.lift .cvar) runtimeRename := by
  intro index
  cases index with
  | there index => exact erases index

theorem eraseSource_rename {source target : SystemFSub.Sig}
    (term : SystemFSub.Tm source)
    {rename : SystemFSub.Rename source target}
    {runtimeRename : Runtime.Rename (sourceRuntimeSig source)
      (sourceRuntimeSig target)}
    (erases : SourceRenameErases rename runtimeRename) :
    eraseSource (term.rename rename) =
      (eraseSource term).rename runtimeRename := by
  induction term generalizing target with
  | var index => exact congrArg Runtime.Term.var (erases index)
  | abs _ body ih => exact congrArg Runtime.Term.abs (ih erases.liftVar)
  | app function argument functionIH argumentIH =>
      simp only [SystemFSub.Tm.rename, eraseSource, Runtime.Term.rename]
      rw [functionIH erases, argumentIH erases]
  | tabs _ body ih =>
      exact congrArg (fun term => Runtime.Term.tabs (.tabs term))
        (ih erases.liftTVar)
  | tapp function _ ih =>
      exact congrArg (fun term => Runtime.Term.tapp (.tapp term)) (ih erases)

theorem eraseTarget_rename {source target : SystemFCo.Sig}
    (expression : SystemFCo.Exp source)
    {rename : SystemFCo.Rename source target}
    {runtimeRename : Runtime.Rename (targetRuntimeSig source)
      (targetRuntimeSig target)}
    (erases : TargetRenameErases rename runtimeRename) :
    eraseTarget (expression.rename rename) =
      (eraseTarget expression).rename runtimeRename := by
  induction expression generalizing target with
  | var index => exact congrArg Runtime.Term.var (erases index)
  | abs _ body ih => exact congrArg Runtime.Term.abs (ih erases.liftVar)
  | app function argument functionIH argumentIH =>
      simp only [SystemFCo.Exp.rename, eraseTarget, Runtime.Term.rename]
      rw [functionIH erases, argumentIH erases]
  | tabs body ih => exact congrArg Runtime.Term.tabs (ih erases.liftTVar)
  | tapp function _ ih => exact congrArg Runtime.Term.tapp (ih erases)
  | cabs _ _ body ih => exact congrArg Runtime.Term.tabs (ih erases.liftCVar)
  | capp function _ ih => exact congrArg Runtime.Term.tapp (ih erases)
  | cast expression _ ih => exact ih erases

theorem sourceRenameWeakenVar (sig : SystemFSub.Sig) :
    SourceRenameErases
      (SystemFSub.Rename.succ (s := sig) (k := .var))
      (Runtime.Rename.weaken (sig := sourceRuntimeSig sig)) := by
  intro index
  rfl

theorem sourceRenameWeakenTVar (sig : SystemFSub.Sig) :
    SourceRenameErases
      (SystemFSub.Rename.succ (s := sig) (k := .tvar))
      (Runtime.Rename.id (sig := sourceRuntimeSig sig)) := by
  intro index
  rfl

theorem targetRenameWeakenVar (sig : SystemFCo.Sig) :
    TargetRenameErases (SystemFCo.Rename.weaken (sig := sig) .var)
      (Runtime.Rename.weaken (sig := targetRuntimeSig sig)) := by
  intro index
  rfl

theorem targetRenameWeakenTVar (sig : SystemFCo.Sig) :
    TargetRenameErases (SystemFCo.Rename.weaken (sig := sig) .tvar)
      (Runtime.Rename.id (sig := targetRuntimeSig sig)) := by
  intro index
  rfl

theorem targetRenameWeakenCVar (sig : SystemFCo.Sig) :
    TargetRenameErases (SystemFCo.Rename.weaken (sig := sig) .cvar)
      (Runtime.Rename.id (sig := targetRuntimeSig sig)) := by
  intro index
  rfl

end SystemFSub.Elaboration
