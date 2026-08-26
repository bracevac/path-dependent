import SystemFSub.ElaborationRenaming
import SystemFCo.Substitution

/-!
Functoriality of binder expansion.  A source term binder maps to one target
term binder; a source type binder maps, in order, to a target type binder and
then its coercion-evidence binder.
-/

namespace SystemFSub.Elaboration

/-! ## Renaming functor laws -/

@[simp] theorem translateRename_id :
    translateRename (SystemFSub.Rename.id (s := sig)) =
      (SystemFCo.Rename.id :
        SystemFCo.Rename (translateSig sig) (translateSig sig)) := by
  apply SystemFCo.Rename.funext
  intro kind x
  cases kind with
  | var =>
      change translateVar (untranslateVar x) = x
      exact translate_untranslateVar x
  | tvar =>
      change translateTVar (untranslateTVar x) = x
      exact translate_untranslateTVar x
  | cvar =>
      change translateBound (untranslateBound x) = x
      exact translate_untranslateBound x

theorem translateRename_comp
    (first : SystemFSub.Rename source middle)
    (second : SystemFSub.Rename middle target) :
    translateRename (first.comp second) =
      (translateRename first).comp (translateRename second) := by
  apply SystemFCo.Rename.funext
  intro kind x
  cases kind with
  | var =>
      change translateVar (second.var (first.var (untranslateVar x))) =
        translateVar
          (second.var
            (untranslateVar (translateVar (first.var (untranslateVar x)))))
      rw [untranslate_translateVar]
  | tvar =>
      change translateTVar (second.var (first.var (untranslateTVar x))) =
        translateTVar
          (second.var
            (untranslateTVar (translateTVar (first.var (untranslateTVar x)))))
      rw [untranslate_translateTVar]
  | cvar =>
      change translateBound (second.var (first.var (untranslateBound x))) =
        translateBound
          (second.var
            (untranslateBound (translateBound (first.var (untranslateBound x)))))
      rw [untranslate_translateBound]

@[simp] theorem translateRename_lift_var
    (rename : SystemFSub.Rename source target) :
    translateRename (rename.lift (k := .var)) =
      (translateRename rename).lift SystemFCo.Kind.var := by
  apply SystemFCo.Rename.funext
  intro kind x
  cases kind with
  | var =>
      cases x with
      | here => rfl
      | there x =>
          change translateVar (.there (rename.var (untranslateVar x))) = _
          rfl
  | tvar =>
      cases x with
      | there x =>
          change translateTVar (.there (rename.var (untranslateTVar x))) = _
          rfl
  | cvar =>
      cases x with
      | there x =>
          change translateBound (.there (rename.var (untranslateBound x))) = _
          rfl

@[simp] theorem translateRename_lift_tvar
    (rename : SystemFSub.Rename source target) :
    translateRename (rename.lift (k := .tvar)) =
      ((translateRename rename).lift SystemFCo.Kind.tvar).lift
        SystemFCo.Kind.cvar := by
  apply SystemFCo.Rename.funext
  intro kind x
  cases kind with
  | var =>
      cases x with
      | there x =>
          cases x with
          | there x =>
              change translateVar
                (.there (rename.var (untranslateVar x))) = _
              rfl
  | tvar =>
      cases x with
      | there x =>
          cases x with
          | here => rfl
          | there x =>
              change translateTVar
                (.there (rename.var (untranslateTVar x))) = _
              rfl
  | cvar =>
      cases x with
      | here => rfl
      | there x =>
          cases x with
          | there x =>
              change translateBound
                (.there (rename.var (untranslateBound x))) = _
              rfl

/-! ## Successor renamings under binder expansion -/

@[simp] theorem translateRename_succ_var :
    translateRename (SystemFSub.Rename.succ (s := sig) (k := .var)) =
      SystemFCo.Rename.weaken SystemFCo.Kind.var := by
  apply SystemFCo.Rename.funext
  intro kind x
  cases kind with
  | var =>
      change translateVar
        (@SystemFSub.BVar.there sig .var .var (untranslateVar x)) =
        .there x
      exact congrArg SystemFCo.BVar.there (translate_untranslateVar x)
  | tvar =>
      change translateTVar
        (@SystemFSub.BVar.there sig .tvar .var (untranslateTVar x)) =
        .there x
      exact congrArg SystemFCo.BVar.there (translate_untranslateTVar x)
  | cvar =>
      change translateBound
        (@SystemFSub.BVar.there sig .tvar .var (untranslateBound x)) =
        .there x
      exact congrArg SystemFCo.BVar.there (translate_untranslateBound x)

@[simp] theorem translateRename_succ_tvar :
    translateRename (SystemFSub.Rename.succ (s := sig) (k := .tvar)) =
      (SystemFCo.Rename.weaken SystemFCo.Kind.tvar).comp
        (SystemFCo.Rename.weaken SystemFCo.Kind.cvar) := by
  apply SystemFCo.Rename.funext
  intro kind x
  cases kind with
  | var =>
      change translateVar
        (@SystemFSub.BVar.there sig .var .tvar (untranslateVar x)) =
        .there (.there x)
      exact congrArg SystemFCo.BVar.there
        (congrArg SystemFCo.BVar.there (translate_untranslateVar x))
  | tvar =>
      change translateTVar
        (@SystemFSub.BVar.there sig .tvar .tvar (untranslateTVar x)) =
        .there (.there x)
      exact congrArg SystemFCo.BVar.there
        (congrArg SystemFCo.BVar.there (translate_untranslateTVar x))
  | cvar =>
      change translateBound
        (@SystemFSub.BVar.there sig .tvar .tvar (untranslateBound x)) =
        .there (.there x)
      exact congrArg SystemFCo.BVar.there
        (congrArg SystemFCo.BVar.there (translate_untranslateBound x))

/-! ## Type translation is natural in renaming -/

theorem translateTy_rename (ty : SystemFSub.Ty source)
    (rename : SystemFSub.Rename source target) :
    translateTy (ty.rename rename) =
      (translateTy ty).rename (translateRename rename) := by
  induction ty generalizing target with
  | top => rfl
  | tvar x =>
      simp only [SystemFSub.Ty.rename, translateTy, SystemFCo.Ty.rename]
      exact congrArg SystemFCo.Ty.tvar
        (translateRename_tvar rename x).symm
  | arrow parameter result parameter_ih result_ih =>
      simp only [SystemFSub.Ty.rename, translateTy, SystemFCo.Ty.rename]
      rw [parameter_ih, result_ih]
  | all bound body bound_ih body_ih =>
      simp only [SystemFSub.Ty.rename, translateTy, SystemFCo.Ty.rename]
      rw [bound_ih]
      rw [SystemFCo.Ty.rename_weaken_comm]
      rw [body_ih]
      simp only [SystemFCo.Rename.lift_here]
      congr 2
      exact congrArg (SystemFCo.Ty.rename (translateTy body))
        (translateRename_lift_tvar rename)

@[simp] theorem translateTy_weaken_var (ty : SystemFSub.Ty sig) :
    translateTy (ty.weaken (k := .var)) =
      (translateTy ty).weaken SystemFCo.Kind.var := by
  unfold SystemFSub.Ty.weaken
  rw [translateTy_rename, translateRename_succ_var]
  rfl

@[simp] theorem translateTy_weaken_tvar (ty : SystemFSub.Ty sig) :
    translateTy (ty.weaken (k := .tvar)) =
      ((translateTy ty).weaken SystemFCo.Kind.tvar).weaken
        SystemFCo.Kind.cvar := by
  unfold SystemFSub.Ty.weaken
  rw [translateTy_rename, translateRename_succ_tvar]
  exact (SystemFCo.Ty.rename_comp (translateTy ty)
    (SystemFCo.Rename.weaken .tvar)
    (SystemFCo.Rename.weaken .cvar)).symm

end SystemFSub.Elaboration
