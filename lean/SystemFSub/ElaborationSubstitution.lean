import SystemFSub.ElaborationRenameLaws

/-!
Substitution through binder expansion.  Source types only observe translated
type variables; the target coercion component is therefore parametric.
-/

namespace SystemFSub.Elaboration

/-- Two target substitutions agree on every component observable by `Ty`. -/
structure TargetTVarEq
    (first second : SystemFCo.Subst source target) : Prop where
  tvar : forall x, first.tvar x = second.tvar x

theorem TargetTVarEq.lift
    (equal : TargetTVarEq first second) (kind : SystemFCo.Kind) :
    TargetTVarEq (first.lift kind) (second.lift kind) := by
  constructor
  intro x
  cases x with
  | here => rfl
  | there x =>
      simp only [SystemFCo.Subst.lift_tvar_there]
      exact congrArg (fun ty =>
        ty.rename (SystemFCo.Rename.weaken kind)) (equal.tvar x)

/-- Target types are insensitive to term and coercion components of a
substitution. -/
theorem targetTy_subst_congr (ty : SystemFCo.Ty source)
    {target : SystemFCo.Sig}
    {first second : SystemFCo.Subst source target}
    (equal : TargetTVarEq first second) :
    ty.subst first = ty.subst second := by
  induction ty generalizing target with
  | top => rfl
  | tvar x =>
      simp only [SystemFCo.Ty.subst]
      exact equal.tvar x
  | arrow parameter result parameter_ih result_ih =>
      simp only [SystemFCo.Ty.subst, parameter_ih equal, result_ih equal]
  | poly body body_ih =>
      simp only [SystemFCo.Ty.subst]
      exact congrArg SystemFCo.Ty.poly (body_ih (equal.lift .tvar))
  | qual source result body source_ih result_ih body_ih =>
      simp only [SystemFCo.Ty.subst, source_ih equal, result_ih equal]
      exact congrArg (SystemFCo.Ty.qual _ _)
        (body_ih (equal.lift .cvar))

/-- Compatibility between a source type substitution and its action on the
expanded target scope. -/
structure TySubstComm
    (sourceSubst : SystemFSub.Subst source target)
    (targetSubst : SystemFCo.Subst (translateSig source)
      (translateSig target)) : Prop where
  tvar : forall x,
    translateTy (sourceSubst.tvar x) =
      targetSubst.tvar (translateTVar x)

theorem TySubstComm.lift
    {source target : SystemFSub.Sig}
    {sourceSubst : SystemFSub.Subst source target}
    {targetSubst : SystemFCo.Subst (translateSig source) (translateSig target)}
    (comm : TySubstComm sourceSubst targetSubst) :
    TySubstComm
      ((@SystemFSub.Subst.lift source target .tvar sourceSubst) :
        SystemFSub.Subst (source,X) (target,X))
      (((targetSubst.lift .tvar).lift .cvar) :
        SystemFCo.Subst (translateSig (source,X)) (translateSig (target,X))) := by
  constructor
  intro x
  cases x with
  | here => rfl
  | there x =>
      change translateTy ((sourceSubst.tvar x).weaken (k := .tvar)) =
        (((targetSubst.tvar (translateTVar x)).rename
          (SystemFCo.Rename.weaken .tvar)).rename
          (SystemFCo.Rename.weaken .cvar))
      rw [translateTy_weaken_tvar, comm.tvar]
      rfl

/-- Type translation commutes with every pair of compatible substitutions. -/
theorem translateTy_subst (ty : SystemFSub.Ty source)
    (sourceSubst : SystemFSub.Subst source target)
    (targetSubst : SystemFCo.Subst (translateSig source)
      (translateSig target))
    (comm : TySubstComm sourceSubst targetSubst) :
    translateTy (ty.subst sourceSubst) =
      (translateTy ty).subst targetSubst := by
  induction ty generalizing target with
  | top => rfl
  | tvar x =>
      simp only [SystemFSub.Ty.subst, translateTy, SystemFCo.Ty.subst]
      exact comm.tvar x
  | arrow parameter result parameter_ih result_ih =>
      simp only [SystemFSub.Ty.subst, translateTy, SystemFCo.Ty.subst]
      rw [parameter_ih sourceSubst targetSubst comm,
        result_ih sourceSubst targetSubst comm]
  | all bound body bound_ih body_ih =>
      simp only [SystemFSub.Ty.subst, translateTy, SystemFCo.Ty.subst]
      rw [bound_ih sourceSubst targetSubst comm]
      have boundEq := SystemFCo.Ty.weaken_subst_comm_base
        (kind := SystemFCo.Kind.tvar) (translateTy bound) targetSubst
      have bodyEq := body_ih _ _ comm.lift
      simp only [SystemFCo.Subst.lift_tvar_here]
      congr

/-- Remove a freshly weakened coercion binder from a target type. -/
theorem targetTy_weaken_openCVar (ty : SystemFCo.Ty sig)
    (evidence : SystemFCo.Co sig) :
    (ty.weaken .cvar).subst (SystemFCo.Subst.openCVar evidence) = ty := by
  unfold SystemFCo.Ty.weaken
  rw [SystemFCo.Ty.rename_asSubst, SystemFCo.Ty.subst_comp]
  have equal : TargetTVarEq
      ((SystemFCo.Rename.weaken .cvar).asSubst.comp
        (SystemFCo.Subst.openCVar evidence)) SystemFCo.Subst.id := by
    constructor
    intro x
    rfl
  rw [targetTy_subst_congr ty equal, SystemFCo.Ty.subst_id]

/-- The target substitution implementing source type instantiation: first
open the translated type variable below its evidence binder, then open that
evidence binder. -/
def openTyPair (argument : SystemFCo.Ty sig)
    (evidence : SystemFCo.Co sig) :
    SystemFCo.Subst ((sig ,, .tvar) ,, .cvar) sig :=
  ((SystemFCo.Subst.openTVar argument).lift .cvar).comp
    (SystemFCo.Subst.openCVar evidence)

theorem openTyPair_comm (argument : SystemFSub.Ty sig)
    (evidence : SystemFCo.Co (translateSig sig)) :
    TySubstComm (SystemFSub.Subst.openTVar argument)
      (openTyPair (translateTy argument) evidence) := by
  constructor
  intro x
  cases x with
  | here =>
      change translateTy argument =
        ((translateTy argument).weaken .cvar).subst
          (SystemFCo.Subst.openCVar evidence)
      exact (targetTy_weaken_openCVar (translateTy argument) evidence).symm
  | there x =>
      change SystemFCo.Ty.tvar (translateTVar x) =
        ((SystemFCo.Ty.tvar (translateTVar x)).weaken .cvar).subst
          (SystemFCo.Subst.openCVar evidence)
      exact (targetTy_weaken_openCVar
        (.tvar (translateTVar x)) evidence).symm

/-- Translation of source type instantiation is target type opening followed
by opening the paired evidence binder.  The evidence is arbitrary because a
translated source type cannot inspect coercion variables. -/
theorem translateTy_open (body : SystemFSub.Ty (sig,X))
    (argument : SystemFSub.Ty sig)
    (evidence : SystemFCo.Co (translateSig sig)) :
    translateTy (body.open argument) =
      ((translateTy body).subst
        ((SystemFCo.Subst.openTVar (translateTy argument)).lift .cvar)).subst
        (SystemFCo.Subst.openCVar evidence) := by
  unfold SystemFSub.Ty.open
  rw [translateTy_subst body (SystemFSub.Subst.openTVar argument)
    (openTyPair (translateTy argument) evidence)
    (openTyPair_comm argument evidence)]
  exact (SystemFCo.Ty.subst_comp (translateTy body)
    ((SystemFCo.Subst.openTVar (translateTy argument)).lift .cvar)
    (SystemFCo.Subst.openCVar evidence)).symm

end SystemFSub.Elaboration
