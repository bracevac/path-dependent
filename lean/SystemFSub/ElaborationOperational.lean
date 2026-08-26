import SystemFSub.ElaborationRuntimeSubstitution

/-!
# Forward operational correspondence through the common runtime

Both source and target steps map to finite common-runtime reductions. Target
cast administration maps to reflexivity; target type and coercion beta each
map to one runtime type phase, while source type beta maps to both phases.
-/

namespace SystemFSub.Elaboration

theorem eraseTranslatedVar : {sig : SystemFSub.Sig} ->
    (index : SystemFSub.BVar sig .var) ->
    eraseTargetVar (translateVar index) = eraseSourceVar index
| _, .here => rfl
| _, @SystemFSub.BVar.there tail .var .var index =>
    congrArg Runtime.BVar.there (eraseTranslatedVar (sig := tail) index)
| _, @SystemFSub.BVar.there tail .var .tvar index =>
    eraseTranslatedVar (sig := tail) index

theorem erase_elaborateTerm
    (derivation : SystemFSub.Tm.HasType context term ty) :
    eraseTarget (elaborateTerm derivation) = eraseSource term := by
  induction derivation with
  | var lookup => exact congrArg Runtime.Term.var (eraseTranslatedVar _)
  | abs _ ih => exact congrArg Runtime.Term.abs ih
  | app _ _ functionIH argumentIH =>
      simp only [elaborateTerm, eraseTarget, eraseSource]
      rw [functionIH, argumentIH]
      rfl
  | tabs _ ih =>
      exact congrArg (fun term => Runtime.Term.tabs (.tabs term)) ih
  | tapp _ _ functionIH =>
      exact congrArg (fun term => Runtime.Term.tapp (.tapp term)) functionIH
  | sub _ _ ih => exact ih

theorem eraseSource_value
    (value : SystemFSub.Tm.IsValue term) :
    Runtime.IsValue (eraseSource term) := by
  cases value with
  | abs => exact .abs
  | tabs => exact .tabs

theorem eraseTarget_value
    (value : SystemFCo.Exp.IsValue expression) :
    Runtime.IsValue (eraseTarget expression) := by
  induction value with
  | abs => exact .abs
  | tabs => exact .tabs
  | cabs => exact .tabs
  | castTop _ ih => exact ih
  | castArrow _ ih => exact ih
  | castPoly _ ih => exact ih
  | castQual _ ih => exact ih

theorem eraseSource_step
    (step : SystemFSub.Tm.Step first last) :
    Runtime.Steps (eraseSource first) (eraseSource last) := by
  induction step with
  | app_left _ ih => exact ih.appFunction
  | app_right value _ ih =>
      exact ih.appArgument (eraseSource_value value)
  | beta value =>
      rw [eraseSource_open]
      exact Runtime.Steps.single (.beta (eraseSource_value value))
  | tapp_fun _ ih => exact (ih.tappFunction).tappFunction
  | type_beta =>
      rw [eraseSource_openTy]
      exact .tail (.tappFunction .typeBeta) (.tail .typeBeta .refl)

theorem eraseSource_steps
    (steps : SystemFSub.Tm.Steps first last) :
    Runtime.Steps (eraseSource first) (eraseSource last) := by
  induction steps with
  | refl => exact .refl
  | tail step rest ih => exact (eraseSource_step step).trans ih

theorem eraseTarget_step
    (step : SystemFCo.Exp.Step first last) :
    Runtime.Steps (eraseTarget first) (eraseTarget last) := by
  induction step with
  | appFunction _ ih => exact ih.appFunction
  | appArgument value _ ih =>
      exact ih.appArgument (eraseTarget_value value)
  | beta value =>
      rw [eraseTarget_openVar]
      exact Runtime.Steps.single (.beta (eraseTarget_value value))
  | tappFunction _ ih => exact ih.tappFunction
  | typeBeta =>
      rw [eraseTarget_openTVar]
      exact Runtime.Steps.single .typeBeta
  | cappFunction _ ih => exact ih.tappFunction
  | coercionBeta =>
      rw [eraseTarget_openCVar]
      exact Runtime.Steps.single .typeBeta
  | castExpression _ ih => exact ih
  | castRefl _ => exact .refl
  | castTrans _ => exact .refl
  | castArrowApp _ _ => exact .refl
  | castPolyTapp _ => exact .refl
  | castQualCapp _ => exact .refl

theorem eraseTarget_steps
    (steps : SystemFCo.Exp.Steps first last) :
    Runtime.Steps (eraseTarget first) (eraseTarget last) := by
  induction steps with
  | refl => exact .refl
  | tail step rest ih => exact (eraseTarget_step step).trans ih

end SystemFSub.Elaboration
