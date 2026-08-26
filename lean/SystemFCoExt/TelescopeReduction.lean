import SystemFCoExt.Telescope
import SystemFCoExt.ReductionSubstitution
import SystemFCoExt.Operational

/-!
# Operational Church beta for mixed telescopes

This module connects the typed telescope encodings to the weak call-by-value
target dynamics. Term fields must be values; type and coercion fields are
administrative arguments and need no readiness premise.
-/

namespace SystemFCoExt
namespace Telescope

namespace Args

/-- Every term argument in a mixed telescope spine is already a value. -/
def AllValues : {tele : Telescope sig} -> Args base tele -> Prop
| _, .nil => True
| _, .var argument _ rest => Exp.IsValue argument /\ AllValues rest
| _, .tvar _ rest => AllValues rest
| _, .cvar _ _ rest => AllValues rest

/-- Applying an argument spine is invariant under transport of its telescope
index. -/
@[simp] theorem apply_index_cast
    {first second : Telescope sig}
    (equal : first = second)
    (arguments : Args base first) (function : Exp sig) :
    (cast (congrArg (Args base) equal) arguments).apply function =
      arguments.apply function := by
  cases equal
  rfl

/-- An argument spine is an evaluation context in its function position. -/
theorem apply_steps (arguments : Args base tele)
    (reductions : Exp.Steps function result) :
    Exp.Steps (arguments.apply function) (arguments.apply result) := by
  induction arguments generalizing function result with
  | nil => exact reductions
  | var argument argumentTyping rest ih =>
      simp only [Args.apply]
      apply ih
      induction reductions with
      | refl => exact .refl
      | tail step steps tailIH =>
          exact .tail (.appFunction step) tailIH
  | tvar argument rest ih =>
      simp only [Args.apply]
      apply ih
      induction reductions with
      | refl => exact .refl
      | tail step steps tailIH =>
          exact .tail (.tappFunction step) tailIH
  | cvar argument argumentTyping rest ih =>
      simp only [Args.apply]
      apply ih
      induction reductions with
      | refl => exact .refl
      | tail step steps tailIH =>
          exact .tail (.cappFunction step) tailIH

/-- Renaming a typed argument spine commutes with applying it. -/
theorem apply_rename
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target} {tele : Telescope source}
    (arguments : Args sourceContext tele) (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping)
    (function : Exp source) :
    (arguments.rename mapping typed).apply (function.rename mapping) =
      (arguments.apply function).rename mapping := by
  induction arguments generalizing target targetContext function with
  | nil => rfl
  | @var type tail argument argumentTyping rest ih =>
      simp only [Args.rename, Args.apply, eq_mpr_eq_cast]
      rw [apply_index_cast
        (tail.rename_subst_comm
          (Subst.openVarRenameComm argument mapping))]
      exact ih mapping typed (.app function argument)
  | @tvar tail argument rest ih =>
      simp only [Args.rename, Args.apply, eq_mpr_eq_cast]
      rw [apply_index_cast
        (tail.rename_subst_comm
          (Subst.openTVarRenameComm argument mapping))]
      exact ih mapping typed (.tapp function argument)
  | @cvar source result tail argument argumentTyping rest ih =>
      simp only [Args.rename, Args.apply, eq_mpr_eq_cast]
      rw [apply_index_cast
        (tail.rename_subst_comm
          (Subst.openCVarRenameComm argument mapping))]
      exact ih mapping typed (.capp function argument)

/-- If a substitution cancels a renaming, opening a renamed argument spine
recovers the original spine while opening its function position. -/
theorem apply_rename_subst_cancel
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target} {tele : Telescope source}
    (arguments : Args sourceContext tele) (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping)
    (opening : Subst target source)
    (cancel : mapping.asSubst.comp opening = Subst.id)
    (function : Exp target) :
    ((arguments.rename mapping typed).apply function).subst opening =
      arguments.apply (function.subst opening) := by
  induction arguments generalizing target targetContext function with
  | nil => rfl
  | @var type tail argument argumentTyping rest ih =>
      simp only [Args.rename, Args.apply, eq_mpr_eq_cast]
      rw [apply_index_cast
        (tail.rename_subst_comm
          (Subst.openVarRenameComm argument mapping))]
      change ((rest.rename mapping typed).apply
          (.app function (argument.rename mapping))).subst opening =
        rest.apply (.app (function.subst opening) argument)
      rw [ih mapping typed opening cancel]
      simp only [Exp.subst]
      rw [Exp.rename_asSubst, Exp.subst_comp, cancel, Exp.subst_id]
  | @tvar tail argument rest ih =>
      simp only [Args.rename, Args.apply, eq_mpr_eq_cast]
      rw [apply_index_cast
        (tail.rename_subst_comm
          (Subst.openTVarRenameComm argument mapping))]
      change ((rest.rename mapping typed).apply
          (.tapp function (argument.rename mapping))).subst opening =
        rest.apply (.tapp (function.subst opening) argument)
      rw [ih mapping typed opening cancel]
      simp only [Exp.subst]
      rw [Ty.rename_asSubst, Ty.subst_comp, cancel, Ty.subst_id]
  | @cvar source result tail argument argumentTyping rest ih =>
      simp only [Args.rename, Args.apply, eq_mpr_eq_cast]
      rw [apply_index_cast
        (tail.rename_subst_comm
          (Subst.openCVarRenameComm argument mapping))]
      change ((rest.rename mapping typed).apply
          (.capp function (argument.rename mapping))).subst opening =
        rest.apply (.capp (function.subst opening) argument)
      rw [ih mapping typed opening cancel]
      simp only [Exp.subst]
      rw [Co.rename_asSubst, Co.subst_comp, cancel, Co.subst_id]

/-- Opening the answer binder and then the handler binder is equal to opening
the weakened handler first and the answer second. -/
theorem openTVar_liftVar_comp_openVar
    (answer : Ty sig) (handler : Exp sig) :
    ((Subst.openTVar answer).lift .var).comp
        (Subst.openVar handler) =
      (Subst.openVar (handler.weaken .tvar)).comp
        (Subst.openTVar answer) := by
  apply Subst.funext
  · intro index
    cases index with
    | here =>
        exact (handler.weaken_subst_cancel (Subst.openTVar answer)
          (Subst.weakenAsSubst_comp_openTVar answer)).symm
    | there index => cases index <;> rfl
  · intro index
    cases index with
    | there index =>
        cases index with
        | here =>
            exact answer.weaken_subst_cancel (Subst.openVar handler)
              (Subst.weakenAsSubst_comp_openVar handler)
        | there index => rfl
  · intro index
    cases index with
    | there index => cases index <;> rfl

/-- Applying a telescope lambda to a ready mixed argument spine performs
exactly the heterogeneous substitution represented by that spine. -/
theorem apply_lambda_steps (arguments : Args base tele)
    (argumentsValue : AllValues arguments) (body : Exp tele.scope) :
    Exp.Steps (arguments.apply (tele.lambda body))
      (body.subst arguments.substitution) := by
  induction arguments with
  | nil =>
      change Exp.Steps body (body.subst Subst.id)
      rw [Exp.subst_id]
      exact .refl
  | @var type tail argument argumentTyping rest ih =>
      rcases argumentsValue with ⟨argumentValue, restValue⟩
      apply Exp.Steps.trans
        (rest.apply_steps (Exp.Steps.single (.beta argumentValue)))
      rw [tail.lambda_subst]
      simpa only [Args.substitution, Exp.subst_comp] using
        ih restValue (body.subst (tail.liftSubst (Subst.openVar argument)))
  | @tvar tail argument rest ih =>
      apply Exp.Steps.trans
        (rest.apply_steps (Exp.Steps.single
          (Exp.Step.typeBeta : Exp.Step _ _)))
      rw [tail.lambda_subst]
      simpa only [Args.substitution, Exp.subst_comp] using
        ih argumentsValue
          (body.subst (tail.liftSubst (Subst.openTVar argument)))
  | @cvar source target tail argument argumentTyping rest ih =>
      apply Exp.Steps.trans
        (rest.apply_steps (Exp.Steps.single
          (Exp.Step.coercionBeta : Exp.Step _ _)))
      rw [tail.lambda_subst]
      simpa only [Args.substitution, Exp.subst_comp] using
        ih argumentsValue
          (body.subst (tail.liftSubst (Subst.openCVar argument)))

end Args

/-- Opening the two outer Church binders of a packed spine recovers ordinary
application of that spine to the supplied handler. -/
theorem Args.forExists_apply_open
    {sig : Sig} {base : Ctx sig} {tele : Telescope sig}
    (arguments : Args base tele) (answer : Ty sig) (handler : Exp sig) :
    ((arguments.forExists.apply (.var .here)).subst
        ((Subst.openTVar answer).lift .var)).subst
      (Subst.openVar handler) =
      arguments.apply handler := by
  let underAnswer := arguments.rename (Rename.weaken .tvar)
    (Rename.Typed.weaken base .tvar)
  let handlerUnderAnswer := handler.weaken .tvar
  have openHandler :
      ((underAnswer.rename (Rename.weaken .var)
          (Rename.Typed.weaken base.bindTVar
            (.var tele.existsHandler))).apply (.var .here)).subst
          (Subst.openVar handlerUnderAnswer) =
        underAnswer.apply handlerUnderAnswer := by
    simpa only [Exp.subst, Subst.openVar] using
      (underAnswer.apply_rename_subst_cancel
        (Rename.weaken .var)
        (Rename.Typed.weaken base.bindTVar (.var tele.existsHandler))
        (Subst.openVar handlerUnderAnswer)
        (Subst.weakenAsSubst_comp_openVar handlerUnderAnswer)
        (.var .here))
  have openAnswer :
      (underAnswer.apply handlerUnderAnswer).subst
          (Subst.openTVar answer) =
        arguments.apply handler := by
    dsimp only [underAnswer]
    rw [arguments.apply_rename_subst_cancel
      (Rename.weaken .tvar) (Rename.Typed.weaken base .tvar)
      (Subst.openTVar answer)
      (Subst.weakenAsSubst_comp_openTVar answer)]
    rw [handler.weaken_subst_cancel (Subst.openTVar answer)
      (Subst.weakenAsSubst_comp_openTVar answer)]
  unfold Args.forExists
  change
    (((underAnswer.rename (Rename.weaken .var)
      (Rename.Typed.weaken base.bindTVar
        (.var tele.existsHandler))).apply (.var .here)).subst
        ((Subst.openTVar answer).lift .var)).subst
      (Subst.openVar handler) = arguments.apply handler
  rw [Exp.subst_comp, openTVar_liftVar_comp_openVar,
    ← Exp.subst_comp, openHandler, openAnswer]

/-- Church introduction followed by elimination exposes the packed arguments
and runs the telescope consumer. -/
theorem unpack_pack_steps
    {sig : Sig} {base : Ctx sig} {tele : Telescope sig}
    (arguments : Args base tele) (argumentsValue : arguments.AllValues)
    (answer : Ty sig) (body : Exp tele.scope)
    (handlerValue : Exp.IsValue (tele.lambda body)) :
    Exp.Steps (tele.unpack (tele.pack arguments) answer body)
      (body.subst arguments.substitution) := by
  unfold unpack pack
  apply Exp.Steps.tail (.appFunction .typeBeta)
  apply Exp.Steps.tail (.beta handlerValue)
  rw [arguments.forExists_apply_open answer (tele.lambda body)]
  exact arguments.apply_lambda_steps argumentsValue body

/-- Every nonempty telescope abstracts its body with a target value
constructor, independently of the body's shape. -/
theorem lambda_isValue_of_ne_nil
    (tele : Telescope sig) (body : Exp tele.scope)
    (nonempty : tele ≠ .nil) :
    Exp.IsValue (tele.lambda body) := by
  cases tele with
  | nil => exact False.elim (nonempty rfl)
  | var => exact .abs
  | tvar => exact .tabs
  | cvar => exact .cabs

/-- Operational Church beta for any nonempty mixed telescope. -/
theorem unpack_pack_steps_of_ne_nil
    {sig : Sig} {base : Ctx sig} {tele : Telescope sig}
    (arguments : Args base tele) (argumentsValue : arguments.AllValues)
    (answer : Ty sig) (body : Exp tele.scope)
    (nonempty : tele ≠ .nil) :
    Exp.Steps (tele.unpack (tele.pack arguments) answer body)
      (body.subst arguments.substitution) :=
  unpack_pack_steps arguments argumentsValue answer body
    (tele.lambda_isValue_of_ne_nil body nonempty)

end Telescope
end SystemFCoExt
