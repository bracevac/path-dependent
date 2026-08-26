import SystemFCo.Syntax

/-!
Simultaneous substitution for the three namespaces of `SystemFCo`.

A `Subst source target` acts on one heterogeneous signature.  Its three
components record the syntactic class replacing variables of each kind; all
lifting and composition operations remain uniform in the binder kind.
-/

namespace SystemFCo

/-- A simultaneous substitution for term, type, and coercion variables. -/
structure Subst (source target : Sig) where
  var : BVar source .var -> Exp target
  tvar : BVar source .tvar -> Ty target
  cvar : BVar source .cvar -> Co target

namespace Subst

/-- Lift a substitution through one binder of an arbitrary kind. -/
def lift (subst : Subst source target) (kind : Kind) :
    Subst (source ,, kind) (target ,, kind) where
  var := fun x => by
    cases x with
    | here => exact .var .here
    | there x => exact (subst.var x).rename (Rename.weaken kind)
  tvar := fun x => by
    cases x with
    | here => exact .tvar .here
    | there x => exact (subst.tvar x).rename (Rename.weaken kind)
  cvar := fun x => by
    cases x with
    | here => exact .cvar .here
    | there x => exact (subst.cvar x).rename (Rename.weaken kind)

/-- Lift a substitution through an ordered telescope of newer binders. -/
def liftMany (subst : Subst source target) :
    (binders : Sig) -> Subst (binders ++ source) (binders ++ target)
  | [] => subst
  | kind :: binders => (subst.liftMany binders).lift kind

/-- The identity simultaneous substitution. -/
def id : Subst sig sig where
  var := .var
  tvar := .tvar
  cvar := .cvar

/-- Replace the newest term variable by an expression. -/
def openVar (argument : Exp sig) : Subst (sig ,, .var) sig where
  var := fun
    | .here => argument
    | .there x => .var x
  tvar := fun
    | .there x => .tvar x
  cvar := fun
    | .there x => .cvar x

/-- Replace the newest type variable by a type. -/
def openTVar (argument : Ty sig) : Subst (sig ,, .tvar) sig where
  var := fun
    | .there x => .var x
  tvar := fun
    | .here => argument
    | .there x => .tvar x
  cvar := fun
    | .there x => .cvar x

/-- Replace the newest coercion variable by a coercion. -/
def openCVar (argument : Co sig) : Subst (sig ,, .cvar) sig where
  var := fun
    | .there x => .var x
  tvar := fun
    | .there x => .tvar x
  cvar := fun
    | .here => argument
    | .there x => .cvar x

end Subst

/-! ## Action on syntax -/

def Ty.subst : Ty source -> Subst source target -> Ty target
  | .top, _ => .top
  | .tvar x, subst => subst.tvar x
  | .arrow parameter result, subst =>
      .arrow (parameter.subst subst) (result.subst subst)
  | .poly body, subst => .poly (body.subst (subst.lift .tvar))
  | .qual source result body, subst =>
      .qual (source.subst subst) (result.subst subst)
        (body.subst (subst.lift .cvar))

def Co.subst : Co source -> Subst source target -> Co target
  | .cvar x, subst => subst.cvar x
  | .refl ty, subst => .refl (ty.subst subst)
  | .trans first second, subst =>
      .trans (first.subst subst) (second.subst subst)
  | .top ty, subst => .top (ty.subst subst)
  | .arrow parameter result, subst =>
      .arrow (parameter.subst subst) (result.subst subst)
  | .poly body, subst => .poly (body.subst (subst.lift .tvar))
  | .qual argument result, subst =>
      .qual (argument.subst (subst.lift .cvar))
        (result.subst (subst.lift .cvar))

def Exp.subst : Exp source -> Subst source target -> Exp target
  | .var x, subst => subst.var x
  | .abs parameter body, subst =>
      .abs (parameter.subst subst) (body.subst (subst.lift .var))
  | .app function argument, subst =>
      .app (function.subst subst) (argument.subst subst)
  | .tabs body, subst => .tabs (body.subst (subst.lift .tvar))
  | .tapp function argument, subst =>
      .tapp (function.subst subst) (argument.subst subst)
  | .cabs source result body, subst =>
      .cabs (source.subst subst) (result.subst subst)
        (body.subst (subst.lift .cvar))
  | .capp function argument, subst =>
      .capp (function.subst subst) (argument.subst subst)
  | .cast expression coercion, subst =>
      .cast (expression.subst subst) (coercion.subst subst)

namespace Subst

/-- Function extensionality for simultaneous substitutions. -/
theorem funext {first second : Subst source target}
    (var : forall x, first.var x = second.var x)
    (tvar : forall x, first.tvar x = second.tvar x)
    (cvar : forall x, first.cvar x = second.cvar x) :
    first = second := by
  cases first
  cases second
  simp only [mk.injEq]
  constructor
  · funext x
    exact var x
  constructor
  · funext x
    exact tvar x
  · funext x
    exact cvar x

/-- Diagrammatic composition: apply `first`, then apply `second`. -/
def comp (first : Subst source middle) (second : Subst middle target) :
    Subst source target where
  var := fun x => (first.var x).subst second
  tvar := fun x => (first.tvar x).subst second
  cvar := fun x => (first.cvar x).subst second

@[simp] theorem lift_var_here (subst : Subst source target) :
    (subst.lift .var).var (.here : BVar (source ,, .var) .var) =
      .var .here := rfl

@[simp] theorem lift_var_there
    (subst : Subst source target) (x : BVar source .var) :
    (subst.lift kind).var (.there x) =
      (subst.var x).rename (Rename.weaken kind) := rfl

@[simp] theorem lift_tvar_here (subst : Subst source target) :
    (subst.lift .tvar).tvar (.here : BVar (source ,, .tvar) .tvar) =
      .tvar .here := rfl

@[simp] theorem lift_tvar_there
    (subst : Subst source target) (x : BVar source .tvar) :
    (subst.lift kind).tvar (.there x) =
      (subst.tvar x).rename (Rename.weaken kind) := rfl

@[simp] theorem lift_cvar_here (subst : Subst source target) :
    (subst.lift .cvar).cvar (.here : BVar (source ,, .cvar) .cvar) =
      .cvar .here := rfl

@[simp] theorem lift_cvar_there
    (subst : Subst source target) (x : BVar source .cvar) :
    (subst.lift kind).cvar (.there x) =
      (subst.cvar x).rename (Rename.weaken kind) := rfl

end Subst

/-! ## Renaming algebra -/

namespace Rename

theorem funext {first second : Rename source target}
    (var : forall {kind} (x : BVar source kind),
      first.var x = second.var x) : first = second := by
  cases first
  cases second
  congr
  funext kind x
  exact var x

/-- Lift a renaming through an ordered telescope of newer binders. -/
def liftMany (rename : Rename source target) :
    (binders : Sig) -> Rename (binders ++ source) (binders ++ target)
  | [] => rename
  | kind :: binders => (rename.liftMany binders).lift kind

@[simp] theorem lift_id :
    (Rename.id : Rename source source).lift kind = Rename.id := by
  apply Rename.funext
  intro other x
  cases x <;> rfl

theorem lift_comp
    (first : Rename source middle) (second : Rename middle target) :
    (first.comp second).lift kind =
      (first.lift kind).comp (second.lift kind) := by
  apply Rename.funext
  intro other x
  cases x <;> rfl

theorem weaken_lift_comm (rename : Rename source target) :
    (Rename.weaken kind).comp (rename.lift kind) =
      rename.comp (Rename.weaken kind) := by
  apply Rename.funext
  intro other x
  rfl

@[simp] theorem id_comp (rename : Rename source target) :
    Rename.id.comp rename = rename := by
  apply Rename.funext
  intro kind x
  rfl

@[simp] theorem comp_id (rename : Rename source target) :
    rename.comp Rename.id = rename := by
  apply Rename.funext
  intro kind x
  rfl

theorem comp_assoc
    (first : Rename source middle)
    (second : Rename middle middle') (third : Rename middle' target) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  apply Rename.funext
  intro kind x
  rfl

@[simp] theorem liftMany_id :
    (Rename.id : Rename source source).liftMany binders = Rename.id := by
  induction binders with
  | nil => rfl
  | cons kind binders ih =>
      simp only [Rename.liftMany, ih, lift_id]
      rfl

theorem liftMany_comp
    (first : Rename source middle) (second : Rename middle target) :
    (first.comp second).liftMany binders =
      (first.liftMany binders).comp (second.liftMany binders) := by
  induction binders with
  | nil => rfl
  | cons kind binders ih =>
      simp only [Rename.liftMany, ih, lift_comp]
      rfl

end Rename

@[simp] theorem Ty.rename_id (ty : Ty sig) : ty.rename Rename.id = ty := by
  induction ty with
  | top | tvar => rfl
  | arrow parameter result parameter_ih result_ih =>
      simp only [Ty.rename, parameter_ih, result_ih]
  | poly body body_ih =>
      simp only [Ty.rename, Rename.lift_id, body_ih]
  | qual source result body source_ih result_ih body_ih =>
      simp only [Ty.rename, Rename.lift_id, source_ih, result_ih, body_ih]

@[simp] theorem Co.rename_id (coercion : Co sig) :
    coercion.rename Rename.id = coercion := by
  induction coercion with
  | cvar => rfl
  | refl ty => simp only [Co.rename, Ty.rename_id]
  | trans first second first_ih second_ih =>
      simp only [Co.rename, first_ih, second_ih]
  | top ty => simp only [Co.rename, Ty.rename_id]
  | arrow parameter result parameter_ih result_ih =>
      simp only [Co.rename, parameter_ih, result_ih]
  | poly body body_ih =>
      simp only [Co.rename, Rename.lift_id, body_ih]
  | qual argument result argument_ih result_ih =>
      simp only [Co.rename, Rename.lift_id, argument_ih, result_ih]

@[simp] theorem Exp.rename_id (expression : Exp sig) :
    expression.rename Rename.id = expression := by
  induction expression with
  | var => rfl
  | abs parameter body body_ih =>
      simp only [Exp.rename, Ty.rename_id, Rename.lift_id, body_ih]
  | app function argument function_ih argument_ih =>
      simp only [Exp.rename, function_ih, argument_ih]
  | tabs body body_ih =>
      simp only [Exp.rename, Rename.lift_id, body_ih]
  | tapp function argument function_ih =>
      simp only [Exp.rename, function_ih, Ty.rename_id]
  | cabs source result body body_ih =>
      simp only [Exp.rename, Ty.rename_id, Rename.lift_id, body_ih]
  | capp function argument function_ih =>
      simp only [Exp.rename, function_ih, Co.rename_id]
  | cast expression coercion expression_ih =>
      simp only [Exp.rename, expression_ih, Co.rename_id]

theorem Ty.rename_comp (ty : Ty source)
    (first : Rename source middle) (second : Rename middle target) :
    (ty.rename first).rename second = ty.rename (first.comp second) := by
  induction ty generalizing middle target with
  | top | tvar => rfl
  | arrow parameter result parameter_ih result_ih =>
      simp only [Ty.rename, parameter_ih, result_ih]
  | poly body body_ih =>
      simp only [Ty.rename, body_ih, Rename.lift_comp]
  | qual source result body source_ih result_ih body_ih =>
      simp only [Ty.rename, source_ih, result_ih, body_ih,
        Rename.lift_comp]

theorem Co.rename_comp (coercion : Co source)
    (first : Rename source middle) (second : Rename middle target) :
    (coercion.rename first).rename second =
      coercion.rename (first.comp second) := by
  induction coercion generalizing middle target with
  | cvar => rfl
  | refl ty => simp only [Co.rename, Ty.rename_comp]
  | trans firstCo secondCo first_ih second_ih =>
      simp only [Co.rename, first_ih, second_ih]
  | top ty => simp only [Co.rename, Ty.rename_comp]
  | arrow parameter result parameter_ih result_ih =>
      simp only [Co.rename, parameter_ih, result_ih]
  | poly body body_ih =>
      simp only [Co.rename, body_ih, Rename.lift_comp]
  | qual argument result argument_ih result_ih =>
      simp only [Co.rename, argument_ih, result_ih, Rename.lift_comp]

theorem Exp.rename_comp (expression : Exp source)
    (first : Rename source middle) (second : Rename middle target) :
    (expression.rename first).rename second =
      expression.rename (first.comp second) := by
  induction expression generalizing middle target with
  | var => rfl
  | abs parameter body body_ih =>
      simp only [Exp.rename, Ty.rename_comp, body_ih, Rename.lift_comp]
  | app function argument function_ih argument_ih =>
      simp only [Exp.rename, function_ih, argument_ih]
  | tabs body body_ih =>
      simp only [Exp.rename, body_ih, Rename.lift_comp]
  | tapp function argument function_ih =>
      simp only [Exp.rename, function_ih, Ty.rename_comp]
  | cabs source result body body_ih =>
      simp only [Exp.rename, Ty.rename_comp, body_ih, Rename.lift_comp]
  | capp function argument function_ih =>
      simp only [Exp.rename, function_ih, Co.rename_comp]
  | cast expression coercion expression_ih =>
      simp only [Exp.rename, expression_ih, Co.rename_comp]

theorem Ty.weaken_rename_comm (ty : Ty source)
    (rename : Rename source target) :
    (ty.weaken kind).rename (rename.lift kind) =
      (ty.rename rename).weaken kind := by
  unfold Ty.weaken
  rw [Ty.rename_comp, Ty.rename_comp, Rename.weaken_lift_comm]

theorem Co.weaken_rename_comm (coercion : Co source)
    (rename : Rename source target) :
    (coercion.weaken kind).rename (rename.lift kind) =
      (coercion.rename rename).weaken kind := by
  unfold Co.weaken
  rw [Co.rename_comp, Co.rename_comp, Rename.weaken_lift_comm]

theorem Exp.weaken_rename_comm (expression : Exp source)
    (rename : Rename source target) :
    (expression.weaken kind).rename (rename.lift kind) =
      (expression.rename rename).weaken kind := by
  unfold Exp.weaken
  rw [Exp.rename_comp, Exp.rename_comp, Rename.weaken_lift_comm]

/-- Renaming commutes with weakening, in the orientation used by binders. -/
theorem Ty.rename_weaken_comm (ty : Ty source)
    (rename : Rename source target) :
    (ty.rename rename).weaken kind =
      (ty.weaken kind).rename (rename.lift kind) :=
  (ty.weaken_rename_comm rename).symm

theorem Co.rename_weaken_comm (coercion : Co source)
    (rename : Rename source target) :
    (coercion.rename rename).weaken kind =
      (coercion.weaken kind).rename (rename.lift kind) :=
  (coercion.weaken_rename_comm rename).symm

theorem Exp.rename_weaken_comm (expression : Exp source)
    (rename : Rename source target) :
    (expression.rename rename).weaken kind =
      (expression.weaken kind).rename (rename.lift kind) :=
  (expression.weaken_rename_comm rename).symm

/-! ## The generic renaming/substitution square -/

namespace Subst

/-- Pointwise compatibility of a substitution with source and target renaming. -/
structure RenameComm (subst : Subst source target)
    (sourceRename : Rename source source')
    (targetRename : Rename target target')
    (subst' : Subst source' target') : Prop where
  var : forall x,
    (subst.var x).rename targetRename = subst'.var (sourceRename.var x)
  tvar : forall x,
    (subst.tvar x).rename targetRename = subst'.tvar (sourceRename.var x)
  cvar : forall x,
    (subst.cvar x).rename targetRename = subst'.cvar (sourceRename.var x)

theorem RenameComm.lift
    (comm : RenameComm subst sourceRename targetRename subst')
    (kind : Kind) :
    RenameComm (subst.lift kind) (sourceRename.lift kind)
      (targetRename.lift kind) (subst'.lift kind) := by
  constructor
  · intro x
    cases x with
    | here => rfl
    | there x =>
        simp only [lift_var_there, Rename.lift_there]
        rw [Exp.rename_comp, Rename.weaken_lift_comm,
          ← Exp.rename_comp, comm.var]
  · intro x
    cases x with
    | here => rfl
    | there x =>
        simp only [lift_tvar_there, Rename.lift_there]
        rw [Ty.rename_comp, Rename.weaken_lift_comm,
          ← Ty.rename_comp, comm.tvar]
  · intro x
    cases x with
    | here => rfl
    | there x =>
        simp only [lift_cvar_there, Rename.lift_there]
        rw [Co.rename_comp, Rename.weaken_lift_comm,
          ← Co.rename_comp, comm.cvar]

theorem RenameComm.liftMany
    (comm : RenameComm subst sourceRename targetRename subst') :
    (binders : Sig) ->
    RenameComm (subst.liftMany binders)
      (sourceRename.liftMany binders) (targetRename.liftMany binders)
      (subst'.liftMany binders)
  | [] => comm
  | kind :: binders => (comm.liftMany binders).lift kind

end Subst

/-- The fundamental commuting-square theorem for types. -/
theorem Ty.rename_subst_comm (ty : Ty source)
    {source' target target' : Sig}
    {substitution : Subst source target}
    {sourceRename : Rename source source'}
    {targetRename : Rename target target'}
    {substitution' : Subst source' target'}
    (comm : Subst.RenameComm substitution sourceRename targetRename
      substitution') :
    (ty.subst substitution).rename targetRename =
      (ty.rename sourceRename).subst substitution' := by
  induction ty generalizing source' target target' with
  | top => rfl
  | tvar =>
      simp only [Ty.subst, Ty.rename]
      exact comm.tvar _
  | arrow parameter result parameter_ih result_ih =>
      simp only [Ty.subst, Ty.rename, parameter_ih comm, result_ih comm]
  | poly body body_ih =>
      simp only [Ty.subst, Ty.rename]
      exact congrArg Ty.poly (body_ih (comm.lift .tvar))
  | qual source result body source_ih result_ih body_ih =>
      simp only [Ty.subst, Ty.rename, source_ih comm, result_ih comm]
      exact congrArg (Ty.qual _ _) (body_ih (comm.lift .cvar))

/-- The fundamental commuting-square theorem for coercions. -/
theorem Co.rename_subst_comm (coercion : Co source)
    {source' target target' : Sig}
    {substitution : Subst source target}
    {sourceRename : Rename source source'}
    {targetRename : Rename target target'}
    {substitution' : Subst source' target'}
    (comm : Subst.RenameComm substitution sourceRename targetRename
      substitution') :
    (coercion.subst substitution).rename targetRename =
      (coercion.rename sourceRename).subst substitution' := by
  induction coercion generalizing source' target target' with
  | cvar =>
      simp only [Co.subst, Co.rename]
      exact comm.cvar _
  | refl ty => simp only [Co.subst, Co.rename, ty.rename_subst_comm comm]
  | trans first second first_ih second_ih =>
      simp only [Co.subst, Co.rename, first_ih comm, second_ih comm]
  | top ty => simp only [Co.subst, Co.rename, ty.rename_subst_comm comm]
  | arrow parameter result parameter_ih result_ih =>
      simp only [Co.subst, Co.rename, parameter_ih comm, result_ih comm]
  | poly body body_ih =>
      simp only [Co.subst, Co.rename]
      exact congrArg Co.poly (body_ih (comm.lift .tvar))
  | qual argument result argument_ih result_ih =>
      simp only [Co.subst, Co.rename]
      congr
      · exact argument_ih (comm.lift .cvar)
      · exact result_ih (comm.lift .cvar)

/-- The fundamental commuting-square theorem for expressions. -/
theorem Exp.rename_subst_comm (expression : Exp source)
    {source' target target' : Sig}
    {substitution : Subst source target}
    {sourceRename : Rename source source'}
    {targetRename : Rename target target'}
    {substitution' : Subst source' target'}
    (comm : Subst.RenameComm substitution sourceRename targetRename
      substitution') :
    (expression.subst substitution).rename targetRename =
      (expression.rename sourceRename).subst substitution' := by
  induction expression generalizing source' target target' with
  | var =>
      simp only [Exp.subst, Exp.rename]
      exact comm.var _
  | abs parameter body body_ih =>
      simp only [Exp.subst, Exp.rename, parameter.rename_subst_comm comm]
      exact congrArg (Exp.abs _) (body_ih (comm.lift .var))
  | app function argument function_ih argument_ih =>
      simp only [Exp.subst, Exp.rename, function_ih comm, argument_ih comm]
  | tabs body body_ih =>
      simp only [Exp.subst, Exp.rename]
      exact congrArg Exp.tabs (body_ih (comm.lift .tvar))
  | tapp function argument function_ih =>
      simp only [Exp.subst, Exp.rename, function_ih comm,
        argument.rename_subst_comm comm]
  | cabs source result body body_ih =>
      simp only [Exp.subst, Exp.rename, source.rename_subst_comm comm,
        result.rename_subst_comm comm]
      exact congrArg (Exp.cabs _ _) (body_ih (comm.lift .cvar))
  | capp function argument function_ih =>
      simp only [Exp.subst, Exp.rename, function_ih comm,
        argument.rename_subst_comm comm]
  | cast expression coercion expression_ih =>
      simp only [Exp.subst, Exp.rename, expression_ih comm,
        coercion.rename_subst_comm comm]

namespace Subst

/-- The commuting square induced by weakening a substitution. -/
theorem weakenComm (subst : Subst source target) (kind : Kind) :
    RenameComm subst (Rename.weaken kind) (Rename.weaken kind)
      (subst.lift kind) := by
  constructor <;> intro x <;> rfl

end Subst

/-! ## Weakening and substitution -/

/-- Weakening/substitution commutation below an arbitrary binder telescope. -/
theorem Ty.weaken_subst_comm
    {ty : Ty (binders ++ source)} (subst : Subst source target) :
    (ty.subst (subst.liftMany binders)).rename
        ((Rename.weaken kind).liftMany binders) =
      (ty.rename ((Rename.weaken kind).liftMany binders)).subst
        ((subst.lift kind).liftMany binders) :=
  ty.rename_subst_comm ((subst.weakenComm kind).liftMany binders)

theorem Co.weaken_subst_comm
    {coercion : Co (binders ++ source)} (subst : Subst source target) :
    (coercion.subst (subst.liftMany binders)).rename
        ((Rename.weaken kind).liftMany binders) =
      (coercion.rename ((Rename.weaken kind).liftMany binders)).subst
        ((subst.lift kind).liftMany binders) :=
  coercion.rename_subst_comm ((subst.weakenComm kind).liftMany binders)

theorem Exp.weaken_subst_comm
    {expression : Exp (binders ++ source)} (subst : Subst source target) :
    (expression.subst (subst.liftMany binders)).rename
        ((Rename.weaken kind).liftMany binders) =
      (expression.rename ((Rename.weaken kind).liftMany binders)).subst
        ((subst.lift kind).liftMany binders) :=
  expression.rename_subst_comm ((subst.weakenComm kind).liftMany binders)

/-- The usual one-binder weakening/substitution equation. -/
theorem Ty.weaken_subst_comm_base (ty : Ty source)
    (subst : Subst source target) :
    (ty.subst subst).weaken kind =
      (ty.weaken kind).subst (subst.lift kind) :=
  ty.rename_subst_comm (subst.weakenComm kind)

theorem Co.weaken_subst_comm_base (coercion : Co source)
    (subst : Subst source target) :
    (coercion.subst subst).weaken kind =
      (coercion.weaken kind).subst (subst.lift kind) :=
  coercion.rename_subst_comm (subst.weakenComm kind)

theorem Exp.weaken_subst_comm_base (expression : Exp source)
    (subst : Subst source target) :
    (expression.subst subst).weaken kind =
      (expression.weaken kind).subst (subst.lift kind) :=
  expression.rename_subst_comm (subst.weakenComm kind)

/-! ## Substitution algebra -/

namespace Subst

@[simp] theorem lift_id :
    (Subst.id : Subst source source).lift kind = Subst.id := by
  apply Subst.funext
  · intro x
    cases x <;> rfl
  · intro x
    cases x <;> rfl
  · intro x
    cases x <;> rfl

@[simp] theorem liftMany_id :
    (Subst.id : Subst source source).liftMany binders = Subst.id := by
  induction binders with
  | nil => rfl
  | cons kind binders ih =>
      simp only [Subst.liftMany, ih, lift_id]
      rfl

/-- Composition is preserved by lifting through one binder. -/
theorem comp_lift
    (first : Subst source middle) (second : Subst middle target) :
    (first.comp second).lift kind =
      (first.lift kind).comp (second.lift kind) := by
  apply Subst.funext
  · intro x
    cases x with
    | here => rfl
    | there x =>
        simp only [lift_var_there, comp]
        exact (first.var x).weaken_subst_comm_base second
  · intro x
    cases x with
    | here => rfl
    | there x =>
        simp only [lift_tvar_there, comp]
        exact (first.tvar x).weaken_subst_comm_base second
  · intro x
    cases x with
    | here => rfl
    | there x =>
        simp only [lift_cvar_there, comp]
        exact (first.cvar x).weaken_subst_comm_base second

/-- Composition is preserved by lifting through a binder telescope. -/
theorem comp_liftMany
    (first : Subst source middle) (second : Subst middle target) :
    (first.comp second).liftMany binders =
      (first.liftMany binders).comp (second.liftMany binders) := by
  induction binders with
  | nil => rfl
  | cons kind binders ih =>
      simp only [Subst.liftMany, ih, comp_lift]
      rfl

end Subst

@[simp] theorem Ty.subst_id (ty : Ty source) :
    ty.subst Subst.id = ty := by
  induction ty with
  | top | tvar => rfl
  | arrow parameter result parameter_ih result_ih =>
      simp only [Ty.subst, parameter_ih, result_ih]
  | poly body body_ih =>
      simp only [Ty.subst, Subst.lift_id, body_ih]
  | qual source result body source_ih result_ih body_ih =>
      simp only [Ty.subst, Subst.lift_id, source_ih, result_ih, body_ih]

@[simp] theorem Co.subst_id (coercion : Co source) :
    coercion.subst Subst.id = coercion := by
  induction coercion with
  | cvar => rfl
  | refl ty => simp only [Co.subst, Ty.subst_id]
  | trans first second first_ih second_ih =>
      simp only [Co.subst, first_ih, second_ih]
  | top ty => simp only [Co.subst, Ty.subst_id]
  | arrow parameter result parameter_ih result_ih =>
      simp only [Co.subst, parameter_ih, result_ih]
  | poly body body_ih =>
      simp only [Co.subst, Subst.lift_id, body_ih]
  | qual argument result argument_ih result_ih =>
      simp only [Co.subst, Subst.lift_id, argument_ih, result_ih]

@[simp] theorem Exp.subst_id (expression : Exp source) :
    expression.subst Subst.id = expression := by
  induction expression with
  | var => rfl
  | abs parameter body body_ih =>
      simp only [Exp.subst, Ty.subst_id, Subst.lift_id, body_ih]
  | app function argument function_ih argument_ih =>
      simp only [Exp.subst, function_ih, argument_ih]
  | tabs body body_ih =>
      simp only [Exp.subst, Subst.lift_id, body_ih]
  | tapp function argument function_ih =>
      simp only [Exp.subst, function_ih, Ty.subst_id]
  | cabs source result body body_ih =>
      simp only [Exp.subst, Ty.subst_id, Subst.lift_id, body_ih]
  | capp function argument function_ih =>
      simp only [Exp.subst, function_ih, Co.subst_id]
  | cast expression coercion expression_ih =>
      simp only [Exp.subst, expression_ih, Co.subst_id]

theorem Ty.subst_comp (ty : Ty source)
    (first : Subst source middle) (second : Subst middle target) :
    (ty.subst first).subst second = ty.subst (first.comp second) := by
  induction ty generalizing middle target with
  | top | tvar => rfl
  | arrow parameter result parameter_ih result_ih =>
      simp only [Ty.subst, parameter_ih, result_ih]
  | poly body body_ih =>
      simp only [Ty.subst, body_ih, Subst.comp_lift]
  | qual source result body source_ih result_ih body_ih =>
      simp only [Ty.subst, source_ih, result_ih, body_ih, Subst.comp_lift]

theorem Co.subst_comp (coercion : Co source)
    (first : Subst source middle) (second : Subst middle target) :
    (coercion.subst first).subst second =
      coercion.subst (first.comp second) := by
  induction coercion generalizing middle target with
  | cvar => rfl
  | refl ty => simp only [Co.subst, Ty.subst_comp]
  | trans firstCo secondCo first_ih second_ih =>
      simp only [Co.subst, first_ih, second_ih]
  | top ty => simp only [Co.subst, Ty.subst_comp]
  | arrow parameter result parameter_ih result_ih =>
      simp only [Co.subst, parameter_ih, result_ih]
  | poly body body_ih =>
      simp only [Co.subst, body_ih, Subst.comp_lift]
  | qual argument result argument_ih result_ih =>
      simp only [Co.subst, argument_ih, result_ih, Subst.comp_lift]

theorem Exp.subst_comp (expression : Exp source)
    (first : Subst source middle) (second : Subst middle target) :
    (expression.subst first).subst second =
      expression.subst (first.comp second) := by
  induction expression generalizing middle target with
  | var => rfl
  | abs parameter body body_ih =>
      simp only [Exp.subst, Ty.subst_comp, body_ih, Subst.comp_lift]
  | app function argument function_ih argument_ih =>
      simp only [Exp.subst, function_ih, argument_ih]
  | tabs body body_ih =>
      simp only [Exp.subst, body_ih, Subst.comp_lift]
  | tapp function argument function_ih =>
      simp only [Exp.subst, function_ih, Ty.subst_comp]
  | cabs source result body body_ih =>
      simp only [Exp.subst, Ty.subst_comp, body_ih, Subst.comp_lift]
  | capp function argument function_ih =>
      simp only [Exp.subst, function_ih, Co.subst_comp]
  | cast expression coercion expression_ih =>
      simp only [Exp.subst, expression_ih, Co.subst_comp]

namespace Subst

@[simp] theorem id_comp (subst : Subst source target) :
    Subst.id.comp subst = subst := by
  apply Subst.funext <;> intro x <;> rfl

@[simp] theorem comp_id (subst : Subst source target) :
    subst.comp Subst.id = subst := by
  apply Subst.funext
  · intro x
    exact Exp.subst_id _
  · intro x
    exact Ty.subst_id _
  · intro x
    exact Co.subst_id _

theorem comp_assoc
    (first : Subst source middle)
    (second : Subst middle middle') (third : Subst middle' target) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  apply Subst.funext
  · intro x
    exact Exp.subst_comp _ _ _
  · intro x
    exact Ty.subst_comp _ _ _
  · intro x
    exact Co.subst_comp _ _ _

end Subst

/-! ## Renamings as substitutions -/

namespace Rename

/-- Embed a sort-preserving renaming into simultaneous substitutions. -/
def asSubst (rename : Rename source target) : Subst source target where
  var := fun x => .var (rename.var x)
  tvar := fun x => .tvar (rename.var x)
  cvar := fun x => .cvar (rename.var x)

@[simp] theorem asSubst_lift (rename : Rename source target) :
    (rename.lift kind).asSubst = rename.asSubst.lift kind := by
  apply Subst.funext
  · intro x
    cases x <;> rfl
  · intro x
    cases x <;> rfl
  · intro x
    cases x <;> rfl

@[simp] theorem asSubst_liftMany (rename : Rename source target) :
    (rename.liftMany binders).asSubst =
      rename.asSubst.liftMany binders := by
  induction binders with
  | nil => rfl
  | cons kind binders ih =>
      simp only [Rename.liftMany, Subst.liftMany]
      exact (asSubst_lift (rename.liftMany binders)).trans
        (congrArg (fun substitution => substitution.lift kind) ih)

@[simp] theorem asSubst_id :
    (Rename.id : Rename source source).asSubst = Subst.id := rfl

theorem asSubst_comp
    (first : Rename source middle) (second : Rename middle target) :
    (first.comp second).asSubst = first.asSubst.comp second.asSubst := by
  apply Subst.funext <;> intro x <;> rfl

end Rename

@[simp] theorem Ty.subst_asSubst (ty : Ty source)
    (rename : Rename source target) :
    ty.subst rename.asSubst = ty.rename rename := by
  induction ty generalizing target with
  | top | tvar => rfl
  | arrow parameter result parameter_ih result_ih =>
      simp only [Ty.subst, Ty.rename, parameter_ih, result_ih]
  | poly body body_ih =>
      simp only [Ty.subst, Ty.rename, ← Rename.asSubst_lift, body_ih]
  | qual source result body source_ih result_ih body_ih =>
      simp only [Ty.subst, Ty.rename, source_ih, result_ih,
        ← Rename.asSubst_lift, body_ih]

@[simp] theorem Co.subst_asSubst (coercion : Co source)
    (rename : Rename source target) :
    coercion.subst rename.asSubst = coercion.rename rename := by
  induction coercion generalizing target with
  | cvar => rfl
  | refl ty => simp only [Co.subst, Co.rename, Ty.subst_asSubst]
  | trans first second first_ih second_ih =>
      simp only [Co.subst, Co.rename, first_ih, second_ih]
  | top ty => simp only [Co.subst, Co.rename, Ty.subst_asSubst]
  | arrow parameter result parameter_ih result_ih =>
      simp only [Co.subst, Co.rename, parameter_ih, result_ih]
  | poly body body_ih =>
      simp only [Co.subst, Co.rename, ← Rename.asSubst_lift, body_ih]
  | qual argument result argument_ih result_ih =>
      simp only [Co.subst, Co.rename, ← Rename.asSubst_lift,
        argument_ih, result_ih]

@[simp] theorem Exp.subst_asSubst (expression : Exp source)
    (rename : Rename source target) :
    expression.subst rename.asSubst = expression.rename rename := by
  induction expression generalizing target with
  | var => rfl
  | abs parameter body body_ih =>
      simp only [Exp.subst, Exp.rename, Ty.subst_asSubst,
        ← Rename.asSubst_lift, body_ih]
  | app function argument function_ih argument_ih =>
      simp only [Exp.subst, Exp.rename, function_ih, argument_ih]
  | tabs body body_ih =>
      simp only [Exp.subst, Exp.rename, ← Rename.asSubst_lift, body_ih]
  | tapp function argument function_ih =>
      simp only [Exp.subst, Exp.rename, function_ih, Ty.subst_asSubst]
  | cabs source result body body_ih =>
      simp only [Exp.subst, Exp.rename, Ty.subst_asSubst,
        ← Rename.asSubst_lift, body_ih]
  | capp function argument function_ih =>
      simp only [Exp.subst, Exp.rename, function_ih, Co.subst_asSubst]
  | cast expression coercion expression_ih =>
      simp only [Exp.subst, Exp.rename, expression_ih, Co.subst_asSubst]

theorem Ty.rename_asSubst (ty : Ty source)
    (rename : Rename source target) :
    ty.rename rename = ty.subst rename.asSubst :=
  (ty.subst_asSubst rename).symm

theorem Co.rename_asSubst (coercion : Co source)
    (rename : Rename source target) :
    coercion.rename rename = coercion.subst rename.asSubst :=
  (coercion.subst_asSubst rename).symm

theorem Exp.rename_asSubst (expression : Exp source)
    (rename : Rename source target) :
    expression.rename rename = expression.subst rename.asSubst :=
  (expression.subst_asSubst rename).symm

end SystemFCo
