import SystemFCoExt.Context
import SystemFCoExt.Substitution

/-!
# Typing for the explicit-coercion target

There is deliberately no subtyping judgment and no subsumption rule here.
Directed type conversion is represented by `Co` syntax, checked by
`Co.HasType`, and used by terms only through `Exp.cast`.

Both judgments live in `Type`: elaboration can recurse over source derivations
and construct the corresponding target evidence.
-/

namespace SystemFCoExt

/-! ## Context-preserving renaming -/

theorem Binding.weaken_rename_comm (binding : Binding source boundKind)
    (rename : Rename source target) (newKind : Kind) :
    (binding.weaken newKind).rename (rename.lift newKind) =
      (binding.rename rename).weaken newKind := by
  cases binding with
  | var ty =>
      change Binding.var ((ty.weaken newKind).rename (rename.lift newKind)) =
        Binding.var ((ty.rename rename).weaken newKind)
      rw [Ty.weaken_rename_comm]
  | tvar => rfl
  | cvar sourceTy targetTy =>
      change Binding.cvar
          ((sourceTy.weaken newKind).rename (rename.lift newKind))
          ((targetTy.weaken newKind).rename (rename.lift newKind)) =
        Binding.cvar ((sourceTy.rename rename).weaken newKind)
          ((targetTy.rename rename).weaken newKind)
      rw [Ty.weaken_rename_comm, Ty.weaken_rename_comm]

namespace Rename

/-- A renaming that preserves every declaration available to typing. -/
structure Typed (sourceContext : Ctx source) (targetContext : Ctx target)
    (rename : Rename source target) : Type where
  lookup : forall {kind : Kind} {index : BVar source kind}
      {binding : Binding source kind},
    sourceContext.Lookup index binding ->
    targetContext.Lookup (rename.var index) (binding.rename rename)

namespace Typed

/-- Lift a typed renaming through one corresponding declaration. -/
def lift {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {rename : Rename source target}
    (typed : Typed sourceContext targetContext rename)
    (binding : Binding source boundKind) :
    Typed (.extend sourceContext binding)
      (.extend targetContext (binding.rename rename))
      (rename.lift boundKind) where
  lookup := by
    intro kind index found lookup
    cases lookup with
    | here =>
        simpa only [Binding.weaken_rename_comm] using
          (Ctx.Lookup.here :
            Ctx.Lookup (.extend targetContext (binding.rename rename))
              (.here : BVar (target ,, boundKind) boundKind)
              ((binding.rename rename).weaken boundKind))
    | there lookup =>
        simpa only [Binding.weaken_rename_comm] using
          Ctx.Lookup.there (typed.lookup lookup)

/-- Include a context into an arbitrary one-declaration extension. -/
def weaken (context : Ctx sig) (binding : Binding sig kind) :
    Typed context (.extend context binding) (Rename.weaken kind) where
  lookup := fun lookup => Ctx.Lookup.there lookup

end Typed

end Rename

/-! ## Evidence opening and rebinding -/

/-- Replace the newest coercion variable without removing its binder. -/
def Subst.rebindCVar (argument : Co (sig ,, .cvar)) :
    Subst (sig ,, .cvar) (sig ,, .cvar) where
  var := fun
    | .there index => .var (.there index)
  tvar := fun
    | .there index => .tvar (.there index)
  cvar := fun
    | .here => argument
    | .there index => .cvar (.there index)

namespace Subst

theorem openVarRenameComm (argument : Exp source)
    (rename : Rename source target) :
    RenameComm (openVar argument) (rename.lift .var) rename
      (openVar (argument.rename rename)) := by
  constructor <;> intro index <;> cases index <;> rfl

theorem openTVarRenameComm (argument : Ty source)
    (rename : Rename source target) :
    RenameComm (openTVar argument) (rename.lift .tvar) rename
      (openTVar (argument.rename rename)) := by
  constructor <;> intro index <;> cases index <;> rfl

theorem openCVarRenameComm (argument : Co source)
    (rename : Rename source target) :
    RenameComm (openCVar argument) (rename.lift .cvar) rename
      (openCVar (argument.rename rename)) := by
  constructor <;> intro index <;> cases index <;> rfl

theorem rebindCVarRenameComm (argument : Co (source ,, .cvar))
    (rename : Rename source target) :
    RenameComm (rebindCVar argument) (rename.lift .cvar)
      (rename.lift .cvar)
      (rebindCVar (argument.rename (rename.lift .cvar))) := by
  constructor <;> intro index <;> cases index <;> rfl

end Subst

theorem Ty.openTVar_rename (body : Ty (source ,, .tvar))
    (argument : Ty source) (rename : Rename source target) :
    (body.subst (Subst.openTVar argument)).rename rename =
      (body.rename (rename.lift .tvar)).subst
        (Subst.openTVar (argument.rename rename)) :=
  body.rename_subst_comm (Subst.openTVarRenameComm argument rename)

theorem Ty.openCVar_rename (body : Ty (source ,, .cvar))
    (argument : Co source) (rename : Rename source target) :
    (body.subst (Subst.openCVar argument)).rename rename =
      (body.rename (rename.lift .cvar)).subst
        (Subst.openCVar (argument.rename rename)) :=
  body.rename_subst_comm (Subst.openCVarRenameComm argument rename)

theorem Ty.rebindCVar_rename (body : Ty (source ,, .cvar))
    (argument : Co (source ,, .cvar)) (rename : Rename source target) :
    (body.subst (Subst.rebindCVar argument)).rename (rename.lift .cvar) =
      (body.rename (rename.lift .cvar)).subst
        (Subst.rebindCVar (argument.rename (rename.lift .cvar))) :=
  body.rename_subst_comm (Subst.rebindCVarRenameComm argument rename)

/-! ## Coercion and expression typing -/

mutual

/-- A coercion is directed evidence from its source type to its target type. -/
inductive Co.HasType : {sig : Sig} -> Ctx sig -> Co sig -> Ty sig -> Ty sig -> Type where
| cvar :
    Ctx.CVarLookup context index source target ->
    Co.HasType context (.cvar index) source target
| refl :
    Co.HasType context (.refl ty) ty ty
| trans :
    Co.HasType context first source middle ->
    Co.HasType context second middle target ->
    Co.HasType context (.trans first second) source target
| top :
    Co.HasType context (.top source) source .top
| bottom :
    Co.HasType context (.bottom target) Ty.bottom target
| adapter :
    Exp.HasType (context.bindVar source) body (target.weaken .var) ->
    Co.HasType context (.adapter source body) source target
| arrow :
    Co.HasType context parameter targetParameter sourceParameter ->
    Co.HasType context result sourceResult targetResult ->
    Co.HasType context (.arrow parameter result)
      (.arrow sourceParameter sourceResult)
      (.arrow targetParameter targetResult)
| poly :
    Co.HasType context.bindTVar body source target ->
    Co.HasType context (.poly body) (.poly source) (.poly target)
| qual :
    Co.HasType (context.bindCVar targetEvidenceSource targetEvidenceTarget)
      argument
      (sourceEvidenceSource.weaken .cvar)
      (sourceEvidenceTarget.weaken .cvar) ->
    Co.HasType (context.bindCVar targetEvidenceSource targetEvidenceTarget)
      result
      (sourceBody.subst (Subst.rebindCVar argument))
      targetBody ->
    Co.HasType context (.qual argument result)
      (.qual sourceEvidenceSource sourceEvidenceTarget sourceBody)
      (.qual targetEvidenceSource targetEvidenceTarget targetBody)

/-- Typing for target terms. `cast` is the sole type-conversion rule. -/
inductive Exp.HasType : {sig : Sig} -> Ctx sig -> Exp sig -> Ty sig -> Type where
| var :
    Ctx.VarLookup context index ty ->
    Exp.HasType context (.var index) ty
| abs :
    Exp.HasType (context.bindVar parameter) body (result.weaken .var) ->
    Exp.HasType context (.abs parameter body) (.arrow parameter result)
| app :
    Exp.HasType context function (.arrow parameter result) ->
    Exp.HasType context argument parameter ->
    Exp.HasType context (.app function argument) result
| tabs :
    Exp.HasType context.bindTVar body result ->
    Exp.HasType context (.tabs body) (.poly result)
| tapp :
    Exp.HasType context function (.poly result) ->
    Exp.HasType context (.tapp function argument)
      (result.subst (Subst.openTVar argument))
| cabs :
    Exp.HasType (context.bindCVar source target) body result ->
    Exp.HasType context (.cabs source target body) (.qual source target result)
| capp :
    Exp.HasType context function (.qual source target result) ->
    Co.HasType context argument source target ->
    Exp.HasType context (.capp function argument)
      (result.subst (Subst.openCVar argument))
| cast :
    Exp.HasType context expression source ->
    Co.HasType context coercion source target ->
    Exp.HasType context (.cast expression coercion) target

end

/-! A shared structural measure for recursive typing transformations. -/

mutual

def Co.HasType.complexity :
    Co.HasType context coercion source target -> Nat
  | .cvar _ | .refl | .top | .bottom => 1
  | .trans first second | .arrow first second | .qual first second =>
      first.complexity + second.complexity + 1
  | .adapter body => body.complexity + 1
  | .poly body => body.complexity + 1

def Exp.HasType.complexity : Exp.HasType context expression ty -> Nat
  | .var _ => 1
  | .abs body | .tabs body | .cabs body => body.complexity + 1
  | .app function argument =>
      function.complexity + argument.complexity + 1
  | .tapp function => function.complexity + 1
  | .capp function argument | .cast function argument =>
      function.complexity + argument.complexity + 1

end

notation:50 context " |-c " coercion " : " source " => " target =>
  Co.HasType context coercion source target

notation:50 context " |-e " expression " : " ty =>
  Exp.HasType context expression ty

/-! ## Renaming the typing judgments -/

mutual

noncomputable def Co.HasType.rename
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target} {rename : Rename source target}
    {coercion : Co source} {sourceTy targetTy : Ty source} :
    (derivation : Co.HasType sourceContext coercion sourceTy targetTy) ->
    (typed : Rename.Typed sourceContext targetContext rename) ->
    Co.HasType targetContext (coercion.rename rename)
      (sourceTy.rename rename) (targetTy.rename rename)
  | .cvar lookup, typed => .cvar (typed.lookup lookup)
  | .refl, _ => .refl
  | .trans first second, typed => by
      exact .trans (Co.HasType.rename first typed)
        (Co.HasType.rename second typed)
  | .top, _ => .top
  | .bottom, _ => .bottom
  | .adapter bodyTyping, typed => by
      apply Co.HasType.adapter
      simpa only [Ty.weaken_rename_comm] using
        Exp.HasType.rename bodyTyping (typed.lift (.var _))
  | .arrow parameter result, typed => by
      exact .arrow (Co.HasType.rename parameter typed)
        (Co.HasType.rename result typed)
  | .poly body, typed => by
      exact .poly (Co.HasType.rename body (typed.lift .tvar))
  | .qual argumentTyping resultTyping, typed => by
      refine Co.HasType.qual ?_ ?_
      · simpa only [Ty.weaken_rename_comm] using
          Co.HasType.rename argumentTyping
            (typed.lift (.cvar _ _))
      · simpa only [Ty.rebindCVar_rename] using
          Co.HasType.rename resultTyping (typed.lift
            (.cvar _ _))
termination_by derivation _ => derivation.complexity
decreasing_by
  all_goals simp_wf
  all_goals simp [Co.HasType.complexity]
  all_goals omega

noncomputable def Exp.HasType.rename
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target} {rename : Rename source target}
    {expression : Exp source} {ty : Ty source} :
    (derivation : Exp.HasType sourceContext expression ty) ->
    (typed : Rename.Typed sourceContext targetContext rename) ->
    Exp.HasType targetContext (expression.rename rename)
      (ty.rename rename)
  | .var lookup, typed => .var (typed.lookup lookup)
  | .abs bodyTyping, typed => by
      apply Exp.HasType.abs
      simpa only [Ty.weaken_rename_comm] using
        Exp.HasType.rename bodyTyping (typed.lift (.var _))
  | .app functionTyping argumentTyping, typed => by
      exact .app (Exp.HasType.rename functionTyping typed)
        (Exp.HasType.rename argumentTyping typed)
  | .tabs bodyTyping, typed => by
      exact .tabs (Exp.HasType.rename bodyTyping (typed.lift .tvar))
  | .tapp functionTyping, typed => by
      simpa only [Ty.openTVar_rename] using
        Exp.HasType.tapp (Exp.HasType.rename functionTyping typed)
  | .cabs bodyTyping, typed => by
      exact .cabs
        (Exp.HasType.rename bodyTyping
          (typed.lift (.cvar _ _)))
  | .capp functionTyping argumentTyping, typed => by
      simpa only [Ty.openCVar_rename] using
        Exp.HasType.capp (Exp.HasType.rename functionTyping typed)
          (Co.HasType.rename argumentTyping typed)
  | .cast expressionTyping coercionTyping, typed => by
      exact .cast (Exp.HasType.rename expressionTyping typed)
        (Co.HasType.rename coercionTyping typed)
termination_by derivation _ => derivation.complexity
decreasing_by
  all_goals simp_wf
  all_goals simp [Exp.HasType.complexity]
  all_goals omega

end

/-! ## Typed substitution -/

def Binding.subst : Binding source kind -> Subst source target ->
    Binding target kind
| .var ty, substitution => .var (ty.subst substitution)
| .tvar, _ => .tvar
| .cvar sourceTy targetTy, substitution =>
    .cvar (sourceTy.subst substitution) (targetTy.subst substitution)

theorem Binding.weaken_subst_comm (binding : Binding source boundKind)
    (substitution : Subst source target) (newKind : Kind) :
    (binding.weaken newKind).subst (substitution.lift newKind) =
      (binding.subst substitution).weaken newKind := by
  cases binding with
  | var ty =>
      change Binding.var ((ty.weaken newKind).subst
          (substitution.lift newKind)) =
        Binding.var ((ty.subst substitution).weaken newKind)
      rw [← Ty.weaken_subst_comm_base]
  | tvar => rfl
  | cvar sourceTy targetTy =>
      change Binding.cvar
          ((sourceTy.weaken newKind).subst (substitution.lift newKind))
          ((targetTy.weaken newKind).subst (substitution.lift newKind)) =
        Binding.cvar ((sourceTy.subst substitution).weaken newKind)
          ((targetTy.subst substitution).weaken newKind)
      rw [← Ty.weaken_subst_comm_base, ← Ty.weaken_subst_comm_base]

namespace Co.HasType

noncomputable def weaken {sig : Sig} {context : Ctx sig}
    {coercion : Co sig} {sourceTy targetTy : Ty sig}
    (derivation : HasType context coercion sourceTy targetTy)
    (binding : Binding sig kind) :
    HasType (.extend context binding) (coercion.weaken kind)
      (sourceTy.weaken kind) (targetTy.weaken kind) :=
  derivation.rename (Rename.Typed.weaken context binding)

end Co.HasType

namespace Exp.HasType

noncomputable def weaken {sig : Sig} {context : Ctx sig}
    {expression : Exp sig} {ty : Ty sig}
    (derivation : HasType context expression ty)
    (binding : Binding sig kind) :
    HasType (.extend context binding) (expression.weaken kind)
      (ty.weaken kind) :=
  derivation.rename (Rename.Typed.weaken context binding)

end Exp.HasType

namespace Subst

def Realizes (targetContext : Ctx target) (substitution : Subst source target)
    (index : BVar source kind) : Binding source kind -> Type
| .var ty => Exp.HasType targetContext (substitution.var index)
    (ty.subst substitution)
| .tvar => PUnit
| .cvar sourceTy targetTy =>
    Co.HasType targetContext (substitution.cvar index)
      (sourceTy.subst substitution) (targetTy.subst substitution)

structure Typed (sourceContext : Ctx source) (targetContext : Ctx target)
    (substitution : Subst source target) : Type where
  lookup : forall {kind : Kind} {index : BVar source kind}
      {binding : Binding source kind},
    sourceContext.Lookup index binding ->
    Realizes targetContext substitution index binding

end Subst

namespace Subst.Typed

noncomputable def lift {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {substitution : Subst source target}
    (typed : Subst.Typed sourceContext targetContext substitution)
    (binding : Binding source boundKind) :
    Subst.Typed (.extend sourceContext binding)
      (.extend targetContext (binding.subst substitution))
      (substitution.lift boundKind) where
  lookup := by
    intro kind index found lookup
    cases lookup with
    | here =>
        cases binding with
        | var ty =>
            have typedHere :
                Exp.HasType
                  (.extend targetContext
                    ((Binding.var ty).subst substitution))
                  (.var (.here : BVar (target ,, .var) .var))
                  ((ty.subst substitution).weaken .var) :=
              .var Ctx.Lookup.here
            rw [Ty.weaken_subst_comm_base] at typedHere
            exact typedHere
        | tvar => exact PUnit.unit
        | cvar sourceTy targetTy =>
            have typedHere :
                Co.HasType
                  (.extend targetContext
                    ((Binding.cvar sourceTy targetTy).subst substitution))
                  (.cvar (.here : BVar (target ,, .cvar) .cvar))
                  ((sourceTy.subst substitution).weaken .cvar)
                  ((targetTy.subst substitution).weaken .cvar) :=
              .cvar Ctx.Lookup.here
            rw [Ty.weaken_subst_comm_base,
              Ty.weaken_subst_comm_base] at typedHere
            exact typedHere
    | @there sig kind newKind context index found newBinding lookup =>
        have realized := typed.lookup lookup
        cases found with
        | var ty =>
            have weakened :=
              Exp.HasType.weaken realized (binding.subst substitution)
            rw [Ty.weaken_subst_comm_base] at weakened
            simpa only [Realizes, Binding.weaken, Binding.rename,
              Subst.lift_var_there] using weakened
        | tvar => exact PUnit.unit
        | cvar sourceTy targetTy =>
            have weakened :=
              Co.HasType.weaken realized (binding.subst substitution)
            rw [Ty.weaken_subst_comm_base,
              Ty.weaken_subst_comm_base] at weakened
            simpa only [Realizes, Binding.weaken, Binding.rename,
              Subst.lift_cvar_there] using weakened

end Subst.Typed

namespace Subst

theorem weakenAsSubst_comp_rebindCVar
    (argument : Co (sig ,, .cvar)) :
    (Rename.weaken .cvar : Rename sig (sig ,, .cvar)).asSubst.comp
        (rebindCVar argument) =
      (Rename.weaken .cvar).asSubst := by
  apply Subst.funext <;> intro index <;> rfl

end Subst

theorem Ty.weaken_subst_rebindCVar (ty : Ty sig)
    (argument : Co (sig ,, .cvar)) :
    (ty.weaken .cvar).subst (Subst.rebindCVar argument) =
      ty.weaken .cvar := by
  unfold Ty.weaken
  calc
    (ty.rename (Rename.weaken .cvar)).subst
        (Subst.rebindCVar argument) =
      (ty.subst (Rename.weaken .cvar).asSubst).subst
        (Subst.rebindCVar argument) := by rw [Ty.subst_asSubst]
    _ = ty.subst ((Rename.weaken .cvar).asSubst.comp
        (Subst.rebindCVar argument)) := Ty.subst_comp _ _ _
    _ = ty.subst (Rename.weaken .cvar).asSubst := by
      rw [Subst.weakenAsSubst_comp_rebindCVar]
    _ = ty.rename (Rename.weaken .cvar) := Ty.subst_asSubst _ _

theorem Co.weaken_subst_rebindCVar (coercion : Co sig)
    (argument : Co (sig ,, .cvar)) :
    (coercion.weaken .cvar).subst (Subst.rebindCVar argument) =
      coercion.weaken .cvar := by
  unfold Co.weaken
  calc
    (coercion.rename (Rename.weaken .cvar)).subst
        (Subst.rebindCVar argument) =
      (coercion.subst (Rename.weaken .cvar).asSubst).subst
        (Subst.rebindCVar argument) := by rw [Co.subst_asSubst]
    _ = coercion.subst ((Rename.weaken .cvar).asSubst.comp
        (Subst.rebindCVar argument)) := Co.subst_comp _ _ _
    _ = coercion.subst (Rename.weaken .cvar).asSubst := by
      rw [Subst.weakenAsSubst_comp_rebindCVar]
    _ = coercion.rename (Rename.weaken .cvar) := Co.subst_asSubst _ _

theorem Exp.weaken_subst_rebindCVar (expression : Exp sig)
    (argument : Co (sig ,, .cvar)) :
    (expression.weaken .cvar).subst (Subst.rebindCVar argument) =
      expression.weaken .cvar := by
  unfold Exp.weaken
  calc
    (expression.rename (Rename.weaken .cvar)).subst
        (Subst.rebindCVar argument) =
      (expression.subst (Rename.weaken .cvar).asSubst).subst
        (Subst.rebindCVar argument) := by rw [Exp.subst_asSubst]
    _ = expression.subst ((Rename.weaken .cvar).asSubst.comp
        (Subst.rebindCVar argument)) := Exp.subst_comp _ _ _
    _ = expression.subst (Rename.weaken .cvar).asSubst := by
      rw [Subst.weakenAsSubst_comp_rebindCVar]
    _ = expression.rename (Rename.weaken .cvar) := Exp.subst_asSubst _ _

namespace Subst

theorem rebindCVar_comp_lift (argument : Co (source ,, .cvar))
    (substitution : Subst source target) :
    (rebindCVar argument).comp (substitution.lift .cvar) =
      (substitution.lift .cvar).comp
        (rebindCVar (argument.subst (substitution.lift .cvar))) := by
  apply Subst.funext
  · intro index
    cases index with
    | there index =>
        exact (substitution.var index).weaken_subst_rebindCVar _ |>.symm
  · intro index
    cases index with
    | there index =>
        exact (substitution.tvar index).weaken_subst_rebindCVar _ |>.symm
  · intro index
    cases index with
    | here => rfl
    | there index =>
        exact (substitution.cvar index).weaken_subst_rebindCVar _ |>.symm

end Subst

theorem Ty.rebindCVar_subst (body : Ty (source ,, .cvar))
    (argument : Co (source ,, .cvar))
    (substitution : Subst source target) :
    (body.subst (Subst.rebindCVar argument)).subst
        (substitution.lift .cvar) =
      (body.subst (substitution.lift .cvar)).subst
        (Subst.rebindCVar
          (argument.subst (substitution.lift .cvar))) := by
  rw [Ty.subst_comp, Ty.subst_comp, Subst.rebindCVar_comp_lift]

namespace Subst

theorem weakenAsSubst_comp_openVar (argument : Exp sig) :
    (Rename.weaken .var : Rename sig (sig ,, .var)).asSubst.comp
        (openVar argument) = Subst.id := by
  apply Subst.funext <;> intro index <;> rfl

theorem weakenAsSubst_comp_openTVar (argument : Ty sig) :
    (Rename.weaken .tvar : Rename sig (sig ,, .tvar)).asSubst.comp
        (openTVar argument) = Subst.id := by
  apply Subst.funext <;> intro index <;> rfl

theorem weakenAsSubst_comp_openCVar (argument : Co sig) :
    (Rename.weaken .cvar : Rename sig (sig ,, .cvar)).asSubst.comp
        (openCVar argument) = Subst.id := by
  apply Subst.funext <;> intro index <;> rfl

end Subst

theorem Ty.weaken_subst_cancel (ty : Ty sig)
    (opening : Subst (sig ,, kind) sig)
    (cancel :
      (Rename.weaken kind : Rename sig (sig ,, kind)).asSubst.comp
        opening = Subst.id) :
    (ty.weaken kind).subst opening = ty := by
  unfold Ty.weaken
  calc
    (ty.rename (Rename.weaken kind)).subst opening =
      (ty.subst (Rename.weaken kind).asSubst).subst opening := by
        rw [Ty.subst_asSubst]
    _ = ty.subst ((Rename.weaken kind).asSubst.comp opening) :=
      Ty.subst_comp _ _ _
    _ = ty.subst Subst.id := by rw [cancel]
    _ = ty := Ty.subst_id _

theorem Co.weaken_subst_cancel (coercion : Co sig)
    (opening : Subst (sig ,, kind) sig)
    (cancel :
      (Rename.weaken kind : Rename sig (sig ,, kind)).asSubst.comp
        opening = Subst.id) :
    (coercion.weaken kind).subst opening = coercion := by
  unfold Co.weaken
  calc
    (coercion.rename (Rename.weaken kind)).subst opening =
      (coercion.subst (Rename.weaken kind).asSubst).subst opening := by
        rw [Co.subst_asSubst]
    _ = coercion.subst ((Rename.weaken kind).asSubst.comp opening) :=
      Co.subst_comp _ _ _
    _ = coercion.subst Subst.id := by rw [cancel]
    _ = coercion := Co.subst_id _

theorem Exp.weaken_subst_cancel (expression : Exp sig)
    (opening : Subst (sig ,, kind) sig)
    (cancel :
      (Rename.weaken kind : Rename sig (sig ,, kind)).asSubst.comp
        opening = Subst.id) :
    (expression.weaken kind).subst opening = expression := by
  unfold Exp.weaken
  calc
    (expression.rename (Rename.weaken kind)).subst opening =
      (expression.subst (Rename.weaken kind).asSubst).subst opening := by
        rw [Exp.subst_asSubst]
    _ = expression.subst ((Rename.weaken kind).asSubst.comp opening) :=
      Exp.subst_comp _ _ _
    _ = expression.subst Subst.id := by rw [cancel]
    _ = expression := Exp.subst_id _

namespace Subst

theorem openVar_comp (argument : Exp source)
    (substitution : Subst source target) :
    (openVar argument).comp substitution =
      (substitution.lift .var).comp
        (openVar (argument.subst substitution)) := by
  apply Subst.funext
  · intro index
    cases index with
    | here => rfl
    | there index =>
        exact (substitution.var index).weaken_subst_cancel _
          (weakenAsSubst_comp_openVar _) |>.symm
  · intro index
    cases index with
    | there index =>
        exact (substitution.tvar index).weaken_subst_cancel _
          (weakenAsSubst_comp_openVar _) |>.symm
  · intro index
    cases index with
    | there index =>
        exact (substitution.cvar index).weaken_subst_cancel _
          (weakenAsSubst_comp_openVar _) |>.symm

theorem openTVar_comp (argument : Ty source)
    (substitution : Subst source target) :
    (openTVar argument).comp substitution =
      (substitution.lift .tvar).comp
        (openTVar (argument.subst substitution)) := by
  apply Subst.funext
  · intro index
    cases index with
    | there index =>
        exact (substitution.var index).weaken_subst_cancel _
          (weakenAsSubst_comp_openTVar _) |>.symm
  · intro index
    cases index with
    | here => rfl
    | there index =>
        exact (substitution.tvar index).weaken_subst_cancel _
          (weakenAsSubst_comp_openTVar _) |>.symm
  · intro index
    cases index with
    | there index =>
        exact (substitution.cvar index).weaken_subst_cancel _
          (weakenAsSubst_comp_openTVar _) |>.symm

theorem openCVar_comp (argument : Co source)
    (substitution : Subst source target) :
    (openCVar argument).comp substitution =
      (substitution.lift .cvar).comp
        (openCVar (argument.subst substitution)) := by
  apply Subst.funext
  · intro index
    cases index with
    | there index =>
        exact (substitution.var index).weaken_subst_cancel _
          (weakenAsSubst_comp_openCVar _) |>.symm
  · intro index
    cases index with
    | there index =>
        exact (substitution.tvar index).weaken_subst_cancel _
          (weakenAsSubst_comp_openCVar _) |>.symm
  · intro index
    cases index with
    | here => rfl
    | there index =>
        exact (substitution.cvar index).weaken_subst_cancel _
          (weakenAsSubst_comp_openCVar _) |>.symm

end Subst

theorem Ty.openTVar_subst (body : Ty (source ,, .tvar))
    (argument : Ty source) (substitution : Subst source target) :
    (body.subst (Subst.openTVar argument)).subst substitution =
      (body.subst (substitution.lift .tvar)).subst
        (Subst.openTVar (argument.subst substitution)) := by
  rw [Ty.subst_comp, Ty.subst_comp, Subst.openTVar_comp]

theorem Ty.openCVar_subst (body : Ty (source ,, .cvar))
    (argument : Co source) (substitution : Subst source target) :
    (body.subst (Subst.openCVar argument)).subst substitution =
      (body.subst (substitution.lift .cvar)).subst
        (Subst.openCVar (argument.subst substitution)) := by
  rw [Ty.subst_comp, Ty.subst_comp, Subst.openCVar_comp]

mutual

/-- The coercion typing judgment is preserved by any typed substitution. -/
noncomputable def Co.HasType.subst {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {substitution : Subst source target}
    {coercion : Co source} {sourceTy targetTy : Ty source} :
    (derivation : Co.HasType sourceContext coercion sourceTy targetTy) ->
    (typed : Subst.Typed sourceContext targetContext substitution) ->
    Co.HasType targetContext (coercion.subst substitution)
      (sourceTy.subst substitution) (targetTy.subst substitution)
  | .cvar lookup, typed => typed.lookup lookup
  | .refl, _ => .refl
  | .trans first second, typed => by
      exact .trans (Co.HasType.subst first typed)
        (Co.HasType.subst second typed)
  | .top, _ => .top
  | .bottom, _ => .bottom
  | .adapter bodyTyping, typed => by
      apply Co.HasType.adapter
      simpa only [Ty.weaken_subst_comm_base] using
        Exp.HasType.subst bodyTyping (typed.lift (.var _))
  | .arrow parameter result, typed => by
      exact .arrow (Co.HasType.subst parameter typed)
        (Co.HasType.subst result typed)
  | .poly body, typed => by
      exact .poly (Co.HasType.subst body (typed.lift .tvar))
  | .qual argumentTyping resultTyping, typed => by
      refine Co.HasType.qual ?_ ?_
      · simpa only [Ty.weaken_subst_comm_base] using
          Co.HasType.subst argumentTyping (typed.lift (.cvar _ _))
      · simpa only [Ty.rebindCVar_subst] using
          Co.HasType.subst resultTyping (typed.lift (.cvar _ _))
termination_by derivation _ => derivation.complexity
decreasing_by
  all_goals simp_wf
  all_goals simp [Co.HasType.complexity]
  all_goals omega

/-- The expression typing judgment is preserved by any typed substitution. -/
noncomputable def Exp.HasType.subst {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {substitution : Subst source target}
    {expression : Exp source} {ty : Ty source} :
    (derivation : Exp.HasType sourceContext expression ty) ->
    (typed : Subst.Typed sourceContext targetContext substitution) ->
    Exp.HasType targetContext (expression.subst substitution)
      (ty.subst substitution)
  | .var lookup, typed => typed.lookup lookup
  | .abs bodyTyping, typed => by
      apply Exp.HasType.abs
      simpa only [Ty.weaken_subst_comm_base] using
        Exp.HasType.subst bodyTyping (typed.lift (.var _))
  | .app functionTyping argumentTyping, typed => by
      exact .app (Exp.HasType.subst functionTyping typed)
        (Exp.HasType.subst argumentTyping typed)
  | .tabs bodyTyping, typed => by
      exact .tabs (Exp.HasType.subst bodyTyping (typed.lift .tvar))
  | .tapp functionTyping, typed => by
      simpa only [Ty.openTVar_subst] using
        Exp.HasType.tapp (Exp.HasType.subst functionTyping typed)
  | .cabs bodyTyping, typed => by
      exact .cabs
        (Exp.HasType.subst bodyTyping (typed.lift (.cvar _ _)))
  | .capp functionTyping argumentTyping, typed => by
      simpa only [Ty.openCVar_subst] using
        Exp.HasType.capp (Exp.HasType.subst functionTyping typed)
          (Co.HasType.subst argumentTyping typed)
  | .cast expressionTyping coercionTyping, typed => by
      exact .cast (Exp.HasType.subst expressionTyping typed)
        (Co.HasType.subst coercionTyping typed)
termination_by derivation _ => derivation.complexity
decreasing_by
  all_goals simp_wf
  all_goals simp [Exp.HasType.complexity]
  all_goals omega

end

namespace Ty

theorem rename_weaken_subst_cancel (ty : Ty sig)
    (opening : Subst (sig ,, kind) sig)
    (cancel :
      (Rename.weaken kind : Rename sig (sig ,, kind)).asSubst.comp
        opening = Subst.id) :
    (ty.rename (Rename.weaken kind)).subst opening = ty := by
  simpa only [Ty.weaken] using ty.weaken_subst_cancel opening cancel

end Ty

namespace Subst.Typed

noncomputable def openVar {sig : Sig} {context : Ctx sig}
    {argument : Exp sig} {ty : Ty sig}
    (argumentTyping : Exp.HasType context argument ty) :
    Subst.Typed (context.bindVar ty) context (Subst.openVar argument) where
  lookup := by
    intro kind index found lookup
    cases lookup with
    | here =>
        change Exp.HasType context argument
          ((ty.rename (Rename.weaken .var)).subst
            (Subst.openVar argument))
        rw [Ty.rename_weaken_subst_cancel ty _
          (Subst.weakenAsSubst_comp_openVar argument)]
        exact argumentTyping
    | @there sig kind newKind context index found newBinding lookup =>
        cases found with
        | var foundTy =>
            change Exp.HasType context (.var index)
              ((foundTy.rename (Rename.weaken .var)).subst
                (Subst.openVar argument))
            rw [Ty.rename_weaken_subst_cancel foundTy _
              (Subst.weakenAsSubst_comp_openVar argument)]
            exact .var lookup
        | tvar => exact PUnit.unit
        | cvar sourceTy targetTy =>
            change Co.HasType context (.cvar index)
              ((sourceTy.rename (Rename.weaken .var)).subst
                (Subst.openVar argument))
              ((targetTy.rename (Rename.weaken .var)).subst
                (Subst.openVar argument))
            rw [Ty.rename_weaken_subst_cancel sourceTy _
                (Subst.weakenAsSubst_comp_openVar argument),
              Ty.rename_weaken_subst_cancel targetTy _
                (Subst.weakenAsSubst_comp_openVar argument)]
            exact .cvar lookup

end Subst.Typed

namespace Subst.Typed

noncomputable def openTVar (context : Ctx sig) (argument : Ty sig) :
    Subst.Typed context.bindTVar context (Subst.openTVar argument) where
  lookup := by
    intro kind index found lookup
    cases lookup with
    | here => exact PUnit.unit
    | @there sig kind newKind context index found newBinding lookup =>
        cases found with
        | var foundTy =>
            change Exp.HasType context (.var index)
              ((foundTy.rename (Rename.weaken .tvar)).subst
                (Subst.openTVar argument))
            rw [Ty.rename_weaken_subst_cancel foundTy _
              (Subst.weakenAsSubst_comp_openTVar argument)]
            exact .var lookup
        | tvar => exact PUnit.unit
        | cvar sourceTy targetTy =>
            change Co.HasType context (.cvar index)
              ((sourceTy.rename (Rename.weaken .tvar)).subst
                (Subst.openTVar argument))
              ((targetTy.rename (Rename.weaken .tvar)).subst
                (Subst.openTVar argument))
            rw [Ty.rename_weaken_subst_cancel sourceTy _
                (Subst.weakenAsSubst_comp_openTVar argument),
              Ty.rename_weaken_subst_cancel targetTy _
                (Subst.weakenAsSubst_comp_openTVar argument)]
            exact .cvar lookup

end Subst.Typed

namespace Subst.Typed

noncomputable def openCVar {sig : Sig} {context : Ctx sig}
    {argument : Co sig} {sourceTy targetTy : Ty sig}
    (argumentTyping : Co.HasType context argument sourceTy targetTy) :
    Subst.Typed (context.bindCVar sourceTy targetTy) context
      (Subst.openCVar argument) where
  lookup := by
    intro kind index found lookup
    cases lookup with
    | here =>
        change Co.HasType context argument
          ((sourceTy.rename (Rename.weaken .cvar)).subst
            (Subst.openCVar argument))
          ((targetTy.rename (Rename.weaken .cvar)).subst
            (Subst.openCVar argument))
        rw [Ty.rename_weaken_subst_cancel sourceTy _
            (Subst.weakenAsSubst_comp_openCVar argument),
          Ty.rename_weaken_subst_cancel targetTy _
            (Subst.weakenAsSubst_comp_openCVar argument)]
        exact argumentTyping
    | @there sig kind newKind context index found newBinding lookup =>
        cases found with
        | var foundTy =>
            change Exp.HasType context (.var index)
              ((foundTy.rename (Rename.weaken .cvar)).subst
                (Subst.openCVar argument))
            rw [Ty.rename_weaken_subst_cancel foundTy _
              (Subst.weakenAsSubst_comp_openCVar argument)]
            exact .var lookup
        | tvar => exact PUnit.unit
        | cvar foundSource foundTarget =>
            change Co.HasType context (.cvar index)
              ((foundSource.rename (Rename.weaken .cvar)).subst
                (Subst.openCVar argument))
              ((foundTarget.rename (Rename.weaken .cvar)).subst
                (Subst.openCVar argument))
            rw [Ty.rename_weaken_subst_cancel foundSource _
                (Subst.weakenAsSubst_comp_openCVar argument),
              Ty.rename_weaken_subst_cancel foundTarget _
                (Subst.weakenAsSubst_comp_openCVar argument)]
            exact .cvar lookup

end Subst.Typed

namespace Co.HasType

noncomputable def openTVar {sig : Sig} {context : Ctx sig}
    {coercion : Co (sig ,, .tvar)}
    {sourceTy targetTy : Ty (sig ,, .tvar)}
    (derivation : HasType context.bindTVar coercion sourceTy targetTy)
    (argument : Ty sig) :
    HasType context (coercion.subst (Subst.openTVar argument))
      (sourceTy.subst (Subst.openTVar argument))
      (targetTy.subst (Subst.openTVar argument)) :=
  derivation.subst (Subst.Typed.openTVar context argument)

noncomputable def openCVar {sig : Sig} {context : Ctx sig}
    {evidenceSource evidenceTarget : Ty sig}
    {coercion : Co (sig ,, .cvar)}
    {sourceTy targetTy : Ty (sig ,, .cvar)}
    (derivation : HasType (context.bindCVar evidenceSource evidenceTarget)
      coercion sourceTy targetTy)
    {argument : Co sig}
    (argumentTyping : HasType context argument evidenceSource evidenceTarget) :
    HasType context (coercion.subst (Subst.openCVar argument))
      (sourceTy.subst (Subst.openCVar argument))
      (targetTy.subst (Subst.openCVar argument)) :=
  derivation.subst (Subst.Typed.openCVar argumentTyping)

end Co.HasType

namespace Exp.HasType

noncomputable def openVar {sig : Sig} {context : Ctx sig}
    {parameter : Ty sig} {body : Exp (sig ,, .var)}
    {result : Ty (sig ,, .var)}
    (derivation : HasType (context.bindVar parameter) body result)
    {argument : Exp sig}
    (argumentTyping : HasType context argument parameter) :
    HasType context (body.subst (Subst.openVar argument))
      (result.subst (Subst.openVar argument)) :=
  derivation.subst (Subst.Typed.openVar argumentTyping)

noncomputable def openTVar {sig : Sig} {context : Ctx sig}
    {body : Exp (sig ,, .tvar)} {result : Ty (sig ,, .tvar)}
    (derivation : HasType context.bindTVar body result)
    (argument : Ty sig) :
    HasType context (body.subst (Subst.openTVar argument))
      (result.subst (Subst.openTVar argument)) :=
  derivation.subst (Subst.Typed.openTVar context argument)

noncomputable def openCVar {sig : Sig} {context : Ctx sig}
    {evidenceSource evidenceTarget : Ty sig}
    {body : Exp (sig ,, .cvar)} {result : Ty (sig ,, .cvar)}
    (derivation : HasType (context.bindCVar evidenceSource evidenceTarget)
      body result)
    {argument : Co sig}
    (argumentTyping : Co.HasType context argument
      evidenceSource evidenceTarget) :
    HasType context (body.subst (Subst.openCVar argument))
      (result.subst (Subst.openCVar argument)) :=
  derivation.subst (Subst.Typed.openCVar argumentTyping)

end Exp.HasType

namespace Subst

theorem rebindCVar_comp_openCVar
    (evidence : Co (sig ,, .cvar)) (argument : Co sig) :
    (rebindCVar evidence).comp (openCVar argument) =
      openCVar (evidence.subst (openCVar argument)) := by
  apply Subst.funext
  · intro index
    cases index <;> rfl
  · intro index
    cases index <;> rfl
  · intro index
    cases index <;> rfl

end Subst

theorem Ty.rebindCVar_openCVar (body : Ty (sig ,, .cvar))
    (evidence : Co (sig ,, .cvar)) (argument : Co sig) :
    (body.subst (Subst.rebindCVar evidence)).subst
        (Subst.openCVar argument) =
      body.subst
        (Subst.openCVar
          (evidence.subst (Subst.openCVar argument))) := by
  rw [Ty.subst_comp, Subst.rebindCVar_comp_openCVar]

end SystemFCoExt
