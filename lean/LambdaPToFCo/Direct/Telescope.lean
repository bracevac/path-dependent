import SystemFCo.ReductionSubstitution
import SystemFCo.Operational

/-!
# Mixed Church telescopes over unchanged SystemFCo

This is the target-generic mixed-telescope library used by the direct
compiler track.  It is a mechanical namespace port of the existing telescope
development: all syntax and typing judgments remain the original
`SystemFCo` definitions.  The local `TyOps` and `TypedSubst` namespaces hold
the two helper families that the original port attached to its forked target
namespace.

The telescope supports term, type, and coercion fields generically.  Direct
packages use only term and type fields; computational dictionary evidence is
therefore ordinary function-valued `Exp`, never a qualified type or coercion
variable.
-/

namespace LambdaPToFCo.Direct

open SystemFCo

namespace TyOps

/-- Target types inspect only type-variable indices. -/
private theorem subst_eq_of_tvar
    (type : Ty source) (first second : Subst source target)
    (equal : forall index, first.tvar index = second.tvar index) :
    type.subst first = type.subst second := by
  induction type generalizing target with
  | top => rfl
  | tvar index => exact equal index
  | arrow parameter result parameterIH resultIH =>
      simp only [Ty.subst]
      congr 1
      · exact parameterIH first second equal
      · exact resultIH first second equal
  | poly body bodyIH =>
      simp only [Ty.subst]
      congr 1
      apply bodyIH
      intro index
      cases index with
      | here => rfl
      | there index =>
          exact congrArg (fun type => type.weaken .tvar) (equal index)
  | qual source target body sourceIH targetIH bodyIH =>
      simp only [Ty.subst]
      congr 1
      · exact sourceIH first second equal
      · exact targetIH first second equal
      · apply bodyIH
        intro index
        cases index with
        | there index =>
            exact congrArg (fun type => type.weaken .cvar) (equal index)

/-- A closed expression used only to strengthen types past term binders. -/
private def closeVarDummy (sig : Sig) : Exp sig :=
  .abs .top (.var .here)

/-- Strengthen a target type past a term binder. Target types contain no term
variables, so the particular dummy expression is unobservable. -/
def closeVar (body : Ty (sig ,, .var)) : Ty sig :=
  body.subst (Subst.openVar (closeVarDummy sig))

/-- Strengthening a type that was weakened across a term binder recovers the
original type. -/
@[simp] theorem closeVar_of_weaken (type : Ty sig) :
    TyOps.closeVar (type.weaken .var) = type := by
  unfold closeVar
  exact type.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openVar (closeVarDummy sig))

@[simp] theorem closeVar_weaken (body : Ty (sig ,, .var)) :
    (TyOps.closeVar body).weaken .var = body := by
  unfold closeVar Ty.weaken
  rw [← Ty.subst_asSubst, Ty.subst_comp]
  calc
    body.subst
        ((Subst.openVar (closeVarDummy sig)).comp
          (Rename.weaken Kind.var).asSubst) =
        body.subst Subst.id := by
          apply subst_eq_of_tvar
          intro index
          cases index with
          | there index => rfl
    _ = body := Ty.subst_id body

@[simp] theorem closeVar_open (body : Ty (sig ,, .var))
    (argument : Exp sig) :
    body.subst (Subst.openVar argument) = TyOps.closeVar body := by
  unfold closeVar
  apply subst_eq_of_tvar
  intro index
  cases index with
  | there index => rfl

theorem closeVar_rename (body : Ty (source ,, .var))
    (mapping : Rename source target) :
    (TyOps.closeVar body).rename mapping =
      TyOps.closeVar (body.rename (mapping.lift .var)) := by
  unfold closeVar
  rw [body.rename_subst_comm
    (Subst.openVarRenameComm (closeVarDummy source) mapping)]
  rfl

theorem closeVar_subst (body : Ty (source ,, .var))
    (substitution : Subst source target) :
    (TyOps.closeVar body).subst substitution =
      TyOps.closeVar (body.subst (substitution.lift .var)) := by
  unfold closeVar
  rw [Ty.subst_comp, Ty.subst_comp]
  apply subst_eq_of_tvar
  intro index
  cases index with
  | there index =>
      exact (substitution.tvar index).weaken_subst_cancel _
        (Subst.weakenAsSubst_comp_openVar _) |>.symm

end TyOps

namespace TypedSubst

/-- Identity is a context-preserving typed substitution. -/
noncomputable def id (context : Ctx sig) :
    Subst.Typed context context Subst.id where
  lookup := by
    intro kind index binding lookup
    cases binding with
    | var type =>
        simpa only [Subst.Realizes, Ty.subst_id] using
          (Exp.HasType.var lookup)
    | tvar => exact PUnit.unit
    | cvar source target =>
        simpa only [Subst.Realizes, Ty.subst_id] using
          (Co.HasType.cvar lookup)

/-- Typed substitutions compose in the same order as raw substitutions. -/
noncomputable def comp
    {source middle target : Sig}
    {sourceContext : Ctx source} {middleContext : Ctx middle}
    {targetContext : Ctx target}
    {first : Subst source middle} {second : Subst middle target}
    (firstTyped : Subst.Typed sourceContext middleContext first)
    (secondTyped : Subst.Typed middleContext targetContext second) :
    Subst.Typed sourceContext targetContext (first.comp second) where
  lookup := by
    intro kind index binding lookup
    have realized := firstTyped.lookup lookup
    cases binding with
    | var type =>
        have substituted := realized.subst secondTyped
        simpa only [Subst.Realizes, Subst.comp, Ty.subst_comp] using
          substituted
    | tvar => exact PUnit.unit
    | cvar source result =>
        have substituted := realized.subst secondTyped
        simpa only [Subst.Realizes, Subst.comp, Ty.subst_comp] using
          substituted

end TypedSubst

/-- A dependent mixed telescope, written from oldest to newest. -/
inductive Telescope : Sig -> Type where
| nil : Telescope sig
| var (type : Ty sig) (tail : Telescope (sig ,, .var)) : Telescope sig
| tvar (tail : Telescope (sig ,, .tvar)) : Telescope sig
| cvar (source target : Ty sig)
    (tail : Telescope (sig ,, .cvar)) : Telescope sig

namespace Telescope

/-- Scope after introducing every telescope field. -/
def scope : Telescope sig -> Sig
| .nil => sig
| .var _ tail | .tvar tail | .cvar _ _ tail => tail.scope

/-- Context after introducing every telescope field. -/
def context : (tele : Telescope sig) -> Ctx sig -> Ctx tele.scope
| .nil, context => context
| .var type tail, context => tail.context (context.bindVar type)
| .tvar tail, context => tail.context context.bindTVar
| .cvar source target tail, context =>
    tail.context (context.bindCVar source target)

/-- Inclusion of the base scope into the final telescope scope. -/
def weaken : (tele : Telescope sig) -> Rename sig tele.scope
| .nil => .id
| .var _ tail => (Rename.weaken .var).comp tail.weaken
| .tvar tail => (Rename.weaken .tvar).comp tail.weaken
| .cvar _ _ tail => (Rename.weaken .cvar).comp tail.weaken

/-- Rename a telescope and every dependent field. -/
def rename : Telescope source -> Rename source target -> Telescope target
| .nil, _ => .nil
| .var type tail, mapping =>
    .var (type.rename mapping) (tail.rename (mapping.lift .var))
| .tvar tail, mapping => .tvar (tail.rename (mapping.lift .tvar))
| .cvar source target tail, mapping =>
    .cvar (source.rename mapping) (target.rename mapping)
      (tail.rename (mapping.lift .cvar))

/-- Rename induced between final telescope scopes. -/
def liftRename : (tele : Telescope source) ->
    (mapping : Rename source target) ->
    Rename tele.scope (tele.rename mapping).scope
| .nil, mapping => mapping
| .var _ tail, mapping => tail.liftRename (mapping.lift .var)
| .tvar tail, mapping => tail.liftRename (mapping.lift .tvar)
| .cvar _ _ tail, mapping => tail.liftRename (mapping.lift .cvar)

/-- Substitute through a telescope and every dependent field. -/
def subst : Telescope source -> Subst source target -> Telescope target
| .nil, _ => .nil
| .var type tail, substitution =>
    .var (type.subst substitution)
      (tail.subst (substitution.lift .var))
| .tvar tail, substitution =>
    .tvar (tail.subst (substitution.lift .tvar))
| .cvar source target tail, substitution =>
    .cvar (source.subst substitution) (target.subst substitution)
      (tail.subst (substitution.lift .cvar))

/-- Substitution induced between final telescope scopes. -/
def liftSubst : (tele : Telescope source) ->
    (substitution : Subst source target) ->
    Subst tele.scope (tele.subst substitution).scope
| .nil, substitution => substitution
| .var _ tail, substitution => tail.liftSubst (substitution.lift .var)
| .tvar tail, substitution => tail.liftSubst (substitution.lift .tvar)
| .cvar _ _ tail, substitution => tail.liftSubst (substitution.lift .cvar)

/-- A typed base renaming lifts through every telescope field. -/
noncomputable def liftRename_typed
    (tele : Telescope source)
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {mapping : Rename source target}
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Rename.Typed (tele.context sourceContext)
      ((tele.rename mapping).context targetContext)
      (tele.liftRename mapping) := by
  induction tele generalizing target targetContext with
  | nil => exact typed
  | var type tail ih => exact ih (typed.lift (.var type))
  | tvar tail ih => exact ih (typed.lift .tvar)
  | cvar source result tail ih =>
      exact ih (typed.lift (.cvar source result))

/-- A typed base substitution lifts through every telescope field. -/
noncomputable def liftSubst_typed
    (tele : Telescope source)
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {substitution : Subst source target}
    (typed : Subst.Typed sourceContext targetContext substitution) :
    Subst.Typed (tele.context sourceContext)
      ((tele.subst substitution).context targetContext)
      (tele.liftSubst substitution) := by
  induction tele generalizing target targetContext with
  | nil => exact typed
  | var type tail ih => exact ih (typed.lift (.var type))
  | tvar tail ih => exact ih (typed.lift .tvar)
  | cvar source result tail ih =>
      exact ih (typed.lift (.cvar source result))

@[simp] theorem rename_id (tele : Telescope sig) :
    tele.rename Rename.id = tele := by
  induction tele with
  | nil => rfl
  | var type tail ih =>
      simp only [rename, Ty.rename_id, Rename.lift_id, ih]
  | tvar tail ih =>
      simp only [rename, Rename.lift_id, ih]
  | cvar source target tail ih =>
      simp only [rename, Ty.rename_id, Rename.lift_id, ih]

theorem rename_comp (tele : Telescope source)
    (first : Rename source middle) (second : Rename middle target) :
    (tele.rename first).rename second = tele.rename (first.comp second) := by
  induction tele generalizing middle target with
  | nil => rfl
  | var type tail ih =>
      simp only [rename, Ty.rename_comp, Rename.lift_comp, ih]
  | tvar tail ih =>
      simp only [rename, Rename.lift_comp, ih]
  | cvar source result tail ih =>
      simp only [rename, Ty.rename_comp, Rename.lift_comp, ih]

@[simp] theorem subst_id (tele : Telescope sig) :
    tele.subst Subst.id = tele := by
  induction tele with
  | nil => rfl
  | var type tail ih =>
      simp only [subst, Ty.subst_id, Subst.lift_id, ih]
  | tvar tail ih =>
      simp only [subst, Subst.lift_id, ih]
  | cvar source target tail ih =>
      simp only [subst, Ty.subst_id, Subst.lift_id, ih]

theorem subst_comp (tele : Telescope source)
    (first : Subst source middle) (second : Subst middle target) :
    (tele.subst first).subst second = tele.subst (first.comp second) := by
  induction tele generalizing middle target with
  | nil => rfl
  | var type tail ih =>
      simp only [subst, Ty.subst_comp, Subst.comp_lift, ih]
  | tvar tail ih =>
      simp only [subst, Subst.comp_lift, ih]
  | cvar source target tail ih =>
      simp only [subst, Ty.subst_comp, Subst.comp_lift, ih]

theorem rename_asSubst (tele : Telescope source)
    (mapping : Rename source target) :
    tele.rename mapping = tele.subst mapping.asSubst := by
  induction tele generalizing target with
  | nil => rfl
  | var type tail ih =>
      simp only [rename, subst, Ty.rename_asSubst,
        Rename.asSubst_lift, ih]
  | tvar tail ih =>
      simp only [rename, subst, Rename.asSubst_lift, ih]
  | cvar source target tail ih =>
      simp only [rename, subst, Ty.rename_asSubst,
        Rename.asSubst_lift, ih]

theorem rename_subst_cancel (tele : Telescope source)
    (mapping : Rename source middle) (opening : Subst middle source)
    (cancel : mapping.asSubst.comp opening = Subst.id) :
    (tele.rename mapping).subst opening = tele := by
  rw [tele.rename_asSubst, tele.subst_comp, cancel, tele.subst_id]

theorem rename_subst_comm (tele : Telescope source)
    {source' middle target : Sig}
    {substitution : Subst source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {substitution' : Subst source' target}
    (comm : Subst.RenameComm substitution sourceRename targetRename
      substitution') :
    (tele.subst substitution).rename targetRename =
      (tele.rename sourceRename).subst substitution' := by
  induction tele generalizing source' middle target with
  | nil => rfl
  | var type tail ih =>
      simp only [subst, rename]
      rw [type.rename_subst_comm comm, ih (comm.lift .var)]
  | tvar tail ih =>
      simp only [subst, rename]
      rw [ih (comm.lift .tvar)]
  | cvar source result tail ih =>
      simp only [subst, rename]
      rw [source.rename_subst_comm comm, result.rename_subst_comm comm,
        ih (comm.lift .cvar)]

theorem weaken_liftRename (tele : Telescope source)
    (mapping : Rename source target) :
    tele.weaken.comp (tele.liftRename mapping) =
      mapping.comp (tele.rename mapping).weaken := by
  induction tele generalizing target with
  | nil =>
      calc
        Rename.id.comp mapping = mapping := Rename.id_comp mapping
        _ = mapping.comp Rename.id := (Rename.comp_id mapping).symm
  | var type tail ih =>
      change ((Rename.weaken .var).comp tail.weaken).comp
          (tail.liftRename (mapping.lift .var)) =
        mapping.comp ((Rename.weaken .var).comp
          (tail.rename (mapping.lift .var)).weaken)
      rw [Rename.comp_assoc, ih, ← Rename.comp_assoc,
        Rename.weaken_lift_comm, Rename.comp_assoc]
  | tvar tail ih =>
      change ((Rename.weaken .tvar).comp tail.weaken).comp
          (tail.liftRename (mapping.lift .tvar)) =
        mapping.comp ((Rename.weaken .tvar).comp
          (tail.rename (mapping.lift .tvar)).weaken)
      rw [Rename.comp_assoc, ih, ← Rename.comp_assoc,
        Rename.weaken_lift_comm, Rename.comp_assoc]
  | cvar source target tail ih =>
      change ((Rename.weaken .cvar).comp tail.weaken).comp
          (tail.liftRename (mapping.lift .cvar)) =
        mapping.comp ((Rename.weaken .cvar).comp
          (tail.rename (mapping.lift .cvar)).weaken)
      rw [Rename.comp_assoc, ih, ← Rename.comp_assoc,
        Rename.weaken_lift_comm, Rename.comp_assoc]

private theorem weaken_liftSubst_head (substitution : Subst source target)
    (kind : Kind) :
    (Rename.weaken kind).asSubst.comp (substitution.lift kind) =
      substitution.comp (Rename.weaken kind).asSubst := by
  apply Subst.funext
  · intro index
    exact Exp.rename_asSubst (substitution.var index)
      (Rename.weaken kind)
  · intro index
    exact Ty.rename_asSubst (substitution.tvar index)
      (Rename.weaken kind)
  · intro index
    exact Co.rename_asSubst (substitution.cvar index)
      (Rename.weaken kind)

theorem weaken_liftSubst (tele : Telescope source)
    (substitution : Subst source target) :
    tele.weaken.asSubst.comp (tele.liftSubst substitution) =
      substitution.comp (tele.subst substitution).weaken.asSubst := by
  induction tele generalizing target with
  | nil =>
      calc
        Rename.id.asSubst.comp substitution = substitution :=
          Subst.id_comp substitution
        _ = substitution.comp Rename.id.asSubst :=
          (Subst.comp_id substitution).symm
  | var type tail ih =>
      change (((Rename.weaken .var).comp tail.weaken).asSubst).comp
          (tail.liftSubst (substitution.lift .var)) =
        substitution.comp
          (((Rename.weaken .var).comp
            (tail.subst (substitution.lift .var)).weaken).asSubst)
      rw [Rename.asSubst_comp, Subst.comp_assoc, ih,
        ← Subst.comp_assoc, weaken_liftSubst_head,
        Subst.comp_assoc, ← Rename.asSubst_comp]

  | tvar tail ih =>
      change (((Rename.weaken .tvar).comp tail.weaken).asSubst).comp
          (tail.liftSubst (substitution.lift .tvar)) =
        substitution.comp
          (((Rename.weaken .tvar).comp
            (tail.subst (substitution.lift .tvar)).weaken).asSubst)
      rw [Rename.asSubst_comp, Subst.comp_assoc, ih,
        ← Subst.comp_assoc, weaken_liftSubst_head,
        Subst.comp_assoc, ← Rename.asSubst_comp]

  | cvar source result tail ih =>
      change (((Rename.weaken .cvar).comp tail.weaken).asSubst).comp
          (tail.liftSubst (substitution.lift .cvar)) =
        substitution.comp
          (((Rename.weaken .cvar).comp
            (tail.subst (substitution.lift .cvar)).weaken).asSubst)
      rw [Rename.asSubst_comp, Subst.comp_assoc, ih,
        ← Subst.comp_assoc, weaken_liftSubst_head,
        Subst.comp_assoc, ← Rename.asSubst_comp]

theorem weakenType_liftRename (tele : Telescope source)
    (type : Ty source) (mapping : Rename source target) :
    (type.rename tele.weaken).rename (tele.liftRename mapping) =
      (type.rename mapping).rename (tele.rename mapping).weaken := by
  rw [Ty.rename_comp, Ty.rename_comp, tele.weaken_liftRename]

theorem weakenType_liftSubst (tele : Telescope source)
    (type : Ty source) (substitution : Subst source target) :
    (type.rename tele.weaken).subst (tele.liftSubst substitution) =
      (type.subst substitution).rename
        (tele.subst substitution).weaken := by
  rw [Ty.rename_asSubst, Ty.subst_comp, tele.weaken_liftSubst,
    ← Ty.subst_comp, Ty.subst_asSubst]

/-- Universally abstract a result type over the telescope. -/
def forallTy : (tele : Telescope sig) -> Ty tele.scope -> Ty sig
| .nil, result => result
| .var type tail, result =>
    .arrow type (TyOps.closeVar (tail.forallTy result))
| .tvar tail, result => .poly (tail.forallTy result)
| .cvar source target tail, result =>
    .qual source target (tail.forallTy result)

/-- Abstract an expression over every telescope field. -/
def lambda : (tele : Telescope sig) -> Exp tele.scope -> Exp sig
| .nil, body => body
| .var type tail, body => .abs type (tail.lambda body)
| .tvar tail, body => .tabs (tail.lambda body)
| .cvar source target tail, body =>
    .cabs source target (tail.lambda body)

theorem forallTy_rename (tele : Telescope source)
    (result : Ty tele.scope) (mapping : Rename source target) :
    (tele.forallTy result).rename mapping =
      (tele.rename mapping).forallTy
        (result.rename (tele.liftRename mapping)) := by
  induction tele generalizing target with
  | nil => rfl
  | var type tail ih =>
      simp only [forallTy, rename, liftRename, Ty.rename]
      rw [TyOps.closeVar_rename, ih]
      rfl
  | tvar tail ih =>
      simp only [forallTy, rename, liftRename, Ty.rename]
      rw [ih]
      rfl
  | cvar source target tail ih =>
      simp only [forallTy, rename, liftRename, Ty.rename]
      rw [ih]
      rfl

theorem forallTy_subst (tele : Telescope source)
    (result : Ty tele.scope) (substitution : Subst source target) :
    (tele.forallTy result).subst substitution =
      (tele.subst substitution).forallTy
        (result.subst (tele.liftSubst substitution)) := by
  induction tele generalizing target with
  | nil => rfl
  | var type tail ih =>
      simp only [forallTy, subst, liftSubst, Ty.subst]
      rw [TyOps.closeVar_subst, ih]
      rfl
  | tvar tail ih =>
      simp only [forallTy, subst, liftSubst, Ty.subst]
      rw [ih]
      rfl
  | cvar source target tail ih =>
      simp only [forallTy, subst, liftSubst, Ty.subst]
      rw [ih]
      rfl

theorem lambda_rename (tele : Telescope source)
    (body : Exp tele.scope) (mapping : Rename source target) :
    (tele.lambda body).rename mapping =
      (tele.rename mapping).lambda
        (body.rename (tele.liftRename mapping)) := by
  induction tele generalizing target with
  | nil => rfl
  | var type tail ih =>
      simp only [lambda, rename, liftRename, Exp.rename]
      rw [ih]
      rfl
  | tvar tail ih =>
      simp only [lambda, rename, liftRename, Exp.rename]
      rw [ih]
      rfl
  | cvar source target tail ih =>
      simp only [lambda, rename, liftRename, Exp.rename]
      rw [ih]
      rfl

theorem lambda_subst (tele : Telescope source)
    (body : Exp tele.scope) (substitution : Subst source target) :
    (tele.lambda body).subst substitution =
      (tele.subst substitution).lambda
        (body.subst (tele.liftSubst substitution)) := by
  induction tele generalizing target with
  | nil => rfl
  | var type tail ih =>
      simp only [lambda, subst, liftSubst, Exp.subst]
      rw [ih]
      rfl
  | tvar tail ih =>
      simp only [lambda, subst, liftSubst, Exp.subst]
      rw [ih]
      rfl
  | cvar source target tail ih =>
      simp only [lambda, subst, liftSubst, Exp.subst]
      rw [ih]
      rfl

/-- Type of a telescope consumer returning `result`. -/
def handler (tele : Telescope sig) (result : Ty sig) : Ty sig :=
  tele.forallTy (result.rename tele.weaken)

theorem handler_rename (tele : Telescope source) (result : Ty source)
    (mapping : Rename source target) :
    (tele.handler result).rename mapping =
      (tele.rename mapping).handler (result.rename mapping) := by
  unfold handler
  rw [tele.forallTy_rename, tele.weakenType_liftRename]

theorem handler_subst (tele : Telescope source) (result : Ty source)
    (substitution : Subst source target) :
    (tele.handler result).subst substitution =
      (tele.subst substitution).handler (result.subst substitution) := by
  unfold handler
  rw [tele.forallTy_subst, tele.weakenType_liftSubst]

/-- Church consumer under a fresh answer-type binder. -/
def existsHandler (tele : Telescope sig) : Ty (sig ,, .tvar) :=
  (tele.rename (Rename.weaken .tvar)).handler (.tvar .here)

/-- Body of the outer answer-type quantifier in a Church existential. -/
def existsBody (tele : Telescope sig) : Ty (sig ,, .tvar) :=
  .arrow tele.existsHandler (.tvar .here)

/-- Church existential hiding all fields in a mixed telescope. -/
def existsTy (tele : Telescope sig) : Ty sig :=
  .poly tele.existsBody

@[simp] theorem existsHandler_open (tele : Telescope sig)
    (answer : Ty sig) :
    tele.existsHandler.subst (Subst.openTVar answer) =
      tele.handler answer := by
  unfold existsHandler
  rw [handler_subst]
  rw [tele.rename_subst_cancel (Rename.weaken .tvar)
    (Subst.openTVar answer)
    (Subst.weakenAsSubst_comp_openTVar answer)]
  rfl

@[simp] theorem existsBody_open (tele : Telescope sig)
    (answer : Ty sig) :
    tele.existsBody.subst (Subst.openTVar answer) =
      .arrow (tele.handler answer) answer := by
  unfold existsBody
  simp only [Ty.subst]
  rw [tele.existsHandler_open]
  rfl

noncomputable def lambda_hasType
    (tele : Telescope sig) {base : Ctx sig} {body : Exp tele.scope}
    {result : Ty tele.scope}
    (bodyTyping : Exp.HasType (tele.context base) body result) :
    Exp.HasType base (tele.lambda body) (tele.forallTy result) := by
  induction tele with
  | nil => exact bodyTyping
  | var type tail ih =>
      apply Exp.HasType.abs
      rw [TyOps.closeVar_weaken]
      exact ih bodyTyping
  | tvar tail ih => exact .tabs (ih bodyTyping)
  | cvar source target tail ih => exact .cabs (ih bodyTyping)

/-- Eliminate a Church existential with a telescope-abstracted consumer. -/
def unpack (tele : Telescope sig) (package : Exp sig) (answer : Ty sig)
    (body : Exp tele.scope) : Exp sig :=
  .app (.tapp package answer) (tele.lambda body)

noncomputable def unpack_hasType
    (tele : Telescope sig) {base : Ctx sig} {package : Exp sig}
    {answer : Ty sig} {body : Exp tele.scope}
    (packageTyping : Exp.HasType base package tele.existsTy)
    (bodyTyping : Exp.HasType (tele.context base) body
      (answer.rename tele.weaken)) :
    Exp.HasType base (tele.unpack package answer body) answer := by
  have opened := Exp.HasType.tapp (argument := answer) packageTyping
  rw [tele.existsBody_open] at opened
  exact .app opened (tele.lambda_hasType bodyTyping)

/-- A fully typed sequence of arguments for a mixed telescope. Later
arguments are indexed by the telescope obtained after opening earlier ones. -/
inductive Args (base : Ctx sig) : Telescope sig -> Type where
| nil : Args base .nil
| var {type : Ty sig} {tail : Telescope (sig ,, .var)}
    (argument : Exp sig) (argumentTyping : Exp.HasType base argument type)
    (rest : Args base (tail.subst (Subst.openVar argument))) :
    Args base (.var type tail)
| tvar {tail : Telescope (sig ,, .tvar)}
    (argument : Ty sig)
    (rest : Args base (tail.subst (Subst.openTVar argument))) :
    Args base (.tvar tail)
| cvar {source target : Ty sig} {tail : Telescope (sig ,, .cvar)}
    (argument : Co sig)
    (argumentTyping : Co.HasType base argument source target)
    (rest : Args base (tail.subst (Subst.openCVar argument))) :
    Args base (.cvar source target tail)

namespace Args

/-- Rename every argument and its typing evidence. -/
noncomputable def rename
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target} {tele : Telescope source}
    (arguments : Args sourceContext tele) (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Args targetContext (tele.rename mapping) := by
  induction arguments generalizing target targetContext with
  | nil => exact .nil
  | @var type tail argument argumentTyping rest ih =>
      refine .var (argument.rename mapping)
        (argumentTyping.rename typed) ?_
      rw [← tail.rename_subst_comm
        (Subst.openVarRenameComm argument mapping)]
      exact ih mapping typed
  | @tvar tail argument rest ih =>
      refine .tvar (argument.rename mapping) ?_
      rw [← tail.rename_subst_comm
        (Subst.openTVarRenameComm argument mapping)]
      exact ih mapping typed
  | @cvar source result tail argument argumentTyping rest ih =>
      refine .cvar (argument.rename mapping)
        (argumentTyping.rename typed) ?_
      rw [← tail.rename_subst_comm
        (Subst.openCVarRenameComm argument mapping)]
      exact ih mapping typed

/-- Apply a function to a fully typed mixed argument sequence. -/
def apply {sig : Sig} {base : Ctx sig} {tele : Telescope sig} :
    Args base tele -> Exp sig -> Exp sig
| .nil, function => function
| .var argument _ rest, function =>
    rest.apply (.app function argument)
| .tvar argument rest, function =>
    rest.apply (.tapp function argument)
| .cvar argument _ rest, function =>
    rest.apply (.capp function argument)

/-- Open a result type with every argument. -/
def instantiate {sig : Sig} {base : Ctx sig} {tele : Telescope sig} :
    (arguments : Args base tele) -> Ty tele.scope -> Ty sig
| .nil, result => result
| @Args.var _ _ _ tail argument _ rest, result =>
    rest.instantiate
      (result.subst (tail.liftSubst (Subst.openVar argument)))
| @Args.tvar _ _ tail argument rest, result =>
    rest.instantiate
      (result.subst (tail.liftSubst (Subst.openTVar argument)))
| @Args.cvar _ _ _ _ tail argument _ rest, result =>
    rest.instantiate
      (result.subst (tail.liftSubst (Subst.openCVar argument)))

/-- Simultaneous heterogeneous substitution represented by an argument
sequence. -/
def substitution {sig : Sig} {base : Ctx sig} {tele : Telescope sig} :
    Args base tele -> Subst tele.scope sig
| .nil => Subst.id
| @Args.var _ _ _ tail argument _ rest =>
    (tail.liftSubst (Subst.openVar argument)).comp rest.substitution
| @Args.tvar _ _ tail argument rest =>
    (tail.liftSubst (Subst.openTVar argument)).comp rest.substitution
| @Args.cvar _ _ _ _ tail argument _ rest =>
    (tail.liftSubst (Subst.openCVar argument)).comp rest.substitution

/-- `instantiate` is exactly ordinary type substitution by the heterogeneous
argument substitution. -/
theorem instantiate_eq_subst
    {sig : Sig} {base : Ctx sig} {tele : Telescope sig}
    (arguments : Args base tele) (result : Ty tele.scope) :
    arguments.instantiate result =
      result.subst arguments.substitution := by
  induction arguments with
  | nil => exact (Ty.subst_id result).symm
  | var argument argumentTyping rest ih =>
      simp only [instantiate, substitution, ih, Ty.subst_comp]
      rfl
  | tvar argument rest ih =>
      simp only [instantiate, substitution, ih, Ty.subst_comp]
      rfl
  | cvar argument argumentTyping rest ih =>
      simp only [instantiate, substitution, ih, Ty.subst_comp]
      rfl

/-- The heterogeneous substitution represented by typed arguments preserves
the complete telescope context. -/
noncomputable def substitution_typed
    {sig : Sig} {base : Ctx sig} {tele : Telescope sig}
    (arguments : Args base tele) :
    Subst.Typed (tele.context base) base arguments.substitution := by
  induction arguments with
  | nil => exact TypedSubst.id base
  | @var type tail argument argumentTyping rest ih =>
      exact TypedSubst.comp (tail.liftSubst_typed
        (Subst.Typed.openVar argumentTyping)) ih
  | @tvar tail argument rest ih =>
      exact TypedSubst.comp (tail.liftSubst_typed
        (Subst.Typed.openTVar base argument)) ih
  | @cvar source target tail argument argumentTyping rest ih =>
      exact TypedSubst.comp (tail.liftSubst_typed
        (Subst.Typed.openCVar argumentTyping)) ih

/-- Opening a base type weakened through a complete argument telescope
recovers the base type. -/
@[simp] theorem instantiate_weaken
    {sig : Sig} {base : Ctx sig} {tele : Telescope sig}
    (arguments : Args base tele) (result : Ty sig) :
    arguments.instantiate (result.rename tele.weaken) = result := by
  induction arguments with
  | nil => exact Ty.rename_id result
  | @var type tail argument argumentTyping rest ih =>
      change rest.instantiate
        ((result.rename ((Rename.weaken .var).comp tail.weaken)).subst
          (tail.liftSubst (Subst.openVar argument))) = result
      rw [← Ty.rename_comp, tail.weakenType_liftSubst]
      change rest.instantiate
        (((result.weaken .var).subst (Subst.openVar argument)).rename
          (tail.subst (Subst.openVar argument)).weaken) = result
      rw [result.weaken_subst_cancel _
        (Subst.weakenAsSubst_comp_openVar argument)]
      exact ih
  | @tvar tail argument rest ih =>
      change rest.instantiate
        ((result.rename ((Rename.weaken .tvar).comp tail.weaken)).subst
          (tail.liftSubst (Subst.openTVar argument))) = result
      rw [← Ty.rename_comp, tail.weakenType_liftSubst]
      change rest.instantiate
        (((result.weaken .tvar).subst (Subst.openTVar argument)).rename
          (tail.subst (Subst.openTVar argument)).weaken) = result
      rw [result.weaken_subst_cancel _
        (Subst.weakenAsSubst_comp_openTVar argument)]
      exact ih
  | @cvar source target tail argument argumentTyping rest ih =>
      change rest.instantiate
        ((result.rename ((Rename.weaken .cvar).comp tail.weaken)).subst
          (tail.liftSubst (Subst.openCVar argument))) = result
      rw [← Ty.rename_comp, tail.weakenType_liftSubst]
      change rest.instantiate
        (((result.weaken .cvar).subst (Subst.openCVar argument)).rename
          (tail.subst (Subst.openCVar argument)).weaken) = result
      rw [result.weaken_subst_cancel _
        (Subst.weakenAsSubst_comp_openCVar argument)]
      exact ih

/-- Universal application is well typed for a fully typed argument spine. -/
noncomputable def apply_hasType
    {sig : Sig} {base : Ctx sig} {tele : Telescope sig}
    (arguments : Args base tele) {function : Exp sig}
    {result : Ty tele.scope}
    (functionTyping : Exp.HasType base function (tele.forallTy result)) :
    Exp.HasType base (arguments.apply function)
      (arguments.instantiate result) := by
  induction arguments generalizing function with
  | nil => exact functionTyping
  | @var type tail argument argumentTyping rest ih =>
      apply ih
      have applied := Exp.HasType.app functionTyping argumentTyping
      rw [← TyOps.closeVar_open] at applied
      rw [tail.forallTy_subst] at applied
      exact applied
  | @tvar tail argument rest ih =>
      apply ih
      have applied := Exp.HasType.tapp (argument := argument) functionTyping
      rw [tail.forallTy_subst] at applied
      exact applied
  | @cvar source target tail argument argumentTyping rest ih =>
      apply ih
      have applied := Exp.HasType.capp functionTyping argumentTyping
      rw [tail.forallTy_subst] at applied
      exact applied

/-- Move package arguments below the Church answer and handler binders. -/
noncomputable def forExists
    {sig : Sig} {base : Ctx sig} {tele : Telescope sig}
    (arguments : Args base tele) :
    Args ((base.bindTVar).bindVar tele.existsHandler)
      ((tele.rename (Rename.weaken .tvar)).rename
        (Rename.weaken .var)) :=
  let underAnswer := arguments.rename (Rename.weaken .tvar)
    (Rename.Typed.weaken base .tvar)
  underAnswer.rename (Rename.weaken .var)
    (Rename.Typed.weaken base.bindTVar (.var tele.existsHandler))

end Args

/-- Introduce a Church existential from a fully typed field sequence. -/
noncomputable def pack
    {sig : Sig} {base : Ctx sig} {tele : Telescope sig}
    (arguments : Args base tele) : Exp sig :=
  .tabs
    (.abs tele.existsHandler
      (arguments.forExists.apply (.var .here)))

noncomputable def pack_hasType
    {sig : Sig} {base : Ctx sig} {tele : Telescope sig}
    (arguments : Args base tele) :
    Exp.HasType base (pack arguments) tele.existsTy := by
  let answerTele := tele.rename (Rename.weaken .tvar)
  let packedTele := answerTele.rename (Rename.weaken .var)
  let answer : Ty ((sig ,, .tvar) ,, .var) :=
    ((.tvar .here : Ty (sig ,, .tvar)).weaken .var)
  let packedArgs := arguments.forExists
  have handlerTyping :
      Exp.HasType ((base.bindTVar).bindVar tele.existsHandler)
        (.var .here) (tele.existsHandler.weaken .var) :=
    .var Ctx.Lookup.here
  have handlerTyping' :
      Exp.HasType ((base.bindTVar).bindVar tele.existsHandler)
        (.var .here) (packedTele.handler answer) := by
    dsimp only [packedTele, answer, answerTele]
    unfold Ty.weaken
    rw [← handler_rename]
    exact handlerTyping
  have applied := packedArgs.apply_hasType handlerTyping'
  rw [packedArgs.instantiate_weaken] at applied
  exact .tabs (.abs applied)

end Telescope

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


namespace TypedRename

noncomputable def id (context : Ctx sig) :
    Rename.Typed context context Rename.id where
  lookup := by
    intro kind index binding lookup
    cases binding with
    | var type =>
        simpa only [Binding.rename, Ty.rename_id] using lookup
    | tvar => exact lookup
    | cvar source target =>
        simpa only [Binding.rename, Ty.rename_id] using lookup

noncomputable def comp
    {source middle target : Sig}
    {sourceContext : Ctx source} {middleContext : Ctx middle}
    {targetContext : Ctx target}
    {first : Rename source middle} {second : Rename middle target}
    (firstTyped : Rename.Typed sourceContext middleContext first)
    (secondTyped : Rename.Typed middleContext targetContext second) :
    Rename.Typed sourceContext targetContext (first.comp second) where
  lookup := by
    intro kind index binding lookup
    have firstLookup := firstTyped.lookup lookup
    have secondLookup := secondTyped.lookup firstLookup
    cases binding with
    | var type =>
        simpa only [Binding.rename, Ty.rename_comp] using secondLookup
    | tvar => exact secondLookup
    | cvar source result =>
        simpa only [Binding.rename, Ty.rename_comp] using secondLookup

end TypedRename

namespace Telescope

private theorem Rename.cast_comp_target
    {firstTarget secondTarget : Sig} (equal : firstTarget = secondTarget)
    (before : Rename source middle) (after : Rename middle firstTarget) :
    cast (congrArg (Rename source) equal) (before.comp after) =
      before.comp (cast (congrArg (Rename middle) equal) after) := by
  cases equal
  rfl

/-- Concatenate a dependent telescope with one beginning in its final
scope. -/
def append : (first : Telescope sig) -> Telescope first.scope -> Telescope sig
| .nil, second => second
| .var type tail, second => .var type (tail.append second)
| .tvar tail, second => .tvar (tail.append second)
| .cvar source target tail, second =>
    .cvar source target (tail.append second)

def appendScopeEq : (first : Telescope sig) ->
    (second : Telescope first.scope) ->
    (first.append second).scope = second.scope
| .nil, _ => rfl
| .var _ tail, second => appendScopeEq tail second
| .tvar tail, second => appendScopeEq tail second
| .cvar _ _ tail, second => appendScopeEq tail second

@[simp] theorem append_scope (first : Telescope sig)
    (second : Telescope first.scope) :
    (first.append second).scope = second.scope :=
  appendScopeEq first second

theorem append_context (first : Telescope sig)
    (second : Telescope first.scope) (base : Ctx sig) :
    HEq ((first.append second).context base)
      (second.context (first.context base)) := by
  induction first with
  | nil => rfl
  | var type tail ih => exact ih second (base.bindVar type)
  | tvar tail ih => exact ih second base.bindTVar
  | cvar source target tail ih =>
      exact ih second (base.bindCVar source target)

theorem append_context_cast (first : Telescope sig)
    (second : Telescope first.scope) (base : Ctx sig) :
    cast (congrArg Ctx (appendScopeEq first second))
        ((first.append second).context base) =
      second.context (first.context base) := by
  induction first with
  | nil => rfl
  | var type tail ih =>
      change cast (congrArg Ctx (appendScopeEq tail second))
          ((tail.append second).context (base.bindVar type)) = _
      exact ih second (base.bindVar type)
  | tvar tail ih =>
      change cast (congrArg Ctx (appendScopeEq tail second))
          ((tail.append second).context base.bindTVar) = _
      exact ih second base.bindTVar
  | cvar source target tail ih =>
      change cast (congrArg Ctx (appendScopeEq tail second))
          ((tail.append second).context (base.bindCVar source target)) = _
      exact ih second (base.bindCVar source target)

theorem append_weaken (first : Telescope sig)
    (second : Telescope first.scope) :
    cast (congrArg (Rename sig) (appendScopeEq first second))
        (first.append second).weaken =
      first.weaken.comp second.weaken := by
  induction first with
  | nil =>
      change second.weaken = Rename.id.comp second.weaken
      exact (Rename.id_comp second.weaken).symm
  | var type tail ih =>
      simp only [append, weaken]
      change cast (congrArg (Rename _) (appendScopeEq tail second))
          ((Rename.weaken .var).comp (tail.append second).weaken) = _
      rw [Rename.cast_comp_target (appendScopeEq tail second),
        Rename.comp_assoc]
      exact congrArg (Rename.comp (Rename.weaken .var)) (ih second)
  | tvar tail ih =>
      simp only [append, weaken]
      change cast (congrArg (Rename _) (appendScopeEq tail second))
          ((Rename.weaken .tvar).comp (tail.append second).weaken) = _
      rw [Rename.cast_comp_target (appendScopeEq tail second),
        Rename.comp_assoc]
      exact congrArg (Rename.comp (Rename.weaken .tvar)) (ih second)
  | cvar source target tail ih =>
      simp only [append, weaken]
      change cast (congrArg (Rename _) (appendScopeEq tail second))
          ((Rename.weaken .cvar).comp (tail.append second).weaken) = _
      rw [Rename.cast_comp_target (appendScopeEq tail second),
        Rename.comp_assoc]
      exact congrArg (Rename.comp (Rename.weaken .cvar)) (ih second)

@[simp] theorem append_rename (first : Telescope source)
    (second : Telescope first.scope) (mapping : Rename source target) :
    (first.append second).rename mapping =
      (first.rename mapping).append
        (second.rename (first.liftRename mapping)) := by
  induction first generalizing target with
  | nil => rfl
  | var type tail ih =>
      simp only [append, rename, liftRename]
      rw [ih]
      rfl
  | tvar tail ih =>
      simp only [append, rename, liftRename]
      rw [ih]
      rfl
  | cvar source result tail ih =>
      simp only [append, rename, liftRename]
      rw [ih]
      rfl

@[simp] theorem append_subst (first : Telescope source)
    (second : Telescope first.scope) (substitution : Subst source target) :
    (first.append second).subst substitution =
      (first.subst substitution).append
        (second.subst (first.liftSubst substitution)) := by
  induction first generalizing target with
  | nil => rfl
  | var type tail ih =>
      simp only [append, subst, liftSubst]
      rw [ih]
      rfl
  | tvar tail ih =>
      simp only [append, subst, liftSubst]
      rw [ih]
      rfl
  | cvar source result tail ih =>
      simp only [append, subst, liftSubst]
      rw [ih]
      rfl

def appendSubstScopeEq (first : Telescope source)
    (second : Telescope first.scope) (substitution : Subst source target) :
    ((first.append second).subst substitution).scope =
      (second.subst (first.liftSubst substitution)).scope :=
  Eq.trans (congrArg Telescope.scope
      (append_subst first second substitution))
    (appendScopeEq (first.subst substitution)
      (second.subst (first.liftSubst substitution)))

/-- The lifted substitution for an appended telescope, normalized to the
literal source and target scopes of the append. -/
def appendLiftSubst (first : Telescope source)
    (second : Telescope first.scope) (substitution : Subst source target) :
    Subst (first.append second).scope
      ((first.append second).subst substitution).scope :=
  cast (by
    rw [append_scope, append_subst, append_scope])
    (second.liftSubst (first.liftSubst substitution))

/-- Lifting through concatenated telescopes is successive dependent
lifting. -/
theorem append_liftSubst (first : Telescope source)
    (second : Telescope first.scope) (substitution : Subst source target) :
    (first.append second).liftSubst substitution =
      first.appendLiftSubst second substitution := by
  induction first generalizing target with
  | nil =>
      simp only [append, liftSubst, appendLiftSubst]
      rfl
  | var type tail ih =>
      simp only [append, liftSubst, appendLiftSubst]
      exact ih second (substitution.lift .var)
  | tvar tail ih =>
      simp only [append, liftSubst, appendLiftSubst]
      exact ih second (substitution.lift .tvar)
  | cvar source result tail ih =>
      simp only [append, liftSubst, appendLiftSubst]
      exact ih second (substitution.lift .cvar)

private theorem liftSubst_congr_heq (tele : Telescope source)
    {first second : Subst source target} (equal : first = second) :
    HEq (tele.liftSubst first) (tele.liftSubst second) := by
  cases equal
  rfl

/-- Telescope lifting preserves substitution composition, including its
dependent target-scope transport. -/
theorem liftSubst_comp_heq (tele : Telescope source)
    (first : Subst source middle) (second : Subst middle target) :
    HEq (tele.liftSubst (first.comp second))
      ((tele.liftSubst first).comp
        ((tele.subst first).liftSubst second)) := by
  induction tele generalizing middle target with
  | nil => rfl
  | var type tail ih =>
      exact HEq.trans
        (liftSubst_congr_heq tail (Subst.comp_lift first second))
        (ih (first.lift .var) (second.lift .var))
  | tvar tail ih =>
      exact HEq.trans
        (liftSubst_congr_heq tail (Subst.comp_lift first second))
        (ih (first.lift .tvar) (second.lift .tvar))
  | cvar source result tail ih =>
      exact HEq.trans
        (liftSubst_congr_heq tail (Subst.comp_lift first second))
        (ih (first.lift .cvar) (second.lift .cvar))

/-- Lifting the identity through a telescope is heterogeneously the identity
on its final scope. -/
theorem liftSubst_id_heq (tele : Telescope sig) :
    HEq (tele.liftSubst Subst.id) (Subst.id : Subst tele.scope tele.scope) := by
  induction tele with
  | nil => rfl
  | var type tail ih =>
      exact HEq.trans (liftSubst_congr_heq tail Subst.lift_id) ih
  | tvar tail ih =>
      exact HEq.trans (liftSubst_congr_heq tail Subst.lift_id) ih
  | cvar source target tail ih =>
      exact HEq.trans (liftSubst_congr_heq tail Subst.lift_id) ih

private theorem Subst.id_heq {first second : Sig} (equal : first = second) :
    HEq (Subst.id : Subst first first) (Subst.id : Subst second second) := by
  cases equal
  rfl

private theorem Subst.comp_heq
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

/-- The inclusion into a telescope's final scope preserves its context. -/
noncomputable def weaken_typed (tele : Telescope sig) (base : Ctx sig) :
    Rename.Typed base (tele.context base) tele.weaken := by
  induction tele with
  | nil => exact TypedRename.id base
  | var type tail ih =>
      exact TypedRename.comp (Rename.Typed.weaken base (.var type))
        (ih (base.bindVar type))
  | tvar tail ih =>
      exact TypedRename.comp (Rename.Typed.weaken base .tvar)
        (ih base.bindTVar)
  | cvar source target tail ih =>
      exact TypedRename.comp
        (Rename.Typed.weaken base (.cvar source target))
        (ih (base.bindCVar source target))

private theorem duplicateVar_open
    (mapping : Rename (sig ,, .var) target) :
    ((((Rename.weaken .var).comp mapping).lift .var).asSubst).comp
        (Subst.openVar ((.var .here : Exp (sig ,, .var)).rename mapping)) =
      mapping.asSubst := by
  apply Subst.funext
  · intro index
    cases index <;> rfl
  · intro index
    cases index <;> rfl
  · intro index
    cases index <;> rfl

private theorem duplicateTVar_open
    (mapping : Rename (sig ,, .tvar) target) :
    ((((Rename.weaken .tvar).comp mapping).lift .tvar).asSubst).comp
        (Subst.openTVar ((.tvar .here : Ty (sig ,, .tvar)).rename mapping)) =
      mapping.asSubst := by
  apply Subst.funext
  · intro index
    cases index <;> rfl
  · intro index
    cases index <;> rfl
  · intro index
    cases index <;> rfl

private theorem duplicateCVar_open
    (mapping : Rename (sig ,, .cvar) target) :
    ((((Rename.weaken .cvar).comp mapping).lift .cvar).asSubst).comp
        (Subst.openCVar ((.cvar .here : Co (sig ,, .cvar)).rename mapping)) =
      mapping.asSubst := by
  apply Subst.funext
  · intro index
    cases index <;> rfl
  · intro index
    cases index <;> rfl
  · intro index
    cases index <;> rfl

private theorem duplicateVar_telescope
    (tail : Telescope (sig ,, .var)) :
    (tail.rename ((((Rename.weaken .var).comp tail.weaken).lift .var))).subst
        (Subst.openVar
          ((.var .here : Exp (sig ,, .var)).rename tail.weaken)) =
      tail.rename tail.weaken := by
  rw [tail.rename_asSubst, tail.subst_comp,
    duplicateVar_open, ← tail.rename_asSubst]

private theorem duplicateTVar_telescope
    (tail : Telescope (sig ,, .tvar)) :
    (tail.rename ((((Rename.weaken .tvar).comp tail.weaken).lift .tvar))).subst
        (Subst.openTVar
          ((.tvar .here : Ty (sig ,, .tvar)).rename tail.weaken)) =
      tail.rename tail.weaken := by
  rw [tail.rename_asSubst, tail.subst_comp,
    duplicateTVar_open, ← tail.rename_asSubst]

private theorem duplicateCVar_telescope
    (tail : Telescope (sig ,, .cvar)) :
    (tail.rename ((((Rename.weaken .cvar).comp tail.weaken).lift .cvar))).subst
        (Subst.openCVar
          ((.cvar .here : Co (sig ,, .cvar)).rename tail.weaken)) =
      tail.rename tail.weaken := by
  rw [tail.rename_asSubst, tail.subst_comp,
    duplicateCVar_open, ← tail.rename_asSubst]

namespace Args

/-- Canonical arguments selecting every freshly bound telescope field. This
is the identity instance used to repackage fields inside an unpack body. -/
noncomputable def identity : (tele : Telescope sig) -> (base : Ctx sig) ->
    Args (tele.context base) (tele.rename tele.weaken)
| .nil, _ => .nil
| .var type tail, base => by
    let argument : Exp tail.scope :=
      (.var .here : Exp (_ ,, .var)).rename tail.weaken
    have immediate :
        Exp.HasType (base.bindVar type) (.var .here) (type.weaken .var) :=
      .var .here
    have argumentTyping := immediate.rename
      (tail.weaken_typed (base.bindVar type))
    refine .var argument ?_ ?_
    · simpa only [argument, Ty.weaken, Telescope.weaken,
        Ty.rename_comp] using argumentTyping
    · simp only [Telescope.weaken]
      dsimp only [argument]
      exact (duplicateVar_telescope tail).symm ▸
        identity tail (base.bindVar type)
| .tvar tail, base => by
    let argument : Ty tail.scope :=
      (.tvar .here : Ty (_ ,, .tvar)).rename tail.weaken
    refine .tvar argument ?_
    simp only [Telescope.weaken]
    dsimp only [argument]
    exact (duplicateTVar_telescope tail).symm ▸
      identity tail base.bindTVar
| .cvar source target tail, base => by
    let argument : Co tail.scope :=
      (.cvar .here : Co (_ ,, .cvar)).rename tail.weaken
    have immediate :
        Co.HasType (base.bindCVar source target) (.cvar .here)
          (source.weaken .cvar) (target.weaken .cvar) :=
      .cvar .here
    have argumentTyping := immediate.rename
      (tail.weaken_typed (base.bindCVar source target))
    refine .cvar argument ?_ ?_
    · simpa only [argument, Ty.weaken, Telescope.weaken,
        Ty.rename_comp] using argumentTyping
    · simp only [Telescope.weaken]
      dsimp only [argument]
      exact (duplicateCVar_telescope tail).symm ▸
        identity tail (base.bindCVar source target)

private theorem liftRename_asSubst_heq
    (tele : Telescope source) (mapping : Rename source target) :
    HEq (tele.liftRename mapping).asSubst
      (tele.liftSubst mapping.asSubst) := by
  induction tele generalizing target with
  | nil => rfl
  | var type tail ih =>
      simp only [liftRename, liftSubst]
      exact HEq.trans (ih (mapping.lift .var))
        (liftSubst_congr_heq tail (Rename.asSubst_lift mapping))
  | tvar tail ih =>
      simp only [liftRename, liftSubst]
      exact HEq.trans (ih (mapping.lift .tvar))
        (liftSubst_congr_heq tail (Rename.asSubst_lift mapping))
  | cvar source target tail ih =>
      simp only [liftRename, liftSubst]
      exact HEq.trans (ih (mapping.lift .cvar))
        (liftSubst_congr_heq tail (Rename.asSubst_lift mapping))

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
  have composed := Subst.comp_heq rfl
    (congrArg Telescope.scope telescopeEqual)
    (congrArg Telescope.scope openedTelescopeEqual)
    (liftRename_asSubst_heq tele mapping) openedEqual
  exact HEq.trans composed
    (tele.liftSubst_comp_heq mapping.asSubst opening).symm

private theorem Args.substitution_transport_heq'
    {first second : Telescope sig} (equal : first = second)
    (arguments : Args base first) :
    HEq (equal ▸ arguments).substitution arguments.substitution := by
  cases equal
  rfl

/-- Reopening the canonically duplicated telescope fields cancels the
renaming into that duplicate scope. -/
theorem identity_liftRename_cancel
    (tele : Telescope sig) (base : Ctx sig) :
    (tele.liftRename tele.weaken).asSubst.comp
        (identity tele base).substitution = Subst.id := by
  induction tele with
  | nil => rfl
  | var type tail ih =>
      simp only [liftRename, weaken, identity, substitution, id_eq]
      let mapping := ((Rename.weaken .var).comp tail.weaken).lift .var
      let opening := Subst.openVar
        ((.var .here : Exp (_ ,, .var)).rename tail.weaken)
      let rest := (duplicateVar_telescope tail).symm ▸
        identity tail (base.bindVar type)
      have opened := liftRename_open_heq tail mapping opening
      have collapsed := liftSubst_congr_heq tail
        (duplicateVar_open tail.weaken)
      have ordinary := (liftRename_asSubst_heq tail tail.weaken).symm
      have firstPair := HEq.trans opened (HEq.trans collapsed ordinary)
      have restSubstitution := Args.substitution_transport_heq'
        (duplicateVar_telescope tail).symm
        (identity tail (base.bindVar type))
      have whole := Subst.comp_heq rfl
        (congrArg Telescope.scope (duplicateVar_telescope tail)) rfl
        firstPair restSubstitution
      calc
        _ = ((tail.liftRename mapping).asSubst.comp
              ((tail.rename mapping).liftSubst opening)).comp
            rest.substitution :=
          (Subst.comp_assoc (tail.liftRename mapping).asSubst
            ((tail.rename mapping).liftSubst opening)
            rest.substitution).symm
        _ = (tail.liftRename tail.weaken).asSubst.comp
            (identity tail (base.bindVar type)).substitution :=
          eq_of_heq whole
        _ = Subst.id := ih (base.bindVar type)
  | tvar tail ih =>
      simp only [liftRename, weaken, identity, substitution, id_eq]
      let mapping := ((Rename.weaken .tvar).comp tail.weaken).lift .tvar
      let opening := Subst.openTVar
        ((.tvar .here : Ty (_ ,, .tvar)).rename tail.weaken)
      let rest := (duplicateTVar_telescope tail).symm ▸
        identity tail base.bindTVar
      have opened := liftRename_open_heq tail mapping opening
      have collapsed := liftSubst_congr_heq tail
        (duplicateTVar_open tail.weaken)
      have ordinary := (liftRename_asSubst_heq tail tail.weaken).symm
      have firstPair := HEq.trans opened (HEq.trans collapsed ordinary)
      have restSubstitution := Args.substitution_transport_heq'
        (duplicateTVar_telescope tail).symm
        (identity tail base.bindTVar)
      have whole := Subst.comp_heq rfl
        (congrArg Telescope.scope (duplicateTVar_telescope tail)) rfl
        firstPair restSubstitution
      calc
        _ = ((tail.liftRename mapping).asSubst.comp
              ((tail.rename mapping).liftSubst opening)).comp
            rest.substitution :=
          (Subst.comp_assoc (tail.liftRename mapping).asSubst
            ((tail.rename mapping).liftSubst opening)
            rest.substitution).symm
        _ = (tail.liftRename tail.weaken).asSubst.comp
            (identity tail base.bindTVar).substitution :=
          eq_of_heq whole
        _ = Subst.id := ih base.bindTVar
  | cvar source target tail ih =>
      simp only [liftRename, weaken, identity, substitution, id_eq]
      let mapping := ((Rename.weaken .cvar).comp tail.weaken).lift .cvar
      let opening := Subst.openCVar
        ((.cvar .here : Co (_ ,, .cvar)).rename tail.weaken)
      let rest := (duplicateCVar_telescope tail).symm ▸
        identity tail (base.bindCVar source target)
      have opened := liftRename_open_heq tail mapping opening
      have collapsed := liftSubst_congr_heq tail
        (duplicateCVar_open tail.weaken)
      have ordinary := (liftRename_asSubst_heq tail tail.weaken).symm
      have firstPair := HEq.trans opened (HEq.trans collapsed ordinary)
      have restSubstitution := Args.substitution_transport_heq'
        (duplicateCVar_telescope tail).symm
        (identity tail (base.bindCVar source target))
      have whole := Subst.comp_heq rfl
        (congrArg Telescope.scope (duplicateCVar_telescope tail)) rfl
        firstPair restSubstitution
      calc
        _ = ((tail.liftRename mapping).asSubst.comp
              ((tail.rename mapping).liftSubst opening)).comp
            rest.substitution :=
          (Subst.comp_assoc (tail.liftRename mapping).asSubst
            ((tail.rename mapping).liftSubst opening)
            rest.substitution).symm
        _ = (tail.liftRename tail.weaken).asSubst.comp
            (identity tail (base.bindCVar source target)).substitution :=
          eq_of_heq whole
        _ = Subst.id := ih (base.bindCVar source target)

/-- Concatenate argument spines for dependent telescopes. The second spine is
indexed by the second telescope after the first spine has instantiated it. -/
noncomputable def append :
    {first : Telescope sig} -> (firstArgs : Args base first) ->
    (second : Telescope first.scope) ->
    (secondArgs : Args base (second.subst firstArgs.substitution)) ->
    Args base (first.append second)
  | _, .nil, second, secondArgs =>
      second.subst_id.symm ▸ secondArgs
  | _, @Args.var _ _ _ tail argument argumentTyping rest,
      second, secondArgs => by
      let opening := tail.liftSubst (Subst.openVar argument)
      let openedSecond := second.subst opening
      have openedArgs :
          Args base (openedSecond.subst rest.substitution) :=
        (second.subst_comp opening rest.substitution).symm ▸ secondArgs
      refine .var argument argumentTyping ?_
      exact (tail.append_subst second (Subst.openVar argument)).symm ▸
        rest.append openedSecond openedArgs
  | _, @Args.tvar _ _ tail argument rest, second, secondArgs => by
      let opening := tail.liftSubst (Subst.openTVar argument)
      let openedSecond := second.subst opening
      have openedArgs :
          Args base (openedSecond.subst rest.substitution) :=
        (second.subst_comp opening rest.substitution).symm ▸ secondArgs
      refine .tvar argument ?_
      exact (tail.append_subst second (Subst.openTVar argument)).symm ▸
        rest.append openedSecond openedArgs
  | _, @Args.cvar _ _ _ _ tail argument argumentTyping rest,
      second, secondArgs => by
      let opening := tail.liftSubst (Subst.openCVar argument)
      let openedSecond := second.subst opening
      have openedArgs :
          Args base (openedSecond.subst rest.substitution) :=
        (second.subst_comp opening rest.substitution).symm ▸ secondArgs
      refine .cvar argument argumentTyping ?_
      exact (tail.append_subst second (Subst.openCVar argument)).symm ▸
        rest.append openedSecond openedArgs

private theorem apply_transport
    {first second : Telescope sig} (equal : first = second)
    (arguments : Args base first) (function : Exp sig) :
    (equal ▸ arguments).apply function = arguments.apply function := by
  cases equal
  rfl

private theorem substitution_transport_heq
    {first second : Telescope sig} (equal : first = second)
    (arguments : Args base first) :
    HEq (equal ▸ arguments).substitution arguments.substitution := by
  cases equal
  rfl

/-- Concatenating argument spines is sequential universal application. -/
@[simp] theorem append_apply
    {first : Telescope sig} (firstArgs : Args base first)
    (second : Telescope first.scope)
    (secondArgs : Args base (second.subst firstArgs.substitution))
    (function : Exp sig) :
    (firstArgs.append second secondArgs).apply function =
      secondArgs.apply (firstArgs.apply function) := by
  induction firstArgs generalizing function with
  | nil =>
      simp only [append, Args.apply]
      exact apply_transport second.subst_id secondArgs function
  | @var type tail argument argumentTyping rest ih =>
      let opening := tail.liftSubst (Subst.openVar argument)
      let openedSecond := second.subst opening
      let openedArgs : Args base (openedSecond.subst rest.substitution) :=
        second.subst_comp opening rest.substitution |>.symm ▸ secondArgs
      change
        ((tail.append_subst second (Subst.openVar argument)).symm ▸
          rest.append openedSecond openedArgs).apply
            (.app function argument) = _
      calc
        _ = (rest.append openedSecond openedArgs).apply
              (.app function argument) :=
          apply_transport _ _ _
        _ = openedArgs.apply (rest.apply (.app function argument)) :=
          ih openedSecond openedArgs (.app function argument)
        _ = secondArgs.apply (rest.apply (.app function argument)) :=
          apply_transport _ secondArgs _
  | @tvar tail argument rest ih =>
      let opening := tail.liftSubst (Subst.openTVar argument)
      let openedSecond := second.subst opening
      let openedArgs : Args base (openedSecond.subst rest.substitution) :=
        second.subst_comp opening rest.substitution |>.symm ▸ secondArgs
      change
        ((tail.append_subst second (Subst.openTVar argument)).symm ▸
          rest.append openedSecond openedArgs).apply
            (.tapp function argument) = _
      calc
        _ = (rest.append openedSecond openedArgs).apply
              (.tapp function argument) :=
          apply_transport _ _ _
        _ = openedArgs.apply (rest.apply (.tapp function argument)) :=
          ih openedSecond openedArgs (.tapp function argument)
        _ = secondArgs.apply (rest.apply (.tapp function argument)) :=
          apply_transport _ secondArgs _
  | @cvar source target tail argument argumentTyping rest ih =>
      let opening := tail.liftSubst (Subst.openCVar argument)
      let openedSecond := second.subst opening
      let openedArgs : Args base (openedSecond.subst rest.substitution) :=
        second.subst_comp opening rest.substitution |>.symm ▸ secondArgs
      change
        ((tail.append_subst second (Subst.openCVar argument)).symm ▸
          rest.append openedSecond openedArgs).apply
            (.capp function argument) = _
      calc
        _ = (rest.append openedSecond openedArgs).apply
              (.capp function argument) :=
          apply_transport _ _ _
        _ = openedArgs.apply (rest.apply (.capp function argument)) :=
          ih openedSecond openedArgs (.capp function argument)
        _ = secondArgs.apply (rest.apply (.capp function argument)) :=
          apply_transport _ secondArgs _

/-- Instantiating through concatenated arguments is exactly ordinary
substitution by the concatenated argument substitution. -/
theorem append_instantiate_eq_subst
    {first : Telescope sig} (firstArgs : Args base first)
    (second : Telescope first.scope)
    (secondArgs : Args base (second.subst firstArgs.substitution))
    (result : Ty (first.append second).scope) :
    (firstArgs.append second secondArgs).instantiate result =
      result.subst (firstArgs.append second secondArgs).substitution :=
  instantiate_eq_subst _ _

private theorem append_nil_substitution_heq
    (second : Telescope sig)
    (secondArgs : Args base (second.subst Subst.id)) :
    HEq ((((Args.nil : Args base (.nil : Telescope sig))).append
        second secondArgs).substitution)
      ((second.liftSubst Subst.id).comp secondArgs.substitution) := by
  have left :
      HEq ((((Args.nil : Args base (.nil : Telescope sig))).append
          second secondArgs).substitution)
        secondArgs.substitution := by
    simp only [append]
    exact substitution_transport_heq _ secondArgs
  have scopeEqual : second.scope = (second.subst Subst.id).scope :=
    congrArg Telescope.scope second.subst_id.symm
  have liftedIdentity :
      HEq (second.liftSubst Subst.id)
        (Subst.id : Subst (second.subst Subst.id).scope
          (second.subst Subst.id).scope) :=
    HEq.trans (second.liftSubst_id_heq) (Subst.id_heq scopeEqual)
  have composed :
      HEq ((second.liftSubst Subst.id).comp secondArgs.substitution)
        ((Subst.id : Subst (second.subst Subst.id).scope
            (second.subst Subst.id).scope).comp
          secondArgs.substitution) :=
    Subst.comp_heq scopeEqual rfl rfl liftedIdentity (HEq.refl _)
  have right :
      HEq ((second.liftSubst Subst.id).comp secondArgs.substitution)
        secondArgs.substitution :=
    HEq.trans composed (heq_of_eq (Subst.id_comp _))
  exact HEq.trans left right.symm

/-- The substitution represented by concatenated arguments is the second
argument substitution after lifting the first substitution through the
dependent second telescope. -/
theorem append_substitution_heq
    {first : Telescope sig} (firstArgs : Args base first)
    (second : Telescope first.scope)
    (secondArgs : Args base (second.subst firstArgs.substitution)) :
    HEq (firstArgs.append second secondArgs).substitution
      ((second.liftSubst firstArgs.substitution).comp
        secondArgs.substitution) := by
  induction firstArgs with
  | nil => exact append_nil_substitution_heq second secondArgs
  | @var type tail argument argumentTyping rest ih =>
      let opening := tail.liftSubst (Subst.openVar argument)
      let openedSecond := second.subst opening
      let openedArgs : Args base (openedSecond.subst rest.substitution) :=
        second.subst_comp opening rest.substitution |>.symm ▸ secondArgs
      let combined := rest.append openedSecond openedArgs
      have firstLift :
          HEq ((tail.append second).liftSubst (Subst.openVar argument))
            (second.liftSubst opening) :=
        HEq.trans
          (heq_of_eq (tail.append_liftSubst second
            (Subst.openVar argument)))
          (cast_heq _ (second.liftSubst opening))
      have combinedSubstitution :
          HEq (((tail.append_subst second
              (Subst.openVar argument)).symm ▸ combined).substitution)
            ((openedSecond.liftSubst rest.substitution).comp
              openedArgs.substitution) :=
        HEq.trans (substitution_transport_heq _ combined)
          (ih openedSecond openedArgs)
      have expanded :
          HEq (((tail.append second).liftSubst
              (Subst.openVar argument)).comp
            (((tail.append_subst second
                (Subst.openVar argument)).symm ▸ combined).substitution))
            ((second.liftSubst opening).comp
              ((openedSecond.liftSubst rest.substitution).comp
                openedArgs.substitution)) :=
        Subst.comp_heq (tail.appendScopeEq second)
          (tail.appendSubstScopeEq second (Subst.openVar argument))
          rfl firstLift
          combinedSubstitution
      have associated :
          HEq ((second.liftSubst opening).comp
              ((openedSecond.liftSubst rest.substitution).comp
                openedArgs.substitution))
            (((second.liftSubst opening).comp
                (openedSecond.liftSubst rest.substitution)).comp
              openedArgs.substitution) :=
        heq_of_eq (Subst.comp_assoc _ _ _).symm
      have openedSubstitution :
          HEq openedArgs.substitution secondArgs.substitution :=
        substitution_transport_heq _ secondArgs
      have collapsed :
          HEq (((second.liftSubst opening).comp
                (openedSecond.liftSubst rest.substitution)).comp
              openedArgs.substitution)
            ((second.liftSubst (opening.comp rest.substitution)).comp
              secondArgs.substitution) :=
        Subst.comp_heq rfl (by
            exact congrArg Telescope.scope
              (second.subst_comp opening rest.substitution))
          rfl (second.liftSubst_comp_heq opening rest.substitution).symm
          openedSubstitution
      change HEq
        (((tail.append second).liftSubst (Subst.openVar argument)).comp
          (((tail.append_subst second
              (Subst.openVar argument)).symm ▸ combined).substitution)) _
      exact HEq.trans expanded (HEq.trans associated collapsed)
  | @tvar tail argument rest ih =>
      let opening := tail.liftSubst (Subst.openTVar argument)
      let openedSecond := second.subst opening
      let openedArgs : Args base (openedSecond.subst rest.substitution) :=
        second.subst_comp opening rest.substitution |>.symm ▸ secondArgs
      let combined := rest.append openedSecond openedArgs
      have firstLift :
          HEq ((tail.append second).liftSubst (Subst.openTVar argument))
            (second.liftSubst opening) :=
        HEq.trans
          (heq_of_eq (tail.append_liftSubst second
            (Subst.openTVar argument)))
          (cast_heq _ (second.liftSubst opening))
      have combinedSubstitution :
          HEq (((tail.append_subst second
              (Subst.openTVar argument)).symm ▸ combined).substitution)
            ((openedSecond.liftSubst rest.substitution).comp
              openedArgs.substitution) :=
        HEq.trans (substitution_transport_heq _ combined)
          (ih openedSecond openedArgs)
      have expanded :
          HEq (((tail.append second).liftSubst
              (Subst.openTVar argument)).comp
            (((tail.append_subst second
                (Subst.openTVar argument)).symm ▸ combined).substitution))
            ((second.liftSubst opening).comp
              ((openedSecond.liftSubst rest.substitution).comp
                openedArgs.substitution)) :=
        Subst.comp_heq (tail.appendScopeEq second)
          (tail.appendSubstScopeEq second (Subst.openTVar argument))
          rfl firstLift
          combinedSubstitution
      have associated :
          HEq ((second.liftSubst opening).comp
              ((openedSecond.liftSubst rest.substitution).comp
                openedArgs.substitution))
            (((second.liftSubst opening).comp
                (openedSecond.liftSubst rest.substitution)).comp
              openedArgs.substitution) :=
        heq_of_eq (Subst.comp_assoc _ _ _).symm
      have openedSubstitution :
          HEq openedArgs.substitution secondArgs.substitution :=
        substitution_transport_heq _ secondArgs
      have collapsed :
          HEq (((second.liftSubst opening).comp
                (openedSecond.liftSubst rest.substitution)).comp
              openedArgs.substitution)
            ((second.liftSubst (opening.comp rest.substitution)).comp
              secondArgs.substitution) :=
        Subst.comp_heq rfl (by
            exact congrArg Telescope.scope
              (second.subst_comp opening rest.substitution))
          rfl (second.liftSubst_comp_heq opening rest.substitution).symm
          openedSubstitution
      change HEq
        (((tail.append second).liftSubst (Subst.openTVar argument)).comp
          (((tail.append_subst second
              (Subst.openTVar argument)).symm ▸ combined).substitution)) _
      exact HEq.trans expanded (HEq.trans associated collapsed)
  | @cvar source target tail argument argumentTyping rest ih =>
      let opening := tail.liftSubst (Subst.openCVar argument)
      let openedSecond := second.subst opening
      let openedArgs : Args base (openedSecond.subst rest.substitution) :=
        second.subst_comp opening rest.substitution |>.symm ▸ secondArgs
      let combined := rest.append openedSecond openedArgs
      have firstLift :
          HEq ((tail.append second).liftSubst (Subst.openCVar argument))
            (second.liftSubst opening) :=
        HEq.trans
          (heq_of_eq (tail.append_liftSubst second
            (Subst.openCVar argument)))
          (cast_heq _ (second.liftSubst opening))
      have combinedSubstitution :
          HEq (((tail.append_subst second
              (Subst.openCVar argument)).symm ▸ combined).substitution)
            ((openedSecond.liftSubst rest.substitution).comp
              openedArgs.substitution) :=
        HEq.trans (substitution_transport_heq _ combined)
          (ih openedSecond openedArgs)
      have expanded :
          HEq (((tail.append second).liftSubst
              (Subst.openCVar argument)).comp
            (((tail.append_subst second
                (Subst.openCVar argument)).symm ▸ combined).substitution))
            ((second.liftSubst opening).comp
              ((openedSecond.liftSubst rest.substitution).comp
                openedArgs.substitution)) :=
        Subst.comp_heq (tail.appendScopeEq second)
          (tail.appendSubstScopeEq second (Subst.openCVar argument))
          rfl firstLift
          combinedSubstitution
      have associated :
          HEq ((second.liftSubst opening).comp
              ((openedSecond.liftSubst rest.substitution).comp
                openedArgs.substitution))
            (((second.liftSubst opening).comp
                (openedSecond.liftSubst rest.substitution)).comp
              openedArgs.substitution) :=
        heq_of_eq (Subst.comp_assoc _ _ _).symm
      have openedSubstitution :
          HEq openedArgs.substitution secondArgs.substitution :=
        substitution_transport_heq _ secondArgs
      have collapsed :
          HEq (((second.liftSubst opening).comp
                (openedSecond.liftSubst rest.substitution)).comp
              openedArgs.substitution)
            ((second.liftSubst (opening.comp rest.substitution)).comp
              secondArgs.substitution) :=
        Subst.comp_heq rfl (by
            exact congrArg Telescope.scope
              (second.subst_comp opening rest.substitution))
          rfl (second.liftSubst_comp_heq opening rest.substitution).symm
          openedSubstitution
      change HEq
        (((tail.append second).liftSubst (Subst.openCVar argument)).comp
          (((tail.append_subst second
              (Subst.openCVar argument)).symm ▸ combined).substitution)) _
      exact HEq.trans expanded (HEq.trans associated collapsed)

/-- The canonical simultaneous substitution for concatenated arguments,
transported back to the literal final scope of `Telescope.append`. -/
def appendSubstitution
    {first : Telescope sig} (firstArgs : Args base first)
    (second : Telescope first.scope)
    (secondArgs : Args base (second.subst firstArgs.substitution)) :
    Subst (first.append second).scope sig :=
  cast
    (congrArg (fun source => Subst source sig)
      (Telescope.appendScopeEq first second).symm)
    ((second.liftSubst firstArgs.substitution).comp
      secondArgs.substitution)

/-- Exact homogeneous form of `append_substitution_heq`. -/
theorem append_substitution
    {first : Telescope sig} (firstArgs : Args base first)
    (second : Telescope first.scope)
    (secondArgs : Args base (second.subst firstArgs.substitution)) :
    (firstArgs.append second secondArgs).substitution =
      appendSubstitution firstArgs second secondArgs := by
  apply eq_of_heq
  exact HEq.trans (append_substitution_heq firstArgs second secondArgs)
    (cast_heq _
      ((second.liftSubst firstArgs.substitution).comp
        secondArgs.substitution)).symm

/-- Exact instantiation law for concatenated dependent arguments. -/
theorem append_instantiate
    {first : Telescope sig} (firstArgs : Args base first)
    (second : Telescope first.scope)
    (secondArgs : Args base (second.subst firstArgs.substitution))
    (result : Ty (first.append second).scope) :
    (firstArgs.append second secondArgs).instantiate result =
      result.subst (appendSubstitution firstArgs second secondArgs) := by
  rw [instantiate_eq_subst, append_substitution]

end Args

end Telescope

end LambdaPToFCo.Direct
