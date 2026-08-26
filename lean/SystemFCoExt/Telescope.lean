import SystemFCoExt.Typing

namespace SystemFCoExt

namespace Ty

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

@[simp] theorem closeVar_weaken (body : Ty (sig ,, .var)) :
    body.closeVar.weaken .var = body := by
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
    body.subst (Subst.openVar argument) = body.closeVar := by
  unfold closeVar
  apply subst_eq_of_tvar
  intro index
  cases index with
  | there index => rfl

theorem closeVar_rename (body : Ty (source ,, .var))
    (mapping : Rename source target) :
    body.closeVar.rename mapping =
      (body.rename (mapping.lift .var)).closeVar := by
  unfold closeVar
  rw [body.rename_subst_comm
    (Subst.openVarRenameComm (closeVarDummy source) mapping)]
  rfl

theorem closeVar_subst (body : Ty (source ,, .var))
    (substitution : Subst source target) :
    body.closeVar.subst substitution =
      (body.subst (substitution.lift .var)).closeVar := by
  unfold closeVar
  rw [Ty.subst_comp, Ty.subst_comp]
  apply subst_eq_of_tvar
  intro index
  cases index with
  | there index =>
      exact (substitution.tvar index).weaken_subst_cancel _
        (Subst.weakenAsSubst_comp_openVar _) |>.symm

end Ty

namespace Subst.Typed

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

end Subst.Typed

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
    .arrow type (tail.forallTy result).closeVar
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
      rw [Ty.closeVar_rename, ih]
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
      rw [Ty.closeVar_subst, ih]
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
      rw [Ty.closeVar_weaken]
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
  | nil => exact Subst.Typed.id base
  | @var type tail argument argumentTyping rest ih =>
      exact (tail.liftSubst_typed
        (Subst.Typed.openVar argumentTyping)).comp ih
  | @tvar tail argument rest ih =>
      exact (tail.liftSubst_typed
        (Subst.Typed.openTVar base argument)).comp ih
  | @cvar source target tail argument argumentTyping rest ih =>
      exact (tail.liftSubst_typed
        (Subst.Typed.openCVar argumentTyping)).comp ih

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
      rw [← Ty.closeVar_open] at applied
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

end SystemFCoExt
