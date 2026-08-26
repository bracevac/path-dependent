import SystemFCoExt.Telescope

namespace SystemFCoExt

namespace Rename.Typed

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

end Rename.Typed

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
  | nil => exact Rename.Typed.id base
  | var type tail ih =>
      exact (Rename.Typed.weaken base (.var type)).comp
        (ih (base.bindVar type))
  | tvar tail ih =>
      exact (Rename.Typed.weaken base .tvar).comp
        (ih base.bindTVar)
  | cvar source target tail ih =>
      exact (Rename.Typed.weaken base (.cvar source target)).comp
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
end SystemFCoExt
