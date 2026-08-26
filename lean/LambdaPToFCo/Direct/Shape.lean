import LambdaPToFCo.Direct.Package

/-!
# Stable and opaque target value shapes

Source type selections do not always expose a structural package plan.  An
abstract interval member reveals only one hidden target type, whereas a
proper source type compiled from its formation derivation has a complete
Church-package plan.  `Shape` is the small target-only sum of those cases.

A shape always supplies an input type and a telescope in which one value can
be inspected.  Stable values open their package plan.  Opaque values merely
bind the raw value as one ordinary term.  This distinction prevents an
abstract selected type from acquiring a fabricated identity wrapper.
-/

namespace LambdaPToFCo.Direct

open SystemFCo

/-- The structural information currently available for one target value. -/
inductive Shape (sig : Sig) : Type where
| stable (plan : Package.Plan sig)
| opaque (type : Ty sig)

namespace Shape

/-- Public target type accepted by a value of this shape. -/
def inputTy : Shape sig -> Ty sig
| .stable plan => plan.inputTy
| .opaque type => type

/-- Binders exposed while inspecting a value.

Stable packages expose their complete mixed telescope.  An opaque value can
only be named by one ordinary term binder. -/
def binders : Shape sig -> Telescope sig
| .stable plan => plan.telescope
| .opaque type => .var type .nil

/-- Scope after exposing the available value interface. -/
def scope (shape : Shape sig) : Sig :=
  shape.binders.scope

/-- Target context after exposing the available value interface. -/
def context (shape : Shape sig) (base : Ctx sig) : Ctx shape.scope :=
  shape.binders.context base

/-- Reindex a value shape. -/
def rename : Shape source -> Rename source target -> Shape target
| .stable plan, mapping => .stable (plan.rename mapping)
| .opaque type, mapping => .opaque (type.rename mapping)

/-- Substitute through a value shape. -/
def subst : Shape source -> Subst source target -> Shape target
| .stable plan, substitution => .stable (plan.subst substitution)
| .opaque type, substitution => .opaque (type.subst substitution)

@[simp] theorem inputTy_rename (shape : Shape source)
    (mapping : Rename source target) :
    shape.inputTy.rename mapping = (shape.rename mapping).inputTy := by
  cases shape <;> simp only [rename, inputTy,
    Package.Plan.inputTy_rename]

@[simp] theorem inputTy_subst (shape : Shape source)
    (substitution : Subst source target) :
    shape.inputTy.subst substitution =
      (shape.subst substitution).inputTy := by
  cases shape <;> simp only [subst, inputTy,
    Package.Plan.inputTy_subst]

@[simp] theorem binders_rename (shape : Shape source)
    (mapping : Rename source target) :
    shape.binders.rename mapping = (shape.rename mapping).binders := by
  cases shape <;> rfl

@[simp] theorem binders_subst (shape : Shape source)
    (substitution : Subst source target) :
    shape.binders.subst substitution = (shape.subst substitution).binders := by
  cases shape <;> rfl

@[simp] theorem rename_id (shape : Shape sig) :
    shape.rename Rename.id = shape := by
  cases shape <;> simp only [rename, Package.Plan.rename_id, Ty.rename_id]

theorem rename_comp (shape : Shape source)
    (first : Rename source middle) (second : Rename middle target) :
    (shape.rename first).rename second =
      shape.rename (first.comp second) := by
  cases shape <;> simp only [rename, Package.Plan.rename_comp,
    Ty.rename_comp]

@[simp] theorem subst_id (shape : Shape sig) :
    shape.subst Subst.id = shape := by
  cases shape <;> simp only [subst, Package.Plan.subst_id, Ty.subst_id]

theorem subst_comp (shape : Shape source)
    (first : Subst source middle) (second : Subst middle target) :
    (shape.subst first).subst second =
      shape.subst (first.comp second) := by
  cases shape <;> simp only [subst, Package.Plan.subst_comp,
    Ty.subst_comp]

/-- Reindexing induced between the two opened shape scopes. -/
def liftRename (shape : Shape source)
    (mapping : Rename source target) :
    Rename shape.scope (shape.rename mapping).scope := by
  change Rename shape.binders.scope (shape.rename mapping).binders.scope
  rw [<- binders_rename]
  exact shape.binders.liftRename mapping

/-- Substitution induced between the two opened shape scopes. -/
def liftSubst (shape : Shape source)
    (substitution : Subst source target) :
    Subst shape.scope (shape.subst substitution).scope := by
  change Subst shape.binders.scope (shape.subst substitution).binders.scope
  rw [<- binders_subst]
  exact shape.binders.liftSubst substitution

/-- Typed base renamings lift through every binder exposed by a shape. -/
noncomputable def liftRename_typed
    (shape : Shape source)
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {mapping : Rename source target}
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Rename.Typed (shape.context sourceContext)
      ((shape.rename mapping).context targetContext)
      (shape.liftRename mapping) := by
  cases shape with
  | stable plan => exact plan.telescope.liftRename_typed typed
  | «opaque» type =>
      exact (Telescope.var type Telescope.nil).liftRename_typed typed

/-- Typed base substitutions lift through every binder exposed by a shape. -/
noncomputable def liftSubst_typed
    (shape : Shape source)
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {substitution : Subst source target}
    (typed : Subst.Typed sourceContext targetContext substitution) :
    Subst.Typed (shape.context sourceContext)
      ((shape.subst substitution).context targetContext)
      (shape.liftSubst substitution) := by
  cases shape with
  | stable plan => exact plan.telescope.liftSubst_typed typed
  | «opaque» type =>
      exact (Telescope.var type Telescope.nil).liftSubst_typed typed

/-- Type of the directly usable value exposed in the shape scope. -/
def valueTy : (shape : Shape sig) -> Ty shape.scope
| .stable plan => plan.identityTy
| .opaque type => type.weaken .var

/-- Directly usable value exposed in the shape scope.

For a stable package this is the hidden payload.  For an opaque shape it is
the sole raw term binder. -/
def value : (shape : Shape sig) -> Exp shape.scope
| .stable plan => plan.payload
| .opaque _ => .var .here

/-- The directly usable value has the shape's opened value type. -/
noncomputable def value_hasType (shape : Shape sig) (base : Ctx sig) :
    Exp.HasType (shape.context base) shape.value shape.valueTy := by
  cases shape with
  | stable plan => exact plan.payload_hasType base
  | «opaque» type => exact .var Ctx.Lookup.here

theorem valueTy_rename (shape : Shape source)
    (mapping : Rename source target) :
    shape.valueTy.rename (shape.liftRename mapping) =
      (shape.rename mapping).valueTy := by
  cases shape with
  | stable plan => exact plan.identityTy_rename mapping
  | «opaque» type =>
      simpa only [valueTy, liftRename, scope, binders, rename] using
        type.weaken_rename_comm mapping

theorem value_rename (shape : Shape source)
    (mapping : Rename source target) :
    shape.value.rename (shape.liftRename mapping) =
      (shape.rename mapping).value := by
  cases shape with
  | stable plan => exact plan.payload_rename mapping
  | «opaque» type => rfl

theorem valueTy_subst (shape : Shape source)
    (substitution : Subst source target) :
    shape.valueTy.subst (shape.liftSubst substitution) =
      (shape.subst substitution).valueTy := by
  cases shape with
  | stable plan => exact plan.identityTy_subst substitution
  | «opaque» type =>
      simpa only [valueTy, liftSubst, scope, binders, subst] using
        (type.weaken_subst_comm_base substitution).symm

theorem value_subst (shape : Shape source)
    (substitution : Subst source target) :
    shape.value.subst (shape.liftSubst substitution) =
      (shape.subst substitution).value := by
  cases shape with
  | stable plan => exact plan.payload_subst substitution
  | «opaque» type => rfl

/-- A typed, already-open view of one value shape. -/
structure Interface (base : Ctx sig) (shape : Shape sig) : Type where
  arguments : Telescope.Args base shape.binders

namespace Interface

/-- Whether every term argument exposed by the interface is a value. -/
def AllValues {shape : Shape sig} {base : Ctx sig}
    (interface : Interface base shape) : Prop :=
  interface.arguments.AllValues

/-- Reindex an already-open interface. -/
noncomputable def rename
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target} {shape : Shape source}
    (interface : Interface sourceContext shape)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Interface targetContext (shape.rename mapping) where
  arguments := by
    rw [<- binders_rename]
    exact interface.arguments.rename mapping typed

/-- The canonical interface available inside a shape elimination body. -/
noncomputable def canonical (base : Ctx sig) (shape : Shape sig) :
    Interface (shape.context base)
      (shape.rename shape.binders.weaken) where
  arguments := by
    rw [<- binders_rename]
    exact Telescope.Args.identity shape.binders base

/-- The sole raw argument of an opaque interface. -/
private def opaqueArgument {base : Ctx sig} {type : Ty sig} :
    Telescope.Args base (.var type .nil) -> Exp sig
| .var argument _ _ => argument

private noncomputable def opaqueArgument_hasType
    {base : Ctx sig} {type : Ty sig}
    (arguments : Telescope.Args base (.var type .nil)) :
    Exp.HasType base (opaqueArgument arguments) type := by
  cases arguments with
  | var argument argumentTyping rest => exact argumentTyping

private theorem opaqueArgument_isValue
    {base : Ctx sig} {type : Ty sig}
    (arguments : Telescope.Args base (.var type .nil))
    (allValues : arguments.AllValues) :
    Exp.IsValue (opaqueArgument arguments) := by
  cases arguments with
  | var argument argumentTyping rest => exact allValues.1

/-- Reclose a typed argument spine at the shape's public input type. -/
private noncomputable def packageArguments (base : Ctx sig) :
    (shape : Shape sig) -> Telescope.Args base shape.binders -> Exp sig
  | .stable plan, arguments => plan.pack arguments
  | .opaque _, arguments => opaqueArgument arguments

/-- Reclose an opened interface at the shape's public input type. -/
noncomputable def package {shape : Shape sig} {base : Ctx sig}
    (interface : Interface base shape) : Exp sig :=
  packageArguments base shape interface.arguments

/-- Substitution induced by an opened interface.

Stable interfaces substitute every mixed package field.  Opaque interfaces
substitute their sole raw value binder directly. -/
noncomputable def substitution {shape : Shape sig} {base : Ctx sig}
    (interface : Interface base shape) : Subst shape.scope sig :=
  match shape with
  | .stable _ => interface.arguments.substitution
  | .opaque _ => Subst.openVar interface.package

/-- Recloses exactly at `Shape.inputTy`. -/
noncomputable def package_hasType
    {shape : Shape sig} {base : Ctx sig}
    (interface : Interface base shape) :
    Exp.HasType base interface.package shape.inputTy := by
  cases shape with
  | stable plan =>
      cases interface with
      | mk arguments => exact plan.pack_hasType arguments
  | «opaque» type =>
      cases interface with
      | mk arguments =>
          exact opaqueArgument_hasType arguments

end Interface

/-- Inspect a value and close the inspection body again.

Stable packages use Church elimination.  Opaque values use one ordinary
lambda/application, because their binder telescope contains only that value.
-/
def eliminate (shape : Shape sig) (package : Exp sig)
    (answer : Ty sig) (body : Exp shape.scope) : Exp sig :=
  match shape with
  | .stable plan => plan.unpack package answer body
  | .opaque type => Adapter.apply (Adapter.ofBody type body) package

/-- Extrinsic typing for shape elimination. -/
noncomputable def eliminate_hasType
    {shape : Shape sig} {base : Ctx sig}
    {package : Exp sig} {answer : Ty sig} {body : Exp shape.scope}
    (packageTyping : Exp.HasType base package shape.inputTy)
    (bodyTyping : Exp.HasType (shape.context base) body
      (answer.rename shape.binders.weaken)) :
    Exp.HasType base (shape.eliminate package answer body) answer := by
  cases shape with
  | stable plan =>
      exact plan.unpack_hasType packageTyping bodyTyping
  | «opaque» type =>
      exact Adapter.apply_hasType
        (Adapter.ofBody_hasType bodyTyping) packageTyping

/-- Eliminating a value rebuilt from an interface exposes exactly the
interface substitution. -/
theorem eliminate_interface_steps
    {shape : Shape sig} {base : Ctx sig}
    (interface : Interface base shape)
    (argumentsValue : interface.AllValues)
    (answer : Ty sig) (body : Exp shape.scope) :
    Exp.Steps
      (shape.eliminate interface.package answer body)
      (body.subst interface.substitution) := by
  cases shape with
  | stable plan =>
      cases interface with
      | mk arguments =>
          exact plan.telescope.unpack_pack_steps_of_ne_nil
            arguments argumentsValue answer body (by
              intro impossible
              cases impossible)
  | «opaque» type =>
      cases interface with
      | mk arguments =>
          exact Exp.Steps.single
            (Adapter.ofBody_apply_step (source := type) (body := body)
              (argument := Interface.opaqueArgument arguments)
              (Interface.opaqueArgument_isValue arguments argumentsValue))

end Shape

end LambdaPToFCo.Direct
