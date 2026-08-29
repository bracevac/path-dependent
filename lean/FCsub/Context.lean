import FCsub.Syntax

/-!
# FCsub contexts and telescope opening

Contexts contain only kernel binders.  In particular there is no DOT member
or path binding.  `extendTelescope` first allocates every abstract type name,
then adds the directed constraints in telescope order.  `extendPayload` adds
the computational payload only after that complete static scope.
-/

namespace FCsub

/-- The payload attached to each kind of FCsub binder. -/
inductive Binding : (scope : Sig) → BinderKind → Type where
  | term {scope : Sig} (type : Ty scope) : Binding scope .term
  | typeVar {scope : Sig} : Binding scope .type
  | equality {scope : Sig} (left right : Ty scope) :
      Binding scope (.evidence .equality)
  | inclusion {scope : Sig} (source target : Ty scope) :
      Binding scope (.evidence .inclusion)

namespace Binding

def rename {source target : Sig} {kind : BinderKind}
    (binding : Binding source kind) (rho : Rename source target) :
    Binding target kind :=
  match binding with
  | .term type => .term (type.rename rho)
  | .typeVar => .typeVar
  | .equality left right => .equality (left.rename rho) (right.rename rho)
  | .inclusion source target =>
      .inclusion (source.rename rho) (target.rename rho)

def weaken {scope : Sig} {kind newest : BinderKind}
    (binding : Binding scope kind) : Binding (scope ▹ newest) kind :=
  binding.rename Rename.succ

@[simp]
theorem rename_id {scope : Sig} {kind : BinderKind}
    (binding : Binding scope kind) :
    binding.rename Rename.id = binding := by
  cases binding <;> simp [rename]

@[simp]
theorem rename_comp {first second third : Sig} {kind : BinderKind}
    (binding : Binding first kind) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (binding.rename rho₁).rename rho₂ =
      binding.rename (rho₁.comp rho₂) := by
  cases binding <;> simp [rename, Ty.rename_comp]

end Binding

/-- A well-shaped heterogeneous FCsub context. -/
inductive Ctx : Sig → Type where
  | nil : Ctx []
  | extend {scope : Sig} {kind : BinderKind} (outer : Ctx scope)
      (binding : Binding scope kind) : Ctx (scope ▹ kind)

namespace Ctx

/-- Kind-correct lookup, weakened into the full ambient scope. -/
def lookup {scope : Sig} {kind : BinderKind} (context : Ctx scope)
    (index : BVar scope kind) : Binding scope kind :=
  match context, index with
  | .extend _ binding, .here => binding.weaken
  | .extend outer _, .there older => (lookup outer older).weaken

def extendTerm {scope : Sig} (context : Ctx scope) (type : Ty scope) :
    Ctx (scope ▹ .term) :=
  .extend context (.term type)

def extendType {scope : Sig} (context : Ctx scope) :
    Ctx (scope ▹ .type) :=
  .extend context .typeVar

def extendEquality {scope : Sig} (context : Ctx scope)
    (left right : Ty scope) : Ctx (scope ▹ .evidence .equality) :=
  .extend context (.equality left right)

def extendInclusion {scope : Sig} (context : Ctx scope)
    (source target : Ty scope) : Ctx (scope ▹ .evidence .inclusion) :=
  .extend context (.inclusion source target)

/-- Allocate several abstract type names before introducing constraints. -/
def extendTypes {scope : Sig} (context : Ctx scope) :
    (names : Nat) → Ctx (TypeScope scope names)
  | 0 => context
  | names + 1 => (extendTypes context names).extendType

/-- Add a telescope's constraints to a context in which all of its abstract
names have already been allocated. -/
def extendConstraints {scope : Sig} {names constraints : Nat}
    (namesContext : Ctx (TypeScope scope names))
    (telescope : Telescope scope names constraints) :
    Ctx (StaticScope scope names constraints) :=
  match telescope with
  | .nil => namesContext
  | @Telescope.snoc _ _ previousCount initial (.inclusion source target) =>
      let previous := extendConstraints namesContext initial
      let weaken := Rename.weakenN (.evidence .inclusion) previousCount
      previous.extendInclusion (source.rename weaken) (target.rename weaken)

/-- Open all static entries of a names-first telescope. -/
def extendTelescope {scope : Sig} {names constraints : Nat}
    (context : Ctx scope) (telescope : Telescope scope names constraints) :
    Ctx (StaticScope scope names constraints) :=
  extendConstraints (context.extendTypes names) telescope

/-- Open a package and add its computational payload after all static entries. -/
def extendPayload {scope : Sig} {names constraints : Nat}
    (context : Ctx scope) (telescope : Telescope scope names constraints)
    (payloadType : Ty (StaticScope scope names constraints)) :
    Ctx (PayloadScope scope names constraints) :=
  (context.extendTelescope telescope).extendTerm payloadType

/-- Allocate one fresh type name and its private equality to a witness. -/
def extendNewtype {scope : Sig} (context : Ctx scope) (witness : Ty scope) :
    Ctx (NewtypeScope scope) :=
  let withType := context.extendType
  let name : Ty (scope ▹ .type) := .tvar .here
  withType.extendEquality name witness.weaken

@[simp]
theorem lookup_here {scope : Sig} {kind : BinderKind}
    (context : Ctx scope) (binding : Binding scope kind) :
    (context.extend binding).lookup
      (.here : BVar (scope ▹ kind) kind) = binding.weaken := rfl

@[simp]
theorem lookup_there {scope : Sig} {kind olderKind : BinderKind}
    (context : Ctx scope) (binding : Binding scope kind)
    (index : BVar scope olderKind) :
    (context.extend binding).lookup (.there index) =
      (context.lookup index).weaken := rfl

@[simp]
theorem extendTypes_zero {scope : Sig} (context : Ctx scope) :
    context.extendTypes 0 = context := rfl

@[simp]
theorem extendTypes_succ {scope : Sig} (context : Ctx scope) (names : Nat) :
    context.extendTypes (names + 1) =
      (context.extendTypes names).extendType := rfl

end Ctx

end FCsub
