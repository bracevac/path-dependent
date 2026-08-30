import Coercions.DOT.Captures.BinderOnly.Syntax

/-!
# Contexts for the binder-only DOT-with-captures source

Each context is intrinsically aligned with its heterogeneous signature.  Term
bindings carry source types and sorted static bindings carry true intervals.
-/

namespace DOTCapture.BinderOnly

/-- The payload associated with a source binder. -/
inductive Binding : (scope : Sig) → BinderKind → Type where
  | term {scope : Sig} (type : Ty scope) : Binding scope .term
  | static {scope : Sig} {sort : StaticSort}
      (interval : Interval sort scope) : Binding scope (.static sort)

deriving instance DecidableEq for Binding

namespace Binding

/-- Extract the type carried by a term binding. -/
def termType {scope : Sig} : Binding scope .term → Ty scope
  | .term type => type

/-- Extract the interval carried by a sorted static binding. -/
def staticInterval {scope : Sig} {sort : StaticSort} :
    Binding scope (.static sort) → Interval sort scope
  | .static interval => interval

/-- Rename a binding payload without changing its binder kind. -/
def rename {source target : Sig} {kind : BinderKind}
    (binding : Binding source kind) (rho : Rename source target) :
    Binding target kind :=
  match binding with
  | .term type => .term (type.rename rho)
  | .static interval => .static (interval.rename rho)

/-- Weaken a binding payload below one new binder. -/
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
  cases binding <;> simp [rename]

end Binding

/-- A source context aligned exactly with its heterogeneous signature. -/
inductive Ctx : Sig → Type where
  | nil : Ctx []
  | extend {scope : Sig} {kind : BinderKind} (outer : Ctx scope)
      (binding : Binding scope kind) : Ctx (scope ▹ kind)

deriving instance DecidableEq for Ctx

namespace Ctx

/-- Total kind-correct lookup, weakened into the complete ambient scope. -/
def lookup {scope : Sig} {kind : BinderKind} (context : Ctx scope)
    (index : BVar scope kind) : Binding scope kind :=
  match context, index with
  | .extend _ binding, .here => binding.weaken
  | .extend outer _, .there older => (lookup outer older).weaken

/-- Add a term variable. -/
def extendTerm {scope : Sig} (context : Ctx scope) (type : Ty scope) :
    Ctx (scope ▹ .term) :=
  .extend context (.term type)

/-- Add a sorted static variable governed by an interval. -/
def extendStatic {scope : Sig} {sort : StaticSort} (context : Ctx scope)
    (interval : Interval sort scope) : Ctx (scope ▹ .static sort) :=
  .extend context (.static interval)

/-- Look up the type of a term variable. -/
def lookupTerm {scope : Sig} (context : Ctx scope)
    (index : BVar scope .term) : Ty scope :=
  (context.lookup index).termType

/-- Look up the interval of a static variable of the requested sort. -/
def lookupStatic {scope : Sig} {sort : StaticSort} (context : Ctx scope)
    (index : BVar scope (.static sort)) : Interval sort scope :=
  (context.lookup index).staticInterval

/-- Remove the newest term binding. -/
def dropTerm {scope : Sig} : Ctx (scope ▹ .term) → Ctx scope
  | .extend outer (.term _) => outer

/-- Return the unweakened type stored at the newest term binding. -/
def newestTerm {scope : Sig} : Ctx (scope ▹ .term) → Ty scope
  | .extend _ (.term type) => type

/-- Remove the newest static binding. -/
def dropStatic {scope : Sig} {sort : StaticSort} :
    Ctx (scope ▹ .static sort) → Ctx scope
  | .extend outer (.static _) => outer

/-- Return the unweakened interval stored at the newest static binding. -/
def newestStatic {scope : Sig} {sort : StaticSort} :
    Ctx (scope ▹ .static sort) → Interval sort scope
  | .extend _ (.static interval) => interval

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
theorem lookup_extendTerm_here {scope : Sig} (context : Ctx scope)
    (type : Ty scope) :
    (context.extendTerm type).lookupTerm
      (.here : BVar (scope ▹ .term) .term) = type.weaken := rfl

@[simp]
theorem lookup_extendStatic_here {scope : Sig} {sort : StaticSort}
    (context : Ctx scope) (interval : Interval sort scope) :
    (context.extendStatic interval).lookupStatic
      (.here : BVar (scope ▹ .static sort) (.static sort)) =
      interval.weaken := rfl

@[simp]
theorem lookup_extendTerm_there {scope : Sig} {kind : BinderKind}
    (context : Ctx scope) (type : Ty scope) (index : BVar scope kind) :
    (context.extendTerm type).lookup (.there index) =
      (context.lookup index).weaken := rfl

@[simp]
theorem lookup_extendStatic_there {scope : Sig} {sort : StaticSort}
    {kind : BinderKind} (context : Ctx scope)
    (interval : Interval sort scope) (index : BVar scope kind) :
    (context.extendStatic interval).lookup (.there index) =
      (context.lookup index).weaken := rfl

end Ctx

end DOTCapture.BinderOnly
