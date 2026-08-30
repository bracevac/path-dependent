import Coercions.DOT.Captures.Acyclic.Syntax

/-!
# Acyclic object contexts

Contexts contain term variables only.  An object binding stores a source
type whose selected members can be exposed without adding a recursive self
assumption during object construction.
-/

namespace DOTCapture.Acyclic

/-- A source context aligned with its term-variable scope. -/
inductive Ctx : Scope → Type where
  | nil : Ctx 0
  | extend {scope : Scope} (outer : Ctx scope) (type : Ty scope) :
      Ctx (scope + 1)
deriving DecidableEq

namespace Ctx

/-- Add a term binding. -/
def extendTerm {scope : Scope} (context : Ctx scope) (type : Ty scope) :
    Ctx (scope + 1) :=
  .extend context type

/-- Total lookup, weakened into the complete ambient scope. -/
def lookup {scope : Scope} (context : Ctx scope) (index : Var scope) :
    Ty scope :=
  match context, index with
  | .extend _ type, .here => type.weaken
  | .extend outer _, .there older => (lookup outer older).weaken

/-- Remove the newest term binding. -/
def drop {scope : Scope} : Ctx (scope + 1) → Ctx scope
  | .extend outer _ => outer

/-- Return the unweakened type stored at the newest binding. -/
def newest {scope : Scope} : Ctx (scope + 1) → Ty scope
  | .extend _ type => type

@[simp]
theorem lookup_here {scope : Scope} (context : Ctx scope) (type : Ty scope) :
    (context.extendTerm type).lookup (.here : Var (scope + 1)) =
      type.weaken := rfl

@[simp]
theorem lookup_there {scope : Scope} (context : Ctx scope) (type : Ty scope)
    (index : Var scope) :
    (context.extendTerm type).lookup (.there index) =
      (context.lookup index).weaken := rfl

end Ctx

end DOTCapture.Acyclic
