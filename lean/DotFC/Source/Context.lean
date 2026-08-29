import DotFC.Source.Syntax

/-!
# Acyclic source contexts

A source context is a telescope of term bindings.  The signature index records
the same binders, and a lookup returns the declared type renamed into the full
current signature.  Consequently older declarations cannot mention newer
variables.
-/

namespace DotFC.Source

/-- An intrinsically scoped, acyclic source typing context. -/
inductive Ctx : Sig → Type where
  | nil : Ctx []
  | snoc {s : Sig} (context : Ctx s) (type : Ty s) : Ctx (s ▹ .term)

namespace Ctx

/-- The number of term bindings in a source context. -/
def length {s : Sig} : Ctx s → Nat
  | .nil => 0
  | .snoc context _ => context.length + 1

end Ctx

/-- Proof-relevant lookup.  A declaration is weakened across every binding
newer than itself, so the resulting type is indexed by the current signature. -/
inductive Lookup : {s : Sig} → Ctx s → BVar s .term → Ty s → Type where
  | here {s : Sig} {context : Ctx s} {type : Ty s} :
      Lookup (.snoc context type) .here type.weaken
  | there {s : Sig} {context : Ctx s} {bound type : Ty s}
      {x : BVar s .term} (lookup : Lookup context x type) :
      Lookup (.snoc context bound) (.there x) type.weaken

namespace Lookup

/-- Weaken a lookup below one newer term binding. -/
def weaken {s : Sig} {context : Ctx s} {x : BVar s .term} {type bound : Ty s}
    (lookup : Lookup context x type) :
    Lookup (context.snoc bound) (.there x) type.weaken :=
  .there lookup

/-- The most recent context entry. -/
def newest {s : Sig} {context : Ctx s} {type : Ty s} :
    Lookup (context.snoc type) .here type.weaken :=
  .here

end Lookup

end DotFC.Source
