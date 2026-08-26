import SystemFCoExt.Syntax

/-!
A single heterogeneous declaration telescope for terms, types, and coercions.

Each declaration is scoped over the preceding signature. Extending a context
therefore extends its signature with exactly the declaration's sort.
-/

namespace SystemFCoExt

inductive Binding : Sig -> Kind -> Type where
| var : Ty sig -> Binding sig .var
| tvar : Binding sig .tvar
| cvar : Ty sig -> Ty sig -> Binding sig .cvar
deriving DecidableEq, Repr

def Binding.rename : Binding sig kind -> Rename sig sig' -> Binding sig' kind
| .var T, rename => .var (T.rename rename)
| .tvar, _ => .tvar
| .cvar S T, rename => .cvar (S.rename rename) (T.rename rename)

def Binding.weaken (binding : Binding sig kind) (newKind : Kind) :
    Binding (sig ,, newKind) kind :=
  binding.rename (Rename.weaken newKind)

/-- A well-scoped heterogeneous telescope of declarations. -/
inductive Ctx : Sig -> Type where
| empty : Ctx []
| extend : Ctx sig -> Binding sig kind -> Ctx (sig ,, kind)
deriving DecidableEq, Repr

namespace Ctx

def bindVar (context : Ctx sig) (T : Ty sig) : Ctx (sig ,, .var) :=
  .extend context (.var T)

def bindTVar (context : Ctx sig) : Ctx (sig ,, .tvar) :=
  .extend context .tvar

def bindCVar (context : Ctx sig) (S T : Ty sig) : Ctx (sig ,, .cvar) :=
  .extend context (.cvar S T)

/--
Evidence that a variable denotes a declaration in the telescope.

The declaration carried by the evidence is always scoped over the *complete*
current signature. In particular, crossing a later binder weakens every type
inside the declaration. Keeping lookup as data, rather than computing it, lets
later typing and coercion derivations retain the exact lookup witness.
-/
inductive Lookup : {sig : Sig} -> Ctx sig ->
    {kind : Kind} -> BVar sig kind -> Binding sig kind -> Type where
| here {sig kind} {context : Ctx sig} {binding : Binding sig kind} :
    Lookup (.extend context binding)
      (.here : BVar (sig ,, kind) kind)
      (binding.weaken kind)
| there {sig kind newKind} {context : Ctx sig}
    {index : BVar sig kind} {found : Binding sig kind}
    {newBinding : Binding sig newKind} :
    Lookup context index found ->
    Lookup (.extend context newBinding) (.there index)
      (found.weaken newKind)

/-- Ordinary-variable lookup, exposing the variable's type. -/
abbrev VarLookup (context : Ctx sig) (index : BVar sig .var)
    (T : Ty sig) : Type :=
  Lookup context index (.var T)

/-- Type-variable membership (there is no payload beyond its sort). -/
abbrev TVarLookup (context : Ctx sig) (index : BVar sig .tvar) : Type :=
  Lookup context index .tvar

/-- Coercion-variable lookup, exposing its directed source and target. -/
abbrev CVarLookup (context : Ctx sig) (index : BVar sig .cvar)
    (S T : Ty sig) : Type :=
  Lookup context index (.cvar S T)

end Ctx

end SystemFCoExt
