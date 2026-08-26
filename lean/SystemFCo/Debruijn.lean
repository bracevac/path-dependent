/-!
Sort-indexed de Bruijn scopes for the explicit-coercion calculi.

A signature records the order and sort of every in-scope binder. Consequently
term, type, and coercion variables share one telescope without becoming
interchangeable.
-/

namespace SystemFCo

inductive Kind where
| var
| tvar
| cvar
deriving DecidableEq, Repr

abbrev Sig := List Kind

namespace Sig

/-- Extend a signature with one newest binder. -/
def extend (sig : Sig) (kind : Kind) : Sig := kind :: sig

end Sig

notation:65 sig " ,, " kind:66 => Sig.extend sig kind

/-- A variable of sort `kind` in the heterogeneous signature `sig`. -/
inductive BVar : Sig -> Kind -> Type where
| here : BVar (sig ,, kind) kind
| there : BVar sig kind -> BVar (sig ,, other) kind
deriving DecidableEq, Repr

/-- A sort-preserving renaming between heterogeneous signatures. -/
structure Rename (source target : Sig) where
  var : forall {kind}, BVar source kind -> BVar target kind

namespace Rename

def id : Rename sig sig where
  var := fun x => x

def comp (first : Rename sig sig') (second : Rename sig' sig'') :
    Rename sig sig'' where
  var := fun x => second.var (first.var x)

/-- Weaken every existing variable past one new binder of arbitrary sort. -/
def weaken (kind : Kind) : Rename sig (sig ,, kind) where
  var := BVar.there

/-- Lift a renaming through one binder of the same sort on both sides. -/
def lift (rename : Rename sig sig') (kind : Kind) :
    Rename (sig ,, kind) (sig' ,, kind) where
  var := fun x => match x with
    | .here => .here
    | .there x => .there (rename.var x)

@[simp] theorem id_var (x : BVar sig kind) : id.var x = x := rfl

@[simp] theorem comp_var
    (first : Rename sig sig') (second : Rename sig' sig'')
    (x : BVar sig kind) :
    (comp first second).var x = second.var (first.var x) := rfl

@[simp] theorem lift_here (rename : Rename sig sig') :
    (lift rename kind).var (.here : BVar (sig ,, kind) kind) = .here := rfl

@[simp] theorem lift_there
    (rename : Rename sig sig') (x : BVar sig other) :
    (lift rename kind).var (.there x) = .there (rename.var x) := rfl

end Rename

end SystemFCo
