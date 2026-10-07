import Coercions.Oopsla16.Syntax

/-!
# Annotated Oopsla16 terms

`ATm` is the version's term syntax `Oopsla16.Tm [] s` with two front end
annotations and nothing else: the self type of an object literal, if it was
written, and an ascription `(t : T)`.  Members carry no label, as in the
version, where a member's label is the length of the list below it.

Why the self type is carried.  `T_Obj` types the members of a literal under
the self type it concludes with (`Oopsla16.HasType.T_Obj`), so the typer
cannot read the self type off the members once it has started typing them.
A literal whose methods are all annotated has one anyway, and `selfOf?`
computes it.  A literal with a Curry style method needs it written, and
`Oopsla16.Tm.tobj` has no slot for it, so it lives here.

Why the ascription is carried.  The version has no ascription, but a program
often wants to state the type it should be checked at, for instance a module
at its module type.  The typer checks the ascribed term at the type and the
erasure drops it.

The store scope is the empty one throughout.  A source program mentions no
location of the runtime store, so every type and term here sits at
`Oopsla16.Ty [] s` and `Oopsla16.Tm [] s`, and the store scope never moves.

Every recursive definition is structural on a family at a variable index, so
the kernel reduces it.  Nothing in this module is part of the metatheory and
no definition here lives in the `Oopsla16` namespace.
-/

namespace Oopsla16Frontend

open FCdot (Kind Sig BVar)
open Oopsla16 (Lb Ty Tm Dm Dms)

/-! ## The syntax -/

mutual
/-- Terms of Oopsla16 at the empty store scope, with a literal's optional
self type and an ascription. -/
inductive ATm : Sig → Type where
  /-- A variable of the local scope. -/
  | var : BVar s .var → ATm s
  /-- An object literal, with its self type if one was written.  Both live
  under the self binder. -/
  | obj : Option (Ty [] (s,x)) → ADms (s,x) → ATm s
  /-- `t.l(u)`, a call at a positional label. -/
  | app : ATm s → Lb → ATm s → ATm s
  /-- `(t : T)`, front end only. -/
  | asc : ATm s → Ty [] s → ATm s
/-- A member of an annotated literal.  It carries no label. -/
inductive ADm : Sig → Type where
  /-- `def (x [: S]) [: U] = t`.  The result type and the body live under the
  parameter. -/
  | dfun : Option (Ty [] s) → Option (Ty [] (s,x)) → ATm (s,x) → ADm s
  /-- `type = T`. -/
  | dty : Ty [] s → ADm s
/-- A member list, newest member first.  The label of a member is the length
of the list below it. -/
inductive ADms : Sig → Type where
  | dnil : ADms s
  | dcons : ADm s → ADms s → ADms s
end

/-! ## Erasure to the version's syntax

The self type and the ascription are dropped and nothing else changes.  This
is the only bridge from the front end's term syntax to `Oopsla16.Tm`. -/

mutual
/-- Drop the annotations of a term. -/
def ATm.erase {s : Sig} (a : ATm s) : Tm [] s :=
  match a with
  | .var x => .tvar (.abs x)
  | .obj _ ds => .tobj ds.erase
  | .app t l u => .tapp t.erase l u.erase
  | .asc t _ => t.erase
termination_by structural a
/-- Drop the annotations of a member. -/
def ADm.erase {s : Sig} (d : ADm s) : Dm [] s :=
  match d with
  | .dfun S U t => .dfun S U t.erase
  | .dty T => .dty T
termination_by structural d
/-- Drop the annotations of a member list. -/
def ADms.erase {s : Sig} (ds : ADms s) : Dms [] s :=
  match ds with
  | .dnil => .dnil
  | .dcons d ds' => .dcons d.erase ds'.erase
termination_by structural ds
end

/-- The number of members, the label that one more member consed onto the
front would carry. -/
def ADms.length {s : Sig} (ds : ADms s) : Nat :=
  match ds with
  | .dnil => 0
  | .dcons _ ds' => ds'.length + 1
termination_by structural ds

/-- Erasure keeps the number of members, so a position read off an annotated
list is the label the version reads off its erasure. -/
theorem ADms.length_erase {s : Sig} : (ds : ADms s) → ds.erase.length = ds.length
  | .dnil => rfl
  | .dcons d ds' => by
      show (Dms.dcons d.erase ds'.erase).length = ds'.length + 1
      rw [Oopsla16.Dms.length_dcons, ADms.length_erase ds']

/-! ## The self type of a fully annotated literal

`D_Nil`, `D_Typ` and `D_Fun` (`Oopsla16.DmsHasType`) give a member list one
type, a right nested intersection ending in `⊤`, whose labels are the
positions.  When every method carries both annotations, that type is a
function of the list, and this is it.  A method with a missing annotation
leaves the type undetermined, and the answer is `none`.

No theorem comes with it.  The typer checks the members against whatever
self type it proposes, so a wrong proposal is a typing failure and never an
unsound derivation. -/

/-- The precise self type of a member list whose methods are all annotated. -/
def selfOf? {σ s : Sig} (ds : Dms σ s) : Option (Ty σ s) :=
  match ds with
  | .dnil => some .TTop
  | .dcons (.dty T) ds' => (selfOf? ds').map (.TAnd (.TTyp ds'.length T T))
  | .dcons (.dfun (some S) (some U) _) ds' => (selfOf? ds').map (.TAnd (.TFun ds'.length S U))
  | .dcons (.dfun _ _ _) _ => none
termination_by structural ds

/-! ## Sanity -/

/-- The empty list has the self type `⊤`, the `D_Nil` type. -/
example : selfOf? (Dms.dnil : Dms [] ([],x)) = some .TTop := by decide

/-- A type member at position `0`. -/
example : selfOf? (Dms.dcons (.dty .TBot) .dnil : Dms [] ([],x))
    = some (.TAnd (.TTyp 0 .TBot .TBot) .TTop) := by decide

/-- A Curry style method leaves the self type undetermined. -/
example : (selfOf? (Dms.dcons (.dfun none (some .TTop) (.tvar (.abs .here))) .dnil
    : Dms [] ([],x))).isSome = false := by decide

/-- Two members: the first written one is at position `1`. -/
example : selfOf? (Dms.dcons (.dfun (some .TTop) (some .TTop) (.tvar (.abs .here)))
      (.dcons (.dty .TTop) .dnil) : Dms [] ([],x))
    = some (.TAnd (.TFun 1 .TTop .TTop) (.TAnd (.TTyp 0 .TTop .TTop) .TTop)) := by decide

/-- An ascription and a written self type both erase.  The version's terms
derive no equality, so the comparison is by `rfl`. -/
example : (ATm.asc (.obj (some .TTop) (.dcons (.dty .TTop) .dnil)) .TTop : ATm []).erase
    = .tobj (.dcons (.dty .TTop) .dnil) := rfl

end Oopsla16Frontend
