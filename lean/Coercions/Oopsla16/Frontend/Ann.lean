import Coercions.Oopsla16.Syntax

/-!
# Annotated Oopsla16 terms

`ATm` is `Oopsla16.Tm [] s` plus two annotations the calculus does not keep.

- The self type of an object literal, when it is written.  `T_Obj` types the
  members under the self type it concludes with, so a literal with a Curry
  style method needs it written, and `Tm.tobj` has no slot for it.  A literal
  whose methods are all annotated gets one from `selfOf?`.
- An ascription `(t : T)`, a point where the typer checks at a stated type.

Members carry no label.  As in the calculus, a member's label is the length of
the list below it.  The store scope is empty throughout, since a source
program names no store location.

Every definition is structural, so `decide` and `rfl` reduce it.  Nothing here
is part of the metatheory.
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

/-! ## Erasure

The only bridge from `ATm` to `Oopsla16.Tm`.  It drops the self type and the
ascription. -/

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

/-- The number of members, the label of a member consed onto the front. -/
def ADms.length {s : Sig} (ds : ADms s) : Nat :=
  match ds with
  | .dnil => 0
  | .dcons _ ds' => ds'.length + 1
termination_by structural ds

/-- Erasure keeps the number of members. -/
theorem ADms.length_erase {s : Sig} : (ds : ADms s) → ds.erase.length = ds.length
  | .dnil => rfl
  | .dcons d ds' => by
      show (Dms.dcons d.erase ds'.erase).length = ds'.length + 1
      rw [Oopsla16.Dms.length_dcons, ADms.length_erase ds']

/-! ## The self type of a fully annotated literal

When every method carries both annotations, `D_Nil`, `D_Typ` and `D_Fun`
(`Oopsla16.DmsHasType`) give a member list one type: a right nested
intersection ending in `⊤`, with the positions as labels.  `selfOf?` computes
it and answers `none` when an annotation is missing.  A wrong proposal only
fails to type, since the typer checks the members against it. -/

/-- The precise self type of a member list whose methods are all annotated. -/
def selfOf? {σ s : Sig} (ds : Dms σ s) : Option (Ty σ s) :=
  match ds with
  | .dnil => some .TTop
  | .dcons (.dty T) ds' => (selfOf? ds').map (.TAnd (.TTyp ds'.length T T))
  | .dcons (.dfun (some S) (some U) _) ds' => (selfOf? ds').map (.TAnd (.TFun ds'.length S U))
  | .dcons (.dfun _ _ _) _ => none
termination_by structural ds

/-! ## Sanity -/

/-- The empty list has the self type `⊤`. -/
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

/-- An ascription and a written self type both erase. -/
example : (ATm.asc (.obj (some .TTop) (.dcons (.dty .TTop) .dnil)) .TTop : ATm []).erase
    = .tobj (.dcons (.dty .TTop) .dnil) := rfl

end Oopsla16Frontend
