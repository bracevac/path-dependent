import Coercions.Oopsla16.Frontend.Surface
import Coercions.Oopsla16.Frontend.Ann
import Coercions.Oopsla16.Examples
import Coercions.FCdotR.CheckerExamples

/-!
# The decided side conditions

Three side conditions of the typer are decided, not searched.

* `Oopsla16.EqSome o T` relates a method's optional annotation to the type it
  is checked at.  It unfolds to `o = none ∨ o = some T`.
* `strengthen2?` removes the second binder of a type.  A method member
  `{def l(x : S) : U}` in the body of `μ z. X` has `U` under the self `z` and
  the parameter `x`.  Reading the member as a method type of the recursive
  type needs `U` free of `z`.  `strengthen2?` drops `z` and fails when `z`
  occurs.  It reuses the partial renamings of `FCdotR.Ty.rename?`, and
  `strengthen2?_iff` is its specification.
* `frag?` decides membership in `FCdotR.TmFrag`, the terms that
  `FCdotR.elabHasType` elaborates.  It returns the membership proof itself, so
  it needs no soundness theorem.

All definitions are structural recursions, so the checks below are `decide`.
Nothing here belongs to the metatheory.
-/

namespace Oopsla16Frontend

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Lb Vr Ty Tm Dm Dms EqSome)
open FCdotR (TmFrag DmFrag DmsFrag PartialRename)

/-! ## `EqSome` -/

/-- `EqSome o a` is `o = none ∨ o = some a`, a disjunction of two decided
equalities. -/
instance instDecidableEqSome {α : Type} [DecidableEq α] (o : Option α) (a : α) :
    Decidable (EqSome o a) :=
  inferInstanceAs (Decidable (o = none ∨ o = some a))

/-! ## Strengthening past the second binder

In the scope `((s,x),x)` the self `z` is the second binder and the parameter
`x` the innermost.  `Rename.succ.lift` inserts `z`, and
`PartialRename.unshift.lift` is its partial inverse. -/

/-- Drop the second binder of a type, if it does not occur. -/
def strengthen2? {σ s : Sig} (T : Ty σ ((s,x),x)) : Option (Ty σ (s,x)) :=
  FCdotR.Ty.rename? T (PartialRename.lift PartialRename.unshift)

/-- `PartialRename.unshift.lift` inverts `Rename.succ.lift`. -/
theorem unshift_lift_inverts {s : Sig} :
    PartialRename.Inverts (PartialRename.lift (k := .var) (PartialRename.unshift (s := s) (k := .var)))
      (Rename.lift Rename.succ) :=
  PartialRename.Inverts.lift PartialRename.unshift_inverts

/-- Inserting the second binder into the result gives back the input. -/
theorem strengthen2?_sound {σ s : Sig} {T : Ty σ ((s,x),x)} {U : Ty σ (s,x)}
    (h : strengthen2? T = some U) : T = U.rename (Rename.lift Rename.succ) :=
  FCdotR.Ty.rename?_sound T U _ _ unshift_lift_inverts h

/-- A type with the second binder inserted strengthens back. -/
theorem strengthen2?_rename {σ s : Sig} (U : Ty σ (s,x)) :
    strengthen2? (U.rename (Rename.lift Rename.succ)) = some U :=
  FCdotR.Ty.rename?_complete U _ _ unshift_lift_inverts

/-- Strengthening past the second binder inverts its insertion. -/
theorem strengthen2?_iff {σ s : Sig} {T : Ty σ ((s,x),x)} {U : Ty σ (s,x)} :
    strengthen2? T = some U ↔ T = U.rename (Rename.lift Rename.succ) := by
  constructor
  · exact strengthen2?_sound
  · intro h; subst h; exact strengthen2?_rename U

/-- `strengthen2?` with the equation it establishes. -/
def strengthen2W? {σ s : Sig} (T : Ty σ ((s,x),x)) :
    Option { U : Ty σ (s,x) // T = U.rename (Rename.lift Rename.succ) } :=
  match FCdotR.witness? (strengthen2? T) with
  | some ⟨U, hU⟩ => some ⟨U, strengthen2?_sound hU⟩
  | none => none

/-- `strengthen2W?` finds exactly what `strengthen2?` finds. -/
theorem strengthen2W?_val {σ s : Sig} (T : Ty σ ((s,x),x)) :
    (strengthen2W? T).map Subtype.val = strengthen2? T :=
  by
  unfold strengthen2W?
  split
  · next U hU heq => exact hU.symm
  · next heq =>
      cases h : strengthen2? T with
      | none => rfl
      | some U => rw [FCdotR.witness?_eq_some h] at heq; cases heq

/-- Weakening a method type inserts the new binder below the parameter in the
codomain. -/
theorem weaken_TFun {σ s : Sig} (l : Lb) (S : Ty σ s) (U : Ty σ (s,x)) :
    (Ty.TFun l S U).weaken = .TFun l S.weaken (U.rename (Rename.lift Rename.succ)) := by
  show Ty.TFun l (S.subst _) (U.subst (Oopsla16.Subst.ofRename Rename.succ).lift) = _
  rw [FCdotR.ofRename_lift]

/-- On a method type, `FCdotR.Ty.strengthen?` strengthens the domain and, for
the codomain, uses `strengthen2?`. -/
theorem strengthen?_TFun {σ s : Sig} (l : Lb) (S : Ty σ (s,x)) (U : Ty σ ((s,x),x)) :
    FCdotR.Ty.strengthen? (Ty.TFun l S U)
      = match FCdotR.Ty.strengthen? S, strengthen2? U with
        | some S', some U' => some (.TFun l S' U')
        | _, _ => none := rfl

/-! ## The elaborable fragment

`FCdotR.TmFrag` has three term shapes: a variable, a literal whose members are
in the fragment, and a call of a variable on a variable.  A member is in the
fragment when it is a type member, or a method with both annotations whose
body is in the fragment. -/

mutual
/-- The fragment proof of a term, if the term is in the fragment. -/
def frag? {σ s : Sig} (t : Tm σ s) : Option (TmFrag t) :=
  match t with
  | .tvar _ => some .tvar
  | .tobj ds => (dmsFrag? ds).map .tobj
  | .tapp (.tvar _) _ (.tvar _) => some .tapp
  | .tapp _ _ _ => none
termination_by structural t
/-- The fragment proof of a member, if the member is in the fragment. -/
def dmFrag? {σ s : Sig} (d : Dm σ s) : Option (DmFrag d) :=
  match d with
  | .dty _ => some .dty
  | .dfun (some _) (some _) t => (frag? t).map .dfun
  | .dfun _ _ _ => none
termination_by structural d
/-- The fragment proof of a member list, if every member is in the
fragment. -/
def dmsFrag? {σ s : Sig} (ds : Dms σ s) : Option (DmsFrag ds) :=
  match ds with
  | .dnil => some .dnil
  | .dcons d ds' =>
      match dmFrag? d, dmsFrag? ds' with
      | some fd, some fds => some (.dcons fd fds)
      | _, _ => none
termination_by structural ds
end

mutual
/-- `frag?` finds every term of the fragment. -/
theorem frag?_complete {σ s : Sig} : {t : Tm σ s} → TmFrag t → (frag? t).isSome = true
  | _, .tvar => by simp [frag?]
  | _, .tobj f => by simp [frag?, dmsFrag?_complete f]
  | _, .tapp => by simp [frag?]
/-- `dmFrag?` finds every member of the fragment. -/
theorem dmFrag?_complete {σ s : Sig} : {d : Dm σ s} → DmFrag d → (dmFrag? d).isSome = true
  | _, .dty => by simp [dmFrag?]
  | _, .dfun f => by simp [dmFrag?, frag?_complete f]
/-- `dmsFrag?` finds every member list of the fragment. -/
theorem dmsFrag?_complete {σ s : Sig} : {ds : Dms σ s} → DmsFrag ds → (dmsFrag? ds).isSome = true
  | _, .dnil => by simp [dmsFrag?]
  | _, .dcons (d := d) (ds := ds) fd fds => by
      have hd := dmFrag?_complete fd
      have hds := dmsFrag?_complete fds
      simp only [dmsFrag?]
      cases h1 : dmFrag? d with
      | none => rw [h1] at hd; cases hd
      | some a =>
          cases h2 : dmsFrag? ds with
          | none => rw [h2] at hds; cases hds
          | some b => rfl
end

/-! ## Checks -/

section Checks
open Oopsla16.Examples.FunctionField (Sbody Tbody)
open FCdotR.CheckerExamples.DotExs (ex1Tm ex1 polyId ex2Tm)
open FCdotR.CheckerExamples.PaperLst (lstTm)

/-- `EqSome` of a missing annotation holds at every type. -/
example : EqSome (none : Option (Ty [] [])) .TTop := by decide
/-- `EqSome` of a written annotation holds at that type. -/
example : EqSome (some (Ty.TTop : Ty [] [])) .TTop := by decide
/-- `EqSome` of a written annotation fails at another type. -/
example : ¬ EqSome (some (Ty.TBot : Ty [] [])) .TTop := by decide

/-- The codomain of `polyId`'s method does not mention the self. -/
example : strengthen2? (s := []) (σ := [])
      (.TFun 0 (.TSel (.abs .here) 0) (.TSel (.abs (.there .here)) 0))
    = some (.TFun 0 (.TSel (.abs .here) 0) (.TSel (.abs (.there .here)) 0)) := by decide

/-- The codomain of `T(z)`'s method `f` selects on the self `z`, so it does
not strengthen (`Oopsla16.Examples.FunctionField.Tbody`). -/
example : strengthen2? (s := []) (σ := []) (.TSel (.abs (.there .here)) 1) = none := by decide

/-- A variable outside the self moves one binder in. -/
example : strengthen2? (s := ([],x)) (σ := [])
      (.TAnd (.TSel (.abs (.there (.there .here))) 0) (.TSel (.abs .here) 1))
    = some (.TAnd (.TSel (.abs (.there .here)) 0) (.TSel (.abs .here) 1)) := by decide

/-- The method member of `T(z)` does not strengthen, because of its codomain. -/
example : FCdotR.Ty.strengthen? Tbody = none := by decide

/-- `ex1` is in the fragment: both methods carry both annotations. -/
example : (frag? ex1Tm).isSome = true := by decide
/-- `paper_lst` is in the fragment. -/
example : (frag? lstTm).isSome = true := by decide
/-- `ex2` calls a method on a literal, which is not a variable. -/
example : (frag? ex2Tm).isSome = false := by decide
/-- A Curry style method, one with an annotation missing, is outside the
fragment. -/
example : (frag? (Tm.tobj (.dcons (.dfun none (some .TTop) (.tvar (.abs .here))) .dnil)
    : Tm [] [])).isSome = false := by decide
/-- The program of `FCdotR.SourceSafety.RecursiveArg` has Curry style methods
and a call on a literal. -/
example : (frag? FCdotR.SourceSafety.RecursiveArg.prog).isSome = false := by decide

/-- The witness `frag?` returns for `ex1` is one `FCdotR.elabHasType` takes,
and the checker accepts the elaboration at `polyId`. -/
example : FCdotR.checkTm Oopsla16.Store.nil FCdotR.emptyStoreTy Oopsla16.Ctx.nil
    (FCdotR.elabHasType FCdotR.emptyStoreTy ex1 ((frag? ex1Tm).get (by decide))).1 polyId
      = true := by
  decide +kernel

end Checks

end Oopsla16Frontend
