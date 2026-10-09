/-!
# Reasons

Why a program is rejected.  The elaborators of the front ends return a
`Reason` for each failed branch of their search, and the pipeline reports one
per rejected program.

The module imports only Lean core, so every front end can import it without
pulling in the DOT-MNF development.  `Reason` is generic in the label type `L`
and in `R`, the type of the reasons the typer of a front end gives of its
own.  The vanilla front end, Paths and Oopsla16 have none and take `R = Empty`.
CapturesCC and Classifiers take their typer's reason type, whose level escape
carries its certificate.

Four reasons name an empty annotation slot: `missingParamType`, `cyclicRef`,
`needsExplicitType` and `ambiguous`.  A program with no empty slot can be
rejected only by the typer, so it never gets one of these.
`Reason.isSlotReason` tells them apart from the rest.

A rejection reports `limit` when the tank ended marked, else the first reason in
search order, else `mismatch` (`Reason.top`).  The first reason of a search is
the nearest match, and the compiler reports the first error of its traversal.
-/

namespace Frontend.Reason

/-- Why a program is rejected.  `L` is the label type and `R` the typer's
own reasons. -/
inductive Reason (L R : Type) where
  /-- `AnonymousFunctionMissingParamType`.  Oopsla16 names the method's label. -/
  | missingParamType (at? : Option L)
  /-- `CyclicReference`, reported as "Recursive value a needs type". -/
  | cyclicRef (l : L)
  /-- `CheckCaptures.checkInferredResult`: an inferred result type is not
  allowed and the definition needs a written one. -/
  | needsExplicitType (l : L)
  /-- The candidates of a field have no least type. -/
  | ambiguous (l : L)
  /-- A reason of the typer, with its proof where it has one. -/
  | landed (r : R)
  /-- The typer rejects and has no reason of its own. -/
  | mismatch
  /-- The tank ended marked, the compiler's recursion limit. -/
  | limit
deriving DecidableEq, Repr

variable {L R : Type}

/-- The four reasons that name an empty annotation slot. -/
def Reason.isSlotReason : Reason L R → Bool
  | .missingParamType _ => true
  | .cyclicRef _ => true
  | .needsExplicitType _ => true
  | .ambiguous _ => true
  | .landed _ => false
  | .mismatch => false
  | .limit => false

/-- The reason a rejection reports.  `out` says that the tank ended marked,
and `rs` are the reasons of the failed branches in search order. -/
def Reason.top (out : Bool) (rs : List (Reason L R)) : Reason L R :=
  if out then .limit
  else
    match rs with
    | [] => .mismatch
    | r :: _ => r

/-- A marked tank reports the recursion limit, whatever the branches said. -/
example : Reason.top (L := Nat) (R := Empty) true [.cyclicRef 3] = .limit := by
  decide +kernel

/-- An unmarked tank reports the first reason in search order. -/
example : Reason.top (L := Nat) (R := Empty) false [.cyclicRef 3, .mismatch] = .cyclicRef 3 := by
  decide +kernel

/-- No reason at all is a mismatch. -/
example : Reason.top (L := Nat) (R := Empty) false [] = .mismatch := by
  decide +kernel

/-- A cyclic reference is a slot reason. -/
example : (Reason.cyclicRef (L := Nat) (R := Empty) 3).isSlotReason = true := by
  decide +kernel

/-- A mismatch and the recursion limit are not. -/
example : (Reason.mismatch (L := Nat) (R := Empty)).isSlotReason = false
    ∧ (Reason.limit (L := Nat) (R := Empty)).isSlotReason = false := by
  decide +kernel

end Frontend.Reason
