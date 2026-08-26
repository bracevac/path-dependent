import LambdaPFC.Runtime

/-!
# Safety observations for the source CK machine

The native `LambdaPFC` transition is heterogeneous because allocation grows
the store.  This file states the source failure condition independently of
any compiler invariant: a state is stuck when it is neither final nor able to
step to a state at any store size, and a closed program goes wrong when a
finite CK execution reaches such a state.

`OperationalOneStepPreservation.source_not_goesWrong` refutes `GoesWrong` for
the closed operationally admissible core.  It lifts CK executions through the
compiler image, while source non-stuckness follows from the source evidence in
the endpoint `StateImage`.  The retained `SystemFCo` steps witness compiler
correspondence; target safety is not a premise of that progress argument.
-/

namespace LambdaPToFCo
namespace OperationalSafety

open LambdaPFC

namespace State

/-- An indexed CK state has an outgoing transition at some target store
size. -/
def CanStep (state : LambdaPFC.State n) : Prop :=
  Exists fun m => Exists fun target : LambdaPFC.State m =>
    LambdaPFC.State.Step state target

/-- A source state is stuck precisely when it is not final and cannot take a
heterogeneous CK transition. -/
def IsStuck (state : LambdaPFC.State n) : Prop :=
  Not state.IsFinal /\ Not (CanStep state)

/-- Progress excludes the source failure condition. -/
theorem not_stuck_of_progress
    {state : LambdaPFC.State n} (progress : state.Progress) :
    Not (IsStuck state) := by
  intro stuck
  cases progress with
  | final final => exact stuck.1 final
  | @step m target reduction => exact stuck.2 ⟨m, target, reduction⟩

end State

/-- A closed source term goes wrong when a finite, possibly allocating CK
execution reaches a stuck state. -/
def GoesWrong (term : LambdaPFC.Tm 0) : Prop :=
  Exists fun n => Exists fun state : LambdaPFC.State n =>
    LambdaPFC.State.Steps (LambdaPFC.State.initial term) state /\
      State.IsStuck state

end OperationalSafety
end LambdaPToFCo
