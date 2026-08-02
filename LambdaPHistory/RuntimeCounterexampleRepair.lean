import LambdaPHistory.LookupCounterexample
import LambdaPHistory.RuntimePathPreservation

/-!
The preservation counterexample under the corrected proof invariant.

This small module checks that runtime conversion repairs exactly the mismatch
which refutes historical source preservation; it is not merely an abstract
replacement principle disconnected from that example.
-/

namespace LambdaPHistory.LookupCounterexample

/-- The source selection and returned location are runtime-equal because they
resolve to the same store cell. -/
theorem selected_runtime_eq :
    Path.RuntimeEq σ selected (Path.var y) :=
  Path.RuntimeEq.of_reduce selected_reduces_to_y

/-- Although the successor has no historical source typing at `{x.1}`, it has
the same type in the runtime-aware state invariant. -/
theorem successor_state_runtime_typed :
    State.RuntimeTy Γ successorState
      (Ty.Single (Path.var x).fst) :=
  State.Ty.path_step_runtime_preservation
    selected_reduces_to_y source_state_typed

/-- The example simultaneously witnesses failure of source preservation and
success of preservation modulo store-justified conversion. -/
theorem preservation_boundary :
    (¬ State.Ty Γ successorState
      (Ty.Single (Path.var x).fst)) ∧
    State.RuntimeTy Γ successorState
      (Ty.Single (Path.var x).fst) :=
  ⟨successor_state_untypable, successor_state_runtime_typed⟩

end LambdaPHistory.LookupCounterexample
