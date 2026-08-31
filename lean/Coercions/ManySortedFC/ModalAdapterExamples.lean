import Coercions.ManySortedFC.Administrative
import Coercions.ManySortedFC.ModalExamples
import Coercions.ManySortedFC.TermCheckerCompleteness

/-!
# Modal structural-adapter regressions

The modal adapter is contravariant in lock requirements and covariant in the
suspended result.  Reboxing remains lazy: applying the adapter creates a new
suspension, and forcing the source suspension happens only after the new lock
is opened.
-/

namespace ManySortedFC.ModalAdapterExamples

open ModalExamples

/-! ## Same-lock result covariance -/

def emptyRequirementMap : ModalTheoryMap [] 0 [] 0 [] where
  evidence := .nil

def sameLockCovariance : Adapter [] :=
  .modal emptyRequirements emptyRequirements emptyRequirementMap
    (.cast (.typeTop .one))

theorem same_lock_covariance_is_accepted :
    Adapter.synth Ctx.nil sameLockCovariance =
      some
        (.modal emptyRequirements .one,
          .modal emptyRequirements .top) := by
  native_decide

/-! ## Contravariant requirement maps -/

/-- The target lock provides a read-only assumption; the source lock needs no
assumptions.  The required evidence block is therefore empty. -/
def readOnlyEntailsEmpty : ModalTheoryMap [] 0 [.readOnly] 0 [] where
  evidence := .nil

def crossLockAdapter : Adapter [] :=
  .modal emptyRequirements readOnlyEmptyRequirements readOnlyEntailsEmpty
    (.identity .one)

theorem cross_lock_adapter_is_accepted :
    Adapter.synth Ctx.nil crossLockAdapter =
      some
        (.modal emptyRequirements .one,
          .modal readOnlyEmptyRequirements .one) := by
  native_decide

theorem cross_lock_map_is_checked_as_an_ordinary_theory_map :
    (TheoryMap.check Ctx.nil
      (readOnlyEntailsEmpty.toTheoryMap readOnlyEmptyRequirements
        emptyRequirements)).isSome = true := by
  native_decide

/-- A nontrivial requirement change: the target assumption covers a union,
and downward closure supplies the source lock's empty-capture obligation. -/
def readOnlyUnionRequirements : ModalContext 0 [.readOnly] [] :=
  .mk .nil (.cons .nil (.union .empty .empty))

def readOnlyUnionEntailsEmpty : ModalTheoryMap [] 0 [.readOnly]
    0 [.readOnly] where
  evidence :=
    .cons
      (.modeSubcapture
        (.captureEmpty (.union .empty .empty))
        (.var .here))
      .nil

def nontrivialCrossLockAdapter : Adapter [] :=
  .modal readOnlyEmptyRequirements readOnlyUnionRequirements
    readOnlyUnionEntailsEmpty (.identity .one)

theorem nontrivial_cross_lock_adapter_is_accepted :
    Adapter.synth Ctx.nil nontrivialCrossLockAdapter =
      some
        (.modal readOnlyEmptyRequirements .one,
          .modal readOnlyUnionRequirements .one) := by
  native_decide

/-! ## Bad and missing map evidence -/

/-- This map has the required evidence-list shape, but proves a mode fact for
`empty union empty` rather than for the source requirement's exact `empty`. -/
def malformedReadOnlyMap : ModalTheoryMap [] 0 [] 0 [.readOnly] where
  evidence := .cons (.modeReadOnly (.union .empty .empty)) .nil

def adapterWithMalformedRequirementMap : Adapter [] :=
  .modal readOnlyEmptyRequirements emptyRequirements malformedReadOnlyMap
    (.identity .one)

theorem malformed_requirement_map_is_rejected :
    (Adapter.check Ctx.nil adapterWithMalformedRequirementMap).isNone =
      true := by
  native_decide

/-- Omitting the required evidence is not representable by the indexed map
syntax; the empty and read-only evidence shapes differ. -/
theorem missing_requirement_map_evidence_is_intrinsically_excluded :
    modalRelations 0 [.readOnly] ≠ [] := by
  decide

/-! ## Captured modal values and lazy reboxing -/

def capturedSameLockCovariance : Adapter [] :=
  .captured (.captureEmpty .empty) sameLockCovariance

theorem captured_modal_adapter_is_accepted :
    Adapter.synth Ctx.nil capturedSameLockCovariance =
      some
        (.capturing .empty (.modal emptyRequirements .one),
          .capturing .empty (.modal emptyRequirements .top)) := by
  native_decide

def reboxedLock : Tm [] :=
  .adapt lockedUnitBetaRedex capturedSameLockCovariance

theorem captured_modal_value_adaptation_is_accepted :
    Tm.synth Ctx.nil reboxedLock =
      some
        (.empty,
          .capturing .empty (.modal emptyRequirements .top)) := by
  native_decide

theorem reboxed_lock_is_a_target_value : Tm.IsValue reboxedLock :=
  .adapt .lock

theorem reboxed_lock_erases_to_a_fresh_suspension :
    reboxedLock.erase =
      .suspend
        (.let'
          (.force (.suspend (runtimeUnitBetaRedex (scope := 0))))
          (.var 0)) := rfl

theorem reboxed_lock_is_a_runtime_value :
    Runtime.IsValue reboxedLock.erase :=
  .suspend

theorem modal_reboxing_is_administrative :
    Runtime.AdministrativeEq reboxedLock.erase
      lockedUnitBetaRedex.erase := by
  exact capturedSameLockCovariance.erase_admin
    lockedUnitBetaRedex.erase .suspend

def runReboxedLock : Tm [] :=
  .unlock emptyRequirements reboxedLock .nil

theorem reboxed_unlock_is_accepted :
    Tm.synth Ctx.nil runReboxedLock = some (.empty, .top) := by
  native_decide

/-- Opening the new lock first exposes the administrative let.  Only then is
the old lock forced, its beta-redex run, and the adapted result returned. -/
theorem reboxed_unlock_runs_after_both_locks_are_opened :
    Runtime.Steps runReboxedLock.erase .unit := by
  have openOuter : Runtime.Step runReboxedLock.erase
      (.let'
        (.force (.suspend (runtimeUnitBetaRedex (scope := 0))))
        (.var 0)) :=
    .forceBeta
  have openInner : Runtime.Step
      (.let'
        (.force (.suspend (runtimeUnitBetaRedex (scope := 0))))
        (.var 0))
      (.let' (runtimeUnitBetaRedex (scope := 0)) (.var 0)) :=
    .letRhs .forceBeta
  have runInner : Runtime.Step
      (.let' (runtimeUnitBetaRedex (scope := 0)) (.var 0))
      (.let' .unit (.var 0)) :=
    .letRhs (.beta .unit)
  exact .tail (.tail (.tail (.single openOuter) openInner) runInner)
    (.zeta .unit)

end ManySortedFC.ModalAdapterExamples
