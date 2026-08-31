import Coercions.ManySortedFC.TermChecker
import Coercions.ManySortedFC.Erasure
import Coercions.ManySortedFC.SeparationConsistency

/-!
# Primitive modal regressions

These examples exercise the primitive modal type and its `lock`/`unlock`
terms.  A lock is a real runtime suspension: forming one does not run its
body, and unlocking first evaluates its scrutinee and then forces the
suspension.
-/

namespace ManySortedFC.ModalExamples

/-! ## Empty requirements and genuine suspension -/

def emptyRequirements : ModalContext 0 [] [] :=
  .mk .nil .nil

/-- The suspended computation is a genuine beta-redex, not a value. -/
def unitBetaRedex : Tm [] :=
  .app
    (.lam .one .one .empty (.var .here)
      (.captureEmpty (.union .empty (.singleton .here))))
    .unit

def lockedUnitBetaRedex : Tm [] :=
  .lock emptyRequirements .one .empty unitBetaRedex
    (.captureUnionElim
      (.captureEmpty .empty)
      (.captureEmpty .empty))

theorem unit_beta_redex_is_not_a_target_value :
    Tm.checkValue unitBetaRedex = none := rfl

theorem lock_of_beta_redex_is_a_target_value :
    Tm.IsValue lockedUnitBetaRedex :=
  .lock

theorem lock_of_beta_redex_passes_value_checker :
    (Tm.checkValue lockedUnitBetaRedex).isSome = true := by
  native_decide

theorem empty_lock_is_accepted :
    (Tm.check Ctx.nil lockedUnitBetaRedex).isSome = true := by
  native_decide

/-- A closed runtime beta-redex, polymorphic in its ambient scope. -/
def runtimeUnitBetaRedex {scope : Nat} : Runtime.Tm scope :=
  .app (.lam (.var 0)) .unit

theorem lock_erases_to_a_real_suspension :
    lockedUnitBetaRedex.erase =
      .suspend (runtimeUnitBetaRedex (scope := 0)) := rfl

theorem lock_of_beta_redex_is_a_runtime_value :
    Runtime.IsValue lockedUnitBetaRedex.erase :=
  .suspend

def unlockedUnitBetaRedex : Tm [] :=
  .unlock emptyRequirements lockedUnitBetaRedex .nil

theorem empty_unlock_is_accepted :
    Tm.synth Ctx.nil unlockedUnitBetaRedex =
      some (.empty, .one) := by
  native_decide

theorem unlock_erases_to_force :
    unlockedUnitBetaRedex.erase =
      .force (.suspend (runtimeUnitBetaRedex (scope := 0))) := rfl

theorem runtime_force_beta_precedes_ordinary_beta :
    Runtime.Steps unlockedUnitBetaRedex.erase .unit := by
  exact .tail (.single .forceBeta) (.beta .unit)

/-! ## A computed unlock scrutinee -/

def emptyModalUnitType : Ty [] :=
  .capturing .empty (.modal emptyRequirements .one)

/-- The right-hand side is evaluated before the lock is returned. -/
def computedLock : Tm [] :=
  .let' emptyModalUnitType .empty .unit lockedUnitBetaRedex.weaken
    (.captureEmpty .empty)

def unlockComputedLock : Tm [] :=
  .unlock emptyRequirements computedLock .nil

theorem computed_unlock_is_accepted :
    (Tm.check Ctx.nil unlockComputedLock).isSome = true := by
  native_decide

theorem computed_unlock_erasure_exposes_one_scrutinee_binding :
    unlockComputedLock.erase =
      .force
        (.let' .unit
          (.suspend (runtimeUnitBetaRedex (scope := 1)))) := rfl

/-- The sole zeta step occurs under `force`; only then can `forceBeta` fire. -/
theorem computed_unlock_scrutinee_is_evaluated_once :
    Runtime.Steps unlockComputedLock.erase .unit := by
  have evaluateScrutinee : Runtime.Step unlockComputedLock.erase
      (.force (.suspend (runtimeUnitBetaRedex (scope := 0)))) := by
    exact .forceSuspension (.zeta .unit)
  have releaseSuspension : Runtime.Step
      (.force (.suspend (runtimeUnitBetaRedex (scope := 0))))
      (runtimeUnitBetaRedex (scope := 0)) :=
    .forceBeta
  have runBody : Runtime.Step (runtimeUnitBetaRedex (scope := 0)) .unit := by
    exact .beta .unit
  exact .tail (.tail (.single evaluateScrutinee) releaseSuspension) runBody

/-! ## Rejected annotations and interfaces -/

def lockWithBadResultAnnotation : Tm [] :=
  .lock emptyRequirements .top .empty unitBetaRedex
    (.captureUnionElim
      (.captureEmpty .empty)
      (.captureEmpty .empty))

theorem bad_lock_result_annotation_is_rejected :
    (Tm.check Ctx.nil lockWithBadResultAnnotation).isNone = true := by
  native_decide

abbrev FunctionScope : Sig := [] ▹ .term

def functionContext : Ctx FunctionScope :=
  Ctx.nil.extendTerm (.capturing .empty (.arr .one .one))

def emptyFunctionRequirements : ModalContext 0 [] FunctionScope :=
  .mk .nil .nil

def callFreeFunction : Tm FunctionScope :=
  .app (.var .here) .unit

/-- The body uses the free function, but the annotation claims no closure. -/
def lockWithInsufficientClosure : Tm FunctionScope :=
  .lock emptyFunctionRequirements .one .empty callFreeFunction
    (.captureEmpty .empty)

theorem insufficient_lock_closure_is_rejected :
    (Tm.check functionContext lockWithInsufficientClosure).isNone = true := by
  native_decide

def unlockNonModalTerm : Tm [] :=
  .unlock emptyRequirements .unit .nil

theorem nonmodal_unlock_is_rejected :
    (Tm.check Ctx.nil unlockNonModalTerm).isNone = true := by
  native_decide

def readOnlyEmptyRequirements : ModalContext 0 [.readOnly] [] :=
  .mk .nil (.cons .nil .empty)

def readOnlyEmptyEvidence : EvidenceArgs [] [.mode .readOnly] :=
  .cons (.modeEmpty .readOnly) .nil

/-- The supplied evidence is valid, but it targets a different modal spec. -/
def unlockWithMismatchedSpec : Tm [] :=
  .unlock readOnlyEmptyRequirements lockedUnitBetaRedex
    readOnlyEmptyEvidence

theorem mismatched_modal_spec_is_rejected :
    (Tm.check Ctx.nil unlockWithMismatchedSpec).isNone = true := by
  native_decide

def readOnlyEmptyLock : Tm [] :=
  .lock readOnlyEmptyRequirements .one .empty .unit
    (.captureEmpty .empty)

def validReadOnlyEmptyUnlock : Tm [] :=
  .unlock readOnlyEmptyRequirements readOnlyEmptyLock
    readOnlyEmptyEvidence

theorem nonempty_mode_requirement_unlock_is_accepted :
    Tm.synth Ctx.nil validReadOnlyEmptyUnlock =
      some (.empty, .one) := by
  native_decide

/-!
`lock` suspends an arbitrary well-typed computation.  Static abstraction
instead retains its value restriction, even when given the same erased
evidence interface.
-/

def staticAbstractionOfBetaRedex : Tm [] :=
  .slam readOnlyEmptyRequirements.toTheory .empty
    (unitBetaRedex.rename
      (Rename.weakenStatic [] [.mode .readOnly]))
    (.inclusionRefl (.capture .empty))

theorem erased_evidence_implication_does_not_remove_slam_value_restriction :
    (Tm.check Ctx.nil staticAbstractionOfBetaRedex).isNone = true := by
  native_decide

def malformedReadOnlyEvidence : EvidenceArgs [] [.mode .readOnly] :=
  .cons (.modeReadOnly (.union .empty .empty)) .nil

def unlockWithMalformedSatisfaction : Tm [] :=
  .unlock readOnlyEmptyRequirements readOnlyEmptyLock
    malformedReadOnlyEvidence

theorem malformed_modal_satisfaction_is_rejected :
    (Tm.check Ctx.nil unlockWithMalformedSatisfaction).isNone = true := by
  native_decide

/-- A missing evidence block is ruled out by the intrinsic list index. -/
theorem nonempty_modal_requirements_do_not_have_empty_evidence_shape :
    modalRelations 0 [.readOnly] ≠ [] := by
  decide

/-! ## Separation requirements -/

open SeparationExamples

def writableSingleton : Capture OneCapabilityScope :=
  .singleton .here

def writableSelfSeparation : SeparationContext 2 OneCapabilityScope :=
  .cons (.cons .nil writableSingleton) writableSingleton

def writableSelfRequirements : ModalContext 2 [] OneCapabilityScope :=
  .mk writableSelfSeparation .nil

def writableSelfLock : Tm OneCapabilityScope :=
  .lock writableSelfRequirements .one .empty .unit
    (.captureEmpty .empty)

theorem unsupported_writable_self_separation_can_be_locked :
    (Tm.check oneCapabilityContext writableSelfLock).isSome = true := by
  native_decide

theorem writable_singleton_is_not_separate_from_itself :
    ¬ SeparationSemantics.Separate oneWritable writableSingleton
      writableSingleton := by
  intro separation
  have atCapability := separation ()
  simp [writableSingleton, Capture.access, oneWritable,
    AccessView.Separate, AccessView.LE] at atCapability

theorem no_checked_writable_self_separation
    {evidence : Evidence .separate OneCapabilityScope}
    (typing : Evidence.Proves oneCapabilityContext evidence
      (.separate writableSingleton writableSingleton)) : False := by
  apply writable_singleton_is_not_separate_from_itself
  exact typing.access_sound oneWritable_respects

/-- No evidence block can satisfy this modal interface in the ambient
context.  Lock formation is nevertheless independent of that fact. -/
theorem writable_self_requirements_have_no_satisfaction
    (evidenceArguments : EvidenceArgs OneCapabilityScope
      (modalRelations 2 []))
    (satisfaction : Theory.SatisfiedBy oneCapabilityContext
      (.nil : SymbolArgs OneCapabilityScope [])
      writableSelfRequirements.toTheory evidenceArguments) : False := by
  cases evidenceArguments with
  | cons evidence rest =>
      cases rest
      apply no_checked_writable_self_separation
      simpa [writableSelfRequirements, writableSelfSeparation,
        ModalContext.toTheory, SeparationContext.toTheory,
        SeparationContext.against, Theory.append] using satisfaction.head

/-- This has the right evidence-list shape but the wrong proposition. -/
def malformedWritableSelfEvidence : EvidenceArgs OneCapabilityScope
    [.separate] :=
  .cons (.separateEmpty writableSingleton) .nil

def attemptedWritableSelfUnlock : Tm OneCapabilityScope :=
  .unlock writableSelfRequirements writableSelfLock
    malformedWritableSelfEvidence

theorem unsupported_writable_self_separation_cannot_be_unlocked :
    (Tm.check oneCapabilityContext attemptedWritableSelfUnlock).isNone =
      true := by
  native_decide

def readOnlyOverlapSeparation : SeparationContext 2 OneCapabilityScope :=
  .cons (.cons .nil sharedReadOnly) sharedReadOnly

def readOnlyOverlapRequirements : ModalContext 2 [] OneCapabilityScope :=
  .mk readOnlyOverlapSeparation .nil

def readOnlyOverlapLock : Tm OneCapabilityScope :=
  .lock readOnlyOverlapRequirements .one .empty .unit
    (.captureEmpty .empty)

def readOnlyOverlapEvidence : EvidenceArgs OneCapabilityScope [.separate] :=
  .cons sharedReadOnlySeparation .nil

def readOnlyOverlapUnlock : Tm OneCapabilityScope :=
  .unlock readOnlyOverlapRequirements readOnlyOverlapLock
    readOnlyOverlapEvidence

theorem read_only_overlap_satisfaction_is_accepted :
    (Tm.check oneCapabilityContext readOnlyOverlapUnlock).isSome = true := by
  native_decide

theorem read_only_overlap_still_does_not_supply_disjoint
    {evidence : Evidence .disjoint OneCapabilityScope}
    (typing : Evidence.Proves oneCapabilityContext evidence
      (.disjoint sharedReadOnly sharedReadOnly)) : False :=
  no_evidence_for_shared_readOnly_disjoint typing

end ManySortedFC.ModalExamples
