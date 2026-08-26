import LambdaPToFCo.OperationalMachineImage

/-!
# Suffix-only elimination of captured frames

The machine image records the reduction of a suspended bound computation
separately from elimination of the surrounding `let` binder.  A one-step
simulation must therefore be able to start at the *current* behavioral
argument, rather than replaying the reduction from the bound compilation.

The generic theorem below is precisely that suffix.  The allocation and
existing-location return corollaries merely identify its extended closing
environment with the code environment constructed by the corresponding CK
transition.
-/

namespace LambdaPToFCo
namespace OperationalFrameElimination

open SystemFCo
open StaticTranslation
open OperationalBindingView
open OperationalEnvironment
open OperationalStoreEnvironment
open OperationalMachineImage

namespace CapturedFrame

/-- Eliminate a behavioral argument through a captured frame without
including any reductions which produced that argument. -/
theorem eliminate_behavior_steps
    (frame : CapturedFrame sourceStore runtimeBody)
    (behavior : EliminationView
      ((TermTranslation.compileBinder frame.scope
        frame.boundTyping.typeWf).plan.subst
        frame.closing.substitution)) :
    Exp.Steps
      (frame.compilation.closeFrame.fill behavior.argument)
      ((behavior.resume
          ((translateType frame.scope frame.image.resultWf).subst
            frame.closing.substitution)).plug
        ((extendClosing frame.closing
            (TermTranslation.compileBinder frame.scope
              frame.boundTyping.typeWf).plan
            behavior).closeExp
          (TermTranslation.elaborate
            (TermTranslation.compileBinder frame.scope
              frame.boundTyping.typeWf).extended
            frame.image.bodyTyping))) := by
  change Exp.Steps
    (((TermTranslation.compileBinder frame.scope
        frame.image.holeWf).plan.subst frame.closing.substitution).close
      behavior.argument
      ((translateType frame.scope frame.image.resultWf).subst
        frame.closing.substitution)
      ((TermTranslation.elaborate
        (TermTranslation.compileBinder frame.scope
          frame.image.holeWf).extended
        frame.image.bodyTyping).subst
          ((TermTranslation.compileBinder frame.scope
            frame.image.holeWf).plan.scopeSubst
              frame.closing.substitution))) _
  rw [frame.holeWf_eq]
  simpa only [OperationalStoreEnvironment.closeExp_extendClosing] using
    (behavior.eliminate
      ((translateType frame.scope frame.image.resultWf).subst
        frame.closing.substitution)
      ((TermTranslation.elaborate
        (TermTranslation.compileBinder frame.scope
          frame.boundTyping.typeWf).extended
        frame.image.bodyTyping).subst
          ((TermTranslation.compileBinder frame.scope
            frame.boundTyping.typeWf).plan.scopeSubst
              frame.closing.substitution)))

/-- Allocation-specific endpoint of suffix-only frame elimination. -/
theorem allocation_suffix_steps
    (frame : CapturedFrame sourceStore runtimeBody)
    (native : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (slot : AllocationSlot frame native runtimeReady) :
    Exp.Steps
      (frame.compilation.closeFrame.fill slot.behavior.argument)
      ((slot.behavior.resume
          ((translateType frame.scope frame.image.resultWf).subst
            frame.closing.substitution)).plug
        ((frame.afterAllocationCode native runtimeReady slot).closing.closeExp
          (TermTranslation.elaborate
            (frame.afterAllocationCode native runtimeReady slot).scope
            frame.image.bodyTyping))) := by
  simpa only [CapturedFrame.afterAllocationCode] using
    eliminate_behavior_steps frame slot.behavior

/-- Existing-location return endpoint of suffix-only frame elimination. -/
theorem return_suffix_steps
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody)
    (location : Fin current)
    (slot : ReturnSlot frame location) :
    Exp.Steps
      (frame.compilation.closeFrame.fill slot.behavior.argument)
      ((slot.behavior.resume
          ((translateType frame.scope frame.image.resultWf).subst
            frame.closing.substitution)).plug
        ((frame.afterReturnCode location slot).closing.closeExp
          (TermTranslation.elaborate
            (frame.afterReturnCode location slot).scope
            frame.image.bodyTyping))) := by
  exact OperationalMachineImage.CapturedFrame.return_steps frame location slot

end CapturedFrame

end OperationalFrameElimination
end LambdaPToFCo
