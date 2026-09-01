import Coercions.Translation.ManySorted.ModalIntersections.ModalTheoryMapElaboration

/-!
# Checked cumulative modal-theory-map regressions

The mode example derives a required read-only fact for `empty` from an
available read-only fact for `empty union empty`.  The separation example
uses a pushed two-position frame, so its certificate is obtained from the
available lock rather than from ambient disjointness.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.ModalTheoryMapElaborationExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.ModalTheoryMapElaboration

namespace ModeExample

def available : DOTCapture.ModalIntersections.ModalRequirements
    0 [.readOnly] [] :=
  .mk .nil (.cons .nil (.union .empty .empty))

def required : DOTCapture.ModalIntersections.ModalRequirements
    0 [.readOnly] [] :=
  .mk .nil (.cons .nil .empty)

def preparedAvailable : PreparedModal Context.nil.core available where
  requirements := .mk .nil (.cons .nil (.union .empty .empty))
  prepared := rfl

def preparedRequired : PreparedModal Context.nil.core required where
  requirements := .mk .nil (.cons .nil .empty)
  prepared := rfl

/-- Downward mode closure is deliberately derived through the available
frame's active-lock assumption. -/
def satisfaction : DOTCapture.ModalIntersections.Satisfies
    DOTCapture.ModalIntersections.Ctx.nil
    (DOTCapture.ModalIntersections.TypingEnv.nil.push available).locks
    required :=
  .mk
    (fun occurrence =>
      match occurrence with
      | .here =>
          .subcapture .captureEmpty (.lock .here .here))
    (fun left => nomatch left)

def compiled? := compile? Context.nil preparedAvailable preparedRequired
  satisfaction

example : compiled?.isSome = true := by native_decide

def compiled := compiled?.get (by native_decide)

example : (Context.nil.push available preparedAvailable).compiler.compileSatisfies?
    compiled.opened satisfaction = some compiled.candidate :=
  compiled.candidateCompiled

example : ManySortedFC.ModalTheoryMap.check Context.nil.core.target
    preparedAvailable.requirements preparedRequired.requirements
    compiled.mapping = some compiled.typing :=
  compiled.checkerAcceptance

example : compiled.mapping.evidence =
    (.cons
      (.modeSubcapture
        (.captureEmpty (.union .empty .empty))
        (.var .here))
      .nil) := by
  native_decide

end ModeExample

namespace SeparationExample

def separation : DOTCapture.ModalIntersections.SeparationContext 2 [] :=
  .cons (.cons .nil .empty) (.union .empty .empty)

def requirements : DOTCapture.ModalIntersections.ModalRequirements 2 [] [] :=
  .mk separation .nil

def prepared : PreparedModal Context.nil.core requirements where
  requirements :=
    .mk (.cons (.cons .nil .empty) (.union .empty .empty)) .nil
  prepared := rfl

/-- Both orientations are available in the source judgment; target
elaboration chooses its canonical pair orientation. -/
def satisfaction : DOTCapture.ModalIntersections.Satisfies
    DOTCapture.ModalIntersections.Ctx.nil
    (DOTCapture.ModalIntersections.TypingEnv.nil.push requirements).locks
    requirements :=
  .mk
    (fun occurrence => nomatch occurrence)
    (fun left right distinct => .lock .here left right distinct)

def compiled? := compile? Context.nil prepared prepared satisfaction

example : compiled?.isSome = true := by native_decide

def compiled := compiled?.get (by native_decide)

example : ManySortedFC.ModalTheoryMap.check Context.nil.core.target
    prepared.requirements prepared.requirements compiled.mapping =
      some compiled.typing :=
  compiled.checkerAcceptance

example : compiled.mapping.evidence =
    (.cons (.var .here) .nil) := by native_decide

end SeparationExample

namespace CumulativeExample

/-- An older ambient lock is present before the available frame used by the
map compiler. -/
def ambientContext := Context.nil.push ModeExample.required
  ModeExample.preparedRequired

def preparedAvailable : PreparedModal ambientContext.core
    ModeExample.available where
  requirements := .mk .nil (.cons .nil (.union .empty .empty))
  prepared := rfl

def preparedRequired : PreparedModal ambientContext.core
    ModeExample.required where
  requirements := .mk .nil (.cons .nil .empty)
  prepared := rfl

/-- The required fact is deliberately taken from the older ambient lock,
past the newer available frame.  This exercises cumulative source and target
coordinate transport rather than merely the empty context. -/
def satisfaction : DOTCapture.ModalIntersections.Satisfies
    (DOTCapture.ModalIntersections.TypingEnv.nil.push
      ModeExample.required).bindings
    ((DOTCapture.ModalIntersections.TypingEnv.nil.push
      ModeExample.required).push ModeExample.available).locks
    ModeExample.required :=
  .mk
    (fun occurrence =>
      match occurrence with
      | .here => .lock (.there .here) .here)
    (fun left => nomatch left)

def compiled? := compile? ambientContext preparedAvailable preparedRequired
  satisfaction

example : compiled?.isSome = true := by native_decide

def compiled := compiled?.get (by native_decide)

example : ManySortedFC.ModalTheoryMap.check ambientContext.core.target
    preparedAvailable.requirements preparedRequired.requirements
    compiled.mapping = some compiled.typing :=
  compiled.checkerAcceptance

/-- The retained certificate points past the newly opened available frame to
the older ambient lock. -/
example : compiled.mapping.evidence =
    (.cons (.var (.there .here)) .nil) := by
  native_decide

end CumulativeExample

/-! ## Rejection boundaries -/

/-- The source mode assumption has the wrong capture for the required
proposition.  The required frame is not pushed, so citing its coordinate
cannot discharge that obligation. -/
def selfDischarge : ManySortedFC.ModalTheoryMap [] 0 [.readOnly]
    0 [.readOnly] where
  evidence := .cons (.var .here) .nil

example : ManySortedFC.ModalTheoryMap.check Context.nil.core.target
    ModeExample.preparedAvailable.requirements
    ModeExample.preparedRequired.requirements selfDischarge = none := by
  native_decide

/-- This direct-coordinate candidate is rejected for the reversed
interfaces.  The reverse implication itself is derivable by other evidence. -/
def reverse : ManySortedFC.ModalTheoryMap [] 0 [.readOnly]
    0 [.readOnly] where
  evidence := .cons (.var .here) .nil

example : ManySortedFC.ModalTheoryMap.check Context.nil.core.target
    ModeExample.preparedRequired.requirements
    ModeExample.preparedAvailable.requirements reverse = none := by
  native_decide

/-- The evidence spine has the right relation shape but proves a different
mode proposition. -/
def malformed : ManySortedFC.ModalTheoryMap [] 0 [.readOnly]
    0 [.readOnly] where
  evidence := .cons (.modeReadOnly (.union .empty .empty)) .nil

example : ManySortedFC.ModalTheoryMap.check Context.nil.core.target
    ModeExample.preparedAvailable.requirements
    ModeExample.preparedRequired.requirements malformed = none := by
  native_decide

/-- A map requiring one mode certificate cannot omit it: the indexed evidence
spine for that modal relation list is nonempty by construction. -/
theorem missingEvidenceIsUnrepresentable :
    ManySortedFC.modalRelations 0 [.readOnly] ≠ [] := by
  decide

end DOTCaptureToManySortedFC.ModalIntersections.ModalTheoryMapElaborationExamples
