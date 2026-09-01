import Coercions.Translation.ManySorted.ModalIntersections.CompilerArtifacts

/-!
# Checked compiler-artifact regressions

These small cases isolate the final checker boundary from the recursive
compiler.  They exercise exact source erasure, public target synthesis, and
the distinct value/computation side conditions.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifactsExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts

namespace Source

abbrev Value := DOTCapture.ModalIntersections.Value
abbrev Term := DOTCapture.ModalIntersections.Term
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv

end Source

namespace Target

abbrev Tm := ManySortedFC.Tm
abbrev Ty := ManySortedFC.Ty
abbrev Capture := ManySortedFC.Capture

end Target

def unitValueTyping :
    DOTCapture.ModalIntersections.Value.HasType
      DOTCapture.ModalIntersections.TypingEnv.nil
      (.unit : Source.Value []) (.one : Source.Ty []) :=
  .unit

def unitTermTyping :
    DOTCapture.ModalIntersections.Term.HasType
      DOTCapture.ModalIntersections.TypingEnv.nil
      (.ret (.unit : Source.Value []))
      (.empty : Source.Capture []) (.one : Source.Ty []) :=
  .ret unitValueTyping

/-- Literal target unit is accepted as the compilation of source unit. -/
def unitValueCompilation :=
  finishValueExact? Core.nil unitValueTyping (.unit : Target.Tm []) rfl

example : unitValueCompilation.isSome = true := rfl

def compiledUnitValue :
    CompiledValue Core.nil (.unit : Source.Value []) (.one : Source.Ty []) :=
  unitValueCompilation.get (by rfl)

example :
    ManySortedFC.Tm.synth ManySortedFC.Ctx.nil compiledUnitValue.term =
      some (.empty, .one) := by
  simpa using compiledUnitValue.checkerAccepts

example :
    ManySortedFC.Runtime.AdministrativeEq compiledUnitValue.term.erase
      .unit := by
  simpa using compiledUnitValue.erasure

/-- Capture-use annotations are computations even when they erase literally
to a value. -/
def annotatedUnit : Target.Tm [] :=
  .use .unit (.captureEmpty .empty)

example : annotatedUnit.erase = .unit := rfl

/-- The computation boundary accepts the checked annotation. -/
def annotatedUnitCompilation :=
  finishTermExact? Core.nil unitTermTyping annotatedUnit rfl

example : annotatedUnitCompilation.isSome = true := rfl

def compiledAnnotatedUnit :
    CompiledTerm Core.nil (.ret (.unit : Source.Value []))
      (.empty : Source.Capture []) (.one : Source.Ty []) :=
  annotatedUnitCompilation.get (by rfl)

example :
    ManySortedFC.Tm.synth ManySortedFC.Ctx.nil compiledAnnotatedUnit.term =
      some (.empty, .one) := by
  simpa using compiledAnnotatedUnit.checkerAccepts

/-- The same syntax is rejected at the value boundary because `use` is not a
target value constructor. -/
example :
    finishValueExact? Core.nil unitValueTyping annotatedUnit rfl = none :=
  rfl

end DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifactsExamples
