import Coercions.DOT.Captures.Intersections.GeneralExpression.TypingExamples
import Coercions.Translation.ManySorted.Intersections.GeneralExpression.Recursive

/-!
# Public object-argument boundary regressions

These tests stop at the public negative-argument entry point.  They do not
depend on the recursive compilation of object applications or object-opening
lets: classification decides whether a computation must first be opened.
-/

namespace DOTCaptureToManySortedFC.Intersections.GeneralExpression.BoundaryRegressions

open ManySortedFC
open DOTCapture.Intersections.GeneralExpression
open DOTCapture.Intersections.GeneralExpression.TypingExamples
open DOTCaptureToManySortedFC.Intersections
open DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler
open DOTCaptureToManySortedFC.Intersections.GeneralExpression.Recursive

/-- The closed compiler state used only to exercise the public diagnostic
boundary. -/
def emptyReady : Ready
    (DOTCapture.Intersections.Source.Ctx.nil :
      DOTCapture.Intersections.Source.Ctx 0) [] where
  layout := Preparation.emptyLayout []
  target := ManySortedFC.Ctx.nil

/-- An arbitrary object-producing computation is rejected before missing
typing evidence or target preparation can obscure the required source open. -/
theorem computed_object_reports_explicit_open :
    compileObjectArgument emptyReady
        (multiObject (scope := 0)) computedObject none =
      .error .ObjectArgumentRequiresExplicitOpen := by
  rfl

/-- A canonical literal has crossed the stability boundary already.  Without
its typing derivation, the public API reports precisely that missing input,
not the explicit-open diagnostic. -/
theorem canonical_literal_without_typing_reports_missing_typing :
    compileObjectArgument emptyReady
        (multiObject (scope := 0))
        (.ret (objectValue (scope := 0))) none =
      .error .MissingObjectArgumentTyping := by
  rfl

/-- Stable-variable syntax is likewise admitted by classification.  This
regression uses a plain one-variable context solely to keep the diagnostic
independent of object preparation. -/
theorem stable_variable_without_typing_reports_missing_typing :
    compileObjectArgument
        (emptyReady.extendPlain
          (DOTCapture.Intersections.Source.Ty.one)
          (ManySortedFC.Ty.one))
        (multiObject (scope := 1))
        (.ret (.var .here)) none =
      .error .MissingObjectArgumentTyping := by
  rfl

end DOTCaptureToManySortedFC.Intersections.GeneralExpression.BoundaryRegressions
