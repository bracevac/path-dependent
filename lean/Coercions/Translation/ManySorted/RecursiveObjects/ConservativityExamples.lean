import Coercions.Translation.ManySorted.RecursiveObjects.Conservativity
import Coercions.Translation.ManySorted.Intersections.GeneralExpression.CompilerSuccessConservativity
import Coercions.DOT.Captures.Intersections.GeneralExpression.TypingExamples

/-!
# Executable Stage 6 conservativity regressions

The first example compiles one existing M11 application both with the
preceding cumulative compiler and, through the structural embedding, with the
Stage 6 cumulative compiler.  Both artifacts cross their standalone checkers
and have literally equal target erasures.

The second example composes the same Stage 6 result with the established
M10/M11 literal-application artifact, exercising the transitive theorem.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.ConservativityExamples

open DOTCaptureToManySortedFC.RecursiveObjects.Conservativity
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext

namespace PreviousCompiler

abbrev emptyReady :=
  DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativity.emptyReady

end PreviousCompiler

namespace Source

abbrev canonical :=
  DOTCapture.Intersections.GeneralExpression.TypingExamples.canonicalApplication

abbrev canonicalTyping :=
  DOTCapture.Intersections.GeneralExpression.TypingExamples.canonicalApplicationTyping

end Source

/-! ## Direct M11-to-Stage-6 instance -/

def previous? :=
  DOTCaptureToManySortedFC.Intersections.GeneralExpression.Recursive.compileTerm?
    PreviousCompiler.emptyReady Source.canonicalTyping

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
theorem previous_compiles : previous?.isSome = true := by
  native_decide

def previous := previous?.get previous_compiles

theorem previous_compile_success :
    previous? = some previous :=
  Option.eq_some_of_isSome previous_compiles

def cumulativeContext : Cumulative.Context
    (Embed.environment
      (DOTCapture.Intersections.Source.Ctx.nil : Previous.Ctx 0)) [] :=
  Context.nil

def cumulative? :=
  compileEmbeddedTerm? cumulativeContext Source.canonicalTyping

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
theorem cumulative_compiles : cumulative?.isSome = true := by
  native_decide

def cumulative := cumulative?.get cumulative_compiles

theorem cumulative_compile_success :
    cumulative? = some cumulative :=
  Option.eq_some_of_isSome cumulative_compiles

/-- The two empty layouts have the same unique runtime projection. -/
def emptyAgreement :
    RuntimeAgreement PreviousCompiler.emptyReady cumulativeContext where
  runtimeRenamingEq := by
    funext name
    nomatch name

def canonicalConservativity : TermConservativity previous cumulative :=
  termConservativity emptyAgreement previous cumulative

/-- The old independently generated M11 artifact is accepted. -/
theorem previous_checker_accepts :
    ManySortedFC.Tm.synth PreviousCompiler.emptyReady.target previous.term =
      some (previous.targetUse, previous.targetType) :=
  canonicalConservativity.previousAccepted

/-- The Stage 6 artifact returned by the actual cumulative compiler is
accepted independently at its recorded indices. -/
theorem cumulative_checker_accepts :
    ManySortedFC.Tm.synth cumulativeContext.core.target cumulative.compiled.term =
      some (cumulative.compiled.targetUse, cumulative.compiled.targetType) :=
  canonicalConservativity.cumulativeAccepted

/-- The wrapper retains the underlying cumulative compiler success equation,
not merely the decidable erasure comparison. -/
theorem cumulative_underlying_compiler_success :
    DOTCaptureToManySortedFC.ModalIntersections.Compiler.compileTerm
        cumulativeContext (Embed.termTyping Source.canonicalTyping) =
      .ok cumulative.compiled :=
  cumulative.compilerSuccess

/-- Literal target-erasure conservativity for the two actual artifacts. -/
theorem canonical_target_erasure_conservative :
    previous.term.erase = cumulative.compiled.term.erase :=
  canonicalConservativity.erasure

/-! ## Transitive M10-to-Stage-6 instance -/

namespace M10Regression

namespace Existing

open DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerSuccessConservativity

abbrev typing := M10.Examples.literalApplicationTyping
noncomputable abbrev compiled := M10.Examples.compiledLiteralApplication
abbrev compileSuccess := M10.Examples.literalApplication_compile_success
noncomputable abbrev asM11 := m10LiteralAsM11Artifact

end Existing

def cumulative? := compileEmbeddedTerm? cumulativeContext
  (DOTCapture.Intersections.GeneralExpression.Embedding.embedTermTyping
    Existing.typing)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
theorem cumulative_compiles : cumulative?.isSome = true := by
  native_decide

def cumulative := cumulative?.get cumulative_compiles

theorem cumulative_compile_success : cumulative? = some cumulative :=
  Option.eq_some_of_isSome cumulative_compiles

theorem target_erasure_conservative :
    Existing.compiled.term.erase = cumulative.compiled.term.erase :=
  m10TermErasureConservativity Existing.compileSuccess Existing.asM11
    DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativity.emptyReady_runtimeRenaming
    cumulative emptyAgreement

theorem m10_checker_accepts :
    ManySortedFC.Tm.synth
        DOTCaptureToManySortedFC.Acyclic.RuntimeContext.nil.target
        Existing.compiled.term =
      some (Existing.compiled.targetUse, Existing.compiled.targetType) :=
  ManySortedFC.Tm.synth_complete Existing.compiled.typing

theorem cumulative_checker_accepts :
    ManySortedFC.Tm.synth cumulativeContext.core.target cumulative.compiled.term =
      some (cumulative.compiled.targetUse, cumulative.compiled.targetType) :=
  cumulative.compiled.checkerAccepts

end M10Regression

end DOTCaptureToManySortedFC.RecursiveObjects.ConservativityExamples
