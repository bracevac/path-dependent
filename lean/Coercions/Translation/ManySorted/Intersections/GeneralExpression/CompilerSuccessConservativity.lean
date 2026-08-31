import Coercions.Translation.ManySorted.Intersections.GeneralExpression.CompilerConservativity
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.ObjectConsumerCompilation

/-!
# Executable M10/M11 compiler conservativity regressions

The M10 typing embedding is executable, so these tests send the original M10
derivations directly through the M11 compiler. They cover a literal object
argument, a stable path established by one open, a computed consumer, and an
explicit open around an object-producing computation. Each generated target
artifact is accepted by the standalone checker and has the same erasure as
the corresponding M10 artifact.

This is executable regression coverage, not a totality theorem for the M11
compiler. `Compiler.Ready` does not state that its layout agrees with its
target context, so success is false for arbitrary `Ready` values. Moreover,
the general M11 stable-object repack branch deliberately rejects closure
proofs that are not recoverable from the exported package theory. A total
compiler-success theorem needs a stronger readiness invariant and either a
restricted source judgment or a more expressive positive package theory.
-/

namespace DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerSuccessConservativity

namespace M10

namespace Source

export DOTCapture.Acyclic.GeneralExpression (Value Term Capture Ty)

namespace Value
export DOTCapture.Acyclic.GeneralExpression.Value (HasType)
end Value

namespace Term
export DOTCapture.Acyclic.GeneralExpression.Term (HasType)
end Term

end Source

namespace Examples

export DOTCapture.Acyclic.GeneralExpression.ObjectConsumerExamples
  (literalApplicationTyping computedConsumerApplicationTyping
    openedApplicationTyping)

export DOTCaptureToManySortedFC.Acyclic.GeneralExpression.ObjectConsumerCompilation
  (stableOpenApplicationTyping compiledLiteralApplication
    compiledStableOpenApplication compiledComputedConsumerApplication
    compiledOpenedApplication literalApplication_compile_success
    stableOpenApplication_compile_success
    computedConsumerApplication_compile_success
    openedApplication_compile_success)

end Examples

end M10

namespace M11

namespace Embedding

export DOTCapture.Intersections.GeneralExpression.Embedding
  (embedValue embedTerm embedValueTyping embedTermTyping)

end Embedding

namespace Compiler

export DOTCaptureToManySortedFC.Intersections.GeneralExpression.Recursive
  (CompiledValue CompiledTerm compileValue? compileTerm?)

end Compiler

abbrev emptyReady :=
  DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativity.emptyReady

end M11

open ManySortedFC

/-! ## Executable embedding entry points -/

/-- Compile an original closed M10 value by applying the structural M11
typing embedding first. The result records the literal embedded source syntax
and type. -/
def compileEmbeddedValue?
    {value : M10.Source.Value 0} {type : M10.Source.Ty 0}
    (typing : M10.Source.Value.HasType DOTCapture.Acyclic.Ctx.nil value type) :=
  M11.Compiler.compileValue? M11.emptyReady
    (M11.Embedding.embedValueTyping typing)

/-- Computation counterpart of `compileEmbeddedValue?`. -/
def compileEmbeddedTerm?
    {term : M10.Source.Term 0} {use : M10.Source.Capture 0}
    {type : M10.Source.Ty 0}
    (typing : M10.Source.Term.HasType DOTCapture.Acyclic.Ctx.nil term use type) :=
  M11.Compiler.compileTerm? M11.emptyReady
    (M11.Embedding.embedTermTyping typing)

/-! ## Direct compiler success -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
theorem literal_argument_compiles :
    (compileEmbeddedTerm? M10.Examples.literalApplicationTyping).isSome =
      true := by
  native_decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
theorem stable_path_compiles :
    (compileEmbeddedTerm? M10.Examples.stableOpenApplicationTyping).isSome =
      true := by
  native_decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
theorem computed_consumer_compiles :
    (compileEmbeddedTerm?
      M10.Examples.computedConsumerApplicationTyping).isSome = true := by
  native_decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
theorem explicit_object_open_compiles :
    (compileEmbeddedTerm? M10.Examples.openedApplicationTyping).isSome =
      true := by
  native_decide

def compiledLiteralArgument :=
  (compileEmbeddedTerm? M10.Examples.literalApplicationTyping).get
    literal_argument_compiles

def compiledStablePath :=
  (compileEmbeddedTerm? M10.Examples.stableOpenApplicationTyping).get
    stable_path_compiles

def compiledComputedConsumer :=
  (compileEmbeddedTerm?
    M10.Examples.computedConsumerApplicationTyping).get
      computed_consumer_compiles

def compiledExplicitObjectOpen :=
  (compileEmbeddedTerm? M10.Examples.openedApplicationTyping).get
    explicit_object_open_compiles

/-! ## Standalone target acceptance -/

theorem literal_argument_checker_accepts :
    Tm.synth M11.emptyReady.target compiledLiteralArgument.term =
      some (compiledLiteralArgument.targetUse,
        compiledLiteralArgument.targetType) :=
  compiledLiteralArgument.checkerAccepts

theorem stable_path_checker_accepts :
    Tm.synth M11.emptyReady.target compiledStablePath.term =
      some (compiledStablePath.targetUse, compiledStablePath.targetType) :=
  compiledStablePath.checkerAccepts

theorem computed_consumer_checker_accepts :
    Tm.synth M11.emptyReady.target compiledComputedConsumer.term =
      some (compiledComputedConsumer.targetUse,
        compiledComputedConsumer.targetType) :=
  compiledComputedConsumer.checkerAccepts

theorem explicit_object_open_checker_accepts :
    Tm.synth M11.emptyReady.target compiledExplicitObjectOpen.term =
      some (compiledExplicitObjectOpen.targetUse,
        compiledExplicitObjectOpen.targetType) :=
  compiledExplicitObjectOpen.checkerAccepts

/-! ## Exact operational conservativity -/

theorem literal_argument_erasure_conservative :
    M10.Examples.compiledLiteralApplication.term.erase =
      compiledLiteralArgument.term.erase :=
  DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativity.closed_m10_m11_term_erasure_coherent
    M10.Examples.literalApplication_compile_success compiledLiteralArgument

theorem stable_path_erasure_conservative :
    M10.Examples.compiledStableOpenApplication.term.erase =
      compiledStablePath.term.erase :=
  DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativity.closed_m10_m11_term_erasure_coherent
    M10.Examples.stableOpenApplication_compile_success compiledStablePath

theorem computed_consumer_erasure_conservative :
    M10.Examples.compiledComputedConsumerApplication.term.erase =
      compiledComputedConsumer.term.erase :=
  DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativity.closed_m10_m11_term_erasure_coherent
    M10.Examples.computedConsumerApplication_compile_success
    compiledComputedConsumer

theorem explicit_object_open_erasure_conservative :
    M10.Examples.compiledOpenedApplication.term.erase =
      compiledExplicitObjectOpen.term.erase :=
  DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativity.closed_m10_m11_term_erasure_coherent
    M10.Examples.openedApplication_compile_success compiledExplicitObjectOpen

end DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerSuccessConservativity
