import Coercions.Translation.ManySorted.Intersections.GeneralExpression.CompilerConservativity
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.ObjectConsumerCompilation

/-!
# Executable M10/M11 compiler conservativity regressions

The M10 typing embedding is executable, so these tests send the original M10
derivations directly through the M11 compiler. They cover a literal object
argument, a stable path established by one open, a computed consumer, and an
explicit open around an object-producing computation. Each generated target
artifact is accepted by the standalone checker and has the same erasure as
the corresponding M10 artifact. The success equations below expose the
actual compiler results, rather than recording only that the options are
inhabited.

This is executable regression coverage, not an unrestricted totality theorem
for the M11 compiler. `Compiler.Ready` does not state that its layout agrees
with its target context, and M11 intentionally rejects source types containing
nested object bounds that M10's recursive static translation accepts. A total
M10-success-implies-M11-success theorem therefore needs both a stronger
readiness invariant and an explicit embeddable-source restriction.

Nor do the independently generated terms coincide syntactically: M11's
payload transport records a value adapter even in a reflexive embedded case.
`CompilerConservativity.exact_m10_term_artifact_as_m11` states the stronger
honest artifact result: once readiness and result translation agree, the
already checked M10 target term itself is a valid M11 artifact. The generated
compiler results below are compared at their target indices and exact erasure.
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

/-! The four executable regressions expose exact compiler-success equations.
These are stronger interfaces than the `isSome` decision proofs above: clients
can rewrite with the concrete generated artifacts. -/

theorem literal_argument_compile_success :
    compileEmbeddedTerm? M10.Examples.literalApplicationTyping =
      some compiledLiteralArgument :=
  Option.eq_some_of_isSome literal_argument_compiles

theorem stable_path_compile_success :
    compileEmbeddedTerm? M10.Examples.stableOpenApplicationTyping =
      some compiledStablePath :=
  Option.eq_some_of_isSome stable_path_compiles

theorem computed_consumer_compile_success :
    compileEmbeddedTerm? M10.Examples.computedConsumerApplicationTyping =
      some compiledComputedConsumer :=
  Option.eq_some_of_isSome computed_consumer_compiles

theorem explicit_object_open_compile_success :
    compileEmbeddedTerm? M10.Examples.openedApplicationTyping =
      some compiledExplicitObjectOpen :=
  Option.eq_some_of_isSome explicit_object_open_compiles

/-- Closed embedded computations at the common `empty / one` interface have
the same checked target indices.  This covers all four regressions above and
does not identify their independently generated evidence syntax. -/
theorem empty_one_target_indices_conservative
    {term : DOTCapture.Acyclic.GeneralExpression.Term 0}
    {ready : DOTCaptureToManySortedFC.Acyclic.RuntimeContext.Ready
      (DOTCapture.Acyclic.Ctx.nil : DOTCapture.Acyclic.Ctx 0)}
    (old : DOTCaptureToManySortedFC.Acyclic.GeneralExpression.Compiler.CompiledTerm
      ready term DOTCapture.Acyclic.Capture.empty DOTCapture.Acyclic.Ty.one)
    (new : M11.Compiler.CompiledTerm M11.emptyReady
      (M11.Embedding.embedTerm term)
      (DOTCapture.Intersections.Source.embedM10Capture
        DOTCapture.Acyclic.Capture.empty)
      (DOTCapture.Intersections.Source.embedM10Ty DOTCapture.Acyclic.Ty.one)) :
    old.targetUse = new.targetUse ∧ old.targetType = new.targetType := by
  have oldUse : old.targetUse = ManySortedFC.Capture.empty := by
    have translated := old.useTranslated
    simpa [DOTCaptureToManySortedFC.Acyclic.StaticTranslation.translateCapture?]
      using translated.symm
  have oldType : old.targetType = ManySortedFC.Ty.one := by
    have translated := old.typeTranslated
    simpa [DOTCaptureToManySortedFC.Acyclic.StaticTranslation.translateTy?]
      using translated.symm
  have newUse : new.targetUse = ManySortedFC.Capture.empty := by
    have translated := new.useTranslated
    simpa [DOTCapture.Intersections.Source.embedM10Capture,
      DOTCaptureToManySortedFC.Intersections.ObjectPreparation.translateCapture]
      using translated.symm
  have newType : new.targetType = ManySortedFC.Ty.one := by
    have translated := new.typeTranslated
    simpa [DOTCapture.Intersections.Source.embedM10Ty,
      DOTCaptureToManySortedFC.Intersections.ObjectPreparation.translateType]
      using translated.symm
  exact ⟨oldUse.trans newUse.symm, oldType.trans newType.symm⟩

/-! ## Exact artifact reuse

The literal regression discharges the agreement premises of the general exact
reindexing theorem.  `m10LiteralAsM11Artifact` contains the original M10 target
term definitionally, while satisfying the M11 artifact interface and checker.
-/

private theorem literal_type_translation_agrees :
    DOTCaptureToManySortedFC.Intersections.ObjectPreparation.translateType
        M11.emptyReady.layout
        (DOTCapture.Intersections.Source.embedM10Ty
          DOTCapture.Acyclic.Ty.one) =
      .ok M10.Examples.compiledLiteralApplication.targetType := by
  have target : M10.Examples.compiledLiteralApplication.targetType =
      ManySortedFC.Ty.one := by
    have translated :=
      M10.Examples.compiledLiteralApplication.typeTranslated
    simpa [DOTCaptureToManySortedFC.Acyclic.StaticTranslation.translateTy?]
      using translated.symm
  rw [target]
  simp [DOTCapture.Intersections.Source.embedM10Ty,
    DOTCaptureToManySortedFC.Intersections.ObjectPreparation.translateType]
  rfl

noncomputable def m10LiteralAsM11Artifact :=
  DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativity.exact_m10_term_artifact_as_m11
    M10.Examples.literalApplication_compile_success
    DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativity.emptyReadyAgreement
    (by rfl)
    literal_type_translation_agrees

@[simp]
theorem m10LiteralAsM11Artifact_term :
    m10LiteralAsM11Artifact.term =
      M10.Examples.compiledLiteralApplication.term := rfl

theorem m10LiteralAsM11Artifact_checker_accepts :
    Tm.synth M11.emptyReady.target m10LiteralAsM11Artifact.term =
      some (m10LiteralAsM11Artifact.targetUse,
        m10LiteralAsM11Artifact.targetType) :=
  m10LiteralAsM11Artifact.checkerAccepts

/-! ## Boundary: independently generated evidence syntax

The independent M11 compiler inserts a payload-transport adapter in this
embedded case.  Counting adapter nodes gives a small, mechanically checked
counterexample to raw generated-term equality. -/

private def countAdapters :
    {scope : ManySortedFC.Sig} → ManySortedFC.Tm scope → Nat
  | _, .var _ => 0
  | _, .unit => 0
  | _, .lam _ _ _ body _ => countAdapters body
  | _, .app function argument =>
      countAdapters function + countAdapters argument
  | _, .let' _ _ rhs body _ => countAdapters rhs + countAdapters body
  | _, .adapt term _ => countAdapters term + 1
  | _, .lock _ _ _ body _ => countAdapters body
  | _, .unlock _ term _ => countAdapters term
  | _, .slam _ _ body _ => countAdapters body
  | _, .sapp _ function _ _ => countAdapters function
  | _, .pack _ _ _ _ _ payload _ => countAdapters payload
  | _, .open _ _ _ _ package body _ =>
      countAdapters package + countAdapters body
  | _, .use term _ => countAdapters term

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
theorem literal_argument_generated_terms_ne :
    M10.Examples.compiledLiteralApplication.term ≠
      compiledLiteralArgument.term := by
  intro equal
  have sameCount := congrArg countAdapters equal
  have oldCount :
      countAdapters M10.Examples.compiledLiteralApplication.term = 1 := by
    rfl
  have newCount : countAdapters compiledLiteralArgument.term = 2 := by
    native_decide
  have impossible : 1 = 2 := oldCount.symm.trans (sameCount.trans newCount)
  omega

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
