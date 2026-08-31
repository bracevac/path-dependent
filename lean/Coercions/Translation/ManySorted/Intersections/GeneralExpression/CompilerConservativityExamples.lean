import Coercions.DOT.Captures.Intersections.GeneralExpression.TypingEmbeddingExamples
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.ObjectConsumerCompilation
import Coercions.Translation.ManySorted.Intersections.GeneralExpression.CompilerConservativity

/-!
# Concrete M10/M11 compiler conservativity regressions

These closed examples run the public M10 and M11 compilers on the same source
programs.  M11 changes static binders and evidence syntax, so conservativity is
stated at the independently checked runtime boundary: both artifacts are
accepted by their target checkers and erase to the same term.
-/

namespace DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativityExamples

namespace M10

export DOTCaptureToManySortedFC.Acyclic.GeneralExpression.ObjectConsumerCompilation
  (compiledLiteralApplication compiledComputedConsumerApplication
    compiledOpenedApplication literalApplication_compile_success
    computedConsumerApplication_compile_success openedApplication_compile_success)

end M10

open DOTCaptureToManySortedFC.Intersections.GeneralExpression
open DOTCapture.Intersections.GeneralExpression

abbrev emptyReady := CompilerConservativity.emptyReady

/-! ## Explicit witnesses for the embedded programs

These three closed regressions spell out the embedded derivations to keep
their target construction visible. Their term indices remain exactly
`Embedding.embedTerm` of the M10 programs. The executable embedding itself is
tested directly in `CompilerSuccessConservativity`.
-/

namespace Embedded

namespace M10Source

export DOTCapture.Acyclic.GeneralExpression.ObjectConsumerExamples
  (exactSignature broadSignature literal broadConsumer literalApplication
    computedBroadConsumer computedConsumerApplication computedObject
    openedApplication)

end M10Source

def exactObject {scope : Scope} : ObjectType scope :=
  .mk
    (.inter
      (.typeMember DOTCapture.Intersections.Source.m10TypeLabel .one .one)
      (.captureMember DOTCapture.Intersections.Source.m10CaptureLabel
        .empty .empty))
    (.capturing
      (.ref (.localCaptureMember
        DOTCapture.Intersections.Source.m10CaptureLabel))
      (.ref (.localTypeMember DOTCapture.Intersections.Source.m10TypeLabel)))
    .empty

def broadObject {scope : Scope} : ObjectType scope :=
  .mk
    (.inter
      (.typeMember DOTCapture.Intersections.Source.m10TypeLabel .bot .top)
      (.captureMember DOTCapture.Intersections.Source.m10CaptureLabel
        .empty .empty))
    (.capturing
      (.ref (.localCaptureMember
        DOTCapture.Intersections.Source.m10CaptureLabel))
      (.ref (.localTypeMember DOTCapture.Intersections.Source.m10TypeLabel)))
    .empty

abbrev model {scope : Scope} : LocalModel.Model scope where
  typeMember := fun _ => .one
  captureMember := fun _ => .empty

abbrev identityMapping {scope : Scope} : LocalModel.Mapping scope :=
  LocalModel.Mapping.identity

abbrev emptyContext : Ctx 0 := .nil

def exactRealization {scope : Scope} (context : Ctx scope) :
    ObjectType.Realization context (exactObject (scope := scope)) where
  model := model
  constraints := by
    change Interface.Realizes context model
      (.inter
        (.typeMember DOTCapture.Intersections.Source.m10TypeLabel .one .one)
        (.captureMember DOTCapture.Intersections.Source.m10CaptureLabel
          .empty .empty))
    exact .inter
      (.typeMember .refl .refl)
      (.captureMember .refl .refl)

def exactAdaptsBroad {scope : Scope} (context : Ctx scope) :
    ObjectType.Adapts context (exactObject (scope := scope))
      (broadObject (scope := scope)) where
  mapping := identityMapping
  theory := by
    change Interface.Derives context (exactObject.interface)
      LocalModel.Mapping.identity broadObject.interface
    exact .inter
      (.typeMember
        (.trans (.ambient .typeBottom) (.typeLower (.left .here)))
        (.trans (.typeUpper (.left .here)) (.ambient .typeTop)))
      (.captureMember
        (.trans (.ambient .refl) (.captureLower (.right .here)))
        (.trans (.captureUpper (.right .here)) (.ambient .refl)))
  constraints := by
    intro availableModel realization
    rw [LocalModel.Mapping.apply_identity]
    cases realization with
    | inter _ captureProof =>
        cases captureProof with
        | captureMember lower upper =>
            exact .inter
              (.typeMember .typeBottom .typeTop)
              (.captureMember lower upper)
  representation := by
    intro availableModel _
    rw [LocalModel.Mapping.apply_identity]
    exact .refl
  outerCapture := by
    change CaptureIncludes context .empty .empty
    exact .refl

def literal {scope : Scope} : Value scope :=
  .object exactObject .unit

def literalValueTyping {scope : Scope} (context : Ctx scope) :
    Value.HasType context (literal (scope := scope))
      (exactObject (scope := scope)).formedType :=
  .object (exactRealization context) .unit
    (by change TypeIncludes context .one .one; exact .refl)
    (by change CaptureIncludes context .empty .empty; exact .refl)
    (by change CaptureIncludes context .empty .empty; exact .refl)

def literalArgument {scope : Scope} (context : Ctx scope) :
    ObjectArgument.HasType context (.ret (literal (scope := scope)))
      (broadObject (scope := scope)) :=
  .literal (exactRealization context) .unit
    (by change TypeIncludes context .one .one; exact .refl)
    (by change CaptureIncludes context .empty .empty; exact .refl)
    (by change CaptureIncludes context .empty .empty; exact .refl)
    (exactAdaptsBroad context)
    (by change CaptureIncludes context .empty .empty; exact .refl)

def broadConsumer {scope : Scope} : Value scope :=
  .lam broadObject.formedType .one (.ret .unit)

def broadConsumerFunction {scope : Scope} (context : Ctx scope) :
    ObjectFunction.HasType context (.ret (broadConsumer (scope := scope)))
      .empty (broadObject (scope := scope)) .one .empty :=
  .embeddedReturned (.ret .unit) .captureEmpty

def literalApplication : Term 0 :=
  .app (.ret broadConsumer) (.ret literal)

def literalApplicationTypingRaw :
    Term.HasType emptyContext
      literalApplication
      (.union .empty .empty) .one :=
  .embeddedObjectApp (broadConsumerFunction emptyContext)
    (literalArgument emptyContext)

def literalApplicationTyping :
    Term.HasType emptyContext
      literalApplication .empty .one :=
  .use literalApplicationTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

def computedConsumer : Term 0 :=
  .let' (.capturing .empty (.arr broadObject.formedType .one))
    (.ret .unit) (.ret broadConsumer)

def computedConsumerFunctionRaw :
    ObjectFunction.HasType emptyContext
      computedConsumer
      (.union .empty .empty) broadObject .one .empty :=
  .letPlain (bound := .one) trivial (.ret .unit)
    (broadConsumerFunction (emptyContext.extendTerm .one)) .captureEmpty

def computedConsumerFunction :
    ObjectFunction.HasType emptyContext
      computedConsumer
      .empty broadObject .one .empty :=
  .use computedConsumerFunctionRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

def computedConsumerApplication : Term 0 :=
  .app computedConsumer (.ret literal)

def computedConsumerApplicationTypingRaw :
    Term.HasType emptyContext
      computedConsumerApplication
      (.union .empty .empty) .one :=
  .embeddedObjectApp computedConsumerFunction (literalArgument emptyContext)

def computedConsumerApplicationTyping :
    Term.HasType emptyContext
      computedConsumerApplication .empty .one :=
  .use computedConsumerApplicationTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

abbrev StableContext : Ctx 1 :=
  emptyContext.extendTerm (exactObject (scope := 0)).formedType

def stableExposure : DOTCapture.Intersections.Source.ExposesObject
    StableContext (.var .here) (exactObject (scope := 1)) :=
  .variable rfl

def stableArgument :
    ObjectArgument.HasType StableContext (.ret (.var .here))
      (broadObject (scope := 1)) :=
  .stable (name := .here) (available := exactObject) rfl
    (exactAdaptsBroad StableContext)
    (by
      change CaptureIncludes StableContext
        (.ref (.captureMember (.var .here)
          DOTCapture.Intersections.Source.m10CaptureLabel)) .empty
      exact .source (.upper (.captureMember stableExposure (.right .here))))

def stableApplicationTypingRaw :
    Term.HasType StableContext
      (.app (.ret broadConsumer) (.ret (.var .here)))
      (.union .empty .empty) .one :=
  .embeddedObjectApp (broadConsumerFunction StableContext) stableArgument

def stableApplicationTyping :
    Term.HasType StableContext
      (.app (.ret broadConsumer) (.ret (.var .here)))
      .empty .one :=
  .use stableApplicationTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

def computedObject : Term 0 :=
  .let' exactObject.formedType (.ret literal) (.ret (.var .here))

def computedObjectTypingRaw :
    Term.HasType emptyContext computedObject
      (.union .empty .empty) exactObject.formedType :=
  .embeddedObjectLet (.ret (literalValueTyping emptyContext))
    (.ret (Value.HasType.var (name := (.here : DOTCapture.Acyclic.Var 1))))
    .captureEmpty

def computedObjectTyping :
    Term.HasType emptyContext computedObject
      .empty exactObject.formedType :=
  .use computedObjectTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

def openedApplication : Term 0 :=
  .let' .one computedObject
    (.app (.ret broadConsumer) (.ret (.var .here)))

def openedApplicationTypingRaw :
    Term.HasType emptyContext
      openedApplication
      (.union .empty .empty) .one :=
  .embeddedObjectLet computedObjectTyping stableApplicationTyping
    .captureEmpty

def openedApplicationTyping :
    Term.HasType emptyContext
      openedApplication .empty .one :=
  .use openedApplicationTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

/- The computable witnesses are the literal structural embeddings of the
corresponding M10 programs, not replacement source examples. -/
theorem literalApplication_is_embedding :
    literalApplication =
      Embedding.embedTerm M10Source.literalApplication := by
  native_decide

theorem computedConsumerApplication_is_embedding :
    computedConsumerApplication =
      Embedding.embedTerm M10Source.computedConsumerApplication := by
  native_decide

theorem openedApplication_is_embedding :
    openedApplication = Embedding.embedTerm M10Source.openedApplication := by
  native_decide

end Embedded

/-! ## Public compiler success -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
abbrev literalApplication_compiles :
    (Recursive.compileTerm? emptyReady
      Embedded.literalApplicationTyping).isSome = true := by
  native_decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
abbrev computedConsumerApplication_compiles :
    (Recursive.compileTerm? emptyReady
      Embedded.computedConsumerApplicationTyping).isSome = true := by
  native_decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
abbrev openedApplication_compiles :
    (Recursive.compileTerm? emptyReady
      Embedded.openedApplicationTyping).isSome = true := by
  native_decide

def compiledLiteralApplication :=
  (Recursive.compileTerm? emptyReady
    Embedded.literalApplicationTyping).get literalApplication_compiles

def compiledComputedConsumerApplication :=
  (Recursive.compileTerm? emptyReady
    Embedded.computedConsumerApplicationTyping).get
      computedConsumerApplication_compiles

def compiledOpenedApplication :=
  (Recursive.compileTerm? emptyReady
    Embedded.openedApplicationTyping).get openedApplication_compiles

/-! ## Independently checked artifacts -/

theorem literal_m11_checker_accepts :
    ManySortedFC.Tm.synth emptyReady.target compiledLiteralApplication.term =
      some (compiledLiteralApplication.targetUse,
        compiledLiteralApplication.targetType) :=
  compiledLiteralApplication.checkerAccepts

theorem computed_consumer_m11_checker_accepts :
    ManySortedFC.Tm.synth emptyReady.target
        compiledComputedConsumerApplication.term =
      some (compiledComputedConsumerApplication.targetUse,
        compiledComputedConsumerApplication.targetType) :=
  compiledComputedConsumerApplication.checkerAccepts

theorem opened_m11_checker_accepts :
    ManySortedFC.Tm.synth emptyReady.target compiledOpenedApplication.term =
      some (compiledOpenedApplication.targetUse,
        compiledOpenedApplication.targetType) :=
  compiledOpenedApplication.checkerAccepts

theorem literal_m10_checker_accepts :
    (ManySortedFC.Tm.check
      DOTCaptureToManySortedFC.Acyclic.GeneralExpression.ObjectConsumerCompilation.emptyReady.target
      M10.compiledLiteralApplication.term).isSome = true :=
  DOTCaptureToManySortedFC.Acyclic.GeneralExpression.ObjectConsumerCompilation.literalApplication_is_independently_accepted

theorem computed_consumer_m10_checker_accepts :
    (ManySortedFC.Tm.check
      DOTCaptureToManySortedFC.Acyclic.GeneralExpression.ObjectConsumerCompilation.emptyReady.target
      M10.compiledComputedConsumerApplication.term).isSome = true :=
  DOTCaptureToManySortedFC.Acyclic.GeneralExpression.ObjectConsumerCompilation.computedConsumerApplication_is_independently_accepted

theorem opened_m10_checker_accepts :
    (ManySortedFC.Tm.check
      DOTCaptureToManySortedFC.Acyclic.GeneralExpression.ObjectConsumerCompilation.emptyReady.target
      M10.compiledOpenedApplication.term).isSome = true :=
  DOTCaptureToManySortedFC.Acyclic.GeneralExpression.ObjectConsumerCompilation.openedApplication_is_independently_accepted

/-! ## Concrete M10/M11 operational conservativity -/

def compiledEmbeddedLiteralApplication :
    Recursive.CompiledTerm emptyReady
      (Embedding.embedTerm Embedded.M10Source.literalApplication)
      (DOTCapture.Intersections.Source.embedM10Capture
        DOTCapture.Acyclic.Capture.empty)
      (DOTCapture.Intersections.Source.embedM10Ty
        DOTCapture.Acyclic.Ty.one) := by
  rw [<- Embedded.literalApplication_is_embedding]
  simpa [DOTCapture.Intersections.Source.embedM10Capture,
    DOTCapture.Intersections.Source.embedM10Ty] using
    compiledLiteralApplication

def compiledEmbeddedComputedConsumerApplication :
    Recursive.CompiledTerm emptyReady
      (Embedding.embedTerm Embedded.M10Source.computedConsumerApplication)
      (DOTCapture.Intersections.Source.embedM10Capture
        DOTCapture.Acyclic.Capture.empty)
      (DOTCapture.Intersections.Source.embedM10Ty
        DOTCapture.Acyclic.Ty.one) := by
  rw [<- Embedded.computedConsumerApplication_is_embedding]
  simpa [DOTCapture.Intersections.Source.embedM10Capture,
    DOTCapture.Intersections.Source.embedM10Ty] using
    compiledComputedConsumerApplication

def compiledEmbeddedOpenedApplication :
    Recursive.CompiledTerm emptyReady
      (Embedding.embedTerm Embedded.M10Source.openedApplication)
      (DOTCapture.Intersections.Source.embedM10Capture
        DOTCapture.Acyclic.Capture.empty)
      (DOTCapture.Intersections.Source.embedM10Ty
        DOTCapture.Acyclic.Ty.one) := by
  rw [<- Embedded.openedApplication_is_embedding]
  simpa [DOTCapture.Intersections.Source.embedM10Capture,
    DOTCapture.Intersections.Source.embedM10Ty] using
    compiledOpenedApplication

theorem literal_compilers_have_equal_erasure :
    M10.compiledLiteralApplication.term.erase =
      compiledEmbeddedLiteralApplication.term.erase :=
  CompilerConservativity.closed_m10_m11_term_erasure_coherent
    M10.literalApplication_compile_success
    compiledEmbeddedLiteralApplication

theorem computed_consumer_compilers_have_equal_erasure :
    M10.compiledComputedConsumerApplication.term.erase =
      compiledEmbeddedComputedConsumerApplication.term.erase :=
  CompilerConservativity.closed_m10_m11_term_erasure_coherent
    M10.computedConsumerApplication_compile_success
    compiledEmbeddedComputedConsumerApplication

theorem opened_compilers_have_equal_erasure :
    M10.compiledOpenedApplication.term.erase =
      compiledEmbeddedOpenedApplication.term.erase :=
  CompilerConservativity.closed_m10_m11_term_erasure_coherent
    M10.openedApplication_compile_success
    compiledEmbeddedOpenedApplication

end DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativityExamples
