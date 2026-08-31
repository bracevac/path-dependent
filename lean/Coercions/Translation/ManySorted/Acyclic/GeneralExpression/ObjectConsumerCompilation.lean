import Coercions.DOT.Captures.Acyclic.GeneralExpression.ObjectConsumerExamples
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.CompilerChecker
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.CompilerErasure

/-!
# Compiled negative object consumers

These regressions exercise the polarized source compiler rather than only the
generic target interface.  They cover direct use of a canonical literal,
reuse of an already-open object root, a computed consumer, and selection from
the stable root installed for an object parameter.
-/

namespace DOTCaptureToManySortedFC.Acyclic.GeneralExpression.ObjectConsumerCompilation

namespace Source

export DOTCapture.Acyclic.GeneralExpression
  (Capture Ctx ObjectSig Term Ty Value)

namespace Examples

export DOTCapture.Acyclic.GeneralExpression.ObjectConsumerExamples
  (exactSignature broadSignature exactAdaptsBroad literal literalTyping
    literalArgument broadConsumer broadConsumerFunction literalApplication
    literalApplicationTyping exactObjectContext stableArgument stableApplication
    stableApplicationTyping
    selectingConsumer selectingConsumerFunction selectingBody exactExposure
    resultType
    computedBroadConsumer computedBroadConsumerTyping
    computedConsumerApplication computedConsumerApplicationTyping
    computedObject computedObjectTyping openedApplication
    openedApplicationTyping)

end Examples

end Source

namespace Target

export ManySortedFC (Capture Ctx Tm Ty)

namespace Tm
export ManySortedFC.Tm (HasType IsValue check synth)
end Tm

end Target

abbrev emptyReady :=
  DOTCaptureToManySortedFC.Acyclic.RuntimeContext.nil

/-! ## Target-shape observations -/

/-- Detect any existential package or opening anywhere in an annotated
artifact.  Static abstraction/application, proof uses, and adapters are
traversed rather than ignored. -/
def hasExistentialBoundary {scope : ManySortedFC.Sig} : Target.Tm scope → Bool
  | .var _ => false
  | .unit => false
  | .lam _ _ _ body _ => hasExistentialBoundary body
  | .app function argument =>
      hasExistentialBoundary function || hasExistentialBoundary argument
  | .let' _ _ rhs body _ =>
      hasExistentialBoundary rhs || hasExistentialBoundary body
  | .adapt term _ => hasExistentialBoundary term
  | .slam _ _ body _ => hasExistentialBoundary body
  | .sapp _ function _ _ => hasExistentialBoundary function
  | .pack _ _ _ _ _ _ _ => true
  | .«open» _ _ _ _ _ _ _ => true
  | .use term _ => hasExistentialBoundary term

/-- The constructor spine required of a direct negative object application.
The outer `use` is only a capture certificate and erases completely. -/
def IsDirectObjectApplication {scope : ManySortedFC.Sig} :
    Target.Tm scope → Prop
  | .use term _ => IsDirectObjectApplication term
  | .app (.sapp _ _ _ _) _ => True
  | _ => False

def IsPackage {scope : ManySortedFC.Sig} : Target.Tm scope → Prop
  | .use term _ => IsPackage term
  | .pack _ _ _ _ _ _ _ => True
  | _ => False

def IsOpenWithDirectBody {scope : ManySortedFC.Sig} :
    Target.Tm scope → Prop
  | .use term _ => IsOpenWithDirectBody term
  | .«open» _ _ _ _ package body _ =>
      IsPackage package ∧ IsDirectObjectApplication body
  | _ => False

def HasLetHead {scope : ManySortedFC.Sig} : Target.Tm scope → Prop
  | .use term _ => HasLetHead term
  | .let' _ _ _ _ _ => True
  | _ => False

def IsDirectComputedConsumerApplication {scope : ManySortedFC.Sig} :
    Target.Tm scope → Prop
  | .use term _ => IsDirectComputedConsumerApplication term
  | .app (.sapp _ function _ _) _ => HasLetHead function
  | _ => False

def IsOpenWithComputedDirectBody {scope : ManySortedFC.Sig} :
    Target.Tm scope → Prop
  | .use term _ => IsOpenWithComputedDirectBody term
  | .«open» _ _ _ _ package body _ =>
      IsPackage package ∧ IsDirectComputedConsumerApplication body
  | _ => False

/-! ## Canonical literal with signature weakening -/

noncomputable abbrev broadInterface_compiles :
    (Compiler.compileObjectSignature? DOTCapture.Acyclic.Ctx.nil
      Source.Examples.broadSignature).isSome = true := by
  rfl

noncomputable abbrev broadInterface :=
  (Compiler.compileObjectSignature? DOTCapture.Acyclic.Ctx.nil
    Source.Examples.broadSignature).get broadInterface_compiles

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
noncomputable abbrev broadConsumer_compiles :
    (Compiler.compileObjectFunction? emptyReady broadInterface
      (Source.Examples.broadConsumerFunction DOTCapture.Acyclic.Ctx.nil)).isSome =
      true := by
  rfl

noncomputable abbrev compiledBroadConsumer :=
  (Compiler.compileObjectFunction? emptyReady broadInterface
    (Source.Examples.broadConsumerFunction DOTCapture.Acyclic.Ctx.nil)).get
      broadConsumer_compiles

/-- This checks the type actually emitted by static abstraction: the outer
captured type contains a universal over the complete model theory, whose body
is another captured runtime arrow. -/
theorem broadConsumer_is_independently_accepted :
    Target.Tm.synth emptyReady.target compiledBroadConsumer.term =
      some (compiledBroadConsumer.targetUse,
        Compiler.Negative.ambientResultType
          (Compiler.Object.theory broadInterface.bounds)
          Compiler.Object.payloadType compiledBroadConsumer.resultType
          compiledBroadConsumer.outerCapture) :=
  ManySortedFC.Tm.synth_complete compiledBroadConsumer.typing

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
noncomputable abbrev literalApplication_compiles :
    (Compiler.compilePolarizedTerm? emptyReady
      Source.Examples.literalApplicationTyping).isSome = true := by
  rfl

noncomputable abbrev compiledLiteralApplication :=
  (Compiler.compilePolarizedTerm? emptyReady
    Source.Examples.literalApplicationTyping).get
      literalApplication_compiles

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem literalApplication_compile_success :
    Compiler.compilePolarizedTerm? emptyReady
        Source.Examples.literalApplicationTyping =
      some compiledLiteralApplication := by
  rfl

theorem literalApplication_is_independently_accepted :
    (Target.Tm.check emptyReady.target
      compiledLiteralApplication.term).isSome = true :=
  compiledLiteralApplication.checker_accepts

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem literalApplication_is_direct :
    IsDirectObjectApplication compiledLiteralApplication.term := by
  change True
  trivial

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem literalApplication_has_no_existential_boundary :
    hasExistentialBoundary compiledLiteralApplication.term = false := by
  rfl

/-! ## Recursive literal payload -/

/-- This payload is a lambda whose body itself uses polarized object
application.  It prevents the literal-argument path from silently falling
back to the older positive value compiler. -/
def nestedApplication {scope : DOTCapture.Acyclic.Scope} : Source.Term scope :=
  .app (.ret Source.Examples.broadConsumer)
    (.ret Source.Examples.literal)

private def nestedApplicationRaw {scope : DOTCapture.Acyclic.Scope}
    (context : DOTCapture.Acyclic.Ctx scope) :
    DOTCapture.Acyclic.GeneralExpression.Term.HasType context
      nestedApplication (.union .empty .empty) .one :=
  .objectApp (Source.Examples.broadConsumerFunction context)
    (Source.Examples.literalArgument context)

def nestedApplicationTyping {scope : DOTCapture.Acyclic.Scope}
    (context : DOTCapture.Acyclic.Ctx scope) :
    DOTCapture.Acyclic.GeneralExpression.Term.HasType context
      nestedApplication .empty .one :=
  .use (nestedApplicationRaw context)
    (.captureUnionElim .captureEmpty .captureEmpty)

def functionSignature {scope : DOTCapture.Acyclic.Scope} :
    Source.ObjectSig scope :=
  .bounds (.arr .one .one) (.arr .one .one) .empty .empty

def functionPayload {scope : DOTCapture.Acyclic.Scope} : Source.Value scope :=
  .lam .one .one nestedApplication

def functionPayloadTyping {scope : DOTCapture.Acyclic.Scope}
    (context : DOTCapture.Acyclic.Ctx scope) :
    DOTCapture.Acyclic.GeneralExpression.Value.HasType context functionPayload
      (.capturing .empty (.arr .one .one)) :=
  .lam rfl (nestedApplicationTyping (context.extendTerm .one)) .captureEmpty

def functionalLiteral {scope : DOTCapture.Acyclic.Scope} : Source.Value scope :=
  .object functionSignature (.arr .one .one) .empty functionPayload

def functionalLiteralArgument {scope : DOTCapture.Acyclic.Scope}
    (context : DOTCapture.Acyclic.Ctx scope) :
    DOTCapture.Acyclic.GeneralExpression.ObjectArgument.HasType context
      (.ret functionalLiteral) functionSignature :=
  .literal .refl .refl .refl .refl (functionPayloadTyping context)
    .refl .refl
    (DOTCapture.Acyclic.GeneralExpression.ObjectSig.Adapts.refl _)

def functionalConsumer {scope : DOTCapture.Acyclic.Scope} :
    Source.Value scope :=
  .lam (functionSignature.formedType) .one (.ret .unit)

def functionalConsumerFunction {scope : DOTCapture.Acyclic.Scope}
    (context : DOTCapture.Acyclic.Ctx scope) :
    DOTCapture.Acyclic.GeneralExpression.ObjectFunction.HasType context
      (.ret functionalConsumer) .empty functionSignature .one .empty :=
  .returned (.ret .unit) .captureEmpty

def recursivePayloadApplication : Source.Term 0 :=
  .app (.ret functionalConsumer) (.ret functionalLiteral)

private def recursivePayloadApplicationRaw :
    DOTCapture.Acyclic.GeneralExpression.Term.HasType DOTCapture.Acyclic.Ctx.nil
      recursivePayloadApplication (.union .empty .empty) .one :=
  .objectApp (functionalConsumerFunction DOTCapture.Acyclic.Ctx.nil)
    (functionalLiteralArgument DOTCapture.Acyclic.Ctx.nil)

def recursivePayloadApplicationTyping :
    DOTCapture.Acyclic.GeneralExpression.Term.HasType DOTCapture.Acyclic.Ctx.nil
      recursivePayloadApplication .empty .one :=
  .use recursivePayloadApplicationRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
noncomputable abbrev recursivePayloadApplication_compiles :
    (Compiler.compilePolarizedTerm? emptyReady
      recursivePayloadApplicationTyping).isSome = true := by
  rfl

noncomputable abbrev compiledRecursivePayloadApplication :=
  (Compiler.compilePolarizedTerm? emptyReady
    recursivePayloadApplicationTyping).get recursivePayloadApplication_compiles

theorem recursivePayloadApplication_is_independently_accepted :
    (Target.Tm.check emptyReady.target
      compiledRecursivePayloadApplication.term).isSome = true :=
  compiledRecursivePayloadApplication.checker_accepts

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
theorem recursivePayloadApplication_has_no_existential_boundary :
    hasExistentialBoundary compiledRecursivePayloadApplication.term = false := by
  rfl

/-! ## One explicit open establishes one stable root -/

def stableOpenApplication : Source.Term 0 :=
  .let' .one (.ret Source.Examples.literal)
    Source.Examples.stableApplication

private def stableOpenApplicationRaw :
    DOTCapture.Acyclic.GeneralExpression.Term.HasType DOTCapture.Acyclic.Ctx.nil
      stableOpenApplication (.union .empty .empty) .one :=
  .letObject (.ret (Source.Examples.literalTyping DOTCapture.Acyclic.Ctx.nil))
    Source.Examples.stableApplicationTyping .captureEmpty

def stableOpenApplicationTyping :
    DOTCapture.Acyclic.GeneralExpression.Term.HasType DOTCapture.Acyclic.Ctx.nil
      stableOpenApplication .empty .one :=
  .use stableOpenApplicationRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
noncomputable abbrev stableOpenApplication_compiles :
    (Compiler.compilePolarizedTerm? emptyReady
      stableOpenApplicationTyping).isSome = true := by
  rfl

noncomputable abbrev compiledStableOpenApplication :=
  (Compiler.compilePolarizedTerm? emptyReady stableOpenApplicationTyping).get
    stableOpenApplication_compiles

theorem stableOpenApplication_is_independently_accepted :
    (Target.Tm.check emptyReady.target
      compiledStableOpenApplication.term).isSome = true :=
  compiledStableOpenApplication.checker_accepts

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem stableOpenApplication_opens_once_then_applies_directly :
    IsOpenWithDirectBody compiledStableOpenApplication.term := by
  change True ∧ True
  exact ⟨trivial, trivial⟩

/-! ## Computed consumer applied to a stable root -/

def computedConsumerAt {scope : DOTCapture.Acyclic.Scope} :
    Source.Term scope :=
  .let'
    (.capturing .empty
      (.arr Source.Examples.broadSignature.formedType .one))
    (.ret .unit) (.ret Source.Examples.broadConsumer)

private def computedConsumerAtRaw {scope : DOTCapture.Acyclic.Scope}
    (context : DOTCapture.Acyclic.Ctx scope) :
    DOTCapture.Acyclic.GeneralExpression.ObjectFunction.HasType context
      computedConsumerAt (.union .empty .empty)
      Source.Examples.broadSignature .one .empty :=
  .letPlain (bound := .one) rfl (.ret .unit)
    (Source.Examples.broadConsumerFunction (context.extendTerm .one))
    .captureEmpty

def computedConsumerAtTyping {scope : DOTCapture.Acyclic.Scope}
    (context : DOTCapture.Acyclic.Ctx scope) :
    DOTCapture.Acyclic.GeneralExpression.ObjectFunction.HasType context
      computedConsumerAt .empty Source.Examples.broadSignature .one .empty :=
  .use (computedConsumerAtRaw context)
    (.captureUnionElim .captureEmpty .captureEmpty)

def computedStableApplication : Source.Term 1 :=
  .app computedConsumerAt (.ret (.var .here))

private def computedStableApplicationRaw :
    DOTCapture.Acyclic.GeneralExpression.Term.HasType
      Source.Examples.exactObjectContext computedStableApplication
      (.union .empty .empty) .one :=
  .objectApp
    (computedConsumerAtTyping Source.Examples.exactObjectContext)
    Source.Examples.stableArgument

def computedStableApplicationTyping :
    DOTCapture.Acyclic.GeneralExpression.Term.HasType
      Source.Examples.exactObjectContext computedStableApplication
      .empty .one :=
  .use computedStableApplicationRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

def computedStableOpenApplication : Source.Term 0 :=
  .let' .one (.ret Source.Examples.literal) computedStableApplication

private def computedStableOpenApplicationRaw :
    DOTCapture.Acyclic.GeneralExpression.Term.HasType DOTCapture.Acyclic.Ctx.nil
      computedStableOpenApplication (.union .empty .empty) .one :=
  .letObject (.ret (Source.Examples.literalTyping DOTCapture.Acyclic.Ctx.nil))
    computedStableApplicationTyping .captureEmpty

def computedStableOpenApplicationTyping :
    DOTCapture.Acyclic.GeneralExpression.Term.HasType DOTCapture.Acyclic.Ctx.nil
      computedStableOpenApplication .empty .one :=
  .use computedStableOpenApplicationRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
noncomputable abbrev computedStableOpenApplication_compiles :
    (Compiler.compilePolarizedTerm? emptyReady
      computedStableOpenApplicationTyping).isSome = true := by
  rfl

noncomputable abbrev compiledComputedStableOpenApplication :=
  (Compiler.compilePolarizedTerm? emptyReady
    computedStableOpenApplicationTyping).get
      computedStableOpenApplication_compiles

theorem computedStableOpenApplication_is_independently_accepted :
    (Target.Tm.check emptyReady.target
      compiledComputedStableOpenApplication.term).isSome = true :=
  compiledComputedStableOpenApplication.checker_accepts

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
theorem computedStableOpenApplication_keeps_computed_scrutinee :
    IsOpenWithComputedDirectBody
      compiledComputedStableOpenApplication.term := by
  change True ∧ True
  exact ⟨trivial, trivial⟩

/-! ## Computed consumer -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
noncomputable abbrev computedConsumerApplication_compiles :
    (Compiler.compilePolarizedTerm? emptyReady
      Source.Examples.computedConsumerApplicationTyping).isSome = true := by
  rfl

noncomputable abbrev compiledComputedConsumerApplication :=
  (Compiler.compilePolarizedTerm? emptyReady
    Source.Examples.computedConsumerApplicationTyping).get
      computedConsumerApplication_compiles

theorem computedConsumerApplication_is_independently_accepted :
    (Target.Tm.check emptyReady.target
      compiledComputedConsumerApplication.term).isSome = true :=
  compiledComputedConsumerApplication.checker_accepts

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem computedConsumerApplication_is_direct :
    IsDirectObjectApplication compiledComputedConsumerApplication.term := by
  change True
  trivial

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem computedConsumerApplication_keeps_computation_in_static_scrutinee :
    IsDirectComputedConsumerApplication
      compiledComputedConsumerApplication.term := by
  change True
  trivial

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem computedConsumerApplication_has_no_existential_boundary :
    hasExistentialBoundary compiledComputedConsumerApplication.term = false := by
  rfl

/-! ## Selection inside the consumer -/

def exactLiteralArgument :
    DOTCapture.Acyclic.GeneralExpression.ObjectArgument.HasType
      DOTCapture.Acyclic.Ctx.nil (.ret Source.Examples.literal)
      Source.Examples.exactSignature :=
  .literal .refl .refl .refl .refl .unit .refl .refl
    (DOTCapture.Acyclic.GeneralExpression.ObjectSig.Adapts.refl _)

def selectingApplication : Source.Term 0 :=
  .app (.ret Source.Examples.selectingConsumer)
    (.ret Source.Examples.literal)

private def selectingApplicationRaw :
    DOTCapture.Acyclic.GeneralExpression.Term.HasType DOTCapture.Acyclic.Ctx.nil
      selectingApplication (.union .empty .empty)
      Source.Examples.resultType :=
  .objectApp Source.Examples.selectingConsumerFunction exactLiteralArgument

def selectingApplicationTyping :
    DOTCapture.Acyclic.GeneralExpression.Term.HasType DOTCapture.Acyclic.Ctx.nil
      selectingApplication .empty Source.Examples.resultType :=
  .use selectingApplicationRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
noncomputable abbrev selectingApplication_compiles :
    (Compiler.compilePolarizedTerm? emptyReady
      selectingApplicationTyping).isSome = true := by
  rfl

noncomputable abbrev compiledSelectingApplication :=
  (Compiler.compilePolarizedTerm? emptyReady selectingApplicationTyping).get
    selectingApplication_compiles

theorem selectingApplication_is_independently_accepted :
    (Target.Tm.check emptyReady.target
      compiledSelectingApplication.term).isSome = true :=
  compiledSelectingApplication.checker_accepts

noncomputable abbrev parameterSelection_compiles :
    (Compiler.compilePolarizedTerm?
      DOTCaptureToManySortedFC.Acyclic.RuntimeContext.exactObjectReady
      (DOTCapture.Acyclic.GeneralExpression.Term.HasType.select
        Source.Examples.exactExposure)).isSome = true := by
  rfl

noncomputable abbrev compiledParameterSelection :=
  (Compiler.compilePolarizedTerm?
    DOTCaptureToManySortedFC.Acyclic.RuntimeContext.exactObjectReady
    (DOTCapture.Acyclic.GeneralExpression.Term.HasType.select
      Source.Examples.exactExposure)).get parameterSelection_compiles

theorem parameterSelection_compile_success :
    Compiler.compilePolarizedTerm?
        DOTCaptureToManySortedFC.Acyclic.RuntimeContext.exactObjectReady
        (DOTCapture.Acyclic.GeneralExpression.Term.HasType.select
          Source.Examples.exactExposure) =
      some compiledParameterSelection := by
  rfl

/-- The selection compiler for the object-parameter context emits the
selection term built from that context's canonical resolved receiver. -/
theorem compiled_parameter_selection_uses_resolved_receiver :
    compiledParameterSelection.term =
      SelectionTranslation.term
        ExposureTranslation.Regression.exactResolved := by
  rfl

/-- The object parameter is installed as the receiver slot belonging to the
outer static telescope and its payload lambda.  Selection therefore reuses
those names; it does not allocate a model for the bound runtime value. -/
theorem selecting_parameter_uses_outer_telescope :
    ExposureTranslation.Regression.exactResolved.slot.alpha.name =
        ObjectEncoding.alphaPayloadName ∧
    ExposureTranslation.Regression.exactResolved.slot.chi.name =
        ObjectEncoding.chiPayloadName ∧
    ExposureTranslation.Regression.exactResolved.slot.payload =
        ObjectEncoding.payloadTerm := by
  rw [ExposureTranslation.Regression.exact_resolves_canonical_slot]
  exact ⟨rfl, rfl, rfl⟩

/-- In particular, `x.v` is checked at the type and capture names supplied by
that same telescope. -/
theorem selecting_parameter_member_type :
    SelectionTranslation.selectedPayloadType
        ExposureTranslation.Regression.exactResolved =
      .capturing (.cvar ObjectEncoding.chiPayloadName)
        (.tvar ObjectEncoding.alphaPayloadName) := by
  unfold SelectionTranslation.selectedPayloadType
  rw [ExposureTranslation.Regression.exact_resolves_canonical_slot]
  rfl

/-! ## Explicit-open diagnostic -/

theorem computed_object_argument_reports_explicit_open :
    Compiler.validateObjectArgument Source.Examples.computedObject =
      .error .objectArgumentRequiresExplicitOpen := by
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
noncomputable abbrev openedApplication_compiles :
    (Compiler.compilePolarizedTerm? emptyReady
      Source.Examples.openedApplicationTyping).isSome = true := by
  rfl

noncomputable abbrev compiledOpenedApplication :=
  (Compiler.compilePolarizedTerm? emptyReady
    Source.Examples.openedApplicationTyping).get openedApplication_compiles

theorem openedApplication_is_independently_accepted :
    (Target.Tm.check emptyReady.target
      compiledOpenedApplication.term).isSome = true :=
  compiledOpenedApplication.checker_accepts

/-! ## Compiler exact erasure -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
theorem recursivePayloadApplication_compile_success :
    Compiler.compilePolarizedTerm? emptyReady
        recursivePayloadApplicationTyping =
      some compiledRecursivePayloadApplication := by
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem stableOpenApplication_compile_success :
    Compiler.compilePolarizedTerm? emptyReady stableOpenApplicationTyping =
      some compiledStableOpenApplication := by
  rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
theorem computedStableOpenApplication_compile_success :
    Compiler.compilePolarizedTerm? emptyReady
        computedStableOpenApplicationTyping =
      some compiledComputedStableOpenApplication := by
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem computedConsumerApplication_compile_success :
    Compiler.compilePolarizedTerm? emptyReady
        Source.Examples.computedConsumerApplicationTyping =
      some compiledComputedConsumerApplication := by
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem selectingApplication_compile_success :
    Compiler.compilePolarizedTerm? emptyReady selectingApplicationTyping =
      some compiledSelectingApplication := by
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem openedApplication_compile_success :
    Compiler.compilePolarizedTerm? emptyReady
        Source.Examples.openedApplicationTyping =
      some compiledOpenedApplication := by
  rfl

theorem literalApplication_erases_exactly :
    compiledLiteralApplication.term.erase =
      SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        Source.Examples.literalApplication :=
  CompilerErasure.compilePolarizedTerm_erase
    literalApplication_compile_success

theorem recursivePayloadApplication_erases_exactly :
    compiledRecursivePayloadApplication.term.erase =
      SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        recursivePayloadApplication :=
  CompilerErasure.compilePolarizedTerm_erase
    recursivePayloadApplication_compile_success

theorem stableOpenApplication_erases_exactly :
    compiledStableOpenApplication.term.erase =
      SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        stableOpenApplication :=
  CompilerErasure.compilePolarizedTerm_erase
    stableOpenApplication_compile_success

theorem computedStableOpenApplication_erases_exactly :
    compiledComputedStableOpenApplication.term.erase =
      SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        computedStableOpenApplication :=
  CompilerErasure.compilePolarizedTerm_erase
    computedStableOpenApplication_compile_success

theorem computedConsumerApplication_erases_exactly :
    compiledComputedConsumerApplication.term.erase =
      SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        Source.Examples.computedConsumerApplication :=
  CompilerErasure.compilePolarizedTerm_erase
    computedConsumerApplication_compile_success

theorem selectingApplication_erases_exactly :
    compiledSelectingApplication.term.erase =
      SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        selectingApplication :=
  CompilerErasure.compilePolarizedTerm_erase
    selectingApplication_compile_success

theorem openedApplication_erases_exactly :
    compiledOpenedApplication.term.erase =
      SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        Source.Examples.openedApplication :=
  CompilerErasure.compilePolarizedTerm_erase
    openedApplication_compile_success

/-! ## Independently defined runtime programs -/

namespace Runtime

open ManySortedFC

theorem literalApplication_shape :
    SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        Source.Examples.literalApplication =
      .app (.lam .unit) .unit := rfl

theorem literalApplication_beta :
    Runtime.Step
      (SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        Source.Examples.literalApplication)
      .unit := by
  rw [literalApplication_shape]
  exact .beta .unit

theorem recursivePayloadApplication_shape :
    SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        recursivePayloadApplication =
      .app (.lam .unit)
        (.lam (.app (.lam .unit) .unit)) := rfl

/-- The functional payload remains real runtime code.  It is already a value,
so the outer consumer can beta-reduce without evaluating its body. -/
theorem recursivePayloadApplication_beta :
    Runtime.Step
      (SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        recursivePayloadApplication)
      .unit := by
  rw [recursivePayloadApplication_shape]
  exact .beta .lam

theorem stableOpenApplication_shape :
    SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil stableOpenApplication =
      .let' .unit (.app (.lam .unit) (.var 0)) := rfl

theorem stableOpenApplication_executes :
    Runtime.Steps
      (SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil stableOpenApplication)
      .unit := by
  rw [stableOpenApplication_shape]
  exact .tail (.single (.zeta .unit)) (.beta .unit)

theorem computedStableOpenApplication_shape :
    SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        computedStableOpenApplication =
      .let' .unit
        (.app (.let' .unit (.lam .unit)) (.var 0)) := rfl

theorem computedStableOpenApplication_executes :
    Runtime.Steps
      (SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        computedStableOpenApplication)
      .unit := by
  rw [computedStableOpenApplication_shape]
  exact .tail
    (.tail (.single (.zeta .unit)) (.appFunction (.zeta .unit)))
    (.beta .unit)

theorem computedConsumerApplication_shape :
    SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        Source.Examples.computedConsumerApplication =
      .app (.let' .unit (.lam .unit)) .unit := rfl

theorem computedConsumerApplication_executes :
    Runtime.Steps
      (SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        Source.Examples.computedConsumerApplication)
      .unit := by
  rw [computedConsumerApplication_shape]
  exact .tail (.single (.appFunction (.zeta .unit))) (.beta .unit)

theorem selectingApplication_shape :
    SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil selectingApplication =
      .app (.lam (.let' (.var 0) (.var 0))) .unit := rfl

theorem selectingApplication_executes :
    Runtime.Steps
      (SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil selectingApplication)
      .unit := by
  rw [selectingApplication_shape]
  exact .tail (.single (.beta .unit)) (.zeta .unit)

theorem openedApplication_shape :
    SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        Source.Examples.openedApplication =
      .let' (.let' .unit (.var 0))
        (.app (.lam .unit) (.var 0)) := rfl

theorem openedApplication_executes :
    Runtime.Steps
      (SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        Source.Examples.openedApplication)
      .unit := by
  rw [openedApplication_shape]
  exact .tail
    (.tail (.single (.letRhs (.zeta .unit))) (.zeta .unit))
    (.beta .unit)

/-! The same executions start from the independently checked compiler
artifacts.  These are consequences of the general exact-erasure theorem, not
separate reductions of hand-written targets. -/

theorem compiled_literalApplication_executes :
    Runtime.Steps compiledLiteralApplication.term.erase .unit :=
  (CompilerErasure.compilePolarizedTerm_steps_iff
    literalApplication_compile_success).mpr
      (.single literalApplication_beta)

theorem compiled_recursivePayloadApplication_executes :
    Runtime.Steps compiledRecursivePayloadApplication.term.erase .unit :=
  (CompilerErasure.compilePolarizedTerm_steps_iff
    recursivePayloadApplication_compile_success).mpr
      (.single recursivePayloadApplication_beta)

theorem compiled_stableOpenApplication_executes :
    Runtime.Steps compiledStableOpenApplication.term.erase .unit :=
  (CompilerErasure.compilePolarizedTerm_steps_iff
    stableOpenApplication_compile_success).mpr
      stableOpenApplication_executes

theorem compiled_computedStableOpenApplication_executes :
    Runtime.Steps compiledComputedStableOpenApplication.term.erase .unit :=
  (CompilerErasure.compilePolarizedTerm_steps_iff
    computedStableOpenApplication_compile_success).mpr
      computedStableOpenApplication_executes

theorem compiled_computedConsumerApplication_executes :
    Runtime.Steps compiledComputedConsumerApplication.term.erase .unit :=
  (CompilerErasure.compilePolarizedTerm_steps_iff
    computedConsumerApplication_compile_success).mpr
      computedConsumerApplication_executes

theorem compiled_selectingApplication_executes :
    Runtime.Steps compiledSelectingApplication.term.erase .unit :=
  (CompilerErasure.compilePolarizedTerm_steps_iff
    selectingApplication_compile_success).mpr selectingApplication_executes

theorem compiled_openedApplication_executes :
    Runtime.Steps compiledOpenedApplication.term.erase .unit :=
  (CompilerErasure.compilePolarizedTerm_steps_iff
    openedApplication_compile_success).mpr openedApplication_executes

end Runtime

end DOTCaptureToManySortedFC.Acyclic.GeneralExpression.ObjectConsumerCompilation
