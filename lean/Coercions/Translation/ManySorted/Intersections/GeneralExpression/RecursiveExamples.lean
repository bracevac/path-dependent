import Coercions.DOT.Captures.Intersections.GeneralExpression.TypingExamples
import Coercions.DOT.Captures.Intersections.GeneralExpression.TypingEmbeddingExamples
import Coercions.Translation.ManySorted.Intersections.GeneralExpression.Recursive

/-!
# Derivation-directed M11 compiler regressions

Closed examples exercise the public source derivations through independently
checked ManySortedFC artifacts.  Their compiler equations use the independent
source erasure recorded by each artifact.
-/

namespace DOTCaptureToManySortedFC.Intersections.GeneralExpression.RecursiveExamples

open ManySortedFC
open DOTCapture.Intersections.GeneralExpression
open DOTCapture.Intersections.GeneralExpression.TypingExamples
open DOTCaptureToManySortedFC.Intersections
open DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler
open DOTCaptureToManySortedFC.Intersections.GeneralExpression.Recursive

def emptyReady : Ready
    (DOTCapture.Intersections.Source.Ctx.nil :
      DOTCapture.Intersections.Source.Ctx 0) [] where
  layout := Preparation.emptyLayout []
  target := ManySortedFC.Ctx.nil

/- A genuine four-name, six-occurrence literal is supplied directly to a
negative consumer of one projected member. -/
#guard (compileObjectApplication? emptyReady
  canonicalApplicationTyping).isSome

/- The same complete many-sorted signature is consumed negatively without a
projection or any package/open redex. -/
#guard (compileObjectApplication? emptyReady
  mergedCanonicalApplicationTyping).isSome

/- The public recursive compiler reaches the same direct object cases. -/
#guard (compileTerm? emptyReady canonicalApplicationTyping).isSome
#guard (compileTerm? emptyReady mergedCanonicalApplicationTyping).isSome

/- A stable root is introduced by one explicit source object open, then
reused as the negative argument. -/
#guard (compileTerm? emptyReady openedApplicationTyping).isSome
#guard (compileTerm? emptyReady mergedOpenedApplicationTyping).isSome

/- A genuine object-producing computation is evaluated once by the explicit
open before its stable payload is supplied to the consumer. -/
#guard (compileTerm? emptyReady computedOpenedApplicationTyping).isSome

/- Repacking a stable object with a nontrivial abstract capture uses the
normalized theory's `χ ≤ ∅` certificate; it is not justified by reflexivity. -/
def repackCaptureLabel : DOTCapture.Intersections.Source.Label := 17

def repackInterface {scope : DOTCapture.Intersections.Source.Scope} :
    DOTCapture.Intersections.Source.Interface scope :=
  .captureMember repackCaptureLabel .empty .empty

def repackObject {scope : DOTCapture.Intersections.Source.Scope} :
    DOTCapture.Intersections.Source.ObjectType scope :=
  .mk repackInterface
    (.capturing (.ref (.localCaptureMember repackCaptureLabel)) .one) .empty

def repackModel {scope : DOTCapture.Intersections.Source.Scope} :
    LocalModel.Model scope where
  typeMember := fun _ => .one
  captureMember := fun _ => .empty

def repackRealization {scope : DOTCapture.Intersections.Source.Scope}
    (context : DOTCapture.Intersections.Source.Ctx scope) :
    ObjectType.Realization context (repackObject (scope := scope)) where
  model := repackModel
  constraints := .captureMember .refl .refl

def repackValue {scope : DOTCapture.Intersections.Source.Scope} : Value scope :=
  .object repackObject .unit

def repackValueTyping {scope : DOTCapture.Intersections.Source.Scope}
    (context : DOTCapture.Intersections.Source.Ctx scope) :
    Value.HasType context (repackValue (scope := scope))
      (repackObject (scope := scope)).formedType :=
  .object (repackRealization context) .unit .refl .refl .refl

def repackBody : Term 1 := .ret (.var .here)

def repackProgram : Term 0 :=
  .objectLet repackObject repackObject.formedType (.ret repackValue)
    repackBody

def repackProgramTypingRaw : Term.HasType
    DOTCapture.Intersections.Source.Ctx.nil repackProgram
      (.union .empty .empty) repackObject.formedType :=
  .objectLet (.ret (repackValueTyping
    DOTCapture.Intersections.Source.Ctx.nil)) (.ret .var) .captureEmpty

def repackProgramTyping : Term.HasType
    DOTCapture.Intersections.Source.Ctx.nil repackProgram .empty
      repackObject.formedType :=
  .use repackProgramTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

#guard (compileTerm? emptyReady repackProgramTyping).isSome

/- The same abstract `χ ≤ ∅` assumption contracts the model-dependent
invocation use of a stable negative argument to the parameter's declared
outer capture. -/
abbrev RepackStableContext : DOTCapture.Intersections.Source.Ctx 1 :=
  DOTCapture.Intersections.Source.Ctx.nil.extendTerm
    (repackObject (scope := 0)).formedType

def repackStableExposure : DOTCapture.Intersections.Source.ExposesObject
    RepackStableContext (.var .here) (repackObject (scope := 1)) :=
  .variable rfl

def repackStableArgument : ObjectArgument.HasType RepackStableContext
    (.ret (.var .here)) (repackObject (scope := 1)) :=
  .stable (name := .here) (available := repackObject) rfl
    (ObjectType.Adapts.refl repackObject)
    (by
      change CaptureIncludes RepackStableContext
        (.ref (.captureMember (.var .here) repackCaptureLabel)) .empty
      exact .source
        (.upper (.captureMember repackStableExposure .here)))

def repackConsumer {scope : DOTCapture.Intersections.Source.Scope} :
    Value scope :=
  .objectConsumer repackObject .one (.ret .unit)

def repackConsumerFunction {scope : DOTCapture.Intersections.Source.Scope}
    (context : DOTCapture.Intersections.Source.Ctx scope) :
    ObjectFunction.HasType context (.ret (repackConsumer (scope := scope)))
      .empty (repackObject (scope := scope)) .one .empty :=
  .returned (.ret .unit) .captureEmpty

def repackStableApplication : Term 1 :=
  .objectApp repackObject (.ret repackConsumer) (.ret (.var .here))

def repackStableApplicationTypingRaw : Term.HasType RepackStableContext
    repackStableApplication (.union .empty .empty) .one :=
  .objectApp (repackConsumerFunction RepackStableContext)
    repackStableArgument

def repackStableApplicationTyping : Term.HasType RepackStableContext
    repackStableApplication .empty .one :=
  .use repackStableApplicationTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

def repackOpenedApplication : Term 0 :=
  .objectLet repackObject .one (.ret repackValue) repackStableApplication

def repackOpenedApplicationTypingRaw : Term.HasType
    DOTCapture.Intersections.Source.Ctx.nil repackOpenedApplication
      (.union .empty .empty) .one :=
  .objectLet (.ret (repackValueTyping
    DOTCapture.Intersections.Source.Ctx.nil))
    repackStableApplicationTyping .captureEmpty

def repackOpenedApplicationTyping : Term.HasType
    DOTCapture.Intersections.Source.Ctx.nil repackOpenedApplication
      .empty .one :=
  .use repackOpenedApplicationTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

#guard (compileTerm? emptyReady repackOpenedApplicationTyping).isSome

/- A negative consumer computed through an ordinary let exercises the
object-function `letPlain` and `use` branches before direct application. -/
def computedConsumer {scope : DOTCapture.Intersections.Source.Scope} :
    Term scope :=
  .let' (.capturing .empty
      (.arr (componentObject (scope := scope)).formedType .one))
    (.ret .unit) (.ret (consumerValue (scope := scope + 1)))

def computedConsumerFunctionTypingRaw : ObjectFunction.HasType
    DOTCapture.Intersections.Source.Ctx.nil (computedConsumer (scope := 0))
      (.union .empty .empty) componentObject .one .empty :=
  .letPlain (by trivial) (.ret .unit)
    (consumerFunctionTyping
      (DOTCapture.Intersections.Source.Ctx.nil.extendTerm .one))
    .captureEmpty

def computedConsumerFunctionTyping : ObjectFunction.HasType
    DOTCapture.Intersections.Source.Ctx.nil (computedConsumer (scope := 0))
      .empty componentObject .one .empty :=
  .use computedConsumerFunctionTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

def computedConsumerApplication : Term 0 :=
  .objectApp componentObject computedConsumer (.ret objectValue)

def computedConsumerApplicationTypingRaw : Term.HasType
    DOTCapture.Intersections.Source.Ctx.nil computedConsumerApplication
      (.union .empty .empty) .one :=
  .objectApp computedConsumerFunctionTyping
    (literalArgument DOTCapture.Intersections.Source.Ctx.nil)

def computedConsumerApplicationTyping : Term.HasType
    DOTCapture.Intersections.Source.Ctx.nil computedConsumerApplication
      .empty .one :=
  .use computedConsumerApplicationTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

#guard (compileTerm? emptyReady computedConsumerApplicationTyping).isSome

/- Proof-carrying artifacts extracted from the public compiler. -/
def canonicalCompiled :=
  (compileTerm? emptyReady canonicalApplicationTyping).get (by native_decide)

def mergedCanonicalCompiled :=
  (compileTerm? emptyReady mergedCanonicalApplicationTyping).get
    (by native_decide)

def openedCompiled :=
  (compileTerm? emptyReady openedApplicationTyping).get (by native_decide)

def mergedOpenedCompiled :=
  (compileTerm? emptyReady mergedOpenedApplicationTyping).get
    (by native_decide)

def computedOpenedCompiled :=
  (compileTerm? emptyReady computedOpenedApplicationTyping).get
    (by native_decide)

def repackCompiled :=
  (compileTerm? emptyReady repackProgramTyping).get (by native_decide)

def repackOpenedCompiled :=
  (compileTerm? emptyReady repackOpenedApplicationTyping).get
    (by native_decide)

def computedConsumerCompiled :=
  (compileTerm? emptyReady computedConsumerApplicationTyping).get
    (by native_decide)

theorem canonical_checker_accepts :
    ManySortedFC.Tm.synth emptyReady.target canonicalCompiled.term =
      some (canonicalCompiled.targetUse, canonicalCompiled.targetType) :=
  canonicalCompiled.checkerAccepts

theorem merged_canonical_checker_accepts :
    ManySortedFC.Tm.synth emptyReady.target mergedCanonicalCompiled.term =
      some (mergedCanonicalCompiled.targetUse,
        mergedCanonicalCompiled.targetType) :=
  mergedCanonicalCompiled.checkerAccepts

theorem opened_checker_accepts :
    ManySortedFC.Tm.synth emptyReady.target openedCompiled.term =
      some (openedCompiled.targetUse, openedCompiled.targetType) :=
  openedCompiled.checkerAccepts

theorem merged_opened_checker_accepts :
    ManySortedFC.Tm.synth emptyReady.target mergedOpenedCompiled.term =
      some (mergedOpenedCompiled.targetUse,
        mergedOpenedCompiled.targetType) :=
  mergedOpenedCompiled.checkerAccepts

theorem computed_opened_checker_accepts :
    ManySortedFC.Tm.synth emptyReady.target computedOpenedCompiled.term =
      some (computedOpenedCompiled.targetUse,
        computedOpenedCompiled.targetType) :=
  computedOpenedCompiled.checkerAccepts

theorem repack_checker_accepts :
    ManySortedFC.Tm.synth emptyReady.target repackCompiled.term =
      some (repackCompiled.targetUse, repackCompiled.targetType) :=
  repackCompiled.checkerAccepts

theorem repack_opened_checker_accepts :
    ManySortedFC.Tm.synth emptyReady.target repackOpenedCompiled.term =
      some (repackOpenedCompiled.targetUse,
        repackOpenedCompiled.targetType) :=
  repackOpenedCompiled.checkerAccepts

theorem computed_consumer_checker_accepts :
    ManySortedFC.Tm.synth emptyReady.target computedConsumerCompiled.term =
      some (computedConsumerCompiled.targetUse,
        computedConsumerCompiled.targetType) :=
  computedConsumerCompiled.checkerAccepts

theorem canonical_exact_erasure :
    canonicalCompiled.term.erase =
      DOTCapture.Intersections.GeneralExpression.Erasure.eraseTerm
        canonicalApplication := by
  simpa [Ready.eraseTerm, Ready.runtimeRenaming, emptyReady] using
    canonicalCompiled.exactErasure

theorem merged_canonical_exact_erasure :
    mergedCanonicalCompiled.term.erase =
      DOTCapture.Intersections.GeneralExpression.Erasure.eraseTerm
        mergedCanonicalApplication := by
  simpa [Ready.eraseTerm, Ready.runtimeRenaming, emptyReady] using
    mergedCanonicalCompiled.exactErasure

theorem opened_exact_erasure :
    openedCompiled.term.erase =
      DOTCapture.Intersections.GeneralExpression.Erasure.eraseTerm
        openedApplication := by
  simpa [Ready.eraseTerm, Ready.runtimeRenaming, emptyReady] using
    openedCompiled.exactErasure

theorem merged_opened_exact_erasure :
    mergedOpenedCompiled.term.erase =
      DOTCapture.Intersections.GeneralExpression.Erasure.eraseTerm
        mergedOpenedApplication := by
  simpa [Ready.eraseTerm, Ready.runtimeRenaming, emptyReady] using
    mergedOpenedCompiled.exactErasure

theorem computed_opened_exact_erasure :
    computedOpenedCompiled.term.erase =
      DOTCapture.Intersections.GeneralExpression.Erasure.eraseTerm
        computedOpenedApplication := by
  simpa [Ready.eraseTerm, Ready.runtimeRenaming, emptyReady] using
    computedOpenedCompiled.exactErasure

theorem repack_opened_exact_erasure :
    repackOpenedCompiled.term.erase =
      DOTCapture.Intersections.GeneralExpression.Erasure.eraseTerm
        repackOpenedApplication := by
  simpa [Ready.eraseTerm, Ready.runtimeRenaming, emptyReady] using
    repackOpenedCompiled.exactErasure

theorem canonical_target_beta :
    ManySortedFC.Runtime.Step canonicalCompiled.term.erase .unit := by
  rw [canonical_exact_erasure]
  exact canonicalApplication_beta

theorem opened_target_executes :
    ManySortedFC.Runtime.Steps openedCompiled.term.erase .unit := by
  rw [opened_exact_erasure]
  exact openedApplication_executes

theorem computed_opened_target_executes :
    ManySortedFC.Runtime.Steps computedOpenedCompiled.term.erase .unit := by
  rw [computed_opened_exact_erasure]
  exact computedOpenedApplication_executes

theorem repack_opened_target_executes :
    ManySortedFC.Runtime.Steps repackOpenedCompiled.term.erase .unit := by
  rw [repack_opened_exact_erasure]
  exact .tail (.single (.zeta .unit)) (.beta .unit)

theorem computed_consumer_exact_erasure :
    computedConsumerCompiled.term.erase =
      DOTCapture.Intersections.GeneralExpression.Erasure.eraseTerm
        computedConsumerApplication := by
  simpa [Ready.eraseTerm, Ready.runtimeRenaming, emptyReady] using
    computedConsumerCompiled.exactErasure

theorem computed_consumer_target_executes :
    ManySortedFC.Runtime.Steps computedConsumerCompiled.term.erase .unit := by
  rw [computed_consumer_exact_erasure]
  exact .tail (.single (.appFunction (.zeta .unit))) (.beta .unit)

end DOTCaptureToManySortedFC.Intersections.GeneralExpression.RecursiveExamples
