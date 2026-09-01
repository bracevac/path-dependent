import Coercions.Translation.ManySorted.ModalIntersections.Compiler
import Coercions.DOT.Captures.Intersections.GeneralExpression.TypingExamples
import Coercions.DOT.Captures.ModalIntersections.CapturedTypingEmbedding
import Coercions.DOT.Captures.ModalIntersections.TypingExamples

/-!
# Cumulative compiler regressions

These examples drive source typing derivations through the recursive compiler
and the standalone target checker.  They cover ordinary beta/zeta programs,
static abstraction and application, existential packaging and opening, modal
locking and unlocking, positive and negative objects, signature projection,
stable opening, dependent application, and value-only adapters. The final
examples pin the remaining deliberate fragment boundaries.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.CompilerExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.Compiler
open DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext

namespace Source

abbrev Env := DOTCapture.ModalIntersections.TypingEnv
abbrev Value := DOTCapture.ModalIntersections.Value
abbrev Term := DOTCapture.ModalIntersections.Term
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture

def onePlain {scope : DOTCapture.ModalIntersections.Sig} :
    DOTCapture.ModalIntersections.Plain (.one : Ty scope) := by
  change True
  exact True.intro

def identityValue {scope : DOTCapture.ModalIntersections.Sig} : Value scope :=
  .lam .one .one (.ret (.var .here))

def identityTyping {scope : DOTCapture.ModalIntersections.Sig}
    {environment : Env scope} :
    DOTCapture.ModalIntersections.Value.HasType environment identityValue
      (.capturing .empty (.arr .one .one)) :=
  .lam onePlain (.ret .var) .captureEmpty

def beta : Term [] :=
  .app (.ret identityValue) (.ret .unit)

def closedUse : Capture [] := .union .empty .empty

def betaTyping : DOTCapture.ModalIntersections.Term.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil beta
    closedUse .one :=
  .app (.ret identityTyping) rfl onePlain (.ret .unit)

def zeta : Term [] :=
  .let' .one (.ret .unit) (.ret (.var .here))

def zetaTyping : DOTCapture.ModalIntersections.Term.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil zeta
    closedUse .one :=
  .letPlain onePlain (.ret .unit) (.ret .var) .refl

end Source

private def success? {alpha : Type} : Except Error alpha -> Option alpha
  | .ok value => some value
  | .error _ => none

def beta? := success? (compileTerm Context.nil Source.betaTyping)
def zeta? := success? (compileTerm Context.nil Source.zetaTyping)

example : beta?.isSome = true := by native_decide
example : zeta?.isSome = true := by native_decide

def betaCompiled := beta?.get (by native_decide)
def zetaCompiled := zeta?.get (by native_decide)

example : ManySortedFC.Tm.check Core.nil.target betaCompiled.term =
    some betaCompiled.checked := betaCompiled.accepted

example : ManySortedFC.Tm.check Core.nil.target zetaCompiled.term =
    some zetaCompiled.checked := zetaCompiled.accepted

theorem betaErasure : betaCompiled.term.erase =
    (.app (.lam (.var 0)) .unit : ManySortedFC.Runtime.Tm 0) := by
  native_decide

theorem zetaErasure : zetaCompiled.term.erase =
    (.let' .unit (.var 0) : ManySortedFC.Runtime.Tm 0) := by
  native_decide

theorem betaExecutes : ManySortedFC.Runtime.Steps betaCompiled.term.erase
    .unit := by
  rw [betaErasure]
  exact .single (.beta .unit)

theorem zetaExecutes : ManySortedFC.Runtime.Steps zetaCompiled.term.erase
    .unit := by
  rw [zetaErasure]
  exact .single (.zeta .unit)

/-! ## Compilation below nonempty ambient scopes -/

namespace Ambient

abbrev TermScope : DOTCapture.ModalIntersections.Sig := [] ▹ .term
abbrev StaticScope : DOTCapture.ModalIntersections.Sig :=
  TermScope ▹ .static .capture

def preparedOne? : Option (PreparedTerm Context.nil.core
    (.one : Source.Ty [])) :=
  match prepared : ObjectContract.translateType Context.nil.core.layout
      (.one : Source.Ty []) with
  | .error _ => none
  | .ok targetType => some { targetType, prepared }

example : preparedOne?.isSome = true := by native_decide

def preparedOne := preparedOne?.get (by native_decide)

def termContext := Context.nil.extendPlain (.one : Source.Ty [])
  Source.onePlain preparedOne

/-- A lexical static name with two checked evidence coordinates. -/
def captureInterval : DOTCapture.ModalIntersections.Interval .capture
    TermScope :=
  .bounds (.some (.capture .empty)) (.some (.capture .empty))

def preparedCaptureInterval? :=
  AdapterElaboration.prepareInterval? termContext.core captureInterval

example : preparedCaptureInterval?.isSome = true := by native_decide

def preparedCaptureInterval :=
  preparedCaptureInterval?.get (by native_decide)

def staticContext := termContext.extendStatic captureInterval
  preparedCaptureInterval

/-- An additional active modal frame contributes another target evidence
coordinate without adding a runtime variable. -/
def requirements : DOTCapture.ModalIntersections.ModalRequirements
    0 [.readOnly] StaticScope :=
  .mk .nil (.cons .nil (.readOnly .empty))

def preparedRequirements : PreparedModal staticContext.core requirements where
  requirements := .mk .nil (.cons .nil (.readOnly .empty))
  prepared := rfl

def context := staticContext.push requirements preparedRequirements

def environment : Source.Env StaticScope :=
  ((DOTCapture.ModalIntersections.TypingEnv.nil.extendTerm .one).extendStatic
    captureInterval).push requirements

def ambientName : DOTCapture.ModalIntersections.BVar StaticScope .term :=
  .there .here

def variableProgram : Source.Term StaticScope :=
  .ret (.var ambientName)

def variableTyping : DOTCapture.ModalIntersections.Term.HasType environment
    variableProgram .empty .one :=
  .ret .var

def variable? := success? (compileTerm context variableTyping)

example : variable?.isSome = true := by native_decide

def variableCompiled := variable?.get (by native_decide)

/-- This invokes the standalone checker again and fixes its synthesized
indices independently of the certificate retained by the compiler result. -/
example : ManySortedFC.Tm.synth context.core.target variableCompiled.term =
    some (.empty, .one) := by
  native_decide

example : variableCompiled.term.erase =
    (.var 0 : ManySortedFC.Runtime.Tm 1) := by
  native_decide

example : context.core.eraseTerm variableProgram =
    (.var 0 : ManySortedFC.Runtime.Tm 1) := by
  native_decide

example : variableCompiled.term.erase =
    context.core.eraseTerm variableProgram := by
  native_decide

/-! Static abstraction/application preserves the ambient runtime variable
across a fresh static symbol and its evidence block. -/

def typeInterval : DOTCapture.ModalIntersections.Interval .type StaticScope :=
  .bounds .none .none

def typeWitness : DOTCapture.ModalIntersections.StaticExpr .type StaticScope :=
  .type .one

def staticBodyName : DOTCapture.ModalIntersections.BVar
    (StaticScope ▹ .static .type) .term :=
  .there ambientName

def staticValue : Source.Value StaticScope :=
  .staticLam typeInterval (.var staticBodyName)

def staticValueTyping : DOTCapture.ModalIntersections.Value.HasType environment
    staticValue (.capturing .empty (.forallI typeInterval .one)) :=
  .staticLam .var .refl

def staticProgram : Source.Term StaticScope :=
  .staticApp typeInterval (.ret staticValue) typeWitness

def staticProgramTyping : DOTCapture.ModalIntersections.Term.HasType
    environment staticProgram .empty .one :=
  .staticApp (.ret staticValueTyping) rfl .unbounded

def static? := success? (compileTerm context staticProgramTyping)

example : static?.isSome = true := by native_decide

def staticCompiled := static?.get (by native_decide)

example : ManySortedFC.Tm.synth context.core.target staticCompiled.term =
    some (.empty, .one) := by
  native_decide

example : staticCompiled.term.erase =
    (.var 0 : ManySortedFC.Runtime.Tm 1) := by
  native_decide

example : staticCompiled.term.erase =
    context.core.eraseTerm staticProgram := by
  native_decide

/-! Existential opening preserves the ambient runtime coordinate while the
new payload receives coordinate zero in the body. -/

def packageValue : Source.Value StaticScope :=
  .pack typeInterval (.one : Source.Ty (StaticScope ▹ .static .type))
    typeWitness (.var ambientName)

def packageValueTyping : DOTCapture.ModalIntersections.Value.HasType
    environment packageValue
      (.capturing .empty (.existsI typeInterval .one)) :=
  .pack .unbounded .var .refl

def openProgram : Source.Term StaticScope :=
  .«open» typeInterval (.one : Source.Ty (StaticScope ▹ .static .type))
    .one (.ret packageValue) (.ret (.var .here))

def openBodyTyping : DOTCapture.ModalIntersections.Term.HasType
    (environment.extendPayload typeInterval .one) (.ret (.var .here))
      .empty .one :=
  .ret .var

def openUse : Source.Capture StaticScope := .union .empty .empty

def openProgramTyping : DOTCapture.ModalIntersections.Term.HasType environment
    openProgram openUse .one :=
  .«open» (.ret packageValueTyping) rfl openBodyTyping .captureEmpty

def open? := success? (compileTerm context openProgramTyping)

example : open?.isSome = true := by native_decide

def openCompiled := open?.get (by native_decide)

example : ManySortedFC.Tm.synth context.core.target openCompiled.term =
    some (.union .empty .empty, .one) := by
  native_decide

example : openCompiled.term.erase =
    (.let' (.var 0) (.var 0) : ManySortedFC.Runtime.Tm 1) := by
  native_decide

example : openCompiled.term.erase =
    context.core.eraseTerm openProgram := by
  native_decide

/-! Modal locking adds another checked evidence frame while preserving the
same ambient runtime coordinate. -/

def lockedValue : Source.Value StaticScope :=
  .lock requirements .one .empty variableProgram

def lockedValueTyping : DOTCapture.ModalIntersections.Value.HasType environment
    lockedValue (.capturing .empty (.modal requirements .one)) :=
  .lock (.ret .var) .refl

def lockedProgram : Source.Term StaticScope := .ret lockedValue

def lockedProgramTyping : DOTCapture.ModalIntersections.Term.HasType
    environment lockedProgram .empty
      (.capturing .empty (.modal requirements .one)) :=
  .ret lockedValueTyping

def locked? := success? (compileTerm context lockedProgramTyping)

example : locked?.isSome = true := by native_decide

def lockedCompiled := locked?.get (by native_decide)

example : (ManySortedFC.Tm.check context.core.target
    lockedCompiled.term).isSome = true := by
  native_decide

example : lockedCompiled.term.erase =
    (.suspend (.var 0) : ManySortedFC.Runtime.Tm 1) := by
  native_decide

example : lockedCompiled.term.erase =
    context.core.eraseTerm lockedProgram := by
  native_decide

end Ambient

/-! ## Static abstraction/application and existential package/open -/

namespace Source

def interval : DOTCapture.ModalIntersections.Interval .type [] :=
  .bounds .none .none

def witness : DOTCapture.ModalIntersections.StaticExpr .type [] :=
  .type .one

def staticValue : Value [] :=
  .staticLam interval
    (.unit : Value ([] ▹ .static .type))

def staticValueTyping : DOTCapture.ModalIntersections.Value.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil
    staticValue (.capturing .empty (.forallI interval .one)) :=
  .staticLam .unit .refl

def staticProgram : Term [] :=
  .staticApp interval (.ret staticValue) witness

def staticProgramTyping : DOTCapture.ModalIntersections.Term.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil
    staticProgram .empty .one :=
  .staticApp (.ret staticValueTyping) rfl .unbounded

def packageValue : Value [] :=
  .pack interval (.one : Ty ([] ▹ .static .type)) witness .unit

def packageValueTyping : DOTCapture.ModalIntersections.Value.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil
    packageValue (.capturing .empty (.existsI interval .one)) :=
  .pack .unbounded .unit .refl

def openProgram : Term [] :=
  .«open» interval (.one : Ty ([] ▹ .static .type)) .one
    (.ret packageValue) (.ret (.var .here))

def openProgramTyping : DOTCapture.ModalIntersections.Term.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil
    openProgram closedUse .one :=
  .«open» (.ret packageValueTyping) rfl (.ret .var) .captureEmpty

end Source

def static? := success? (compileTerm Context.nil Source.staticProgramTyping)
def open? := success? (compileTerm Context.nil Source.openProgramTyping)

example : static?.isSome = true := by native_decide
example : open?.isSome = true := by native_decide

def staticCompiled := static?.get (by native_decide)
def openCompiled := open?.get (by native_decide)

example : ManySortedFC.Tm.check Core.nil.target staticCompiled.term =
    some staticCompiled.checked := staticCompiled.accepted

example : ManySortedFC.Tm.check Core.nil.target openCompiled.term =
    some openCompiled.checked := openCompiled.accepted

example : staticCompiled.term.erase =
    (.unit : ManySortedFC.Runtime.Tm 0) := by native_decide

theorem openErasure : openCompiled.term.erase =
    (.let' .unit (.var 0) : ManySortedFC.Runtime.Tm 0) := by
  native_decide

example : ManySortedFC.Runtime.Steps openCompiled.term.erase .unit := by
  rw [openErasure]
  exact .single (.zeta .unit)

/-! ## Primitive modal lock and unlock -/

namespace Source

def emptyRequirements :
    DOTCapture.ModalIntersections.ModalRequirements 0 [] [] :=
  .mk .nil .nil

def emptySatisfaction : DOTCapture.ModalIntersections.Satisfies
    DOTCapture.ModalIntersections.TypingEnv.nil.bindings
    DOTCapture.ModalIntersections.TypingEnv.nil.locks emptyRequirements :=
  .mk
    (fun occurrence => nomatch occurrence)
    (fun left => nomatch left)

def lockedValue : Value [] :=
  .lock emptyRequirements .one .empty (.ret .unit)

def lockedValueTyping : DOTCapture.ModalIntersections.Value.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil lockedValue
      (.capturing .empty (.modal emptyRequirements .one)) :=
  .lock (.ret .unit) .refl

def unlockedProgram : Term [] :=
  .unlock emptyRequirements (.ret lockedValue)

def unlockedProgramTyping : DOTCapture.ModalIntersections.Term.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil unlockedProgram .empty .one :=
  .unlock (.ret lockedValueTyping) rfl emptySatisfaction

end Source

def modal? := success?
  (compileTerm Context.nil Source.unlockedProgramTyping)

example : modal?.isSome = true := by native_decide

def modalCompiled := modal?.get (by native_decide)

example : ManySortedFC.Tm.check Core.nil.target modalCompiled.term =
    some modalCompiled.checked := modalCompiled.accepted

theorem modalErasure : modalCompiled.term.erase =
    (.force (.suspend .unit) : ManySortedFC.Runtime.Tm 0) := by
  native_decide

example : ManySortedFC.Runtime.Steps modalCompiled.term.erase .unit := by
  rw [modalErasure]
  exact .single .forceBeta

/-! ## Positive object and value-only adapter -/

namespace Source

def objectType : DOTCapture.ModalIntersections.ObjectType [] :=
  .mk .empty .one .empty

def objectModel : DOTCapture.ModalIntersections.LocalModel.Model [] where
  typeMember := fun _ => .one
  captureMember := fun _ => .empty

def objectRealization : DOTCapture.ModalIntersections.ObjectType.Realization
    DOTCapture.ModalIntersections.Ctx.nil objectType where
  model := objectModel
  constraints := .empty

def objectValue : Value [] := .object objectType .unit

def objectValueTyping : DOTCapture.ModalIntersections.Value.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil objectValue
      objectType.formedType :=
  .object objectRealization .unit .refl .refl .refl

def objectProgram : Term [] := .ret objectValue

def objectProgramTyping : DOTCapture.ModalIntersections.Term.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil objectProgram .empty
      objectType.formedType :=
  .ret objectValueTyping

def adaptedValue : Value [] := .unit

def adaptedValueTyping : DOTCapture.ModalIntersections.Value.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil adaptedValue .top :=
  .adapt .unit (.cast .typeTop)

def adaptedProgramTyping : DOTCapture.ModalIntersections.Term.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil (.ret adaptedValue) .empty
      .top :=
  .ret adaptedValueTyping

def widenedUseTyping : DOTCapture.ModalIntersections.Term.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil (.ret (.unit : Value []))
      .empty .one :=
  .use (.ret .unit) .refl

end Source

def object? := success?
  (compileTerm Context.nil Source.objectProgramTyping)
def adapter? := success?
  (compileTerm Context.nil Source.adaptedProgramTyping)
def use? := success?
  (compileTerm Context.nil Source.widenedUseTyping)

example : object?.isSome = true := by native_decide
example : adapter?.isSome = true := by native_decide
example : use?.isSome = true := by native_decide

def objectCompiled := object?.get (by native_decide)
def adapterCompiled := adapter?.get (by native_decide)
def useCompiled := use?.get (by native_decide)

example : ManySortedFC.Tm.check Core.nil.target objectCompiled.term =
    some objectCompiled.checked := objectCompiled.accepted

example : ManySortedFC.Tm.check Core.nil.target adapterCompiled.term =
    some adapterCompiled.checked := adapterCompiled.accepted

example : ManySortedFC.Tm.check Core.nil.target useCompiled.term =
    some useCompiled.checked := useCompiled.accepted

example : objectCompiled.term.erase =
    (.unit : ManySortedFC.Runtime.Tm 0) := by native_decide

example : adapterCompiled.term.erase =
    (.unit : ManySortedFC.Runtime.Tm 0) := by native_decide

example : useCompiled.term.erase =
    (.unit : ManySortedFC.Runtime.Tm 0) := by native_decide

example : ManySortedFC.Runtime.AdministrativeEq objectCompiled.term.erase
    (Core.nil.eraseTerm Source.objectProgram) := objectCompiled.erasure

example : ManySortedFC.Runtime.AdministrativeEq adapterCompiled.term.erase
    (Core.nil.eraseTerm (.ret Source.adaptedValue)) :=
  adapterCompiled.erasure

/-! ## Negative object consumers and stable object programs -/

namespace Source

def objectConsumer : Value [] :=
  .objectConsumer objectType .one (.ret .unit)

def objectConsumerTyping : DOTCapture.ModalIntersections.Value.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil objectConsumer
      (.capturing .empty (.objectArrow objectType .one)) :=
  .objectConsumer (.ret .unit) .captureEmpty

def legacyObjectConsumerTyping : DOTCapture.ModalIntersections.Value.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil objectConsumer
      (.capturing .empty (.arr objectType.formedType .one)) :=
  .legacyObjectConsumer (.ret .unit) .captureEmpty

def embeddedObjectConsumer : Value [] :=
  .lam objectType.formedType .one (.ret .unit)

def embeddedObjectConsumerTyping :
    DOTCapture.ModalIntersections.Value.HasType
      DOTCapture.ModalIntersections.TypingEnv.nil embeddedObjectConsumer
        (.capturing .empty (.arr objectType.formedType .one)) :=
  .embeddedObjectConsumer (.ret .unit) .captureEmpty

def objectPayloadType : Ty ([] ▹ .static .type) :=
  (objectType.weaken (kind := .static .type)).formedType

def objectPackage : Value [] :=
  .pack interval objectPayloadType witness objectValue

def objectPackageTyping : DOTCapture.ModalIntersections.Value.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil objectPackage
      (.capturing .empty (.existsI interval objectPayloadType)) := by
  apply DOTCapture.ModalIntersections.Value.HasType.pack .unbounded
    objectValueTyping .refl

def objectOpen : Term [] :=
  .«open» interval objectPayloadType .one (.ret objectPackage)
    (.ret .unit)

def objectOpenTyping : DOTCapture.ModalIntersections.Term.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil objectOpen closedUse .one :=
  .«open» (.ret objectPackageTyping) rfl (.ret .unit) .captureEmpty

end Source

def objectConsumer? := success?
  (compileValue Context.nil Source.objectConsumerTyping)
def legacyObjectConsumer? := success?
  (compileValue Context.nil Source.legacyObjectConsumerTyping)
def embeddedObjectConsumer? := success?
  (compileValue Context.nil Source.embeddedObjectConsumerTyping)

example : objectConsumer?.isSome = true := by native_decide
example : legacyObjectConsumer?.isSome = true := by native_decide
example : embeddedObjectConsumer?.isSome = true := by native_decide

def objectConsumerCompiled := objectConsumer?.get (by native_decide)
def legacyObjectConsumerCompiled :=
  legacyObjectConsumer?.get (by native_decide)
def embeddedObjectConsumerCompiled :=
  embeddedObjectConsumer?.get (by native_decide)

example : ManySortedFC.Tm.check Core.nil.target objectConsumerCompiled.term =
    some objectConsumerCompiled.checked :=
  objectConsumerCompiled.accepted

example : ManySortedFC.Tm.check Core.nil.target
    legacyObjectConsumerCompiled.term =
      some legacyObjectConsumerCompiled.checked :=
  legacyObjectConsumerCompiled.accepted

example : ManySortedFC.Tm.check Core.nil.target
    embeddedObjectConsumerCompiled.term =
      some embeddedObjectConsumerCompiled.checked :=
  embeddedObjectConsumerCompiled.accepted

example : objectConsumerCompiled.term.erase =
    (.lam .unit : ManySortedFC.Runtime.Tm 0) := by
  native_decide

example : objectConsumerCompiled.term.erase =
    Core.nil.eraseValue Source.objectConsumer := by
  native_decide

example : compileTerm Context.nil Source.objectOpenTyping =
    .error (.unsupported .objectPayloadRequiresObjectLet) := rfl

/-! ## Embedded M11 programs through the cumulative compiler -/

namespace EmbeddedM11

def canonicalSource :=
  DOTCapture.ModalIntersections.Embedding.term
    DOTCapture.Intersections.GeneralExpression.TypingExamples.canonicalApplication
def openedSource :=
  DOTCapture.ModalIntersections.Embedding.term
    DOTCapture.Intersections.GeneralExpression.TypingExamples.openedApplication
def mergedCanonicalSource :=
  DOTCapture.ModalIntersections.Embedding.term
    DOTCapture.Intersections.GeneralExpression.TypingExamples.mergedCanonicalApplication
def mergedOpenedSource :=
  DOTCapture.ModalIntersections.Embedding.term
    DOTCapture.Intersections.GeneralExpression.TypingExamples.mergedOpenedApplication
def computedOpenedSource :=
  DOTCapture.ModalIntersections.Embedding.term
    DOTCapture.Intersections.GeneralExpression.TypingExamples.computedOpenedApplication

def canonicalTyping :=
  DOTCapture.ModalIntersections.Embedding.CapturedIntersections.termTyping
    DOTCapture.Intersections.GeneralExpression.TypingExamples.canonicalApplicationTyping
def openedTyping :=
  DOTCapture.ModalIntersections.Embedding.CapturedIntersections.termTyping
    DOTCapture.Intersections.GeneralExpression.TypingExamples.openedApplicationTyping
def mergedCanonicalTyping :=
  DOTCapture.ModalIntersections.Embedding.CapturedIntersections.termTyping
    DOTCapture.Intersections.GeneralExpression.TypingExamples.mergedCanonicalApplicationTyping
def mergedOpenedTyping :=
  DOTCapture.ModalIntersections.Embedding.CapturedIntersections.termTyping
    DOTCapture.Intersections.GeneralExpression.TypingExamples.mergedOpenedApplicationTyping
def computedOpenedTyping :=
  DOTCapture.ModalIntersections.Embedding.CapturedIntersections.termTyping
    DOTCapture.Intersections.GeneralExpression.TypingExamples.computedOpenedApplicationTyping

def canonical? := success? (compileTerm Context.nil canonicalTyping)
def opened? := success? (compileTerm Context.nil openedTyping)
def mergedCanonical? := success?
  (compileTerm Context.nil mergedCanonicalTyping)
def mergedOpened? := success? (compileTerm Context.nil mergedOpenedTyping)
def computedOpened? := success? (compileTerm Context.nil computedOpenedTyping)

example : canonical?.isSome = true := by native_decide
example : opened?.isSome = true := by native_decide
example : mergedCanonical?.isSome = true := by native_decide
example : mergedOpened?.isSome = true := by native_decide
example : computedOpened?.isSome = true := by native_decide

def canonicalCompiled := canonical?.get (by native_decide)
def openedCompiled := opened?.get (by native_decide)
def mergedCanonicalCompiled := mergedCanonical?.get (by native_decide)
def mergedOpenedCompiled := mergedOpened?.get (by native_decide)
def computedOpenedCompiled := computedOpened?.get (by native_decide)

example : ManySortedFC.Tm.check Core.nil.target canonicalCompiled.term =
    some canonicalCompiled.checked := canonicalCompiled.accepted

example : ManySortedFC.Tm.check Core.nil.target openedCompiled.term =
    some openedCompiled.checked := openedCompiled.accepted

example : ManySortedFC.Tm.check Core.nil.target mergedCanonicalCompiled.term =
    some mergedCanonicalCompiled.checked := mergedCanonicalCompiled.accepted

example : ManySortedFC.Tm.check Core.nil.target mergedOpenedCompiled.term =
    some mergedOpenedCompiled.checked := mergedOpenedCompiled.accepted

example : ManySortedFC.Tm.check Core.nil.target computedOpenedCompiled.term =
    some computedOpenedCompiled.checked := computedOpenedCompiled.accepted

theorem canonicalExactErasure : canonicalCompiled.term.erase =
    Core.nil.eraseTerm canonicalSource := by
  native_decide

theorem openedExactErasure : openedCompiled.term.erase =
    Core.nil.eraseTerm openedSource := by
  native_decide

theorem mergedCanonicalExactErasure : mergedCanonicalCompiled.term.erase =
    Core.nil.eraseTerm mergedCanonicalSource := by
  native_decide

theorem mergedOpenedExactErasure : mergedOpenedCompiled.term.erase =
    Core.nil.eraseTerm mergedOpenedSource := by
  native_decide

theorem computedOpenedExactErasure : computedOpenedCompiled.term.erase =
    Core.nil.eraseTerm computedOpenedSource := by
  native_decide

theorem canonicalErasure : canonicalCompiled.term.erase =
    (.app (.lam (.var 0)) .unit : ManySortedFC.Runtime.Tm 0) := by
  native_decide

theorem openedErasure : openedCompiled.term.erase =
    (.let' .unit (.app (.lam (.var 0)) (.var 0)) :
      ManySortedFC.Runtime.Tm 0) := by
  native_decide

theorem mergedCanonicalErasure : mergedCanonicalCompiled.term.erase =
    (.app (.lam (.var 0)) .unit : ManySortedFC.Runtime.Tm 0) := by
  native_decide

theorem mergedOpenedErasure : mergedOpenedCompiled.term.erase =
    (.let' .unit (.app (.lam (.var 0)) (.var 0)) :
      ManySortedFC.Runtime.Tm 0) := by
  native_decide

theorem computedOpenedErasure : computedOpenedCompiled.term.erase =
    (.let' (.let' .unit (.var 0))
      (.app (.lam (.var 0)) (.var 0)) : ManySortedFC.Runtime.Tm 0) := by
  native_decide

theorem canonicalExecutes : ManySortedFC.Runtime.Steps
    canonicalCompiled.term.erase .unit := by
  rw [canonicalErasure]
  exact .single (.beta .unit)

theorem openedExecutes : ManySortedFC.Runtime.Steps
    openedCompiled.term.erase .unit := by
  rw [openedErasure]
  exact .tail (.single (.zeta .unit)) (.beta .unit)

theorem mergedCanonicalExecutes : ManySortedFC.Runtime.Steps
    mergedCanonicalCompiled.term.erase .unit := by
  rw [mergedCanonicalErasure]
  exact .single (.beta .unit)

theorem mergedOpenedExecutes : ManySortedFC.Runtime.Steps
    mergedOpenedCompiled.term.erase .unit := by
  rw [mergedOpenedErasure]
  exact .tail (.single (.zeta .unit)) (.beta .unit)

theorem computedOpenedExecutes : ManySortedFC.Runtime.Steps
    computedOpenedCompiled.term.erase .unit := by
  rw [computedOpenedErasure]
  exact .tail
    (.tail (.single (.letRhs (.zeta .unit))) (.zeta .unit))
    (.beta .unit)

/-- The actual opened multi-member root used by the stable projection
regression below. -/
def multiObject :=
  DOTCapture.ModalIntersections.Embedding.objectType
    (DOTCapture.Intersections.GeneralExpression.TypingExamples.multiObject
      (scope := 0))

def multiPrepared? := prepareObject? Context.nil.core multiObject

example : multiPrepared?.isSome = true := by native_decide

def multiPrepared := multiPrepared?.get (by native_decide)

def multiContext := Context.nil.extendContractedObject multiObject
  multiPrepared

def stableArgumentTyping :=
  DOTCapture.ModalIntersections.Embedding.CapturedIntersections.objectArgumentTyping
    DOTCapture.Intersections.GeneralExpression.TypingExamples.stableArgument

def componentObject :=
  DOTCapture.ModalIntersections.Embedding.objectType
    (DOTCapture.Intersections.GeneralExpression.TypingExamples.componentObject
      (scope := 1))

def componentPrepared? := prepareObject? multiContext.core componentObject

example : componentPrepared?.isSome = true := by native_decide

def componentPrepared := componentPrepared?.get (by native_decide)

def stableArgument? := success?
  (compileObjectArgument multiContext componentPrepared stableArgumentTyping)

example : stableArgument?.isSome = true := by native_decide

def stableArgumentCompiled := stableArgument?.get (by native_decide)

example : (ManySortedFC.Theory.checkModel multiContext.core.target
    componentPrepared.object.theory stableArgumentCompiled.model.symbols
    stableArgumentCompiled.model.evidence).isSome = true := by
  native_decide

example : ManySortedFC.Tm.check multiContext.core.target
    stableArgumentCompiled.payload =
      some stableArgumentCompiled.payloadChecked :=
  stableArgumentCompiled.payloadAccepted

example : ManySortedFC.Tm.checkValue stableArgumentCompiled.payload =
    some stableArgumentCompiled.payloadValueChecked :=
  stableArgumentCompiled.payloadValueAccepted

def newestRoot? := multiContext.roots.root
  (Context.newestObjectExposure multiObject)

example : newestRoot?.isSome = true := by native_decide

def newestRoot := newestRoot?.get (by native_decide)

/-- Projection reuses the opened object's representation-capture name. -/
def projectedRepresentationCapture : ManySortedFC.Capture
    (ManySortedFC.PayloadScope [] multiPrepared.object.symbols
      multiPrepared.object.relations) :=
  match stableArgumentCompiled.model.symbols with
  | .cons (.capture capture) _ => capture

example : projectedRepresentationCapture =
    newestRoot.boundRepresentation.outerCapture := by
  native_decide

example : stableArgumentCompiled.payload.erase =
    (.var 0 : ManySortedFC.Runtime.Tm 1) := by
  native_decide

end EmbeddedM11

/-! ## Native dependent object programs -/

namespace NativeObjects

def dependentApplication? := success?
  (compileTerm Context.nil
    DOTCapture.ModalIntersections.TypingExamples.dependentObjectApplicationTyping)
def computedObject? := success?
  (compileTerm Context.nil
    DOTCapture.ModalIntersections.TypingExamples.computedExactTypeObjectTyping)

example : dependentApplication?.isSome = true := by native_decide
example : computedObject?.isSome = true := by native_decide

def dependentApplicationCompiled := dependentApplication?.get
  (by native_decide)
def computedObjectCompiled := computedObject?.get (by native_decide)

example : ManySortedFC.Tm.check Core.nil.target
    dependentApplicationCompiled.term =
      some dependentApplicationCompiled.checked :=
  dependentApplicationCompiled.accepted

example : ManySortedFC.Tm.check Core.nil.target computedObjectCompiled.term =
    some computedObjectCompiled.checked := computedObjectCompiled.accepted

example : dependentApplicationCompiled.term.erase = Core.nil.eraseTerm
    DOTCapture.ModalIntersections.TypingExamples.dependentObjectApplication := by
  native_decide

example : computedObjectCompiled.term.erase = Core.nil.eraseTerm
    DOTCapture.ModalIntersections.TypingExamples.computedExactTypeObject := by
  native_decide

theorem dependentApplicationErasure : dependentApplicationCompiled.term.erase =
    (.app (.let' (.lam .unit) (.var 0)) .unit :
      ManySortedFC.Runtime.Tm 0) := by
  native_decide

theorem dependentApplicationExecutes : ManySortedFC.Runtime.Steps
    dependentApplicationCompiled.term.erase .unit := by
  rw [dependentApplicationErasure]
  exact .tail (.single (.appFunction (.zeta .lam))) (.beta .unit)

theorem computedObjectErasure : computedObjectCompiled.term.erase =
    (.let' .unit (.var 0) : ManySortedFC.Runtime.Tm 0) := by
  native_decide

theorem computedObjectExecutes : ManySortedFC.Runtime.Steps
    computedObjectCompiled.term.erase .unit := by
  rw [computedObjectErasure]
  exact .single (.zeta .unit)

example : DOTCapture.ModalIntersections.ObjectArgument.classify
    DOTCapture.ModalIntersections.TypingExamples.computedExactTypeObject =
      .requiresExplicitOpen :=
  DOTCapture.ModalIntersections.TypingExamples.computedObjectRequiresExplicitOpen

example {model : DOTCapture.ModalIntersections.LocalModel.Model []} :
    DOTCapture.ModalIntersections.ObjectArgument.HasType
      DOTCapture.ModalIntersections.TypingEnv.nil
      DOTCapture.ModalIntersections.TypingExamples.computedExactTypeObject
      DOTCapture.ModalIntersections.TypingExamples.exactTypeObject model ->
        False :=
  DOTCapture.ModalIntersections.TypingExamples.computedObjectHasNoNegativeArgumentDerivation

end NativeObjects

/-! ## A negative use with a genuinely capturing representation -/

namespace CapturingObjectApplication

abbrev Scope : DOTCapture.ModalIntersections.Sig := [] ▹ .term

def boundType : Source.Ty [] := .capturing .empty .one

def boundPrepared? : Option (PreparedTerm Context.nil.core boundType) :=
  match prepared : ObjectContract.translateType Context.nil.core.layout
      boundType with
  | .error _ => none
  | .ok targetType => some { targetType, prepared }

example : boundPrepared?.isSome = true := by native_decide

def boundPrepared := boundPrepared?.get (by native_decide)

def context := Context.nil.extendPlain boundType (by trivial) boundPrepared

def environment : Source.Env Scope :=
  DOTCapture.ModalIntersections.TypingEnv.nil.extendTerm boundType

def actualCapture : Source.Capture Scope := .singleton (.var .here)

def object : DOTCapture.ModalIntersections.ObjectType Scope :=
  .mk .empty (.capturing actualCapture .one) actualCapture

def prepared? := prepareObject? context.core object

example : prepared?.isSome = true := by native_decide

def prepared := prepared?.get (by native_decide)

def model : DOTCapture.ModalIntersections.LocalModel.Model Scope where
  typeMember := fun _ => .one
  captureMember := fun _ => .empty

def realization : DOTCapture.ModalIntersections.ObjectType.Realization
    environment.bindings object where
  model := model
  constraints := .empty

def payloadTyping : DOTCapture.ModalIntersections.Value.HasType environment
    (.var .here) (.capturing actualCapture .one) :=
  .var

def argumentTyping : DOTCapture.ModalIntersections.ObjectArgument.HasType
    environment (.ret (.object object (.var .here))) object model := by
  simpa using
    (DOTCapture.ModalIntersections.ObjectArgument.HasType.literal rfl realization
      payloadTyping .refl .refl .refl
      (DOTCapture.ModalIntersections.ObjectType.Adapts.refl object)
      .refl .refl)

def consumer : Source.Value Scope :=
  .objectConsumer object .one (.ret .unit)

def consumerTyping : DOTCapture.ModalIntersections.Value.HasType environment
    consumer (.capturing .empty (.objectArrow object .one)) :=
  .objectConsumer (.ret .unit) .captureEmpty

def application : Source.Term Scope :=
  .objectApp object (.ret consumer) (.ret (.object object (.var .here)))

def applicationTyping :=
  DOTCapture.ModalIntersections.Term.HasType.objectApp
    (.ret consumerTyping) rfl argumentTyping

def argument? := success?
  (compileObjectArgument context prepared argumentTyping)
def application? := success? (compileTerm context applicationTyping)

example : argument?.isSome = true := by native_decide
example : application?.isSome = true := by native_decide

def argumentCompiled := argument?.get (by native_decide)
def applicationCompiled := application?.get (by native_decide)

/-- The negative-use model carries the payload's actual singleton capture. -/
example : argumentCompiled.model.symbols =
    .cons (.capture (.singleton .here)) .nil := by
  native_decide

example : prepared.object.relations =
    [.equality .capture, .inclusion .capture] := rfl

example : prepared.object.actualCapture (.nil) =
    (.singleton .here : ManySortedFC.Capture [ManySortedFC.BinderKind.term]) :=
  rfl

example : prepared.object.outerCapture =
    (.singleton .here : ManySortedFC.Capture [ManySortedFC.BinderKind.term]) :=
  rfl

example : ManySortedFC.Theory.SatisfiedBy context.core.target
    argumentCompiled.model.symbols prepared.object.theory
    argumentCompiled.model.evidence :=
  argumentCompiled.model.satisfies

example : (ManySortedFC.Theory.checkModel context.core.target
    prepared.object.theory argumentCompiled.model.symbols
    argumentCompiled.model.evidence).isSome = true := by
  native_decide

example : ManySortedFC.Tm.check context.core.target argumentCompiled.payload =
    some argumentCompiled.payloadChecked := argumentCompiled.payloadAccepted

example : ManySortedFC.Tm.checkValue argumentCompiled.payload =
    some argumentCompiled.payloadValueChecked :=
  argumentCompiled.payloadValueAccepted

example : ManySortedFC.Tm.check context.core.target applicationCompiled.term =
    some applicationCompiled.checked := applicationCompiled.accepted

example : applicationCompiled.term.erase = context.core.eraseTerm application := by
  native_decide

example : argumentCompiled.payload.erase =
    (.var 0 : ManySortedFC.Runtime.Tm 1) := by
  native_decide

theorem applicationErasure : applicationCompiled.term.erase =
    (.app (.lam .unit) (.var 0) : ManySortedFC.Runtime.Tm 1) := by
  native_decide

theorem applicationExecutes : ManySortedFC.Runtime.Steps
    applicationCompiled.term.erase .unit := by
  rw [applicationErasure]
  exact .single (.beta .var)

end CapturingObjectApplication

/-! ## Deliberate stable-object boundaries -/

namespace RawPreciseObject

def prepared? := prepareObject? Context.nil.core Source.objectType

example : prepared?.isSome = true := by native_decide

def prepared := prepared?.get (by native_decide)

def context := Context.nil.extendContractedObject Source.objectType prepared

def typing :=
  DOTCapture.ModalIntersections.Value.HasType.var
    (environment :=
      DOTCapture.ModalIntersections.TypingEnv.nil.extendTerm
        Source.objectType.formedType)
    (name := .here)

example : compileValue context typing =
    .error (.unsupported .rawPreciseObjectValue) := rfl

end RawPreciseObject

/-! ## Structured fragment diagnostics -/

namespace StructuredBoundaries

example : checkObjectArgumentForm
    DOTCapture.ModalIntersections.TypingExamples.computedExactTypeObject =
      .error (.unsupported .objectArgumentRequiresExplicitOpen) := rfl

def nestedMemberBound : DOTCapture.ModalIntersections.ObjectType [] :=
  .mk (.typeMember 0 (.object Source.objectType) .top) .one .empty

def nestedRepresentation : DOTCapture.ModalIntersections.ObjectType [] :=
  .mk .empty (.object Source.objectType) .empty

example : prepareObject Core.nil nestedMemberBound =
    .error (.unsupported .nestedObjectMemberBound) := rfl

example : prepareObject Core.nil nestedRepresentation =
    .error (.unsupported .nestedObjectRepresentation) := rfl

def parameterPrepared? := prepareObject? Core.nil Source.objectType

example : parameterPrepared?.isSome = true := by native_decide

def parameterPrepared := parameterPrepared?.get (by native_decide)

example : parameterPrepared.object.symbols = [.capture] := rfl

example : parameterPrepared.object.relations =
    [.equality .capture, .inclusion .capture] := rfl

example : prepareObjectResult parameterPrepared (.object Source.objectType) =
    .error (.unsupported .nestedObjectDependentResult) := rfl

/-! Lexical quantifier endpoints use the cumulative object translation too. -/

def nestedInterval : DOTCapture.ModalIntersections.Interval .type [] :=
  .exact (.type (.object Source.objectType))

def hasRepresentationCaptureContract : ManySortedFC.Ty [] -> Bool
  | @ManySortedFC.Ty.existsT _ symbols relations _ _ =>
      decide (symbols = [.capture] ∧
        relations = [.equality .capture, .inclusion .capture])
  | _ => false

def nestedEndpointIsContracted : Bool :=
  match ObjectContract.translateStaticExpr Core.nil.layout
      (.type (.object Source.objectType)) with
  | .ok (.type type) => hasRepresentationCaptureContract type
  | _ => false

example : nestedEndpointIsContracted = true := by native_decide

def nestedForall : Source.Value [] :=
  .staticLam nestedInterval .unit

def nestedForallTyping : DOTCapture.ModalIntersections.Value.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil nestedForall
      (.capturing .empty (.forallI nestedInterval .one)) :=
  .staticLam .unit .captureEmpty

def nestedForall? := success? (compileValue Context.nil nestedForallTyping)

example : nestedForall?.isSome = true := by native_decide

def nestedForallCompiled := nestedForall?.get (by native_decide)

example : ManySortedFC.Tm.check Core.nil.target nestedForallCompiled.term =
    some nestedForallCompiled.checked := nestedForallCompiled.accepted

example : nestedForallCompiled.term.erase =
    (.unit : ManySortedFC.Runtime.Tm 0) := by
  native_decide

def nestedExists : Source.Value [] :=
  .pack nestedInterval (.one : Source.Ty ([] ▹ .static .type))
    (.type (.object Source.objectType)) .unit

def nestedExistsTyping : DOTCapture.ModalIntersections.Value.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil nestedExists
      (.capturing .empty (.existsI nestedInterval .one)) :=
  .pack (.between .refl .refl) .unit .captureEmpty

def nestedExists? := success? (compileValue Context.nil nestedExistsTyping)

example : nestedExists?.isSome = true := by native_decide

def nestedExistsCompiled := nestedExists?.get (by native_decide)

example : ManySortedFC.Tm.check Core.nil.target nestedExistsCompiled.term =
    some nestedExistsCompiled.checked := nestedExistsCompiled.accepted

example : nestedExistsCompiled.term.erase =
    (.unit : ManySortedFC.Runtime.Tm 0) := by native_decide

def invalidNestedInterval : DOTCapture.ModalIntersections.Interval .type [] :=
  .exact (.type (.object nestedRepresentation))

def invalidNestedForall : Source.Value [] :=
  .staticLam invalidNestedInterval .unit

def invalidNestedForallTyping : DOTCapture.ModalIntersections.Value.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil invalidNestedForall
      (.capturing .empty (.forallI invalidNestedInterval .one)) :=
  .staticLam .unit .captureEmpty

def invalidNestedForallError : Option Error :=
  match compileValue Context.nil invalidNestedForallTyping with
  | .ok _ => none
  | .error error => some error

example : invalidNestedForallError =
    some (.unsupported .nestedObjectStaticInterval) := by native_decide

end StructuredBoundaries

end DOTCaptureToManySortedFC.ModalIntersections.CompilerExamples
