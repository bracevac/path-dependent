import Coercions.Translation.ManySorted.ModalIntersections.EvidenceContext

/-!
# Executable cumulative evidence-context regressions

Every result below uses the public `Context` constructors and the standalone
evidence checker reached through `Context.compiler`.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.EvidenceContextExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext

namespace Source

abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev Interval := DOTCapture.ModalIntersections.Interval
abbrev StaticExpr := DOTCapture.ModalIntersections.StaticExpr
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv

def unboundedType {scope : DOTCapture.ModalIntersections.Sig} :
    Interval .type scope := .bounds .none .none

def unboundedCapture {scope : DOTCapture.ModalIntersections.Sig} :
    Interval .capture scope := .bounds .none .none

def capturedOne {scope : DOTCapture.ModalIntersections.Sig} : Ty scope :=
  .capturing .empty .one

def readOnlyRequirements {scope : DOTCapture.ModalIntersections.Sig} :
    DOTCapture.ModalIntersections.ModalRequirements 0 [.readOnly] scope :=
  .mk .nil (.cons .nil (.readOnly .empty))

def lexicalInterval : Interval .capture [] :=
  .bounds (.some (.capture .empty)) (.some (.capture .empty))

def emptyObject : DOTCapture.ModalIntersections.ObjectType [] :=
  .mk .empty .one .empty

end Source

abbrev OneTermScope : DOTCapture.ModalIntersections.Sig := [] ▹ .term
abbrev LexicalScope : DOTCapture.ModalIntersections.Sig :=
  ([] ▹ .static .capture) ▹ .term
abbrev CapturedStaticScope : DOTCapture.ModalIntersections.Sig :=
  OneTermScope ▹ .static .capture
abbrev FinalScope : DOTCapture.ModalIntersections.Sig :=
  (CapturedStaticScope ▹ .static .type) ▹ .term

def preparedOne {sourceScope : DOTCapture.ModalIntersections.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : ManySortedFC.Sig}
    (context : Context environment targetScope) :
    PreparedTerm context.core (.one : Source.Ty sourceScope) where
  targetType := .one
  prepared := by simp [ObjectContract.translateType]

def preparedCapturedOne :
    PreparedTerm Context.nil.core (Source.capturedOne (scope := [])) where
  targetType := .capturing .empty .one
  prepared := by
    have emptyCapture : Preparation.translateCapture
        Context.nil.core.layout
        (DOTCapture.ModalIntersections.Capture.empty : Source.Capture []) =
        .ok .empty := rfl
    simp [Source.capturedOne, ObjectContract.translateType, emptyCapture,
      bind, Except.bind, pure, Except.pure]

def preparedUnboundedType {sourceScope : DOTCapture.ModalIntersections.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : ManySortedFC.Sig}
    (context : Context environment targetScope) :
    PreparedStatic context.core
      (Source.unboundedType (scope := sourceScope)) where
  theory := ManySortedFC.Interval.unconstrained .type
  prepared := rfl

def preparedUnboundedCapture
    {sourceScope : DOTCapture.ModalIntersections.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : ManySortedFC.Sig}
    (context : Context environment targetScope) :
    PreparedStatic context.core
      (Source.unboundedCapture (scope := sourceScope)) where
  theory := ManySortedFC.Interval.unconstrained .capture
  prepared := rfl

def preparedUnitPayload {sourceScope : DOTCapture.ModalIntersections.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : ManySortedFC.Sig}
    (context : Context environment targetScope) :
    PreparedPayload context.core (Source.unboundedType (scope := sourceScope))
      (.one : Source.Ty (sourceScope ▹ .static .type)) where
  theory := ManySortedFC.Interval.unconstrained .type
  intervalPrepared := rfl
  targetPayload := .one
  payloadPrepared := by simp [ObjectContract.translateType]

def preparedReadOnly {sourceScope : DOTCapture.ModalIntersections.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : ManySortedFC.Sig}
    (context : Context environment targetScope) :
    PreparedModal context.core
      (Source.readOnlyRequirements (scope := sourceScope)) where
  requirements := .mk .nil (.cons .nil (.readOnly .empty))
  prepared := rfl

/-! ## Current-frame acceptance and checker rejection -/

def lockedContext := Context.nil.push
  (Source.readOnlyRequirements (scope := [])) (preparedReadOnly Context.nil)

def lockedMode : DOTCapture.ModalIntersections.Mode
    (DOTCapture.ModalIntersections.TypingEnv.nil.push
      (Source.readOnlyRequirements (scope := []))).bindings
    (DOTCapture.ModalIntersections.TypingEnv.nil.push
      (Source.readOnlyRequirements (scope := []))).locks
    (.readOnly .empty) .readOnly := by
  exact .lock .here .here

def compiledLockedMode? := lockedContext.compiler.compileMode? lockedMode

example : compiledLockedMode?.isSome = true := by native_decide

def wrongCurrentCandidate? := finishMode?
  (.canonical : CaptureTranslation lockedContext.core)
  (.readOnly .empty) .readOnly (.modeEmpty .readOnly)

example : wrongCurrentCandidate? = none := by native_decide

/-! ## Lexical coordinates survive an ordinary extension -/

def preparedLexical : PreparedStatic Context.nil.core Source.lexicalInterval
    where
  theory := ManySortedFC.Interval.between
    (.capture .empty) (.capture .empty)
  prepared := rfl

def lexicalContext := Context.nil.extendStatic Source.lexicalInterval
  preparedLexical

def lexicalPlainPrepared :
    PreparedTerm lexicalContext.core (.one : Source.Ty
      ([.static .capture] : DOTCapture.ModalIntersections.Sig)) :=
  preparedOne lexicalContext

def lexicalPlainContext := lexicalContext.extendPlain .one (by trivial)
  lexicalPlainPrepared

def lexicalLower : DOTCapture.ModalIntersections.Includes
    ((DOTCapture.ModalIntersections.TypingEnv.nil.extendStatic
      Source.lexicalInterval).extendTerm .one).bindings
    (.capture .empty)
    (.capture (.ref (.bound (.there .here)))) := by
  exact .lower (DOTCapture.ModalIntersections.HasLower.bound
    (context := ((DOTCapture.ModalIntersections.TypingEnv.nil.extendStatic
      Source.lexicalInterval).extendTerm .one).bindings)
    (index := (.there .here : DOTCapture.ModalIntersections.BVar
      LexicalScope (.static .capture)))
    (lower := .capture .empty) (upper := .some (.capture .empty)) rfl)

def lexicalUpper : DOTCapture.ModalIntersections.Includes
    ((DOTCapture.ModalIntersections.TypingEnv.nil.extendStatic
      Source.lexicalInterval).extendTerm .one).bindings
    (.capture (.ref (.bound (.there .here))))
    (.capture .empty) := by
  exact .upper (DOTCapture.ModalIntersections.HasUpper.bound
    (context := ((DOTCapture.ModalIntersections.TypingEnv.nil.extendStatic
      Source.lexicalInterval).extendTerm .one).bindings)
    (index := (.there .here : DOTCapture.ModalIntersections.BVar
      LexicalScope (.static .capture)))
    (lower := .some (.capture .empty)) (upper := .capture .empty) rfl)

def compiledLexicalLower? :=
  compileIncludes? lexicalPlainContext.compiler.leaves lexicalLower

def compiledLexicalUpper? :=
  compileIncludes? lexicalPlainContext.compiler.leaves lexicalUpper

example : compiledLexicalLower?.isSome = true := by native_decide
example : compiledLexicalUpper?.isSome = true := by native_decide

/-! ## A term-variable leaf survives static and payload extensions -/

def capturedContext := Context.nil.extendPlain
  (Source.capturedOne (scope := [])) (by trivial) preparedCapturedOne

def capturedStaticContext := capturedContext.extendStatic
  (Source.unboundedCapture (scope := OneTermScope))
  (preparedUnboundedCapture capturedContext)

def capturedPayloadContext := capturedStaticContext.extendPayload
  (Source.unboundedType (scope := CapturedStaticScope)) .one (by trivial)
  (preparedUnitPayload capturedStaticContext)

def oldCapturedName : DOTCapture.ModalIntersections.BVar
    FinalScope .term := .there (.there (.there .here))

def capturedPayloadEnvironment :
    DOTCapture.ModalIntersections.TypingEnv FinalScope :=
  (((DOTCapture.ModalIntersections.TypingEnv.nil.extendTerm
    (Source.capturedOne (scope := []))).extendStatic
    (Source.unboundedCapture (scope := OneTermScope))).extendPayload
    (Source.unboundedType (scope := CapturedStaticScope)) .one)

def oldCaptureVariable : DOTCapture.ModalIntersections.CaptureIncludes
    capturedPayloadEnvironment.bindings
    (.singleton (.var oldCapturedName)) .empty := by
  exact .captureVariable rfl

def compiledOldCaptureVariable? := compileCaptureIncludes?
  capturedPayloadContext.compiler.captures
  capturedPayloadContext.compiler.leaves oldCaptureVariable

example : compiledOldCaptureVariable?.isSome = true := by native_decide
example : (capturedPayloadContext.bindings.term oldCapturedName).isSome = true :=
  by native_decide

/-! ## Duplicate frames remain distinct after term/static/payload transport -/

def firstLock := Context.nil.push (Source.readOnlyRequirements (scope := []))
  (preparedReadOnly Context.nil)

def secondLock := firstLock.push (Source.readOnlyRequirements (scope := []))
  (preparedReadOnly firstLock)

def transportedLocksPlainPrepared :
    PreparedTerm secondLock.core (.one : Source.Ty []) :=
  preparedOne secondLock

def transportedLocksPlain := secondLock.extendPlain .one (by trivial)
  transportedLocksPlainPrepared

def transportedLocksStatic := transportedLocksPlain.extendStatic
  (Source.unboundedCapture (scope := OneTermScope))
  (preparedUnboundedCapture transportedLocksPlain)

def transportedLocks := transportedLocksStatic.extendPayload
  (Source.unboundedType (scope := CapturedStaticScope)) .one (by trivial)
  (preparedUnitPayload transportedLocksStatic)

def transportedEnvironment : DOTCapture.ModalIntersections.TypingEnv
    FinalScope :=
  ((((DOTCapture.ModalIntersections.TypingEnv.nil.push
      (Source.readOnlyRequirements (scope := []))).push
      (Source.readOnlyRequirements (scope := []))).extendTerm .one).extendStatic
      (Source.unboundedCapture (scope := OneTermScope))).extendPayload
      (Source.unboundedType (scope := CapturedStaticScope)) .one

def newestTransportedLock : DOTCapture.ModalIntersections.Mode
    transportedEnvironment.bindings transportedEnvironment.locks
    (.readOnly .empty) .readOnly := .lock .here .here

def olderTransportedLock : DOTCapture.ModalIntersections.Mode
    transportedEnvironment.bindings transportedEnvironment.locks
    (.readOnly .empty) .readOnly := .lock (.there .here) .here

def compiledNewestTransported? :=
  transportedLocks.compiler.compileMode? newestTransportedLock

def compiledOlderTransported? :=
  transportedLocks.compiler.compileMode? olderTransportedLock

example : compiledNewestTransported?.isSome = true := by native_decide
example : compiledOlderTransported?.isSome = true := by native_decide

example : compiledNewestTransported?.map (fun result => result.evidence) ≠
    compiledOlderTransported?.map (fun result => result.evidence) := by
  native_decide

/-! ## Contracted object installation -/

def emptyEncoding :
    DOTCaptureToManySortedFC.Intersections.Encoding.Encoding [] where
  prepared := { symbols := [], entries := [] }

def targetEmptyObject : ObjectContract.PreparedObject [] where
  encoding := emptyEncoding
  sourceRepresentationAtNames := .one
  outerCapture := .empty

def preparedEmptyObject : PreparedContractedObject Context.nil.core
    Source.emptyObject where
  object := targetEmptyObject
  prepared := by rfl

def emptyObjectContext := Context.nil.extendContractedObject
  Source.emptyObject preparedEmptyObject

def acceptedEmptyRoot? := emptyObjectContext.roots.root
  (Context.newestObjectExposure Source.emptyObject)

example : acceptedEmptyRoot?.isSome = true := by native_decide

example : acceptedEmptyRoot?.map (fun root =>
    root.boundRepresentation.outerCapture) =
      some (.cvar (.there targetEmptyObject.repCaptureName)) := by
  native_decide

example : acceptedEmptyRoot?.map (fun root => root.adapter) =
    some (.compose
      (.retagCapture
        ((targetEmptyObject.representation.rename ManySortedFC.Rename.succ).precise
          .here)
        .empty .one
        (.inclusionTrans (.captureVariable .here)
          (.equalityToInclusion
            (.var (.there targetEmptyObject.repExactEvidence))))
        (.inclusionRefl (.type .one)))
      (.forgetEmptyCapture .one)) := by native_decide

def malformedRootCore : Core
    (DOTCapture.ModalIntersections.TypingEnv.nil.extendTerm
      Source.emptyObject.formedType)
    ([] ▹ .term) where
  layout := Layout.empty.extendPlain
  target := ManySortedFC.Ctx.nil.extendTerm .top

def rejectedNewestRoot? := finishRoot? malformedRootCore
  (Context.newestObjectExposure Source.emptyObject) .here

example : rejectedNewestRoot? = none := by native_decide

end DOTCaptureToManySortedFC.ModalIntersections.EvidenceContextExamples
