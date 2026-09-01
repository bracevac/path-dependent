import Coercions.DOT.Captures.Acyclic.GeneralExpression.Typing
import Coercions.Translation.ManySorted.Acyclic.ValueTranslation
import Coercions.Translation.ManySorted.Acyclic.NegativeObjectInterface
import Coercions.Translation.ManySorted.BinderOnly.LayoutMetatheory
import Coercions.ManySortedFC.TermCheckerCompleteness

/-!
# Direct compiler for general captured-DOT expressions

This compiler consumes general-expression typing derivations directly.  It
does not normalize through the value-MNF source.  General application and
object opening map to the target's computation-accepting `app` and `open`
constructors, while the existing static layout, evidence compiler, object
encoding, and executable-context invariant are reused unchanged.

The supported surface remains acyclic and fixed-member: selection uses stable
variable paths, object payloads are values, ordinary lambda parameters are
plain, and object opening consumes an exact formed-object result.  Negative
object parameters use a separate static-model interface.  The development
does not claim to compile full DOT.
-/

namespace DOTCaptureToManySortedFC.Acyclic.GeneralExpression.Compiler

namespace Source

export DOTCapture.Acyclic.GeneralExpression
  (Scope StaticSort Var Path Capture Ty ObjectSig StaticExpr Ctx Value Term
    ValueLabel)

export DOTCapture.Acyclic
  (ExposesObject TypeIncludes CaptureIncludes)

namespace Value
export DOTCapture.Acyclic.GeneralExpression.Value (HasType)
end Value

namespace Term
export DOTCapture.Acyclic.GeneralExpression.Term (HasType)
end Term

namespace ObjectArgument
export DOTCapture.Acyclic.GeneralExpression.ObjectArgument (HasType)
end ObjectArgument

namespace ObjectFunction
export DOTCapture.Acyclic.GeneralExpression.ObjectFunction (HasType)
end ObjectFunction

namespace ObjectSig
export DOTCapture.Acyclic.ObjectSig
  (typeLower typeUpper captureLower captureUpper)
export DOTCapture.Acyclic.GeneralExpression.ObjectSig (Adapts)
end ObjectSig

namespace Ty
export DOTCapture.Acyclic.Ty (stripCapture outerCapture)
end Ty

end Source

namespace CoreSource

export DOTCapture.Acyclic (Value Term)

namespace Value
export DOTCapture.Acyclic.Value (HasType)
end Value

end CoreSource

namespace Target

export ManySortedFC
  (StaticExpr Capture Ty Binding Ctx Evidence Adapter Theory Tm)

namespace Tm
export ManySortedFC.Tm (HasType IsValue check synth)
end Tm

namespace Evidence
export ManySortedFC.Evidence (Proves)
end Evidence

namespace Adapter
export ManySortedFC.Adapter (HasType)
end Adapter

end Target

namespace Translation

export StaticTranslation
  (translateTy? translateCapture? translateObjectSig? translateExpr?)

end Translation

namespace Runtime

export DOTCaptureToManySortedFC.Acyclic.RuntimeContext
  (Ready resolveVariable nil)

end Runtime

namespace Selection

export DOTCaptureToManySortedFC.Acyclic.SelectionTranslation
  (selectedPayloadType term compile)

end Selection

namespace Object

export ObjectEncoding
  (Bounds symbols relations theory payloadType existentialShape objectType
    symbolWeakening alphaSymbol chiSymbol symbolArguments evidenceArguments
    retagPayload pack openOnce payloadTypeOpened exactBounds staticWeakening)

end Object

namespace Negative

export DOTCaptureToManySortedFC.Acyclic.NegativeObjectInterface
  (Argument bodyType consumerType ambientResultType abstract applyArgument
    abstract_hasType abstract_isValue apply_hasType)

end Negative

/-! ## Proof-carrying compiler results -/

structure CompiledValue {scope : Source.Scope} {context : Source.Ctx scope}
    (ready : Runtime.Ready context) (value : Source.Value scope)
    (type : Source.Ty scope) where
  targetType : Target.Ty (Layout.sig context)
  typeTranslated :
    Translation.translateTy? context type = some targetType
  term : Target.Tm (Layout.sig context)
  isValue : Target.Tm.IsValue term
  typing : Target.Tm.HasType ready.target term .empty targetType

structure CompiledTerm {scope : Source.Scope} {context : Source.Ctx scope}
    (ready : Runtime.Ready context) (sourceTerm : Source.Term scope)
    (sourceUse : Source.Capture scope) (sourceType : Source.Ty scope) where
  sourceTyping : Source.Term.HasType context sourceTerm sourceUse sourceType
  targetUse : Target.Capture (Layout.sig context)
  targetType : Target.Ty (Layout.sig context)
  useTranslated :
    Translation.translateCapture? context sourceUse = some targetUse
  typeTranslated :
    Translation.translateTy? context sourceType = some targetType
  term : Target.Tm (Layout.sig context)
  typing : Target.Tm.HasType ready.target term targetUse targetType

/-! The positive translation above remains unchanged.  The following results
describe the distinct negative view used when an object occurs as a function
parameter. -/

/-- One successfully translated source signature.  Passing this value to the
consumer and argument compilers makes it impossible for the two sides of an
application to choose different target theories. -/
structure CompiledObjectSignature {scope : Source.Scope}
    (context : Source.Ctx scope) (signature : Source.ObjectSig scope) where
  bounds : Object.Bounds (Layout.sig context)
  translated :
    Translation.translateObjectSig? context signature = some bounds

/-- A source object lambda compiled at its negative type.  The result is
shared by the object-function compiler and the recursive polarized compiler
below. -/
structure CompiledObjectConsumer {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope}
    (interface : CompiledObjectSignature context signature)
    (codomain : Source.Ty scope) (body : Source.Term (scope + 1))
    (bodyUse : Source.Capture (scope + 1))
    (closure : Source.Capture scope) where
  bodySourceTyping : Source.Term.HasType
    (context.extendTerm signature.formedType) body bodyUse codomain.weaken
  sourceCaptures : Source.CaptureIncludes
    (context.extendTerm signature.formedType) bodyUse
    (.union closure.weaken (.singleton (.var .here)))
  sourceTyping : Source.Value.HasType context
    (.lam signature.formedType codomain body)
    (.capturing closure (.arr signature.formedType codomain))
  resultType : Target.Ty (Layout.sig context)
  resultTranslated :
    Translation.translateTy? context codomain = some resultType
  closureTarget : Target.Capture (Layout.sig context)
  closureTranslated :
    Translation.translateCapture? context closure = some closureTarget
  bodyCompiled : CompiledTerm
    (ready.extendObject signature interface.translated) body bodyUse
      codomain.weaken
  bodyTyping : Target.Tm.HasType
    ((ready.target.extendTheory (Object.theory interface.bounds)).extendTerm
      Object.payloadType)
    bodyCompiled.term bodyCompiled.targetUse
    ((resultType.rename Object.staticWeakening).weaken)
  bodyCaptures : Target.Evidence (.inclusion .capture)
    (ObjectEncoding.PayloadScope (Layout.sig context))
  bodyCapturesTyping : Target.Evidence.Proves
    ((ready.target.extendTheory (Object.theory interface.bounds)).extendTerm
      Object.payloadType)
    bodyCaptures
    (.inclusion (.capture bodyCompiled.targetUse)
      (.capture
        (.union
          ((closureTarget.rename Object.staticWeakening).weaken)
          (.singleton .here))))

namespace CompiledObjectConsumer

/-- The real target type is captured outside the universal and captured again
around the runtime arrow after the whole signature telescope is introduced. -/
def targetType {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context} {signature : Source.ObjectSig scope}
    {interface : CompiledObjectSignature context signature}
    {codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {closure : Source.Capture scope}
    (compiled : CompiledObjectConsumer ready interface codomain body bodyUse
      closure) : Target.Ty (Layout.sig context) :=
  Negative.ambientResultType (Object.theory interface.bounds)
    Object.payloadType compiled.resultType compiled.closureTarget

/-- Static abstraction over the complete object theory followed by the
ordinary runtime payload lambda. -/
def term {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context} {signature : Source.ObjectSig scope}
    {interface : CompiledObjectSignature context signature}
    {codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {closure : Source.Capture scope}
    (compiled : CompiledObjectConsumer ready interface codomain body bodyUse
      closure) : Target.Tm (Layout.sig context) :=
  Negative.abstract (Object.theory interface.bounds) Object.payloadType
    (compiled.resultType.rename Object.staticWeakening)
    compiled.closureTarget
    (compiled.closureTarget.rename Object.staticWeakening)
    compiled.bodyCompiled.term compiled.bodyCaptures
    (.inclusionRefl
      (.capture (compiled.closureTarget.rename Object.staticWeakening)))

def isValue {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context} {signature : Source.ObjectSig scope}
    {interface : CompiledObjectSignature context signature}
    {codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {closure : Source.Capture scope}
    (compiled : CompiledObjectConsumer ready interface codomain body bodyUse
      closure) : Target.Tm.IsValue compiled.term :=
  Negative.abstract_isValue _ _ _ _ _ _ _ _

def typing {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context} {signature : Source.ObjectSig scope}
    {interface : CompiledObjectSignature context signature}
    {codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {closure : Source.Capture scope}
    (compiled : CompiledObjectConsumer ready interface codomain body bodyUse
      closure) : Target.Tm.HasType ready.target compiled.term .empty
        compiled.targetType := by
  apply Negative.abstract_hasType compiled.bodyTyping
    compiled.bodyCapturesTyping
  exact .inclusionRefl
    (.capture (compiled.closureTarget.rename Object.staticWeakening))

end CompiledObjectConsumer

/-- A computation already known to produce the negative translation of one
object consumer.  This separate input is what permits computed consumers
without changing the old positive compiler recursively. -/
structure CompiledObjectFunction {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope}
    (interface : CompiledObjectSignature context signature)
    (function : Source.Term scope) (functionUse : Source.Capture scope)
    (codomain : Source.Ty scope) (closure : Source.Capture scope) where
  sourceTyping : Source.ObjectFunction.HasType context function functionUse
    signature codomain closure
  targetUse : Target.Capture (Layout.sig context)
  useTranslated :
    Translation.translateCapture? context functionUse = some targetUse
  outerCapture : Target.Capture (Layout.sig context)
  outerTranslated :
    Translation.translateCapture? context closure = some outerCapture
  resultType : Target.Ty (Layout.sig context)
  resultTranslated :
    Translation.translateTy? context codomain = some resultType
  term : Target.Tm (Layout.sig context)
  typing : Target.Tm.HasType ready.target term targetUse
    (Negative.ambientResultType (Object.theory interface.bounds)
      Object.payloadType resultType outerCapture)

/-- Direct negative elaboration of a canonical literal or stable object root.
The payload is a value and the target contains no package/open pair. -/
structure CompiledObjectArgument {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope}
    (interface : CompiledObjectSignature context signature)
    (argument : Source.Term scope) where
  sourceTyping : Source.ObjectArgument.HasType context argument signature
  typeWitness : Target.Ty (Layout.sig context)
  captureWitness : Target.Capture (Layout.sig context)
  target : Negative.Argument ready.target (Object.theory interface.bounds)
    Object.payloadType
  symbolsEquation : target.symbols =
    Object.symbolArguments typeWitness captureWitness
  captureUpper : Target.Evidence (.inclusion .capture) (Layout.sig context)
  captureUpperTyping : Target.Evidence.Proves ready.target captureUpper
    (.inclusion (.capture captureWitness)
      (.capture interface.bounds.captureUpper))

/-- A checked direct object application.  `term` is an evidence-only use cast
around `app (sapp function model) payload`; the cast aligns the precise model
capture with the source rule's signature upper bound and erases completely. -/
structure CompiledObjectApplication {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope}
    (interface : CompiledObjectSignature context signature)
    (function argument : Source.Term scope)
    (functionUse : Source.Capture scope) (codomain : Source.Ty scope)
    (closure : Source.Capture scope)
    where
  sourceTyping : Source.Term.HasType context (.app function argument)
    (DOTCapture.Acyclic.GeneralExpression.Capture.seq functionUse
      (.union closure signature.captureUpper)) codomain
  targetUse : Target.Capture (Layout.sig context)
  useTranslated : Translation.translateCapture? context
    (DOTCapture.Acyclic.GeneralExpression.Capture.seq functionUse
      (.union closure signature.captureUpper)) =
      some targetUse
  resultType : Target.Ty (Layout.sig context)
  resultTranslated : Translation.translateTy? context codomain = some resultType
  term : Target.Tm (Layout.sig context)
  typing : Target.Tm.HasType ready.target term targetUse resultType

/-! ## Endpoint alignment -/

private structure BoundsTranslation {scope : Source.Scope}
    {context : Source.Ctx scope} (signature : Source.ObjectSig scope)
    (bounds : Object.Bounds (Layout.sig context)) where
  typeLower : Translation.translateTy? context signature.typeLower =
    some bounds.typeLower
  typeUpper : Translation.translateTy? context signature.typeUpper =
    some bounds.typeUpper
  captureLower : Translation.translateCapture? context signature.captureLower =
    some bounds.captureLower
  captureUpper : Translation.translateCapture? context signature.captureUpper =
    some bounds.captureUpper

private def BoundsTranslation.ofTranslated {scope : Source.Scope}
    {context : Source.Ctx scope} {signature : Source.ObjectSig scope}
    {bounds : Object.Bounds (Layout.sig context)}
    (translated :
      Translation.translateObjectSig? context signature = some bounds) :
    BoundsTranslation signature bounds := by
  cases signature with
  | bounds typeLower typeUpper captureLower captureUpper =>
      unfold StaticTranslation.translateObjectSig? at translated
      generalize htl : Translation.translateTy? context typeLower = rtl
        at translated
      cases rtl with
      | none => simp at translated
      | some tl =>
          generalize htu : Translation.translateTy? context typeUpper = rtu
            at translated
          cases rtu with
          | none => simp at translated
          | some tu =>
              generalize hcl :
                Translation.translateCapture? context captureLower = rcl
                  at translated
              cases rcl with
              | none => simp at translated
              | some cl =>
                  generalize hcu :
                    Translation.translateCapture? context captureUpper = rcu
                      at translated
                  cases rcu with
                  | none => simp at translated
                  | some cu =>
                      simp at translated
                      subst bounds
                      exact ⟨htl, htu, hcl, hcu⟩

private theorem translatedTypeExpression {scope : Source.Scope}
    {context : Source.Ctx scope} {source : Source.Ty scope}
    {target : Target.Ty (Layout.sig context)}
    (translated : Translation.translateTy? context source = some target) :
    Translation.translateExpr? context (.type source) =
      some (.type target) := by
  simp [Translation.translateExpr?, translated]

private theorem translatedCaptureExpression {scope : Source.Scope}
    {context : Source.Ctx scope} {source : Source.Capture scope}
    {target : Target.Capture (Layout.sig context)}
    (translated : Translation.translateCapture? context source = some target) :
    Translation.translateExpr? context (.capture source) =
      some (.capture target) := by
  simp [Translation.translateExpr?, translated]

private structure ExactInclusion {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translatedContext : ExposureTranslation.TranslatedContext context)
    {sort : Source.StaticSort}
    (source target :
      Target.StaticExpr (Layout.translateSort sort) (Layout.sig context)) where
  evidence : Target.Evidence (.inclusion (Layout.translateSort sort))
    (Layout.sig context)
  typing : Target.Evidence.Proves translatedContext.target evidence
    (.inclusion source target)

private def ExactInclusion.align {scope : Source.Scope}
    {context : Source.Ctx scope}
    {translatedContext : ExposureTranslation.TranslatedContext context}
    {sort : Source.StaticSort} {source target : Source.StaticExpr sort scope}
    (compiled : EvidenceTranslation.CompiledInclusion translatedContext
      source target)
    {sourceTarget targetTarget :
      Target.StaticExpr (Layout.translateSort sort) (Layout.sig context)}
    (sourceTranslated :
      Translation.translateExpr? context source = some sourceTarget)
    (targetTranslated :
      Translation.translateExpr? context target = some targetTarget) :
    ExactInclusion translatedContext sourceTarget targetTarget := by
  have hs := StaticTranslation.TranslatesExpr.functional
    compiled.sourceTranslated sourceTranslated
  have ht := StaticTranslation.TranslatesExpr.functional
    compiled.targetTranslated targetTranslated
  cases hs
  cases ht
  exact ⟨compiled.evidence, compiled.typing⟩

private noncomputable def compileTypeInclusion? {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translated : ExposureTranslation.TranslatedContext context)
    {source target : Source.Ty scope}
    (derivation : Source.TypeIncludes context source target)
    {sourceTarget targetTarget : Target.Ty (Layout.sig context)}
    (sourceTranslated :
      Translation.translateTy? context source = some sourceTarget)
    (targetTranslated :
      Translation.translateTy? context target = some targetTarget) :
    Option (ExactInclusion (sort := .type) translated
      (.type sourceTarget) (.type targetTarget)) := do
  let compiled ← EvidenceTranslation.compileIncludes? translated derivation
  pure (ExactInclusion.align compiled
    (translatedTypeExpression sourceTranslated)
    (translatedTypeExpression targetTranslated))

private noncomputable def compileCaptureInclusion? {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translated : ExposureTranslation.TranslatedContext context)
    {source target : Source.Capture scope}
    (derivation : Source.CaptureIncludes context source target)
    {sourceTarget targetTarget : Target.Capture (Layout.sig context)}
    (sourceTranslated :
      Translation.translateCapture? context source = some sourceTarget)
    (targetTranslated :
      Translation.translateCapture? context target = some targetTarget) :
    Option (ExactInclusion (sort := .capture) translated
      (.capture sourceTarget) (.capture targetTarget)) := do
  let compiled ← EvidenceTranslation.compileIncludes? translated derivation
  pure (ExactInclusion.align compiled
    (translatedCaptureExpression sourceTranslated)
    (translatedCaptureExpression targetTranslated))

/-- Translation commutes with the source and target smart sequencing
operators. -/
theorem translateCapture?_seq {scope : Source.Scope}
    {context : Source.Ctx scope} {first second : Source.Capture scope}
    {firstTarget secondTarget : Target.Capture (Layout.sig context)}
    (firstTranslated :
      Translation.translateCapture? context first = some firstTarget)
    (secondTranslated :
      Translation.translateCapture? context second = some secondTarget) :
    Translation.translateCapture? context
        (DOTCapture.Acyclic.GeneralExpression.Capture.seq first second) =
      some (firstTarget.sequence secondTarget) := by
  cases first with
  | empty =>
      simp only [Translation.translateCapture?] at firstTranslated
      cases Option.some.inj firstTranslated
      simpa [DOTCapture.Acyclic.GeneralExpression.Capture.seq,
        ManySortedFC.Capture.sequence] using secondTranslated
  | union left right =>
      unfold Translation.translateCapture? at firstTranslated
      generalize hl : Translation.translateCapture? context left = rl
        at firstTranslated
      cases rl with
      | none => simp at firstTranslated
      | some leftTarget =>
          generalize hr : Translation.translateCapture? context right = rr
            at firstTranslated
          cases rr with
          | none => simp at firstTranslated
          | some rightTarget =>
              simp at firstTranslated
              subst firstTarget
              simp only [DOTCapture.Acyclic.GeneralExpression.Capture.seq,
                Translation.translateCapture?, hl, hr]
              rw [secondTranslated]
              rfl
  | singleton path =>
      simp only [Translation.translateCapture?] at firstTranslated
      cases Option.some.inj firstTranslated
      simp only [DOTCapture.Acyclic.GeneralExpression.Capture.seq,
        Translation.translateCapture?]
      rw [secondTranslated]
      rfl
  | ref reference =>
      unfold Translation.translateCapture? at firstTranslated
      cases reference with
      | captureMember receiver =>
          unfold StaticTranslation.translateRef? at firstTranslated
          generalize slotEquation :
            Layout.memberSlot? context (.captureMember receiver) = slotResult
              at firstTranslated
          cases slotResult with
          | none => simp at firstTranslated
          | some slot =>
              simp at firstTranslated
              cases Option.some.inj firstTranslated
              simp only [DOTCapture.Acyclic.GeneralExpression.Capture.seq,
                Translation.translateCapture?,
                StaticTranslation.translateRef?, slotEquation]
              rw [secondTranslated]
              rfl

private theorem translateTy?_outerCapture {scope : Source.Scope}
    {context : Source.Ctx scope} {source : Source.Ty scope}
    {target : Target.Ty (Layout.sig context)}
    (translated : Translation.translateTy? context source = some target) :
    Translation.translateCapture? context source.outerCapture =
      some target.outerCapture := by
  cases source with
  | top => cases translated; rfl
  | bot => cases translated; rfl
  | one => cases translated; rfl
  | ref reference =>
      unfold StaticTranslation.translateTy? at translated
      cases reference with
      | typeMember receiver =>
          generalize slotEquation :
            Layout.memberSlot? context (.typeMember receiver) = result
              at translated
          cases result with
          | none =>
              have refNone : StaticTranslation.translateRef? context
                  (.typeMember receiver) = none := by
                unfold StaticTranslation.translateRef?
                simp [slotEquation]
              rw [refNone] at translated
              contradiction
          | some slot =>
              have refSome : StaticTranslation.translateRef? context
                  (.typeMember receiver) =
                    some (.type (.tvar slot.name)) := by
                unfold StaticTranslation.translateRef?
                rw [slotEquation]
                rfl
              rw [refSome] at translated
              have targetEquality := Option.some.inj translated
              rw [← targetEquality]
              change Translation.translateCapture? context .empty =
                some (ManySortedFC.Ty.tvar slot.name).outerCapture
              rfl
  | arr domain codomain =>
      unfold StaticTranslation.translateTy? at translated
      generalize domainEquation :
        Translation.translateTy? context domain = domainResult at translated
      cases domainResult with
      | none => contradiction
      | some domainTarget =>
          generalize codomainEquation :
            Translation.translateTy? context codomain = codomainResult
              at translated
          cases codomainResult with
          | none => contradiction
          | some codomainTarget => cases translated; rfl
  | capturing captures shape =>
      unfold StaticTranslation.translateTy? at translated
      generalize captureEquation :
        Translation.translateCapture? context captures = captureResult
          at translated
      cases captureResult with
      | none => contradiction
      | some captureTarget =>
          generalize shapeEquation :
            Translation.translateTy? context shape = shapeResult at translated
          cases shapeResult with
          | none => contradiction
          | some shapeTarget => cases translated; exact captureEquation
  | object signature =>
      unfold StaticTranslation.translateTy? at translated
      generalize signatureEquation :
        Translation.translateObjectSig? context signature = signatureResult
          at translated
      cases signatureResult with
      | none => contradiction
      | some bounds => cases translated; rfl

private theorem translateTy?_stripCapture {scope : Source.Scope}
    {context : Source.Ctx scope} {source : Source.Ty scope}
    {target : Target.Ty (Layout.sig context)}
    (translated : Translation.translateTy? context source = some target) :
    Translation.translateTy? context source.stripCapture =
      some target.stripCapture := by
  cases source with
  | top => cases translated; rfl
  | bot => cases translated; rfl
  | one => cases translated; rfl
  | ref reference =>
      unfold StaticTranslation.translateTy? at translated ⊢
      cases reference with
      | typeMember receiver =>
          generalize slotEquation :
            Layout.memberSlot? context (.typeMember receiver) = result
              at translated ⊢
          cases result with
          | none =>
              have refNone : StaticTranslation.translateRef? context
                  (.typeMember receiver) = none := by
                unfold StaticTranslation.translateRef?
                simp [slotEquation]
              rw [refNone] at translated
              contradiction
          | some slot =>
              have refSome : StaticTranslation.translateRef? context
                  (.typeMember receiver) =
                    some (.type (.tvar slot.name)) := by
                unfold StaticTranslation.translateRef?
                rw [slotEquation]
                rfl
              rw [refSome] at translated
              have targetEquality := Option.some.inj translated
              rw [← targetEquality]
              change Translation.translateTy? context
                (.ref (.typeMember receiver)) = some (.tvar slot.name)
              simp [StaticTranslation.translateTy?, refSome]
  | arr domain codomain =>
      unfold StaticTranslation.translateTy? at translated
      generalize domainEquation :
        Translation.translateTy? context domain = domainResult at translated
      cases domainResult with
      | none => contradiction
      | some domainTarget =>
          generalize codomainEquation :
            Translation.translateTy? context codomain = codomainResult
              at translated
          cases codomainResult with
          | none => contradiction
          | some codomainTarget =>
              cases translated
              simp [DOTCapture.Acyclic.Ty.stripCapture,
                ManySortedFC.Ty.stripCapture,
                StaticTranslation.translateTy?, domainEquation,
                codomainEquation]
  | capturing captures shape =>
      unfold StaticTranslation.translateTy? at translated
      generalize captureEquation :
        Translation.translateCapture? context captures = captureResult
          at translated
      cases captureResult with
      | none => contradiction
      | some captureTarget =>
          generalize shapeEquation :
            Translation.translateTy? context shape = shapeResult at translated
          cases shapeResult with
          | none => contradiction
          | some shapeTarget => cases translated; exact shapeEquation
  | object signature =>
      unfold StaticTranslation.translateTy? at translated ⊢
      generalize signatureEquation :
        Translation.translateObjectSig? context signature = signatureResult
          at translated ⊢
      cases signatureResult with
      | none => contradiction
      | some bounds =>
          have targetEquality := Option.some.inj translated
          rw [← targetEquality]
          change Translation.translateTy? context (.object signature) =
            some (Object.existentialShape bounds)
          simp [StaticTranslation.translateTy?, signatureEquation]

/-! ## Fixed object-theory model -/

private def symbolInstantiationCancels {scope : ManySortedFC.Sig}
    (typeWitness : Target.Ty scope)
    (captureWitness : Target.Capture scope) :
    BinderOnly.TargetStaticInstantiation.Cancels
      (Object.symbolWeakening (scope := scope))
      (ManySortedFC.StaticSubst.ofSymbolArgs ManySortedFC.Rename.id
        (Object.symbolArguments typeWitness captureWitness)) := by
  constructor
  · intro index
    rfl
  · intro sort index
    rfl

private theorem ambientExpression_instantiates {scope : ManySortedFC.Sig}
    {sort : ManySortedFC.StaticSort}
    (expression : Target.StaticExpr sort scope)
    (typeWitness : Target.Ty scope)
    (captureWitness : Target.Capture scope) :
    (expression.rename Object.symbolWeakening).substitute
        (ManySortedFC.StaticSubst.ofSymbolArgs ManySortedFC.Rename.id
          (Object.symbolArguments typeWitness captureWitness)) =
      expression :=
  BinderOnly.TargetStaticInstantiation.expression_rename_substitute
    expression (symbolInstantiationCancels typeWitness captureWitness)

private theorem typeLowerInstance {scope : ManySortedFC.Sig}
    (bounds : Object.Bounds scope) (typeWitness : Target.Ty scope)
    (captureWitness : Target.Capture scope) :
    (ManySortedFC.Proposition.inclusion
      (((.type bounds.typeLower : Target.StaticExpr .type scope)).rename
        Object.symbolWeakening)
      (Object.alphaSymbol (scope := scope))).instantiateSymbols
        (Object.symbolArguments typeWitness captureWitness) =
      .inclusion (.type bounds.typeLower) (.type typeWitness) := by
  unfold ManySortedFC.Proposition.instantiateSymbols
    ManySortedFC.Proposition.substitute
  congr 1
  exact ambientExpression_instantiates
    (.type bounds.typeLower) typeWitness captureWitness

private theorem typeUpperInstance {scope : ManySortedFC.Sig}
    (bounds : Object.Bounds scope) (typeWitness : Target.Ty scope)
    (captureWitness : Target.Capture scope) :
    (ManySortedFC.Proposition.inclusion
      (Object.alphaSymbol (scope := scope))
      (((.type bounds.typeUpper : Target.StaticExpr .type scope)).rename
        Object.symbolWeakening)).instantiateSymbols
        (Object.symbolArguments typeWitness captureWitness) =
      .inclusion (.type typeWitness) (.type bounds.typeUpper) := by
  unfold ManySortedFC.Proposition.instantiateSymbols
    ManySortedFC.Proposition.substitute
  congr 1
  exact ambientExpression_instantiates
    (.type bounds.typeUpper) typeWitness captureWitness

private theorem captureLowerInstance {scope : ManySortedFC.Sig}
    (bounds : Object.Bounds scope) (typeWitness : Target.Ty scope)
    (captureWitness : Target.Capture scope) :
    (ManySortedFC.Proposition.inclusion
      (((.capture bounds.captureLower : Target.StaticExpr .capture scope)).rename
        Object.symbolWeakening)
      (Object.chiSymbol (scope := scope))).instantiateSymbols
        (Object.symbolArguments typeWitness captureWitness) =
      .inclusion (.capture bounds.captureLower) (.capture captureWitness) := by
  unfold ManySortedFC.Proposition.instantiateSymbols
    ManySortedFC.Proposition.substitute
  congr 1
  exact ambientExpression_instantiates
    (.capture bounds.captureLower) typeWitness captureWitness

private theorem captureUpperInstance {scope : ManySortedFC.Sig}
    (bounds : Object.Bounds scope) (typeWitness : Target.Ty scope)
    (captureWitness : Target.Capture scope) :
    (ManySortedFC.Proposition.inclusion
      (Object.chiSymbol (scope := scope))
      (((.capture bounds.captureUpper : Target.StaticExpr .capture scope)).rename
        Object.symbolWeakening)).instantiateSymbols
        (Object.symbolArguments typeWitness captureWitness) =
      .inclusion (.capture captureWitness) (.capture bounds.captureUpper) := by
  unfold ManySortedFC.Proposition.instantiateSymbols
    ManySortedFC.Proposition.substitute
  congr 1
  exact ambientExpression_instantiates
    (.capture bounds.captureUpper) typeWitness captureWitness

private def satisfiesObjectTheory {scope : ManySortedFC.Sig}
    (context : Target.Ctx scope) (bounds : Object.Bounds scope)
    (typeWitness : Target.Ty scope)
    (captureWitness : Target.Capture scope)
    (typeLower typeUpper : Target.Evidence (.inclusion .type) scope)
    (captureLower captureUpper :
      Target.Evidence (.inclusion .capture) scope)
    (typeLowerTyping : Target.Evidence.Proves context typeLower
      (.inclusion (.type bounds.typeLower) (.type typeWitness)))
    (typeUpperTyping : Target.Evidence.Proves context typeUpper
      (.inclusion (.type typeWitness) (.type bounds.typeUpper)))
    (captureLowerTyping : Target.Evidence.Proves context captureLower
      (.inclusion (.capture bounds.captureLower) (.capture captureWitness)))
    (captureUpperTyping : Target.Evidence.Proves context captureUpper
      (.inclusion (.capture captureWitness) (.capture bounds.captureUpper))) :
    ManySortedFC.Theory.SatisfiedBy context
      (Object.symbolArguments typeWitness captureWitness)
      (Object.theory bounds)
      (Object.evidenceArguments typeLower typeUpper
        captureLower captureUpper) := by
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
  · change Target.Evidence.Proves context typeLower
      ((ManySortedFC.Proposition.inclusion
        (((.type bounds.typeLower : Target.StaticExpr .type scope)).rename
          Object.symbolWeakening)
        Object.alphaSymbol).instantiateSymbols
          (Object.symbolArguments typeWitness captureWitness))
    rw [typeLowerInstance]
    exact typeLowerTyping
  · change Target.Evidence.Proves context typeUpper
      ((ManySortedFC.Proposition.inclusion Object.alphaSymbol
        (((.type bounds.typeUpper : Target.StaticExpr .type scope)).rename
          Object.symbolWeakening)).instantiateSymbols
          (Object.symbolArguments typeWitness captureWitness))
    rw [typeUpperInstance]
    exact typeUpperTyping
  · change Target.Evidence.Proves context captureLower
      ((ManySortedFC.Proposition.inclusion
        (((.capture bounds.captureLower :
          Target.StaticExpr .capture scope)).rename Object.symbolWeakening)
        Object.chiSymbol).instantiateSymbols
          (Object.symbolArguments typeWitness captureWitness))
    rw [captureLowerInstance]
    exact captureLowerTyping
  · change Target.Evidence.Proves context captureUpper
      ((ManySortedFC.Proposition.inclusion Object.chiSymbol
        (((.capture bounds.captureUpper :
          Target.StaticExpr .capture scope)).rename Object.symbolWeakening)
          ).instantiateSymbols
          (Object.symbolArguments typeWitness captureWitness))
    rw [captureUpperInstance]
    exact captureUpperTyping

/-! ## Runtime-scope alignment for binder finishers -/

private theorem plainSig {scope : Source.Scope}
    (context : Source.Ctx scope) (type : Source.Ty scope)
    (plain : type.IsPlain) :
    Layout.sig (context.extendTerm type) =
      (Layout.sig context) ▹ .term := by
  cases type with
  | top | bot | one | ref | arr => rfl
  | object signature =>
      simp [DOTCapture.Acyclic.Ty.IsPlain,
        DOTCapture.Acyclic.Ty.objectSignature?,
        DOTCapture.Acyclic.Ty.stripCapture] at plain
  | capturing captures shape =>
      cases shape with
      | object signature =>
          simp [DOTCapture.Acyclic.Ty.IsPlain,
            DOTCapture.Acyclic.Ty.objectSignature?,
            DOTCapture.Acyclic.Ty.stripCapture] at plain
      | top | bot | one | ref | arr | capturing => rfl

/-- View a compiled plain-binder body at the canonical one-term runtime
extension of the ambient target scope. -/
private def erasePlainBody {scope : Source.Scope}
    {context : Source.Ctx scope} {domain : Source.Ty scope}
    (domainPlain : domain.IsPlain)
    (body : Target.Tm (Layout.sig (context.extendTerm domain))) :
    ManySortedFC.Runtime.Tm ((Layout.sig context).termCount + 1) :=
  cast (congrArg ManySortedFC.Runtime.Tm
    (congrArg ManySortedFC.Sig.termCount
      (plainSig context domain domainPlain))) body.erase

private theorem erasePlainBody_heq {scope : Source.Scope}
    {context : Source.Ctx scope} {domain : Source.Ty scope}
    (domainPlain : domain.IsPlain)
    (body : Target.Tm (Layout.sig (context.extendTerm domain))) :
    HEq body.erase (erasePlainBody domainPlain body) := by
  exact (cast_heq _ _).symm

private theorem payloadRenamingIdentity (scope : ManySortedFC.Sig) :
    (ManySortedFC.Erasure.Renaming.identity scope).liftPayload
        Object.symbols Object.relations =
      ManySortedFC.Erasure.Renaming.identity
        (ObjectEncoding.PayloadScope scope) := by
  funext index
  cases index with
  | here => rfl
  | there index =>
      cases index with
      | there index =>
        cases index with
        | there index =>
          cases index with
          | there index =>
            cases index with
            | there index =>
              cases index with
              | there index =>
                cases index with
                | there index => rfl

private theorem payloadEraseCanonical (scope : ManySortedFC.Sig)
    (body : ManySortedFC.Tm (ObjectEncoding.PayloadScope scope)) :
    body.eraseWith
        ((ManySortedFC.Erasure.Renaming.identity scope).liftPayload
          Object.symbols Object.relations) =
      body.erase := by
  unfold ManySortedFC.Tm.erase
  rw [payloadRenamingIdentity]
  rfl

private theorem objectSig {scope : Source.Scope}
    (context : Source.Ctx scope) (signature : Source.ObjectSig scope) :
    Layout.sig (context.extendTerm
      (.capturing signature.captureUpper (.object signature))) =
        ObjectEncoding.PayloadScope (Layout.sig context) := rfl

/-- View a compiled opened-object body at the canonical one-term runtime
extension of the ambient target scope. -/
private def eraseObjectBody {scope : Source.Scope}
    {context : Source.Ctx scope} {signature : Source.ObjectSig scope}
    (body : Target.Tm (Layout.sig (context.extendTerm
      (.capturing signature.captureUpper (.object signature))))) :
    ManySortedFC.Runtime.Tm ((Layout.sig context).termCount + 1) :=
  cast (congrArg ManySortedFC.Runtime.Tm
    (congrArg ManySortedFC.Sig.termCount
      (objectSig context signature))) body.erase

private theorem eraseObjectBody_heq {scope : Source.Scope}
    {context : Source.Ctx scope} {signature : Source.ObjectSig scope}
    (body : Target.Tm (Layout.sig (context.extendTerm
      (.capturing signature.captureUpper (.object signature))))) :
    HEq body.erase (eraseObjectBody body) := by
  exact (cast_heq _ _).symm

/-! ## Leaf and conversion helpers -/

private noncomputable def compileVariable? {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    (name : Source.Var scope) :
    Option (CompiledValue ready (.var name) (context.lookup name)) := do
  let coreResult : Option
      (DOTCaptureToManySortedFC.Acyclic.ValueTranslation.CompiledValue ready
        (.var name) (context.lookup name)) :=
    DOTCaptureToManySortedFC.Acyclic.ValueTranslation.compileValue? ready
      (by exact .var)
  let core ← coreResult
  pure
    { targetType := core.targetType
      typeTranslated := core.typeTranslated
      term := core.term
      isValue := core.isValue
      typing := core.typing }

private noncomputable def compileSelect {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (exposes : Source.ExposesObject context receiver signature) :
    CompiledTerm ready (.select receiver .v) (.singleton receiver)
      receiver.valueMemberType := by
  let selected := Selection.compile ready.translated exposes
  exact
    { sourceTyping := .select exposes
      targetUse := .singleton selected.resolved.slot.payload
      targetType := Selection.selectedPayloadType selected.resolved
      useTranslated := selected.useTranslated
      typeTranslated := selected.typeTranslated
      term := Selection.term selected.resolved
      typing := selected.targetTyping }

private noncomputable def compileAdapt? {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {value : Source.Value scope} {source target : Source.Ty scope}
    (inner : CompiledValue ready value source)
    (inclusion : Source.TypeIncludes context source target)
    {targetType : Target.Ty (Layout.sig context)}
    (targetTranslated :
      Translation.translateTy? context target = some targetType) :
    Option (CompiledValue ready value target) := do
  let compiled ← compileTypeInclusion? ready.translated inclusion
    inner.typeTranslated targetTranslated
  pure
    { targetType := targetType
      typeTranslated := targetTranslated
      term := .adapt inner.term (.cast compiled.evidence)
      isValue := .adapt inner.isValue
      typing := .adapt inner.isValue inner.typing (.cast compiled.typing) }

private noncomputable def compileUse? {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {term : Source.Term scope} {sourceUse targetUse : Source.Capture scope}
    {type : Source.Ty scope}
    (inner : CompiledTerm ready term sourceUse type)
    (inclusion : Source.CaptureIncludes context sourceUse targetUse) :
    Option (CompiledTerm ready term targetUse type) :=
  match targetTranslated :
      Translation.translateCapture? context targetUse with
  | none => none
  | some target => do
      let compiled ← compileCaptureInclusion? ready.translated inclusion
        inner.useTranslated targetTranslated
      pure
        { sourceTyping := .use inner.sourceTyping inclusion
          targetUse := target
          targetType := inner.targetType
          useTranslated := targetTranslated
          typeTranslated := inner.typeTranslated
          term := .use inner.term compiled.evidence
          typing := .use inner.typing compiled.typing }

/-! ## Binder finishers -/

/-- Internal lambda-finishing result carrying the erasure alignment proved at
the same dependent case split that constructs the target lambda. -/
private structure FinishedLambda {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {domain codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)} {closure : Source.Capture scope}
    {domainPlain : domain.IsPlain}
    {domainTarget : Target.Ty (Layout.sig context)}
    {domainTranslated : Translation.translateTy? context domain =
      some domainTarget}
    (bodyCompiled : CompiledTerm
      (ready.extendPlain domainPlain domainTranslated) body bodyUse
        codomain.weaken) where
  compiled : CompiledValue ready (.lam domain codomain body)
    (.capturing closure (.arr domain codomain))
  erasedBody : ManySortedFC.Runtime.Tm
    ((Layout.sig context).termCount + 1)
  bodyErases : HEq bodyCompiled.term.erase erasedBody
  compiledErases : compiled.term.erase =
    ManySortedFC.Runtime.Tm.lam erasedBody

private noncomputable def finishLambdaDetailed? {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {domain codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)} {closure : Source.Capture scope}
    (domainPlain : domain.IsPlain)
    (captures : Source.CaptureIncludes (context.extendTerm domain) bodyUse
      (.union closure.weaken (.singleton (.var .here))))
    {domainTarget codomainTarget : Target.Ty (Layout.sig context)}
    {closureTarget : Target.Capture (Layout.sig context)}
    (domainTranslated :
      Translation.translateTy? context domain = some domainTarget)
    (codomainTranslated :
      Translation.translateTy? context codomain = some codomainTarget)
    (closureTranslated :
      Translation.translateCapture? context closure = some closureTarget)
    (bodyCompiled : CompiledTerm
      (ready.extendPlain domainPlain domainTranslated) body bodyUse
        codomain.weaken) :
    Option (@FinishedLambda scope context ready domain codomain body bodyUse
      closure domainPlain domainTarget domainTranslated bodyCompiled) := by
  let binding := domain
  cases domain with
  | object signature =>
      simp [DOTCapture.Acyclic.Ty.IsPlain,
        DOTCapture.Acyclic.Ty.objectSignature?,
        DOTCapture.Acyclic.Ty.stripCapture] at domainPlain
  | capturing domainCapture shape =>
      cases shape with
      | object signature =>
          simp [DOTCapture.Acyclic.Ty.IsPlain,
            DOTCapture.Acyclic.Ty.objectSignature?,
            DOTCapture.Acyclic.Ty.stripCapture] at domainPlain
      | top | bot | one | ref | arr | capturing =>
          let bodyReady := ready.extendPlain domainPlain domainTranslated
          have codomainWeakenTranslated :
              Translation.translateTy? (context.extendTerm binding)
                  codomain.weaken =
                some (codomainTarget.rename
                  (ManySortedFC.Rename.succ (kind := .term))) := by
            rw [StaticTranslationMetatheory.translateTy?_weaken,
              codomainTranslated]
            rfl
          have codomainEquality :=
            StaticTranslation.TranslatesTy.functional
              bodyCompiled.typeTranslated codomainWeakenTranslated
          have upperTranslated :
              Translation.translateCapture? (context.extendTerm binding)
                  (.union closure.weaken (.singleton (.var .here))) =
                some (.union
                  (closureTarget.rename
                    (ManySortedFC.Rename.succ (kind := .term)))
                  (.singleton
                    (.here : ManySortedFC.BVar
                      (Layout.sig context ▹ .term) .term))) := by
            simp only [Translation.translateCapture?]
            rw [StaticTranslationMetatheory.translateCapture?_weaken,
              closureTranslated]
            simp [binding, Layout.extendRename,
              StaticTranslation.translatePath, Layout.translatePath,
              Layout.termVar, DOTCapture.Acyclic.Ctx.extendTerm]
          exact do
            let capturesCompiled ←
              compileCaptureInclusion? bodyReady.translated captures
                bodyCompiled.useTranslated upperTranslated
            have bodyTargetTyping : Target.Tm.HasType
                (ready.target.extendTerm domainTarget) bodyCompiled.term
                bodyCompiled.targetUse
                (codomainTarget.rename
                  (ManySortedFC.Rename.succ (kind := .term))) := by
              simpa [bodyReady, codomainEquality] using bodyCompiled.typing
            let compiled : CompiledValue ready (.lam binding codomain body)
                (.capturing closure (.arr binding codomain)) :=
              { targetType := .capturing closureTarget
                  (.arr domainTarget codomainTarget)
                typeTranslated := by
                  have arrowTranslated :
                      Translation.translateTy? context
                          (.arr binding codomain) =
                        some (.arr domainTarget codomainTarget) := by
                    unfold Translation.translateTy?
                    have bindingTranslated :
                        Translation.translateTy? context binding =
                          some domainTarget := by
                      simpa [binding] using domainTranslated
                    rw [bindingTranslated, codomainTranslated]
                    rfl
                  change (do
                    let closure' ← Translation.translateCapture? context
                      closure
                    let shape' ← Translation.translateTy? context
                      (.arr binding codomain)
                    pure (ManySortedFC.Ty.capturing closure' shape')) = _
                  rw [closureTranslated, arrowTranslated]
                  rfl
                term := .lam domainTarget codomainTarget closureTarget
                  bodyCompiled.term capturesCompiled.evidence
                isValue := .lam
                typing := .lam bodyTargetTyping capturesCompiled.typing }
            pure
              { compiled := compiled
                erasedBody := erasePlainBody domainPlain bodyCompiled.term
                bodyErases := erasePlainBody_heq domainPlain bodyCompiled.term
                compiledErases := by
                  dsimp only [compiled]
                  rw [ManySortedFC.Tm.erase_lam]
                  congr 1 }
  | top | bot | one | ref | arr =>
      let bodyReady := ready.extendPlain domainPlain domainTranslated
      have codomainWeakenTranslated :
          Translation.translateTy? (context.extendTerm binding)
              codomain.weaken =
            some (codomainTarget.rename
              (ManySortedFC.Rename.succ (kind := .term))) := by
        rw [StaticTranslationMetatheory.translateTy?_weaken,
          codomainTranslated]
        rfl
      have codomainEquality :=
        StaticTranslation.TranslatesTy.functional
          bodyCompiled.typeTranslated codomainWeakenTranslated
      have upperTranslated :
          Translation.translateCapture? (context.extendTerm binding)
              (.union closure.weaken (.singleton (.var .here))) =
            some (.union
              (closureTarget.rename
                (ManySortedFC.Rename.succ (kind := .term)))
              (.singleton
                (.here : ManySortedFC.BVar
                  (Layout.sig context ▹ .term) .term))) := by
        simp only [Translation.translateCapture?]
        rw [StaticTranslationMetatheory.translateCapture?_weaken,
          closureTranslated]
        simp [binding, Layout.extendRename, StaticTranslation.translatePath,
          Layout.translatePath, Layout.termVar,
          DOTCapture.Acyclic.Ctx.extendTerm]
      exact do
        let capturesCompiled ←
          compileCaptureInclusion? bodyReady.translated captures
            bodyCompiled.useTranslated upperTranslated
        have bodyTargetTyping : Target.Tm.HasType
            (ready.target.extendTerm domainTarget) bodyCompiled.term
            bodyCompiled.targetUse
            (codomainTarget.rename
              (ManySortedFC.Rename.succ (kind := .term))) := by
          simpa [bodyReady, codomainEquality] using bodyCompiled.typing
        let compiled : CompiledValue ready (.lam binding codomain body)
            (.capturing closure (.arr binding codomain)) :=
          { targetType := .capturing closureTarget
              (.arr domainTarget codomainTarget)
            typeTranslated := by
              have arrowTranslated :
                  Translation.translateTy? context (.arr binding codomain) =
                    some (.arr domainTarget codomainTarget) := by
                unfold Translation.translateTy?
                have bindingTranslated :
                    Translation.translateTy? context binding =
                      some domainTarget := by
                  simpa [binding] using domainTranslated
                rw [bindingTranslated, codomainTranslated]
                rfl
              change (do
                let closure' ← Translation.translateCapture? context closure
                let shape' ← Translation.translateTy? context
                  (.arr binding codomain)
                pure (ManySortedFC.Ty.capturing closure' shape')) = _
              rw [closureTranslated, arrowTranslated]
              rfl
            term := .lam domainTarget codomainTarget closureTarget
              bodyCompiled.term capturesCompiled.evidence
            isValue := .lam
            typing := .lam bodyTargetTyping capturesCompiled.typing }
        pure
          { compiled := compiled
            erasedBody := erasePlainBody domainPlain bodyCompiled.term
            bodyErases := erasePlainBody_heq domainPlain bodyCompiled.term
            compiledErases := by
              dsimp only [compiled]
              rw [ManySortedFC.Tm.erase_lam]
              congr 1 }

/-- Finish a lambda while keeping the internal scope-alignment witness private. -/
noncomputable def finishLambda? {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {domain codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)} {closure : Source.Capture scope}
    (domainPlain : domain.IsPlain)
    (captures : Source.CaptureIncludes (context.extendTerm domain) bodyUse
      (.union closure.weaken (.singleton (.var .here))))
    {domainTarget codomainTarget : Target.Ty (Layout.sig context)}
    {closureTarget : Target.Capture (Layout.sig context)}
    (domainTranslated :
      Translation.translateTy? context domain = some domainTarget)
    (codomainTranslated :
      Translation.translateTy? context codomain = some codomainTarget)
    (closureTranslated :
      Translation.translateCapture? context closure = some closureTarget)
    (bodyCompiled : CompiledTerm
      (ready.extendPlain domainPlain domainTranslated) body bodyUse
        codomain.weaken) :
    Option (CompiledValue ready (.lam domain codomain body)
      (.capturing closure (.arr domain codomain))) := do
  let finished ← finishLambdaDetailed? domainPlain captures domainTranslated
    codomainTranslated closureTranslated bodyCompiled
  pure finished.compiled

/-- Internal plain-let finishing result carrying the target/body runtime-scope
alignment established by the plainness witness. -/
private structure FinishedPlainLet {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {result bound : Source.Ty scope} {rhs : Source.Term scope}
    {body : Source.Term (scope + 1)} {rhsUse : Source.Capture scope}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope} {boundPlain : bound.IsPlain}
    (rhsCompiled : CompiledTerm ready rhs rhsUse bound)
    (bodyCompiled : CompiledTerm
      (ready.extendPlain boundPlain rhsCompiled.typeTranslated) body bodyUse
        result.weaken) where
  compiled : CompiledTerm ready (.let' result rhs body)
    (.union rhsUse bodyOuterUse) result
  erasedBody : ManySortedFC.Runtime.Tm
    ((Layout.sig context).termCount + 1)
  bodyErases : HEq bodyCompiled.term.erase erasedBody
  compiledErases : compiled.term.erase =
    ManySortedFC.Runtime.Tm.let' rhsCompiled.term.erase erasedBody

private noncomputable def finishPlainLetDetailed? {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {result bound : Source.Ty scope} {rhs : Source.Term scope}
    {body : Source.Term (scope + 1)} {rhsUse : Source.Capture scope}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (boundPlain : bound.IsPlain)
    (discharge : Source.CaptureIncludes (context.extendTerm bound) bodyUse
      bodyOuterUse.weaken)
    {resultTarget : Target.Ty (Layout.sig context)}
    {bodyOuterTarget : Target.Capture (Layout.sig context)}
    (resultTranslated :
      Translation.translateTy? context result = some resultTarget)
    (bodyOuterTranslated :
      Translation.translateCapture? context bodyOuterUse =
        some bodyOuterTarget)
    (rhsCompiled : CompiledTerm ready rhs rhsUse bound)
    (bodyCompiled : CompiledTerm
      (ready.extendPlain boundPlain rhsCompiled.typeTranslated) body bodyUse
        result.weaken) :
    Option (@FinishedPlainLet scope context ready result bound rhs body rhsUse
      bodyUse bodyOuterUse boundPlain rhsCompiled bodyCompiled) := by
  let binding := bound
  cases bound with
  | object signature =>
      simp [DOTCapture.Acyclic.Ty.IsPlain,
        DOTCapture.Acyclic.Ty.objectSignature?,
        DOTCapture.Acyclic.Ty.stripCapture] at boundPlain
  | capturing boundCapture shape =>
      cases shape with
      | object signature =>
          simp [DOTCapture.Acyclic.Ty.IsPlain,
            DOTCapture.Acyclic.Ty.objectSignature?,
            DOTCapture.Acyclic.Ty.stripCapture] at boundPlain
      | top | bot | one | ref | arr | capturing =>
          let bodyReady := ready.extendPlain boundPlain
            rhsCompiled.typeTranslated
          have resultWeakenTranslated :
              Translation.translateTy? (context.extendTerm binding)
                  result.weaken =
                some (resultTarget.rename
                  (ManySortedFC.Rename.succ (kind := .term))) := by
            rw [StaticTranslationMetatheory.translateTy?_weaken,
              resultTranslated]
            rfl
          have resultEquality :=
            StaticTranslation.TranslatesTy.functional
              bodyCompiled.typeTranslated resultWeakenTranslated
          have bodyOuterWeakenTranslated :
              Translation.translateCapture? (context.extendTerm binding)
                  bodyOuterUse.weaken =
                some (bodyOuterTarget.rename
                  (ManySortedFC.Rename.succ (kind := .term))) := by
            rw [StaticTranslationMetatheory.translateCapture?_weaken,
              bodyOuterTranslated]
            rfl
          exact do
            let dischargeCompiled ←
              compileCaptureInclusion? bodyReady.translated discharge
                bodyCompiled.useTranslated bodyOuterWeakenTranslated
            have bodyTargetTyping : Target.Tm.HasType
                (ready.target.extendTerm rhsCompiled.targetType)
                bodyCompiled.term bodyCompiled.targetUse
                (resultTarget.rename
                  (ManySortedFC.Rename.succ (kind := .term))) := by
              simpa [bodyReady, resultEquality] using bodyCompiled.typing
            let compiled : CompiledTerm ready (.let' result rhs body)
                (.union rhsUse bodyOuterUse) result :=
              { sourceTyping := .letPlain boundPlain rhsCompiled.sourceTyping
                  bodyCompiled.sourceTyping discharge
                targetUse := .union rhsCompiled.targetUse bodyOuterTarget
                targetType := resultTarget
                useTranslated := by
                  simp [Translation.translateCapture?,
                    rhsCompiled.useTranslated, bodyOuterTranslated]
                typeTranslated := resultTranslated
                term := .let' resultTarget bodyOuterTarget rhsCompiled.term
                  bodyCompiled.term dischargeCompiled.evidence
                typing := .let' rhsCompiled.typing bodyTargetTyping
                  dischargeCompiled.typing }
            pure
              { compiled := compiled
                erasedBody := erasePlainBody boundPlain bodyCompiled.term
                bodyErases := erasePlainBody_heq boundPlain bodyCompiled.term
                compiledErases := by
                  dsimp only [compiled]
                  rw [ManySortedFC.Tm.erase_let]
                  congr 1 }
  | top | bot | one | ref | arr =>
      let bodyReady := ready.extendPlain boundPlain
        rhsCompiled.typeTranslated
      have resultWeakenTranslated :
          Translation.translateTy? (context.extendTerm binding)
              result.weaken =
            some (resultTarget.rename
              (ManySortedFC.Rename.succ (kind := .term))) := by
        rw [StaticTranslationMetatheory.translateTy?_weaken,
          resultTranslated]
        rfl
      have resultEquality :=
        StaticTranslation.TranslatesTy.functional
          bodyCompiled.typeTranslated resultWeakenTranslated
      have bodyOuterWeakenTranslated :
          Translation.translateCapture? (context.extendTerm binding)
              bodyOuterUse.weaken =
            some (bodyOuterTarget.rename
              (ManySortedFC.Rename.succ (kind := .term))) := by
        rw [StaticTranslationMetatheory.translateCapture?_weaken,
          bodyOuterTranslated]
        rfl
      exact do
        let dischargeCompiled ←
          compileCaptureInclusion? bodyReady.translated discharge
            bodyCompiled.useTranslated bodyOuterWeakenTranslated
        have bodyTargetTyping : Target.Tm.HasType
            (ready.target.extendTerm rhsCompiled.targetType)
            bodyCompiled.term bodyCompiled.targetUse
            (resultTarget.rename
              (ManySortedFC.Rename.succ (kind := .term))) := by
          simpa [bodyReady, resultEquality] using bodyCompiled.typing
        let compiled : CompiledTerm ready (.let' result rhs body)
            (.union rhsUse bodyOuterUse) result :=
          { sourceTyping := .letPlain boundPlain rhsCompiled.sourceTyping
              bodyCompiled.sourceTyping discharge
            targetUse := .union rhsCompiled.targetUse bodyOuterTarget
            targetType := resultTarget
            useTranslated := by
              simp [Translation.translateCapture?,
                rhsCompiled.useTranslated, bodyOuterTranslated]
            typeTranslated := resultTranslated
            term := .let' resultTarget bodyOuterTarget rhsCompiled.term
              bodyCompiled.term dischargeCompiled.evidence
            typing := .let' rhsCompiled.typing bodyTargetTyping
              dischargeCompiled.typing }
        pure
          { compiled := compiled
            erasedBody := erasePlainBody boundPlain bodyCompiled.term
            bodyErases := erasePlainBody_heq boundPlain bodyCompiled.term
            compiledErases := by
              dsimp only [compiled]
              rw [ManySortedFC.Tm.erase_let]
              congr 1 }

/-- Finish a plain let while keeping its dependent runtime alignment private. -/
noncomputable def finishPlainLet? {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {result bound : Source.Ty scope} {rhs : Source.Term scope}
    {body : Source.Term (scope + 1)} {rhsUse : Source.Capture scope}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (boundPlain : bound.IsPlain)
    (discharge : Source.CaptureIncludes (context.extendTerm bound) bodyUse
      bodyOuterUse.weaken)
    {resultTarget : Target.Ty (Layout.sig context)}
    {bodyOuterTarget : Target.Capture (Layout.sig context)}
    (resultTranslated :
      Translation.translateTy? context result = some resultTarget)
    (bodyOuterTranslated :
      Translation.translateCapture? context bodyOuterUse =
        some bodyOuterTarget)
    (rhsCompiled : CompiledTerm ready rhs rhsUse bound)
    (bodyCompiled : CompiledTerm
      (ready.extendPlain boundPlain rhsCompiled.typeTranslated) body bodyUse
        result.weaken) :
    Option (CompiledTerm ready (.let' result rhs body)
      (.union rhsUse bodyOuterUse) result) := do
  let finished ← finishPlainLetDetailed? boundPlain discharge resultTranslated
    bodyOuterTranslated rhsCompiled bodyCompiled
  pure finished.compiled

/-- Internal object-let result carrying the canonical erased payload-body
alignment proved where the target existential `open` is constructed. -/
private structure FinishedObjectLet {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {signature : Source.ObjectSig scope} {result : Source.Ty scope}
    {rhs : Source.Term scope} {rhsUse : Source.Capture scope}
    {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (rhsCompiled : CompiledTerm ready rhs rhsUse
      (.capturing signature.captureUpper (.object signature)))
    {bounds : Object.Bounds (Layout.sig context)}
    {signatureTranslated : Translation.translateObjectSig? context signature =
      some bounds}
    (bodyCompiled : CompiledTerm
      (ready.extendObject signature signatureTranslated) body bodyUse
        result.weaken) where
  compiled : CompiledTerm ready (.let' result rhs body)
    (DOTCapture.Acyclic.GeneralExpression.Capture.seq rhsUse
      (.union signature.captureUpper bodyOuterUse)) result
  erasedBody : ManySortedFC.Runtime.Tm
    ((Layout.sig context).termCount + 1)
  bodyErases : HEq bodyCompiled.term.erase erasedBody
  compiledErases : compiled.term.erase =
    ManySortedFC.Runtime.Tm.let' rhsCompiled.term.erase erasedBody

private noncomputable def finishObjectLetDetailed? {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {signature : Source.ObjectSig scope} {result : Source.Ty scope}
    {rhs : Source.Term scope} {rhsUse : Source.Capture scope}
    {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (discharge : Source.CaptureIncludes
      (context.extendTerm
        (.capturing signature.captureUpper (.object signature))) bodyUse
      (.union bodyOuterUse.weaken (.singleton (.var .here))))
    {bounds : Object.Bounds (Layout.sig context)}
    {resultTarget : Target.Ty (Layout.sig context)}
    {bodyOuterTarget : Target.Capture (Layout.sig context)}
    (signatureTranslated :
      Translation.translateObjectSig? context signature = some bounds)
    (resultTranslated :
      Translation.translateTy? context result = some resultTarget)
    (bodyOuterTranslated :
      Translation.translateCapture? context bodyOuterUse =
        some bodyOuterTarget)
    (rhsCompiled : CompiledTerm ready rhs rhsUse
      (.capturing signature.captureUpper (.object signature)))
    (bodyCompiled : CompiledTerm
      (ready.extendObject signature signatureTranslated) body bodyUse
        result.weaken) :
    Option (@FinishedObjectLet scope context ready signature result rhs rhsUse
      body bodyUse bodyOuterUse rhsCompiled bounds signatureTranslated
      bodyCompiled) := do
  have resultWeakenTranslated :
      Translation.translateTy?
          (context.extendTerm
            (.capturing signature.captureUpper (.object signature)))
          result.weaken =
        some ((resultTarget.rename Object.staticWeakening).weaken) := by
    rw [StaticTranslationMetatheory.translateTy?_weaken, resultTranslated]
    simp [Layout.extendRename, ManySortedFC.Ty.weaken,
      ManySortedFC.Ty.rename_comp]
    rfl
  have resultEquality :=
    StaticTranslation.TranslatesTy.functional bodyCompiled.typeTranslated
      resultWeakenTranslated
  have dischargeTargetTranslated :
      Translation.translateCapture?
          (context.extendTerm
            (.capturing signature.captureUpper (.object signature)))
          (.union bodyOuterUse.weaken (.singleton (.var .here))) =
        some (.union
          ((bodyOuterTarget.rename Object.staticWeakening).weaken)
          (.singleton .here)) := by
    simp only [Translation.translateCapture?]
    rw [StaticTranslationMetatheory.translateCapture?_weaken,
      bodyOuterTranslated]
    simp [Layout.extendRename, ManySortedFC.Capture.weaken,
      ManySortedFC.Capture.rename_comp, StaticTranslation.translatePath,
      Layout.translatePath, Layout.termVar,
      DOTCapture.Acyclic.Ctx.extendTerm]
    constructor <;> rfl
  let dischargeCompiled ← compileCaptureInclusion?
    (ready.extendObject signature signatureTranslated).translated discharge
      bodyCompiled.useTranslated dischargeTargetTranslated
  have bodyTargetTyping : Target.Tm.HasType
      ((ready.target.extendTheory (Object.theory bounds)).extendTerm
        Object.payloadType)
      bodyCompiled.term bodyCompiled.targetUse
      ((resultTarget.rename Object.staticWeakening).weaken) := by
    simpa [resultEquality] using bodyCompiled.typing
  have expectedPackageTranslated :
      Translation.translateTy? context
          (.capturing signature.captureUpper (.object signature)) =
        some (Object.objectType bounds) :=
    StaticTranslation.translateTy?_formedObject signature bounds
      signatureTranslated
  have rhsTypeEquality :=
    StaticTranslation.TranslatesTy.functional rhsCompiled.typeTranslated
      expectedPackageTranslated
  have rhsTargetTyping : Target.Tm.HasType ready.target rhsCompiled.term
      rhsCompiled.targetUse (Object.objectType bounds) := by
    simpa [rhsTypeEquality] using rhsCompiled.typing
  have packageShape : (Object.objectType bounds).stripCapture =
      Object.existentialShape bounds := rfl
  have followingTranslated :
      Translation.translateCapture? context
          (.union signature.captureUpper bodyOuterUse) =
        some (.union bounds.captureUpper bodyOuterTarget) := by
    have boundsTranslation := BoundsTranslation.ofTranslated
      signatureTranslated
    simp [Translation.translateCapture?, boundsTranslation.captureUpper,
      bodyOuterTranslated]
  have useTranslated := translateCapture?_seq
    rhsCompiled.useTranslated followingTranslated
  let compiled : CompiledTerm ready (.let' result rhs body)
      (DOTCapture.Acyclic.GeneralExpression.Capture.seq rhsUse
        (.union signature.captureUpper bodyOuterUse)) result :=
    { sourceTyping := .letObject rhsCompiled.sourceTyping
        bodyCompiled.sourceTyping discharge
      targetUse := rhsCompiled.targetUse.sequence
        (.union bounds.captureUpper bodyOuterTarget)
      targetType := resultTarget
      useTranslated := useTranslated
      typeTranslated := resultTranslated
      term := Object.openOnce bounds resultTarget bodyOuterTarget
        rhsCompiled.term bodyCompiled.term dischargeCompiled.evidence
      typing := by
        unfold ObjectEncoding.openOnce
        exact .«open» rhsTargetTyping packageShape bodyTargetTyping
          dischargeCompiled.typing }
  pure
    { compiled := compiled
      erasedBody := eraseObjectBody bodyCompiled.term
      bodyErases := eraseObjectBody_heq bodyCompiled.term
      compiledErases := by
        dsimp only [compiled]
        unfold ObjectEncoding.openOnce
        rw [ManySortedFC.Tm.erase_open]
        rw [payloadEraseCanonical]
        congr 1 }

/-- Finish a computed object let while keeping the payload-scope witness
private. -/
noncomputable def finishObjectLet? {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {signature : Source.ObjectSig scope} {result : Source.Ty scope}
    {rhs : Source.Term scope} {rhsUse : Source.Capture scope}
    {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (discharge : Source.CaptureIncludes
      (context.extendTerm
        (.capturing signature.captureUpper (.object signature))) bodyUse
      (.union bodyOuterUse.weaken (.singleton (.var .here))))
    {bounds : Object.Bounds (Layout.sig context)}
    {resultTarget : Target.Ty (Layout.sig context)}
    {bodyOuterTarget : Target.Capture (Layout.sig context)}
    (signatureTranslated :
      Translation.translateObjectSig? context signature = some bounds)
    (resultTranslated :
      Translation.translateTy? context result = some resultTarget)
    (bodyOuterTranslated :
      Translation.translateCapture? context bodyOuterUse =
        some bodyOuterTarget)
    (rhsCompiled : CompiledTerm ready rhs rhsUse
      (.capturing signature.captureUpper (.object signature)))
    (bodyCompiled : CompiledTerm
      (ready.extendObject signature signatureTranslated) body bodyUse
        result.weaken) :
    Option (CompiledTerm ready (.let' result rhs body)
      (DOTCapture.Acyclic.GeneralExpression.Capture.seq rhsUse
        (.union signature.captureUpper bodyOuterUse)) result) := do
  let finished ← finishObjectLetDetailed? discharge signatureTranslated
    resultTranslated bodyOuterTranslated rhsCompiled bodyCompiled
  pure finished.compiled

/-! ## Mutually derivation-directed direct compiler -/

mutual

@[simp]
noncomputable def compileValue? {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context) :
    {value : Source.Value scope} → {type : Source.Ty scope} →
      Source.Value.HasType context value type →
        Option (CompiledValue ready value type)
  | _, _, @DOTCapture.Acyclic.GeneralExpression.Value.HasType.var _ _ name =>
      compileVariable? ready name
  | _, _, .unit =>
      some
        { targetType := .one
          typeTranslated := rfl
          term := .unit
          isValue := .unit
          typing := .unit }
  | _, _, @DOTCapture.Acyclic.GeneralExpression.Value.HasType.lam _ _
      domain codomain body bodyUse closure domainPlain bodyTyping captures =>
      match domainTranslated :
          Translation.translateTy? context domain with
      | none => none
      | some domainTarget =>
          match codomainTranslated :
              Translation.translateTy? context codomain with
          | none => none
          | some codomainTarget =>
              match closureTranslated :
                  Translation.translateCapture? context closure with
              | none => none
              | some closureTarget => do
                  let bodyReady := ready.extendPlain domainPlain
                    domainTranslated
                  let bodyCompiled ← compileTerm? bodyReady bodyTyping
                  finishLambda? domainPlain captures domainTranslated
                    codomainTranslated closureTranslated bodyCompiled
  | _, _, @DOTCapture.Acyclic.GeneralExpression.Value.HasType.objectLam _ _
      _signature _codomain _body _bodyUse _closure _bodyTyping _captures =>
      none
  | _, _, @DOTCapture.Acyclic.GeneralExpression.Value.HasType.object _ _
      signature typeWitness captureWitness payload payloadType typeLower
      typeUpper captureLower captureUpper payloadTyping payloadShape
      payloadCapture =>
      match signatureTranslated :
          Translation.translateObjectSig? context signature with
      | none => none
      | some bounds =>
          match typeWitnessTranslated :
              Translation.translateTy? context typeWitness with
          | none => none
          | some typeWitnessTarget =>
              match captureWitnessTranslated :
                  Translation.translateCapture? context captureWitness with
              | none => none
              | some captureWitnessTarget => do
                  let payloadCompiled ← compileValue? ready payloadTyping
                  let boundsTranslation :=
                    BoundsTranslation.ofTranslated signatureTranslated
                  let typeLowerCompiled ←
                    compileTypeInclusion? ready.translated typeLower
                      boundsTranslation.typeLower typeWitnessTranslated
                  let typeUpperCompiled ←
                    compileTypeInclusion? ready.translated typeUpper
                      typeWitnessTranslated boundsTranslation.typeUpper
                  let captureLowerCompiled ←
                    compileCaptureInclusion? ready.translated captureLower
                      boundsTranslation.captureLower
                      captureWitnessTranslated
                  let captureUpperCompiled ←
                    compileCaptureInclusion? ready.translated captureUpper
                      captureWitnessTranslated
                      boundsTranslation.captureUpper
                  let payloadShapeCompiled ←
                    compileTypeInclusion? ready.translated payloadShape
                      (translateTy?_stripCapture
                        payloadCompiled.typeTranslated)
                      typeWitnessTranslated
                  let payloadCaptureCompiled ←
                    compileCaptureInclusion? ready.translated payloadCapture
                      (translateTy?_outerCapture
                        payloadCompiled.typeTranslated)
                      captureWitnessTranslated
                  let term := Object.pack bounds typeWitnessTarget
                    captureWitnessTarget typeLowerCompiled.evidence
                    typeUpperCompiled.evidence captureLowerCompiled.evidence
                    captureUpperCompiled.evidence payloadCompiled.term
                    payloadCompiled.targetType
                    payloadCaptureCompiled.evidence
                    payloadShapeCompiled.evidence
                  have satisfaction := satisfiesObjectTheory ready.target
                    bounds typeWitnessTarget captureWitnessTarget
                    typeLowerCompiled.evidence typeUpperCompiled.evidence
                    captureLowerCompiled.evidence
                    captureUpperCompiled.evidence typeLowerCompiled.typing
                    typeUpperCompiled.typing captureLowerCompiled.typing
                    captureUpperCompiled.typing
                  have adaptedPayloadTyping : Target.Tm.HasType ready.target
                      (Object.retagPayload payloadCompiled.term
                        payloadCompiled.targetType typeWitnessTarget
                        captureWitnessTarget
                        payloadCaptureCompiled.evidence
                        payloadShapeCompiled.evidence)
                      .empty
                      (.capturing captureWitnessTarget
                        typeWitnessTarget) := by
                    unfold ObjectEncoding.retagPayload
                    exact ManySortedFC.Tm.HasType.adapt
                      payloadCompiled.isValue payloadCompiled.typing
                      (ManySortedFC.Adapter.HasType.retagCapture
                        payloadCaptureCompiled.typing
                        payloadShapeCompiled.typing)
                  have termTyping : Target.Tm.HasType ready.target term
                      .empty (Object.objectType bounds) := by
                    unfold term ObjectEncoding.pack
                    exact ManySortedFC.Tm.HasType.pack satisfaction
                      (.adapt payloadCompiled.isValue)
                      adaptedPayloadTyping captureUpperCompiled.typing
                  pure
                    { targetType := Object.objectType bounds
                      typeTranslated :=
                        StaticTranslation.translateTy?_formedObject
                          signature bounds signatureTranslated
                      term := term
                      isValue := by
                        unfold term ObjectEncoding.pack
                        exact .pack (.adapt payloadCompiled.isValue)
                      typing := termTyping }
  | _, _, @DOTCapture.Acyclic.GeneralExpression.Value.HasType.adapt _ _
      value source target valueTyping inclusion =>
      match targetTranslated :
          Translation.translateTy? context target with
      | none => none
      | some targetType => do
          let valueCompiled ← compileValue? ready valueTyping
          compileAdapt? valueCompiled inclusion targetTranslated

@[simp]
noncomputable def compileTerm? {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context) :
    {term : Source.Term scope} → {use : Source.Capture scope} →
      {type : Source.Ty scope} →
      Source.Term.HasType context term use type →
        Option (CompiledTerm ready term use type)
  | _, _, _, @DOTCapture.Acyclic.GeneralExpression.Term.HasType.ret _ _
      value type valueTyping => do
      let valueCompiled ← compileValue? ready valueTyping
      pure
        { sourceTyping := .ret valueTyping
          targetUse := .empty
          targetType := valueCompiled.targetType
          useTranslated := rfl
          typeTranslated := valueCompiled.typeTranslated
          term := valueCompiled.term
          typing := valueCompiled.typing }
  | _, _, _, @DOTCapture.Acyclic.GeneralExpression.Term.HasType.select _ _
      receiver signature exposes =>
      some (compileSelect ready exposes)
  | _, _, _, @DOTCapture.Acyclic.GeneralExpression.Term.HasType.app _ _
      function argument functionUse argumentUse functionType domain codomain
      functionTyping functionShape domainPlain argumentTyping =>
      match codomainTranslated :
          Translation.translateTy? context codomain with
      | none => none
      | some codomainTarget => do
          let functionCompiled ← compileTerm? ready functionTyping
          let argumentCompiled ← compileTerm? ready argumentTyping
          have translatedShape :
              Translation.translateTy? context (.arr domain codomain) =
                some functionCompiled.targetType.stripCapture := by
            have translatedShape := translateTy?_stripCapture
              functionCompiled.typeTranslated
            rw [functionShape] at translatedShape
            exact translatedShape
          have arrowTranslated :
              Translation.translateTy? context (.arr domain codomain) =
                some (.arr argumentCompiled.targetType codomainTarget) := by
            simp [Translation.translateTy?, argumentCompiled.typeTranslated,
              codomainTranslated]
          have functionShapeTarget :=
            StaticTranslation.TranslatesTy.functional translatedShape
              arrowTranslated
          have functionOuterTranslated := translateTy?_outerCapture
            functionCompiled.typeTranslated
          have argumentOuterTranslated := translateTy?_outerCapture
            argumentCompiled.typeTranslated
          have invocationTranslated :
              Translation.translateCapture? context
                  (.union functionType.outerCapture domain.outerCapture) =
                some (.union functionCompiled.targetType.outerCapture
                  argumentCompiled.targetType.outerCapture) := by
            simp [Translation.translateCapture?, functionOuterTranslated,
              argumentOuterTranslated]
          have argumentSequenceTranslated := translateCapture?_seq
            argumentCompiled.useTranslated invocationTranslated
          have totalUseTranslated := translateCapture?_seq
            functionCompiled.useTranslated argumentSequenceTranslated
          pure
            { sourceTyping := .app functionCompiled.sourceTyping functionShape
                domainPlain argumentCompiled.sourceTyping
              targetUse := functionCompiled.targetUse.sequence
                (argumentCompiled.targetUse.sequence
                  (.union functionCompiled.targetType.outerCapture
                    argumentCompiled.targetType.outerCapture))
              targetType := codomainTarget
              useTranslated := totalUseTranslated
              typeTranslated := codomainTranslated
              term := .app functionCompiled.term argumentCompiled.term
              typing := .app functionCompiled.typing functionShapeTarget
                argumentCompiled.typing }
  | _, _, _, @DOTCapture.Acyclic.GeneralExpression.Term.HasType.objectApp _ _
      _function _argument _functionUse _closure _codomain _signature
      _functionTyping _argumentTyping =>
      none
  | _, _, _, @DOTCapture.Acyclic.GeneralExpression.Term.HasType.letPlain _ _
      result bound rhs body rhsUse bodyUse bodyOuterUse boundPlain rhsTyping
      bodyTyping discharge =>
      match resultTranslated :
          Translation.translateTy? context result with
      | none => none
      | some resultTarget =>
          match bodyOuterTranslated :
              Translation.translateCapture? context bodyOuterUse with
          | none => none
          | some bodyOuterTarget => do
              let rhsCompiled ← compileTerm? ready rhsTyping
              let bodyReady := ready.extendPlain boundPlain
                rhsCompiled.typeTranslated
              let bodyCompiled ← compileTerm? bodyReady bodyTyping
              finishPlainLet? boundPlain discharge resultTranslated
                bodyOuterTranslated rhsCompiled bodyCompiled
  | _, _, _, @DOTCapture.Acyclic.GeneralExpression.Term.HasType.letObject _ _
      signature result rhs rhsUse body bodyUse bodyOuterUse rhsTyping
      bodyTyping discharge =>
      match signatureTranslated :
          Translation.translateObjectSig? context signature with
      | none => none
      | some bounds =>
          match resultTranslated :
              Translation.translateTy? context result with
          | none => none
          | some resultTarget =>
              match bodyOuterTranslated :
                  Translation.translateCapture? context bodyOuterUse with
              | none => none
              | some bodyOuterTarget => do
                  let rhsCompiled ← compileTerm? ready rhsTyping
                  let bodyReady := ready.extendObject signature
                    signatureTranslated
                  let bodyCompiled ← compileTerm? bodyReady bodyTyping
                  finishObjectLet? discharge signatureTranslated
                    resultTranslated bodyOuterTranslated rhsCompiled
                    bodyCompiled
  | _, _, _, @DOTCapture.Acyclic.GeneralExpression.Term.HasType.use _ _
      term sourceUse targetUse type termTyping inclusion => do
      let inner ← compileTerm? ready termTyping
      compileUse? inner inclusion

end

/-! ## Negative object-consumer compilation

These entry points are intentionally separate from `compileValue?` and
`compileTerm?`.  Those definitions remain the positive compiler and therefore
continue to return `none` on the negative object derivation constructors. -/

/-- Front-door failure reported before proof-directed object-argument
compilation.  It names the required source repair instead of leaking a target
type-checking failure. -/
inductive Error : Type where
  | objectArgumentRequiresExplicitOpen
deriving DecidableEq, Repr

def validateObjectArgument {scope : Source.Scope}
    (argument : Source.Term scope) : Except Error Unit :=
  match DOTCapture.Acyclic.GeneralExpression.ObjectArgument.classify argument with
  | .canonicalLiteral | .stableVariable => .ok ()
  | .unsupported .requiresExplicitOpen =>
      .error .objectArgumentRequiresExplicitOpen

theorem validateObjectArgument_requiresExplicitOpen {scope : Source.Scope}
    {argument : Source.Term scope}
    (classified :
      DOTCapture.Acyclic.GeneralExpression.ObjectArgument.classify argument =
        .unsupported .requiresExplicitOpen) :
    validateObjectArgument argument =
      .error .objectArgumentRequiresExplicitOpen := by
  simp [validateObjectArgument, classified]

@[simp]
theorem validateObjectArgument_literal {scope : Source.Scope}
    (signature : Source.ObjectSig scope) (typeWitness : Source.Ty scope)
    (captureWitness : Source.Capture scope) (payload : Source.Value scope) :
    validateObjectArgument
      (.ret (.object signature typeWitness captureWitness payload)) = .ok () :=
  rfl

@[simp]
theorem validateObjectArgument_stable {scope : Source.Scope}
    (name : Source.Var scope) :
    validateObjectArgument (.ret (.var name)) = .ok () := rfl

noncomputable def compileObjectSignature? {scope : Source.Scope}
    (context : Source.Ctx scope) (signature : Source.ObjectSig scope) :
    Option (CompiledObjectSignature context signature) :=
  match translated : Translation.translateObjectSig? context signature with
  | none => none
  | some bounds => some ⟨bounds, translated⟩

/-- Regard a freshly compiled object lambda as a negative function
computation.  This is the base case used by direct object application; other
compiler phases may construct `CompiledObjectFunction` for computed consumers. -/
def CompiledObjectConsumer.asFunction {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {signature : Source.ObjectSig scope}
    {interface : CompiledObjectSignature context signature}
    {codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {closure : Source.Capture scope}
    (compiled : CompiledObjectConsumer ready interface codomain body bodyUse
      closure) :
    CompiledObjectFunction ready interface
      (.ret (.lam signature.formedType codomain body)) .empty codomain
      closure where
  sourceTyping := .returned compiled.bodySourceTyping compiled.sourceCaptures
  targetUse := .empty
  useTranslated := rfl
  outerCapture := compiled.closureTarget
  outerTranslated := compiled.closureTranslated
  resultType := compiled.resultType
  resultTranslated := compiled.resultTranslated
  term := compiled.term
  typing := compiled.typing

/- Internal implementation retained for the stable-path branch below.  The
polarized compiler owns canonical-literal recursion, so this definition is
not part of the public compiler interface. -/
private noncomputable def compileObjectArgumentBacking? {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope}
    (interface : CompiledObjectSignature context signature) :
    {argument : Source.Term scope} →
      Source.ObjectArgument.HasType context argument signature →
      Option (CompiledObjectArgument ready interface argument)
  | _, @DOTCapture.Acyclic.GeneralExpression.ObjectArgument.HasType.literal
      _ _ available _ typeWitness captureWitness payload payloadType
      typeLower typeUpper captureLower captureUpper payloadTyping payloadShape
      payloadCapture adaptation =>
      match availableTranslated :
          Translation.translateObjectSig? context available with
      | none => none
      | some availableBounds =>
          match typeWitnessTranslated :
              Translation.translateTy? context typeWitness with
          | none => none
          | some typeWitnessTarget =>
              match captureWitnessTranslated :
                  Translation.translateCapture? context captureWitness with
              | none => none
              | some captureWitnessTarget => do
                  let payloadCompiled ← compileValue? ready payloadTyping
                  let availableTranslation :=
                    BoundsTranslation.ofTranslated availableTranslated
                  let expectedTranslation :=
                    BoundsTranslation.ofTranslated interface.translated
                  let availableTypeLower ←
                    compileTypeInclusion? ready.translated typeLower
                      availableTranslation.typeLower typeWitnessTranslated
                  let availableTypeUpper ←
                    compileTypeInclusion? ready.translated typeUpper
                      typeWitnessTranslated availableTranslation.typeUpper
                  let availableCaptureLower ←
                    compileCaptureInclusion? ready.translated captureLower
                      availableTranslation.captureLower
                      captureWitnessTranslated
                  let availableCaptureUpper ←
                    compileCaptureInclusion? ready.translated captureUpper
                      captureWitnessTranslated
                      availableTranslation.captureUpper
                  let expectedTypeLower ←
                    compileTypeInclusion? ready.translated adaptation.typeLower
                      expectedTranslation.typeLower
                      availableTranslation.typeLower
                  let expectedTypeUpper ←
                    compileTypeInclusion? ready.translated adaptation.typeUpper
                      availableTranslation.typeUpper
                      expectedTranslation.typeUpper
                  let expectedCaptureLower ←
                    compileCaptureInclusion? ready.translated
                      adaptation.captureLower expectedTranslation.captureLower
                      availableTranslation.captureLower
                  let expectedCaptureUpper ←
                    compileCaptureInclusion? ready.translated
                      adaptation.captureUpper availableTranslation.captureUpper
                      expectedTranslation.captureUpper
                  let payloadShapeCompiled ←
                    compileTypeInclusion? ready.translated payloadShape
                      (translateTy?_stripCapture
                        payloadCompiled.typeTranslated)
                      typeWitnessTranslated
                  let payloadCaptureCompiled ←
                    compileCaptureInclusion? ready.translated payloadCapture
                      (translateTy?_outerCapture
                        payloadCompiled.typeTranslated)
                      captureWitnessTranslated
                  let finalTypeLower : Target.Evidence (.inclusion .type)
                      (Layout.sig context) :=
                    .inclusionTrans expectedTypeLower.evidence
                      availableTypeLower.evidence
                  let finalTypeUpper : Target.Evidence (.inclusion .type)
                      (Layout.sig context) :=
                    .inclusionTrans availableTypeUpper.evidence
                      expectedTypeUpper.evidence
                  let finalCaptureLower :
                      Target.Evidence (.inclusion .capture)
                        (Layout.sig context) :=
                    .inclusionTrans expectedCaptureLower.evidence
                      availableCaptureLower.evidence
                  let finalCaptureUpper :
                      Target.Evidence (.inclusion .capture)
                        (Layout.sig context) :=
                    .inclusionTrans availableCaptureUpper.evidence
                      expectedCaptureUpper.evidence
                  have finalTypeLowerTyping : Target.Evidence.Proves
                      ready.target finalTypeLower
                      (.inclusion (.type interface.bounds.typeLower)
                        (.type typeWitnessTarget)) :=
                    .inclusionTrans expectedTypeLower.typing
                      availableTypeLower.typing
                  have finalTypeUpperTyping : Target.Evidence.Proves
                      ready.target finalTypeUpper
                      (.inclusion (.type typeWitnessTarget)
                        (.type interface.bounds.typeUpper)) :=
                    .inclusionTrans availableTypeUpper.typing
                      expectedTypeUpper.typing
                  have finalCaptureLowerTyping : Target.Evidence.Proves
                      ready.target finalCaptureLower
                      (.inclusion (.capture interface.bounds.captureLower)
                        (.capture captureWitnessTarget)) :=
                    .inclusionTrans expectedCaptureLower.typing
                      availableCaptureLower.typing
                  have finalCaptureUpperTyping : Target.Evidence.Proves
                      ready.target finalCaptureUpper
                      (.inclusion (.capture captureWitnessTarget)
                        (.capture interface.bounds.captureUpper)) :=
                    .inclusionTrans availableCaptureUpper.typing
                      expectedCaptureUpper.typing
                  let retagged := Object.retagPayload payloadCompiled.term
                    payloadCompiled.targetType typeWitnessTarget
                    captureWitnessTarget payloadCaptureCompiled.evidence
                    payloadShapeCompiled.evidence
                  have retaggedTyping : Target.Tm.HasType ready.target
                      retagged .empty
                      (.capturing captureWitnessTarget typeWitnessTarget) := by
                    unfold retagged ObjectEncoding.retagPayload
                    exact .adapt payloadCompiled.isValue payloadCompiled.typing
                      (ManySortedFC.Adapter.HasType.retagCapture
                        payloadCaptureCompiled.typing
                        payloadShapeCompiled.typing)
                  have satisfaction := satisfiesObjectTheory ready.target
                    interface.bounds typeWitnessTarget captureWitnessTarget
                    finalTypeLower finalTypeUpper finalCaptureLower
                    finalCaptureUpper finalTypeLowerTyping finalTypeUpperTyping
                    finalCaptureLowerTyping finalCaptureUpperTyping
                  let targetArgument : Negative.Argument ready.target
                      (Object.theory interface.bounds) Object.payloadType :=
                    { symbols := Object.symbolArguments typeWitnessTarget
                        captureWitnessTarget
                      evidence := Object.evidenceArguments finalTypeLower
                        finalTypeUpper finalCaptureLower finalCaptureUpper
                      satisfies := satisfaction
                      payload := retagged
                      payloadValue := .adapt payloadCompiled.isValue
                      payloadTyping := by
                        simpa [ObjectEncoding.payloadType,
                          ObjectEncoding.symbolArguments,
                          ManySortedFC.Ty.instantiateStatic,
                          ManySortedFC.Ty.substitute,
                          ManySortedFC.StaticSubst.ofSymbolArgs]
                          using retaggedTyping }
                  pure
                    { sourceTyping := .literal typeLower typeUpper captureLower
                        captureUpper payloadTyping payloadShape payloadCapture
                        adaptation
                      typeWitness := typeWitnessTarget
                      captureWitness := captureWitnessTarget
                      target := targetArgument
                      symbolsEquation := rfl
                      captureUpper := finalCaptureUpper
                      captureUpperTyping := finalCaptureUpperTyping }
  | _, @DOTCapture.Acyclic.GeneralExpression.ObjectArgument.HasType.stable
      _ _ name available _ canonical adaptation => do
      let exposes : Source.ExposesObject context (.var name) available :=
        .variable (by rw [canonical]; rfl)
      let resolved := ExposureTranslation.resolve ready.translated exposes
      let availableTranslation :=
        BoundsTranslation.ofTranslated resolved.boundsTranslated
      let expectedTranslation :=
        BoundsTranslation.ofTranslated interface.translated
      let expectedTypeLower ←
        compileTypeInclusion? ready.translated adaptation.typeLower
          expectedTranslation.typeLower availableTranslation.typeLower
      let expectedTypeUpper ←
        compileTypeInclusion? ready.translated adaptation.typeUpper
          availableTranslation.typeUpper expectedTranslation.typeUpper
      let expectedCaptureLower ←
        compileCaptureInclusion? ready.translated adaptation.captureLower
          expectedTranslation.captureLower availableTranslation.captureLower
      let expectedCaptureUpper ←
        compileCaptureInclusion? ready.translated adaptation.captureUpper
          availableTranslation.captureUpper expectedTranslation.captureUpper
      let typeWitnessTarget : Target.Ty (Layout.sig context) :=
        .tvar resolved.slot.alpha.name
      let captureWitnessTarget : Target.Capture (Layout.sig context) :=
        .cvar resolved.slot.chi.name
      let availableTypeLower : Target.Evidence (.inclusion .type)
          (Layout.sig context) := .var resolved.facts.typeLower
      let availableTypeUpper : Target.Evidence (.inclusion .type)
          (Layout.sig context) := .var resolved.facts.typeUpper
      let availableCaptureLower : Target.Evidence (.inclusion .capture)
          (Layout.sig context) := .var resolved.facts.captureLower
      let availableCaptureUpper : Target.Evidence (.inclusion .capture)
          (Layout.sig context) := .var resolved.facts.captureUpper
      have availableTypeLowerTyping : Target.Evidence.Proves ready.target
          availableTypeLower
          (.inclusion (.type resolved.bounds.typeLower)
            (.type typeWitnessTarget)) := by
        simpa [availableTypeLower, typeWitnessTarget,
          ManySortedTranslation.StaticSlot.expression]
          using ManySortedFC.Evidence.Proves.var
            resolved.facts.typeLowerLookup
      have availableTypeUpperTyping : Target.Evidence.Proves ready.target
          availableTypeUpper
          (.inclusion (.type typeWitnessTarget)
            (.type resolved.bounds.typeUpper)) := by
        simpa [availableTypeUpper, typeWitnessTarget,
          ManySortedTranslation.StaticSlot.expression]
          using ManySortedFC.Evidence.Proves.var
            resolved.facts.typeUpperLookup
      have availableCaptureLowerTyping : Target.Evidence.Proves ready.target
          availableCaptureLower
          (.inclusion (.capture resolved.bounds.captureLower)
            (.capture captureWitnessTarget)) := by
        simpa [availableCaptureLower, captureWitnessTarget,
          ManySortedTranslation.StaticSlot.expression]
          using ManySortedFC.Evidence.Proves.var
            resolved.facts.captureLowerLookup
      have availableCaptureUpperTyping : Target.Evidence.Proves ready.target
          availableCaptureUpper
          (.inclusion (.capture captureWitnessTarget)
            (.capture resolved.bounds.captureUpper)) := by
        simpa [availableCaptureUpper, captureWitnessTarget,
          ManySortedTranslation.StaticSlot.expression]
          using ManySortedFC.Evidence.Proves.var
            resolved.facts.captureUpperLookup
      let finalTypeLower : Target.Evidence (.inclusion .type)
          (Layout.sig context) := .inclusionTrans expectedTypeLower.evidence
            availableTypeLower
      let finalTypeUpper : Target.Evidence (.inclusion .type)
          (Layout.sig context) := .inclusionTrans availableTypeUpper
            expectedTypeUpper.evidence
      let finalCaptureLower : Target.Evidence (.inclusion .capture)
          (Layout.sig context) :=
        .inclusionTrans expectedCaptureLower.evidence availableCaptureLower
      let finalCaptureUpper : Target.Evidence (.inclusion .capture)
          (Layout.sig context) :=
        .inclusionTrans availableCaptureUpper expectedCaptureUpper.evidence
      have finalTypeLowerTyping : Target.Evidence.Proves ready.target
          finalTypeLower
          (.inclusion (.type interface.bounds.typeLower)
            (.type typeWitnessTarget)) :=
        .inclusionTrans expectedTypeLower.typing availableTypeLowerTyping
      have finalTypeUpperTyping : Target.Evidence.Proves ready.target
          finalTypeUpper
          (.inclusion (.type typeWitnessTarget)
            (.type interface.bounds.typeUpper)) :=
        .inclusionTrans availableTypeUpperTyping expectedTypeUpper.typing
      have finalCaptureLowerTyping : Target.Evidence.Proves ready.target
          finalCaptureLower
          (.inclusion (.capture interface.bounds.captureLower)
            (.capture captureWitnessTarget)) :=
        .inclusionTrans expectedCaptureLower.typing availableCaptureLowerTyping
      have finalCaptureUpperTyping : Target.Evidence.Proves ready.target
          finalCaptureUpper
          (.inclusion (.capture captureWitnessTarget)
            (.capture interface.bounds.captureUpper)) :=
        .inclusionTrans availableCaptureUpperTyping expectedCaptureUpper.typing
      let payloadSourceType : Target.Ty (Layout.sig context) :=
        .capturing (.singleton resolved.slot.payload) typeWitnessTarget
      let payloadCaptures : Target.Evidence (.inclusion .capture)
          (Layout.sig context) := .captureVariable resolved.slot.payload
      let payloadShape : Target.Evidence (.inclusion .type)
          (Layout.sig context) := .inclusionRefl (.type typeWitnessTarget)
      have rawPayloadTyping : Target.Tm.HasType ready.target
          (.var resolved.slot.payload) .empty payloadSourceType := by
        have raw := ManySortedFC.Tm.HasType.var
          (context := ready.target) resolved.slot.payload
        have payloadLookup := resolved.facts.payloadLookup
        change ready.target.lookup resolved.slot.payload = _ at payloadLookup
        rw [payloadLookup] at raw
        simpa [payloadSourceType, captureWitnessTarget, typeWitnessTarget]
          using raw
      have payloadCapturesTyping : Target.Evidence.Proves ready.target
          payloadCaptures
          (.inclusion (.capture (.singleton resolved.slot.payload))
            (.capture captureWitnessTarget)) := by
        exact .captureVariable resolved.facts.payloadLookup
      have payloadShapeTyping : Target.Evidence.Proves ready.target payloadShape
          (.inclusion (.type typeWitnessTarget)
            (.type typeWitnessTarget)) :=
        .inclusionRefl (.type typeWitnessTarget)
      let retagged := Object.retagPayload (.var resolved.slot.payload)
        payloadSourceType typeWitnessTarget captureWitnessTarget
        payloadCaptures payloadShape
      have retaggedTyping : Target.Tm.HasType ready.target retagged .empty
          (.capturing captureWitnessTarget typeWitnessTarget) := by
        unfold retagged ObjectEncoding.retagPayload
        exact .adapt .var rawPayloadTyping
          (ManySortedFC.Adapter.HasType.retagCapture payloadCapturesTyping
            payloadShapeTyping)
      have satisfaction := satisfiesObjectTheory ready.target
        interface.bounds typeWitnessTarget captureWitnessTarget finalTypeLower
        finalTypeUpper finalCaptureLower finalCaptureUpper
        finalTypeLowerTyping finalTypeUpperTyping finalCaptureLowerTyping
        finalCaptureUpperTyping
      let targetArgument : Negative.Argument ready.target
          (Object.theory interface.bounds) Object.payloadType :=
        { symbols := Object.symbolArguments typeWitnessTarget
            captureWitnessTarget
          evidence := Object.evidenceArguments finalTypeLower finalTypeUpper
            finalCaptureLower finalCaptureUpper
          satisfies := satisfaction
          payload := retagged
          payloadValue := .adapt .var
          payloadTyping := by
            simpa [ObjectEncoding.payloadType,
              ObjectEncoding.symbolArguments,
              ManySortedFC.Ty.instantiateStatic,
              ManySortedFC.Ty.substitute,
              ManySortedFC.StaticSubst.ofSymbolArgs]
              using retaggedTyping }
      pure
        { sourceTyping := .stable canonical adaptation
          typeWitness := typeWitnessTarget
          captureWitness := captureWitnessTarget
          target := targetArgument
          symbolsEquation := rfl
          captureUpper := finalCaptureUpper
          captureUpperTyping := finalCaptureUpperTyping }

/-- Reuse the model and payload already installed for a stable object root. -/
noncomputable def compileStableObjectArgument? {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope}
    (interface : CompiledObjectSignature context signature)
    {name : Source.Var scope} {available : Source.ObjectSig scope}
    (canonical : context.lookup name = available.formedType)
    (adaptation : available.Adapts context signature) :
    Option (CompiledObjectArgument ready interface (.ret (.var name))) :=
  compileObjectArgumentBacking? ready interface
    (.stable canonical adaptation)

/-- Stable negative arguments erase to the runtime variable installed for
their payload coordinate. -/
theorem compileStableObjectArgument?_erase {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope}
    (interface : CompiledObjectSignature context signature)
    {name : Source.Var scope} {available : Source.ObjectSig scope}
    (canonical : context.lookup name = available.formedType)
    (adaptation : available.Adapts context signature)
    {compiled : CompiledObjectArgument ready interface (.ret (.var name))}
    (success : compileStableObjectArgument? ready interface canonical
      adaptation = some compiled) :
    compiled.target.payload.erase =
      .var (ManySortedFC.BVar.toTermIndex (Layout.termVar context name)) := by
  unfold compileStableObjectArgument? at success
  unfold compileObjectArgumentBacking? at success
  simp only [Bind.bind, Option.bind] at success
  split at success <;> try contradiction
  simp only at success
  split at success <;> try contradiction
  simp only at success
  split at success <;> try contradiction
  simp only at success
  split at success <;> try contradiction
  simp only at success
  cases success
  simp [ObjectEncoding.retagPayload, ManySortedFC.Tm.erase,
    ManySortedFC.Tm.eraseWith, ManySortedFC.Adapter.erase]
  rw [(ExposureTranslation.resolve ready.translated
    (.variable (by rw [canonical]; rfl) :
      Source.ExposesObject context (.var name) available)).payloadIsPath]
  rfl

private structure CaptureEvidence {scope : ManySortedFC.Sig}
    (context : Target.Ctx scope) (source target : Target.Capture scope) where
  evidence : Target.Evidence (.inclusion .capture) scope
  typing : Target.Evidence.Proves context evidence
    (.inclusion (.capture source) (.capture target))

private def widenInvocationUse {scope : ManySortedFC.Sig}
    (context : Target.Ctx scope) (functionUse outer actual upper :
      Target.Capture scope)
    (actualUpper : CaptureEvidence context actual upper) :
    CaptureEvidence context
      ((functionUse.sequence outer).sequence (.union outer actual))
      (functionUse.sequence (.union outer upper)) := by
  let outerInto : CaptureEvidence context outer (.union outer upper) :=
    { evidence := .captureUnionLeft outer upper
      typing := .captureUnionLeft outer upper }
  let actualInto : CaptureEvidence context actual (.union outer upper) :=
    { evidence := .inclusionTrans actualUpper.evidence
        (.captureUnionRight outer upper)
      typing := .inclusionTrans actualUpper.typing
        (.captureUnionRight outer upper) }
  let tail : CaptureEvidence context (.union outer actual)
      (.union outer upper) :=
    { evidence := .captureUnionElim outerInto.evidence actualInto.evidence
      typing := .captureUnionElim outerInto.typing actualInto.typing }
  let nonempty (immediate : Target.Capture scope) : CaptureEvidence context
      (.union (.union immediate outer) (.union outer actual))
      (.union immediate (.union outer upper)) := by
    let functionInto : CaptureEvidence context
        (.union immediate outer)
        (.union immediate (.union outer upper)) :=
      { evidence := .captureUnionElim
          (.captureUnionLeft immediate (.union outer upper))
          (.inclusionTrans outerInto.evidence
            (.captureUnionRight immediate (.union outer upper)))
        typing := .captureUnionElim
          (.captureUnionLeft immediate (.union outer upper))
          (.inclusionTrans outerInto.typing
            (.captureUnionRight immediate (.union outer upper))) }
    let tailInto : CaptureEvidence context (.union outer actual)
        (.union immediate (.union outer upper)) :=
      { evidence := .inclusionTrans tail.evidence
          (.captureUnionRight immediate (.union outer upper))
        typing := .inclusionTrans tail.typing
          (.captureUnionRight immediate (.union outer upper)) }
    exact
      { evidence := .captureUnionElim functionInto.evidence tailInto.evidence
        typing := .captureUnionElim functionInto.typing tailInto.typing }
  cases functionUse with
  | empty =>
      cases outer with
      | empty => exact tail
      | union left right | singleton left | cvar left =>
          exact
            { evidence := .captureUnionElim outerInto.evidence tail.evidence
              typing := .captureUnionElim outerInto.typing tail.typing }
      | readOnly capture =>
          exact
            { evidence := .captureUnionElim outerInto.evidence tail.evidence
              typing := .captureUnionElim outerInto.typing tail.typing }
      | project capture kind =>
          exact
            { evidence := .captureUnionElim outerInto.evidence tail.evidence
              typing := .captureUnionElim outerInto.typing tail.typing }
  | union left right => exact nonempty (.union left right)
  | singleton path => exact nonempty (.singleton path)
  | cvar name => exact nonempty (.cvar name)
  | readOnly capture => exact nonempty (.readOnly capture)
  | project capture kind => exact nonempty (.project capture kind)

private def staticInstantiationCancels {scope : ManySortedFC.Sig}
    (typeWitness : Target.Ty scope)
    (captureWitness : Target.Capture scope) :
    BinderOnly.TargetStaticInstantiation.Cancels
      (Object.staticWeakening (scope := scope))
      (ManySortedFC.StaticSubst.staticOfSymbolArgs ManySortedFC.Rename.id
        (Object.symbolArguments typeWitness captureWitness)
        Object.relations) := by
  constructor
  · intro index
    rfl
  · intro sort index
    rfl

private theorem negativeType_rename {source target : ManySortedFC.Sig}
    (bounds : Object.Bounds source) (result : Target.Ty source)
    (closure : Target.Capture source) (rho : ManySortedFC.Rename source target) :
    (Negative.ambientResultType (Object.theory bounds) Object.payloadType
        result closure).rename rho =
      Negative.ambientResultType (Object.theory (bounds.rename rho))
        Object.payloadType (result.rename rho) (closure.rename rho) := by
  simp [Negative.ambientResultType, Negative.consumerType, Negative.bodyType,
    ManySortedFC.Ty.rename, ManySortedFC.Capture.rename_comp,
    ManySortedFC.Ty.rename_comp]
  rw [← DOTCaptureToManySortedFC.BinderOnly.ManySortedRename.comp_weakenStatic
    rho Object.symbols Object.relations]
  exact ⟨rfl, rfl⟩

/-- Compile direct negative application from an already compiled negative
function and a dedicated object argument.  The only wrapper added around the
requested `app (sapp ...) payload` is a logical use certificate. -/
noncomputable def compileObjectApplication {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {signature : Source.ObjectSig scope}
    {interface : CompiledObjectSignature context signature}
    {function argument : Source.Term scope}
    {functionUse : Source.Capture scope} {codomain : Source.Ty scope}
    {closure : Source.Capture scope}
    (functionCompiled : CompiledObjectFunction ready interface function
      functionUse codomain closure)
    (argumentCompiled : CompiledObjectArgument ready interface argument) :
    CompiledObjectApplication ready interface function argument functionUse
      codomain closure := by
  let directTerm := Negative.applyArgument (Object.theory interface.bounds)
    functionCompiled.term argumentCompiled.target
  have directTypingRaw := Negative.apply_hasType functionCompiled.typing
    argumentCompiled.target
  have symbolCancellation := staticInstantiationCancels
    argumentCompiled.typeWitness argumentCompiled.captureWitness
  have resultInstantiation :
      (functionCompiled.resultType.rename Object.staticWeakening).instantiateStatic
          argumentCompiled.target.symbols = functionCompiled.resultType := by
    rw [argumentCompiled.symbolsEquation]
    exact BinderOnly.TargetStaticInstantiation.ty_rename_substitute
      functionCompiled.resultType symbolCancellation
  have closureInstantiation :
      (functionCompiled.outerCapture.rename Object.staticWeakening).instantiateStatic
          argumentCompiled.target.symbols = functionCompiled.outerCapture := by
    rw [argumentCompiled.symbolsEquation]
    exact BinderOnly.TargetStaticInstantiation.capture_rename_substitute
      functionCompiled.outerCapture symbolCancellation
  have representationInstantiation :
      Object.payloadType.instantiateStatic argumentCompiled.target.symbols =
        .capturing argumentCompiled.captureWitness
          argumentCompiled.typeWitness := by
    rw [argumentCompiled.symbolsEquation]
    rfl
  have bodyOuterInstantiation :
      ((Negative.bodyType Object.payloadType
          (functionCompiled.resultType.rename Object.staticWeakening)
          (functionCompiled.outerCapture.rename
            Object.staticWeakening)).instantiateStatic
        argumentCompiled.target.symbols).outerCapture =
        functionCompiled.outerCapture := by
    change
      (functionCompiled.outerCapture.rename
        Object.staticWeakening).instantiateStatic
          argumentCompiled.target.symbols = functionCompiled.outerCapture
    exact closureInstantiation
  have directTyping : Target.Tm.HasType ready.target directTerm
      ((functionCompiled.targetUse.sequence functionCompiled.outerCapture).sequence
      (.union functionCompiled.outerCapture
          argumentCompiled.captureWitness))
      functionCompiled.resultType := by
    change Target.Tm.HasType ready.target directTerm
      ((functionCompiled.targetUse.sequence
        functionCompiled.outerCapture).sequence
        (.union
          ((functionCompiled.outerCapture.rename
            Object.staticWeakening).instantiateStatic
              argumentCompiled.target.symbols)
          (Object.payloadType.instantiateStatic
            argumentCompiled.target.symbols).outerCapture))
      ((functionCompiled.resultType.rename
        Object.staticWeakening).instantiateStatic
          argumentCompiled.target.symbols) at directTypingRaw
    rw [closureInstantiation, representationInstantiation,
      resultInstantiation] at directTypingRaw
    exact directTypingRaw
  let actualUpper : CaptureEvidence ready.target
      argumentCompiled.captureWitness interface.bounds.captureUpper :=
    { evidence := argumentCompiled.captureUpper
      typing := argumentCompiled.captureUpperTyping }
  let widening := widenInvocationUse ready.target functionCompiled.targetUse
    functionCompiled.outerCapture argumentCompiled.captureWitness
    interface.bounds.captureUpper actualUpper
  let targetUse := functionCompiled.targetUse.sequence
    (.union functionCompiled.outerCapture interface.bounds.captureUpper)
  let term : Target.Tm (Layout.sig context) :=
    .use directTerm widening.evidence
  have typing : Target.Tm.HasType ready.target term targetUse
      functionCompiled.resultType := by
    exact .use directTyping widening.typing
  have upperTranslated :=
    (BoundsTranslation.ofTranslated interface.translated).captureUpper
  have followingTranslated :
      Translation.translateCapture? context
          (.union closure signature.captureUpper) =
        some (.union functionCompiled.outerCapture
          interface.bounds.captureUpper) := by
    simp [Translation.translateCapture?, functionCompiled.outerTranslated,
      upperTranslated]
  have useTranslated := translateCapture?_seq functionCompiled.useTranslated
    followingTranslated
  exact
    { sourceTyping := .objectApp functionCompiled.sourceTyping
        argumentCompiled.sourceTyping
      targetUse := targetUse
      useTranslated := useTranslated
      resultType := functionCompiled.resultType
      resultTranslated := functionCompiled.resultTranslated
      term := term
      typing := typing }

/-! ## Successful constructor shapes -/

/-- Variable compilation is delegated to the already verified value-MNF
variable compiler.  Exposing that child result keeps downstream proofs from
unfolding the private `compileVariable?` implementation across a module
boundary. -/
theorem compileValue?_var_result {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    (name : Source.Var scope)
    {compiled : CompiledValue ready (.var name) (context.lookup name)}
    (success : compileValue? ready
      (DOTCapture.Acyclic.GeneralExpression.Value.HasType.var
        (context := context) (name := name)) = some compiled) :
    ∃ core :
        DOTCaptureToManySortedFC.Acyclic.ValueTranslation.CompiledValue ready
          (.var name) (context.lookup name),
      DOTCaptureToManySortedFC.Acyclic.ValueTranslation.compileValue? ready
          (DOTCapture.Acyclic.Value.HasType.var
            (context := context) (name := name)) = some core ∧
      compiled.term = core.term := by
  unfold compileValue? at success
  unfold compileVariable? at success
  generalize coreEquation :
    DOTCaptureToManySortedFC.Acyclic.ValueTranslation.compileValue? ready
      (DOTCapture.Acyclic.Value.HasType.var
        (context := context) (name := name)) = coreResult at success
  cases coreResult with
  | none => simp at success
  | some core =>
      cases success
      exact ⟨core, rfl, rfl⟩

/-- Successful object-value compilation exposes the recursively compiled
payload and confirms that all target packaging, retagging, and static evidence
erase away.  Downstream erasure proofs therefore need not unfold the private
object-evidence compilation pipeline. -/
theorem compileValue?_object_erase {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope} {typeWitness : Source.Ty scope}
    {captureWitness : Source.Capture scope} {payload : Source.Value scope}
    {payloadType : Source.Ty scope}
    (typeLower : Source.TypeIncludes context signature.typeLower typeWitness)
    (typeUpper : Source.TypeIncludes context typeWitness signature.typeUpper)
    (captureLower : Source.CaptureIncludes context signature.captureLower
      captureWitness)
    (captureUpper : Source.CaptureIncludes context captureWitness
      signature.captureUpper)
    (payloadTyping : Source.Value.HasType context payload payloadType)
    (payloadShape : Source.TypeIncludes context payloadType.stripCapture
      typeWitness)
    (payloadCapture : Source.CaptureIncludes context payloadType.outerCapture
      captureWitness)
    {compiled : CompiledValue ready
      (.object signature typeWitness captureWitness payload)
      (.capturing signature.captureUpper (.object signature))}
    (success : compileValue? ready
      (.object typeLower typeUpper captureLower captureUpper payloadTyping
        payloadShape payloadCapture) = some compiled) :
    ∃ payloadCompiled : CompiledValue ready payload payloadType,
      compileValue? ready payloadTyping = some payloadCompiled ∧
      compiled.term.erase = payloadCompiled.term.erase := by
  unfold compileValue? at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  generalize payloadEquation :
    compileValue? ready payloadTyping = payloadResult at success
  cases payloadResult with
  | none => simp at success
  | some payloadCompiled =>
      simp only [Bind.bind, Option.bind] at success
      split at success <;> try contradiction
      simp only at success
      split at success <;> try contradiction
      simp only at success
      split at success <;> try contradiction
      simp only at success
      split at success <;> try contradiction
      simp only at success
      split at success <;> try contradiction
      simp only at success
      split at success <;> try contradiction
      simp only at success
      cases success
      exact ⟨payloadCompiled, rfl, by
        simp [ObjectEncoding.pack, ObjectEncoding.retagPayload,
          ManySortedFC.Tm.erase, ManySortedFC.Tm.eraseWith,
          ManySortedFC.Adapter.erase]⟩

/-- Successful lambda finishing exposes the recursively compiled body's
canonical erased scope and the exact runtime lambda spine. -/
theorem finishLambda?_erase {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {domain codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)} {closure : Source.Capture scope}
    (domainPlain : domain.IsPlain)
    (captures : Source.CaptureIncludes (context.extendTerm domain) bodyUse
      (.union closure.weaken (.singleton (.var .here))))
    {domainTarget codomainTarget : Target.Ty (Layout.sig context)}
    {closureTarget : Target.Capture (Layout.sig context)}
    (domainTranslated :
      Translation.translateTy? context domain = some domainTarget)
    (codomainTranslated :
      Translation.translateTy? context codomain = some codomainTarget)
    (closureTranslated :
      Translation.translateCapture? context closure = some closureTarget)
    (bodyCompiled : CompiledTerm
      (ready.extendPlain domainPlain domainTranslated) body bodyUse
        codomain.weaken)
    {compiled : CompiledValue ready (.lam domain codomain body)
      (.capturing closure (.arr domain codomain))}
    (success : finishLambda? domainPlain captures domainTranslated
      codomainTranslated closureTranslated bodyCompiled = some compiled) :
    ∃ erasedBody : ManySortedFC.Runtime.Tm
        ((Layout.sig context).termCount + 1),
      HEq bodyCompiled.term.erase erasedBody ∧
      compiled.term.erase = ManySortedFC.Runtime.Tm.lam erasedBody := by
  unfold finishLambda? at success
  generalize finishEquation :
    finishLambdaDetailed? domainPlain captures domainTranslated
      codomainTranslated closureTranslated bodyCompiled = finishResult
        at success
  cases finishResult with
  | none => simp at success
  | some finished =>
      cases success
      exact ⟨finished.erasedBody, finished.bodyErases,
        finished.compiledErases⟩

/-- Successful plain-let finishing exposes the canonical erased body and one
exact runtime let node. -/
theorem finishPlainLet?_erase {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {result bound : Source.Ty scope} {rhs : Source.Term scope}
    {body : Source.Term (scope + 1)} {rhsUse : Source.Capture scope}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (boundPlain : bound.IsPlain)
    (discharge : Source.CaptureIncludes (context.extendTerm bound) bodyUse
      bodyOuterUse.weaken)
    {resultTarget : Target.Ty (Layout.sig context)}
    {bodyOuterTarget : Target.Capture (Layout.sig context)}
    (resultTranslated :
      Translation.translateTy? context result = some resultTarget)
    (bodyOuterTranslated :
      Translation.translateCapture? context bodyOuterUse =
        some bodyOuterTarget)
    (rhsCompiled : CompiledTerm ready rhs rhsUse bound)
    (bodyCompiled : CompiledTerm
      (ready.extendPlain boundPlain rhsCompiled.typeTranslated) body bodyUse
        result.weaken)
    {compiled : CompiledTerm ready (.let' result rhs body)
      (.union rhsUse bodyOuterUse) result}
    (success : finishPlainLet? boundPlain discharge resultTranslated
      bodyOuterTranslated rhsCompiled bodyCompiled = some compiled) :
    ∃ erasedBody : ManySortedFC.Runtime.Tm
        ((Layout.sig context).termCount + 1),
      HEq bodyCompiled.term.erase erasedBody ∧
      compiled.term.erase = ManySortedFC.Runtime.Tm.let'
        rhsCompiled.term.erase erasedBody := by
  unfold finishPlainLet? at success
  generalize finishEquation :
    finishPlainLetDetailed? boundPlain discharge resultTranslated
      bodyOuterTranslated rhsCompiled bodyCompiled = finishResult at success
  cases finishResult with
  | none => simp at success
  | some finished =>
      cases success
      exact ⟨finished.erasedBody, finished.bodyErases,
        finished.compiledErases⟩

/-- Successful computed-object-let finishing exposes the canonical erased
opened body and the single runtime let contributed by target `open`. -/
theorem finishObjectLet?_erase {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {signature : Source.ObjectSig scope} {result : Source.Ty scope}
    {rhs : Source.Term scope} {rhsUse : Source.Capture scope}
    {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (discharge : Source.CaptureIncludes
      (context.extendTerm
        (.capturing signature.captureUpper (.object signature))) bodyUse
      (.union bodyOuterUse.weaken (.singleton (.var .here))))
    {bounds : Object.Bounds (Layout.sig context)}
    {resultTarget : Target.Ty (Layout.sig context)}
    {bodyOuterTarget : Target.Capture (Layout.sig context)}
    (signatureTranslated :
      Translation.translateObjectSig? context signature = some bounds)
    (resultTranslated :
      Translation.translateTy? context result = some resultTarget)
    (bodyOuterTranslated :
      Translation.translateCapture? context bodyOuterUse =
        some bodyOuterTarget)
    (rhsCompiled : CompiledTerm ready rhs rhsUse
      (.capturing signature.captureUpper (.object signature)))
    (bodyCompiled : CompiledTerm
      (ready.extendObject signature signatureTranslated) body bodyUse
        result.weaken)
    {compiled : CompiledTerm ready (.let' result rhs body)
      (DOTCapture.Acyclic.GeneralExpression.Capture.seq rhsUse
        (.union signature.captureUpper bodyOuterUse)) result}
    (success : finishObjectLet? discharge signatureTranslated
      resultTranslated bodyOuterTranslated rhsCompiled bodyCompiled =
        some compiled) :
    ∃ erasedBody : ManySortedFC.Runtime.Tm
        ((Layout.sig context).termCount + 1),
      HEq bodyCompiled.term.erase erasedBody ∧
      compiled.term.erase = ManySortedFC.Runtime.Tm.let'
        rhsCompiled.term.erase erasedBody := by
  unfold finishObjectLet? at success
  generalize finishEquation :
    finishObjectLetDetailed? discharge signatureTranslated resultTranslated
      bodyOuterTranslated rhsCompiled bodyCompiled = finishResult at success
  cases finishResult with
  | none => simp at success
  | some finished =>
      cases success
      exact ⟨finished.erasedBody, finished.bodyErases,
        finished.compiledErases⟩

theorem compileTerm?_app_term {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {function argument : Source.Term scope}
    {functionUse argumentUse : Source.Capture scope}
    {functionType domain codomain : Source.Ty scope}
    (functionTyping : Source.Term.HasType context function functionUse
      functionType)
    (functionShape : functionType.stripCapture = .arr domain codomain)
    (domainPlain : domain.IsPlain)
    (argumentTyping : Source.Term.HasType context argument argumentUse domain)
    {compiled : CompiledTerm ready (.app function argument)
      (DOTCapture.Acyclic.GeneralExpression.Capture.seq functionUse
        (DOTCapture.Acyclic.GeneralExpression.Capture.seq argumentUse
          (.union functionType.outerCapture domain.outerCapture))) codomain}
    (success : compileTerm? ready
      (.app functionTyping functionShape domainPlain argumentTyping) =
        some compiled) :
    ∃ functionCompiled argumentCompiled,
      compileTerm? ready functionTyping = some functionCompiled ∧
      compileTerm? ready argumentTyping = some argumentCompiled ∧
      compiled.term =
        .app functionCompiled.term argumentCompiled.term := by
  unfold compileTerm? at success
  split at success <;> try contradiction
  generalize functionEquation :
    compileTerm? ready functionTyping = functionResult at success
  cases functionResult with
  | none => simp at success
  | some functionCompiled =>
      generalize argumentEquation :
        compileTerm? ready argumentTyping = argumentResult at success
      cases argumentResult with
      | none => simp at success
      | some argumentCompiled =>
          cases success
          exact ⟨functionCompiled, argumentCompiled, rfl, rfl, rfl⟩

theorem compileValue?_adapt_term {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {value : Source.Value scope} {source target : Source.Ty scope}
    (valueTyping : Source.Value.HasType context value source)
    (inclusion : Source.TypeIncludes context source target)
    {compiled : CompiledValue ready value target}
    (success : compileValue? ready (.adapt valueTyping inclusion) =
      some compiled) :
    ∃ inner evidence,
      compileValue? ready valueTyping = some inner ∧
      compiled.term = .adapt inner.term (.cast evidence) := by
  unfold compileValue? at success
  split at success <;> try contradiction
  rename_i targetType targetTranslated
  generalize innerEquation :
    compileValue? ready valueTyping = innerResult at success
  cases innerResult with
  | none => simp at success
  | some inner =>
      change compileAdapt? inner inclusion targetTranslated = some compiled
        at success
      unfold compileAdapt? at success
      generalize evidenceEquation :
        compileTypeInclusion? ready.translated inclusion
          inner.typeTranslated targetTranslated = evidenceResult at success
      cases evidenceResult with
      | none => simp at success
      | some evidence =>
          cases success
          exact ⟨inner, evidence.evidence, rfl, rfl⟩

theorem compileTerm?_use_term {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {term : Source.Term scope} {sourceUse targetUse : Source.Capture scope}
    {type : Source.Ty scope}
    (termTyping : Source.Term.HasType context term sourceUse type)
    (inclusion : Source.CaptureIncludes context sourceUse targetUse)
    {compiled : CompiledTerm ready term targetUse type}
    (success : compileTerm? ready (.use termTyping inclusion) =
      some compiled) :
    ∃ inner evidence,
      compileTerm? ready termTyping = some inner ∧
      compiled.term = .use inner.term evidence := by
  unfold compileTerm? at success
  generalize innerEquation :
    compileTerm? ready termTyping = innerResult at success
  cases innerResult with
  | none => simp at success
  | some inner =>
      change compileUse? inner inclusion = some compiled at success
      unfold compileUse? at success
      split at success <;> try contradiction
      rename_i targetTarget targetTranslated
      generalize evidenceEquation :
        compileCaptureInclusion? ready.translated inclusion
          inner.useTranslated targetTranslated = evidenceResult at success
      cases evidenceResult with
      | none => simp at success
      | some evidence =>
          cases success
          exact ⟨inner, evidence.evidence, rfl, rfl⟩

theorem compileValue?_lam_result {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {domain codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)} {closure : Source.Capture scope}
    (domainPlain : domain.IsPlain)
    (bodyTyping : Source.Term.HasType (context.extendTerm domain) body
      bodyUse codomain.weaken)
    (captures : Source.CaptureIncludes (context.extendTerm domain) bodyUse
      (.union closure.weaken (.singleton (.var .here))))
    {compiled : CompiledValue ready (.lam domain codomain body)
      (.capturing closure (.arr domain codomain))}
    (success : compileValue? ready
      (.lam domainPlain bodyTyping captures) = some compiled) :
    ∃ (domainTarget codomainTarget : Target.Ty (Layout.sig context))
        (closureTarget : Target.Capture (Layout.sig context))
        (domainTranslated :
          Translation.translateTy? context domain = some domainTarget)
        (codomainTranslated :
          Translation.translateTy? context codomain = some codomainTarget)
        (closureTranslated :
          Translation.translateCapture? context closure = some closureTarget)
        (bodyCompiled : CompiledTerm
          (ready.extendPlain domainPlain domainTranslated) body bodyUse
            codomain.weaken),
      compileTerm? (ready.extendPlain domainPlain domainTranslated)
          bodyTyping = some bodyCompiled ∧
      finishLambda? domainPlain captures domainTranslated codomainTranslated
          closureTranslated bodyCompiled = some compiled := by
  unfold compileValue? at success
  split at success <;> try contradiction
  rename_i domainTarget domainTranslated
  split at success <;> try contradiction
  rename_i codomainTarget codomainTranslated
  split at success <;> try contradiction
  rename_i closureTarget closureTranslated
  change (do
    let bodyCompiled ←
      compileTerm? (ready.extendPlain domainPlain domainTranslated) bodyTyping
    finishLambda? domainPlain captures domainTranslated codomainTranslated
      closureTranslated bodyCompiled) = some compiled at success
  generalize bodyEquation :
    compileTerm? (ready.extendPlain domainPlain domainTranslated) bodyTyping =
      bodyResult at success ⊢
  cases bodyResult with
  | none => simp at success
  | some bodyCompiled =>
      exact ⟨domainTarget, codomainTarget, closureTarget,
        domainTranslated, codomainTranslated, closureTranslated,
        bodyCompiled, bodyEquation, success⟩

theorem compileTerm?_letPlain_result {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {result bound : Source.Ty scope} {rhs : Source.Term scope}
    {body : Source.Term (scope + 1)} {rhsUse : Source.Capture scope}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (boundPlain : bound.IsPlain)
    (rhsTyping : Source.Term.HasType context rhs rhsUse bound)
    (bodyTyping : Source.Term.HasType (context.extendTerm bound) body
      bodyUse result.weaken)
    (discharge : Source.CaptureIncludes (context.extendTerm bound) bodyUse
      bodyOuterUse.weaken)
    {compiled : CompiledTerm ready (.let' result rhs body)
      (.union rhsUse bodyOuterUse) result}
    (success : compileTerm? ready
      (.letPlain boundPlain rhsTyping bodyTyping discharge) = some compiled) :
    ∃ (resultTarget : Target.Ty (Layout.sig context))
        (bodyOuterTarget : Target.Capture (Layout.sig context))
        (resultTranslated :
          Translation.translateTy? context result = some resultTarget)
        (bodyOuterTranslated :
          Translation.translateCapture? context bodyOuterUse =
            some bodyOuterTarget)
        (rhsCompiled : CompiledTerm ready rhs rhsUse bound)
        (bodyCompiled : CompiledTerm
          (ready.extendPlain boundPlain rhsCompiled.typeTranslated) body
            bodyUse result.weaken),
      compileTerm? ready rhsTyping = some rhsCompiled ∧
      compileTerm?
          (ready.extendPlain boundPlain rhsCompiled.typeTranslated)
          bodyTyping = some bodyCompiled ∧
      finishPlainLet? boundPlain discharge resultTranslated
          bodyOuterTranslated rhsCompiled bodyCompiled = some compiled := by
  unfold compileTerm? at success
  split at success <;> try contradiction
  rename_i resultTarget resultTranslated
  split at success <;> try contradiction
  rename_i bodyOuterTarget bodyOuterTranslated
  change (do
    let rhsCompiled ← compileTerm? ready rhsTyping
    let bodyReady := ready.extendPlain boundPlain rhsCompiled.typeTranslated
    let bodyCompiled ← compileTerm? bodyReady bodyTyping
    finishPlainLet? boundPlain discharge resultTranslated
      bodyOuterTranslated rhsCompiled bodyCompiled) = some compiled at success
  generalize rhsEquation :
    compileTerm? ready rhsTyping = rhsResult at success
  cases rhsResult with
  | none => simp at success
  | some rhsCompiled =>
      change (do
        let bodyCompiled ← compileTerm?
          (ready.extendPlain boundPlain rhsCompiled.typeTranslated) bodyTyping
        finishPlainLet? boundPlain discharge resultTranslated
          bodyOuterTranslated rhsCompiled bodyCompiled) = some compiled
        at success
      generalize bodyEquation :
        compileTerm?
            (ready.extendPlain boundPlain rhsCompiled.typeTranslated)
            bodyTyping = bodyResult at success
      cases bodyResult with
      | none => simp at success
      | some bodyCompiled =>
          exact ⟨resultTarget, bodyOuterTarget, resultTranslated,
            bodyOuterTranslated, rhsCompiled, bodyCompiled, rfl,
            bodyEquation, success⟩

theorem compileTerm?_letObject_result {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope} {result : Source.Ty scope}
    {rhs : Source.Term scope} {rhsUse : Source.Capture scope}
    {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (rhsTyping : Source.Term.HasType context rhs rhsUse
      (.capturing signature.captureUpper (.object signature)))
    (bodyTyping : Source.Term.HasType
      (context.extendTerm
        (.capturing signature.captureUpper (.object signature)))
      body bodyUse result.weaken)
    (discharge : Source.CaptureIncludes
      (context.extendTerm
        (.capturing signature.captureUpper (.object signature))) bodyUse
      (.union bodyOuterUse.weaken (.singleton (.var .here))))
    {compiled : CompiledTerm ready (.let' result rhs body)
      (DOTCapture.Acyclic.GeneralExpression.Capture.seq rhsUse
        (.union signature.captureUpper bodyOuterUse)) result}
    (success : compileTerm? ready
      (.letObject rhsTyping bodyTyping discharge) = some compiled) :
    ∃ (bounds : Object.Bounds (Layout.sig context))
        (resultTarget : Target.Ty (Layout.sig context))
        (bodyOuterTarget : Target.Capture (Layout.sig context))
        (signatureTranslated :
          Translation.translateObjectSig? context signature = some bounds)
        (resultTranslated :
          Translation.translateTy? context result = some resultTarget)
        (bodyOuterTranslated :
          Translation.translateCapture? context bodyOuterUse =
            some bodyOuterTarget)
        (rhsCompiled : CompiledTerm ready rhs rhsUse
          (.capturing signature.captureUpper (.object signature)))
        (bodyCompiled : CompiledTerm
          (ready.extendObject signature signatureTranslated) body bodyUse
            result.weaken),
      compileTerm? ready rhsTyping = some rhsCompiled ∧
      compileTerm? (ready.extendObject signature signatureTranslated)
          bodyTyping = some bodyCompiled ∧
      finishObjectLet? discharge signatureTranslated resultTranslated
          bodyOuterTranslated rhsCompiled bodyCompiled = some compiled := by
  unfold compileTerm? at success
  split at success <;> try contradiction
  rename_i bounds signatureTranslated
  split at success <;> try contradiction
  rename_i resultTarget resultTranslated
  split at success <;> try contradiction
  rename_i bodyOuterTarget bodyOuterTranslated
  change (do
    let rhsCompiled ← compileTerm? ready rhsTyping
    let bodyReady := ready.extendObject signature signatureTranslated
    let bodyCompiled ← compileTerm? bodyReady bodyTyping
    finishObjectLet? discharge signatureTranslated resultTranslated
      bodyOuterTranslated rhsCompiled bodyCompiled) = some compiled at success
  generalize rhsEquation :
    compileTerm? ready rhsTyping = rhsResult at success
  cases rhsResult with
  | none => simp at success
  | some rhsCompiled =>
      change (do
        let bodyCompiled ← compileTerm?
          (ready.extendObject signature signatureTranslated) bodyTyping
        finishObjectLet? discharge signatureTranslated resultTranslated
          bodyOuterTranslated rhsCompiled bodyCompiled) = some compiled
        at success
      generalize bodyEquation :
        compileTerm? (ready.extendObject signature signatureTranslated)
          bodyTyping = bodyResult at success
      cases bodyResult with
      | none => simp at success
      | some bodyCompiled =>
          exact ⟨bounds, resultTarget, bodyOuterTarget,
            signatureTranslated, resultTranslated, bodyOuterTranslated,
            rhsCompiled, bodyCompiled, rfl, bodyEquation, success⟩

/-! ## Recursive polarized compiler

The positive entry points above deliberately retain their old result and
equations.  This derivation-directed entry point adds negative object functions
and direct object application recursively, so an object application may occur
in an ordinary lambda body, either branch of an ordinary application, or below
an explicit object opening. -/

private noncomputable def finishObjectLambdaCompiled? {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope}
    (interface : CompiledObjectSignature context signature)
    {codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {closure : Source.Capture scope}
    (bodyTyping : Source.Term.HasType
      (context.extendTerm signature.formedType) body bodyUse codomain.weaken)
    (captures : Source.CaptureIncludes
      (context.extendTerm signature.formedType) bodyUse
      (.union closure.weaken (.singleton (.var .here))))
    (bodyCompiled : CompiledTerm
      (ready.extendObject signature interface.translated) body bodyUse
        codomain.weaken) :
    Option (CompiledObjectConsumer ready interface codomain body bodyUse
      closure) :=
  match resultTranslated : Translation.translateTy? context codomain with
  | none => none
  | some resultType =>
      match closureTranslated :
          Translation.translateCapture? context closure with
      | none => none
      | some closureTarget => do
          let bodyReady := ready.extendObject signature interface.translated
          have resultWeakenTranslated :
              Translation.translateTy?
                  (context.extendTerm signature.formedType) codomain.weaken =
                some ((resultType.rename Object.staticWeakening).weaken) := by
            rw [StaticTranslationMetatheory.translateTy?_weaken,
              resultTranslated]
            simp [DOTCapture.Acyclic.GeneralExpression.ObjectSig.formedType,
              Layout.extendRename, ManySortedFC.Ty.weaken,
              ManySortedFC.Ty.rename_comp]
            rfl
          have resultEquality :=
            StaticTranslation.TranslatesTy.functional
              bodyCompiled.typeTranslated resultWeakenTranslated
          have upperTranslated :
              Translation.translateCapture?
                  (context.extendTerm signature.formedType)
                  (.union closure.weaken (.singleton (.var .here))) =
                some
                  (.union
                    ((closureTarget.rename Object.staticWeakening).weaken)
                    (.singleton .here)) := by
            simp only [Translation.translateCapture?]
            rw [StaticTranslationMetatheory.translateCapture?_weaken,
              closureTranslated]
            simp [DOTCapture.Acyclic.GeneralExpression.ObjectSig.formedType,
              Layout.extendRename, ManySortedFC.Capture.weaken,
              ManySortedFC.Capture.rename_comp,
              StaticTranslation.translatePath, Layout.translatePath,
              Layout.termVar, DOTCapture.Acyclic.Ctx.extendTerm]
            constructor <;> rfl
          let capturesCompiled ← compileCaptureInclusion?
            bodyReady.translated captures bodyCompiled.useTranslated
              upperTranslated
          have alignedBodyTyping : Target.Tm.HasType
              ((ready.target.extendTheory (Object.theory interface.bounds)).extendTerm
                Object.payloadType)
              bodyCompiled.term bodyCompiled.targetUse
              ((resultType.rename Object.staticWeakening).weaken) := by
            simpa [bodyReady, resultEquality] using bodyCompiled.typing
          pure
            { bodySourceTyping := bodyTyping
              sourceCaptures := captures
              sourceTyping := .objectLam bodyTyping captures
              resultType := resultType
              resultTranslated := resultTranslated
              closureTarget := closureTarget
              closureTranslated := closureTranslated
              bodyCompiled := bodyCompiled
              bodyTyping := alignedBodyTyping
              bodyCaptures := capturesCompiled.evidence
              bodyCapturesTyping := capturesCompiled.typing }

private noncomputable def finishObjectFunctionLet? {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope}
    (interface : CompiledObjectSignature context signature)
    {codomain bound : Source.Ty scope} {closure : Source.Capture scope}
    {rhs : Source.Term scope} {body : Source.Term (scope + 1)}
    {rhsUse : Source.Capture scope} {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (boundPlain : bound.IsPlain)
    (rhsTyping : Source.Term.HasType context rhs rhsUse bound)
    (bodyTyping : Source.ObjectFunction.HasType (context.extendTerm bound)
      body bodyUse signature.weaken codomain.weaken closure.weaken)
    (discharge : Source.CaptureIncludes (context.extendTerm bound) bodyUse
      bodyOuterUse.weaken)
    (rhsCompiled : CompiledTerm ready rhs rhsUse bound)
    (bodyInterface : CompiledObjectSignature (context.extendTerm bound)
      signature.weaken)
    (bodyBounds : bodyInterface.bounds = interface.bounds.rename
      (Layout.extendRename context bound))
    (bodyCompiled : CompiledObjectFunction
      (ready.extendPlain boundPlain rhsCompiled.typeTranslated) bodyInterface
      body bodyUse codomain.weaken closure.weaken) :
    Option (CompiledObjectFunction ready interface
      (.let' (.capturing closure (.arr signature.formedType codomain)) rhs body)
      (.union rhsUse bodyOuterUse) codomain closure) :=
  match resultTranslated : Translation.translateTy? context codomain with
  | none => none
  | some resultType =>
      match closureTranslated :
          Translation.translateCapture? context closure with
      | none => none
      | some closureTarget =>
          match bodyOuterTranslated :
              Translation.translateCapture? context bodyOuterUse with
          | none => none
          | some bodyOuterTarget => by
              let bodyReady := ready.extendPlain boundPlain
                rhsCompiled.typeTranslated
              have resultWeakenTranslated :
                  Translation.translateTy? (context.extendTerm bound)
                      codomain.weaken =
                    some (resultType.rename
                      (Layout.extendRename context bound)) := by
                rw [StaticTranslationMetatheory.translateTy?_weaken,
                  resultTranslated]
                rfl
              have resultEquality :=
                StaticTranslation.TranslatesTy.functional
                  bodyCompiled.resultTranslated resultWeakenTranslated
              have closureWeakenTranslated :
                  Translation.translateCapture? (context.extendTerm bound)
                      closure.weaken =
                    some (closureTarget.rename
                      (Layout.extendRename context bound)) := by
                rw [StaticTranslationMetatheory.translateCapture?_weaken,
                  closureTranslated]
                rfl
              have closureEquality :=
                StaticTranslation.TranslatesCapture.functional
                  bodyCompiled.outerTranslated closureWeakenTranslated
              have bodyOuterWeakenTranslated :
                  Translation.translateCapture? (context.extendTerm bound)
                      bodyOuterUse.weaken =
                    some (bodyOuterTarget.rename
                      (Layout.extendRename context bound)) := by
                rw [StaticTranslationMetatheory.translateCapture?_weaken,
                  bodyOuterTranslated]
                rfl
              exact do
                let dischargeCompiled ← compileCaptureInclusion?
                  bodyReady.translated discharge bodyCompiled.useTranslated
                    bodyOuterWeakenTranslated
                let targetType := Negative.ambientResultType
                  (Object.theory interface.bounds) Object.payloadType resultType
                  closureTarget
                have bodyTypeEquality :
                    Negative.ambientResultType
                        (Object.theory bodyInterface.bounds) Object.payloadType
                        bodyCompiled.resultType bodyCompiled.outerCapture =
                      targetType.rename (Layout.extendRename context bound) := by
                  rw [negativeType_rename]
                  rw [bodyBounds, resultEquality, closureEquality]
                by
                  cases bound with
                  | object signature =>
                      simp [DOTCapture.Acyclic.Ty.IsPlain,
                        DOTCapture.Acyclic.Ty.objectSignature?,
                        DOTCapture.Acyclic.Ty.stripCapture] at boundPlain
                  | capturing boundCapture shape =>
                      cases shape with
                      | object signature =>
                          simp [DOTCapture.Acyclic.Ty.IsPlain,
                            DOTCapture.Acyclic.Ty.objectSignature?,
                            DOTCapture.Acyclic.Ty.stripCapture] at boundPlain
                      | top | bot | one | ref | arr | capturing =>
                          have bodyTargetTyping : Target.Tm.HasType
                              (ready.target.extendTerm rhsCompiled.targetType)
                              bodyCompiled.term bodyCompiled.targetUse
                              targetType.weaken := by
                            simpa [bodyReady, ManySortedFC.Ty.weaken,
                              bodyTypeEquality, Layout.extendRename] using
                              bodyCompiled.typing
                          let term : Target.Tm (Layout.sig context) :=
                            .let' targetType bodyOuterTarget rhsCompiled.term
                              bodyCompiled.term dischargeCompiled.evidence
                          exact pure
                            { sourceTyping := .letPlain boundPlain
                                rhsCompiled.sourceTyping bodyCompiled.sourceTyping
                                discharge
                              targetUse := .union rhsCompiled.targetUse
                                bodyOuterTarget
                              useTranslated := by
                                simp [Translation.translateCapture?,
                                  rhsCompiled.useTranslated, bodyOuterTranslated]
                              outerCapture := closureTarget
                              outerTranslated := closureTranslated
                              resultType := resultType
                              resultTranslated := resultTranslated
                              term := term
                              typing := .let' rhsCompiled.typing bodyTargetTyping
                                dischargeCompiled.typing }
                  | top | bot | one | ref | arr =>
                        have bodyTargetTyping : Target.Tm.HasType
                            (ready.target.extendTerm rhsCompiled.targetType)
                            bodyCompiled.term bodyCompiled.targetUse
                            targetType.weaken := by
                          simpa [bodyReady, ManySortedFC.Ty.weaken,
                            bodyTypeEquality, Layout.extendRename] using
                            bodyCompiled.typing
                        let term : Target.Tm (Layout.sig context) :=
                          .let' targetType bodyOuterTarget rhsCompiled.term
                            bodyCompiled.term dischargeCompiled.evidence
                        exact pure
                          { sourceTyping := .letPlain boundPlain
                              rhsCompiled.sourceTyping bodyCompiled.sourceTyping
                              discharge
                            targetUse := .union rhsCompiled.targetUse
                              bodyOuterTarget
                            useTranslated := by
                              simp [Translation.translateCapture?,
                                rhsCompiled.useTranslated, bodyOuterTranslated]
                            outerCapture := closureTarget
                            outerTranslated := closureTranslated
                            resultType := resultType
                            resultTranslated := resultTranslated
                            term := term
                            typing := .let' rhsCompiled.typing bodyTargetTyping
                              dischargeCompiled.typing }

mutual

@[simp]
noncomputable def compilePolarizedValue? {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context) :
    {value : Source.Value scope} → {type : Source.Ty scope} →
      Source.Value.HasType context value type →
        Option (CompiledValue ready value type)
  | _, _, @DOTCapture.Acyclic.GeneralExpression.Value.HasType.lam _ _
      domain codomain body bodyUse closure domainPlain bodyTyping captures =>
      match domainTranslated : Translation.translateTy? context domain with
      | none => none
      | some domainTarget =>
          match codomainTranslated : Translation.translateTy? context codomain with
          | none => none
          | some codomainTarget =>
              match closureTranslated :
                  Translation.translateCapture? context closure with
              | none => none
              | some closureTarget => do
                  let bodyReady := ready.extendPlain domainPlain domainTranslated
                  let bodyCompiled ← compilePolarizedTerm? bodyReady bodyTyping
                  finishLambda? domainPlain captures domainTranslated
                    codomainTranslated closureTranslated bodyCompiled
  | _, _, @DOTCapture.Acyclic.GeneralExpression.Value.HasType.object _ _
      signature typeWitness captureWitness payload payloadType typeLower
      typeUpper captureLower captureUpper payloadTyping payloadShape
      payloadCapture =>
      match signatureTranslated :
          Translation.translateObjectSig? context signature with
      | none => none
      | some bounds =>
          match typeWitnessTranslated :
              Translation.translateTy? context typeWitness with
          | none => none
          | some typeWitnessTarget =>
              match captureWitnessTranslated :
                  Translation.translateCapture? context captureWitness with
              | none => none
              | some captureWitnessTarget => do
                  let payloadCompiled ← compilePolarizedValue? ready payloadTyping
                  let boundsTranslation :=
                    BoundsTranslation.ofTranslated signatureTranslated
                  let typeLowerCompiled ←
                    compileTypeInclusion? ready.translated typeLower
                      boundsTranslation.typeLower typeWitnessTranslated
                  let typeUpperCompiled ←
                    compileTypeInclusion? ready.translated typeUpper
                      typeWitnessTranslated boundsTranslation.typeUpper
                  let captureLowerCompiled ←
                    compileCaptureInclusion? ready.translated captureLower
                      boundsTranslation.captureLower
                      captureWitnessTranslated
                  let captureUpperCompiled ←
                    compileCaptureInclusion? ready.translated captureUpper
                      captureWitnessTranslated
                      boundsTranslation.captureUpper
                  let payloadShapeCompiled ←
                    compileTypeInclusion? ready.translated payloadShape
                      (translateTy?_stripCapture
                        payloadCompiled.typeTranslated)
                      typeWitnessTranslated
                  let payloadCaptureCompiled ←
                    compileCaptureInclusion? ready.translated payloadCapture
                      (translateTy?_outerCapture
                        payloadCompiled.typeTranslated)
                      captureWitnessTranslated
                  let term := Object.pack bounds typeWitnessTarget
                    captureWitnessTarget typeLowerCompiled.evidence
                    typeUpperCompiled.evidence captureLowerCompiled.evidence
                    captureUpperCompiled.evidence payloadCompiled.term
                    payloadCompiled.targetType
                    payloadCaptureCompiled.evidence
                    payloadShapeCompiled.evidence
                  have satisfaction := satisfiesObjectTheory ready.target
                    bounds typeWitnessTarget captureWitnessTarget
                    typeLowerCompiled.evidence typeUpperCompiled.evidence
                    captureLowerCompiled.evidence
                    captureUpperCompiled.evidence typeLowerCompiled.typing
                    typeUpperCompiled.typing captureLowerCompiled.typing
                    captureUpperCompiled.typing
                  have adaptedPayloadTyping : Target.Tm.HasType ready.target
                      (Object.retagPayload payloadCompiled.term
                        payloadCompiled.targetType typeWitnessTarget
                        captureWitnessTarget
                        payloadCaptureCompiled.evidence
                        payloadShapeCompiled.evidence)
                      .empty
                      (.capturing captureWitnessTarget
                        typeWitnessTarget) := by
                    unfold ObjectEncoding.retagPayload
                    exact ManySortedFC.Tm.HasType.adapt
                      payloadCompiled.isValue payloadCompiled.typing
                      (ManySortedFC.Adapter.HasType.retagCapture
                        payloadCaptureCompiled.typing
                        payloadShapeCompiled.typing)
                  have termTyping : Target.Tm.HasType ready.target term
                      .empty (Object.objectType bounds) := by
                    unfold term ObjectEncoding.pack
                    exact ManySortedFC.Tm.HasType.pack satisfaction
                      (.adapt payloadCompiled.isValue)
                      adaptedPayloadTyping captureUpperCompiled.typing
                  pure
                    { targetType := Object.objectType bounds
                      typeTranslated :=
                        StaticTranslation.translateTy?_formedObject
                          signature bounds signatureTranslated
                      term := term
                      isValue := by
                        unfold term ObjectEncoding.pack
                        exact .pack (.adapt payloadCompiled.isValue)
                      typing := termTyping }
  | _, _, @DOTCapture.Acyclic.GeneralExpression.Value.HasType.adapt _ _
      value source target valueTyping inclusion =>
      match targetTranslated : Translation.translateTy? context target with
      | none => none
      | some targetType => do
          let valueCompiled ← compilePolarizedValue? ready valueTyping
          compileAdapt? valueCompiled inclusion targetTranslated
  | _, _, typing => compileValue? ready typing

@[simp]
noncomputable def compilePolarizedTerm? {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context) :
    {term : Source.Term scope} → {use : Source.Capture scope} →
      {type : Source.Ty scope} →
      Source.Term.HasType context term use type →
        Option (CompiledTerm ready term use type)
  | _, _, _, @DOTCapture.Acyclic.GeneralExpression.Term.HasType.ret _ _
      value type valueTyping => do
      let valueCompiled ← compilePolarizedValue? ready valueTyping
      pure
        { sourceTyping := .ret valueTyping
          targetUse := .empty
          targetType := valueCompiled.targetType
          useTranslated := rfl
          typeTranslated := valueCompiled.typeTranslated
          term := valueCompiled.term
          typing := valueCompiled.typing }
  | _, _, _, @DOTCapture.Acyclic.GeneralExpression.Term.HasType.select _ _
      receiver signature exposes =>
      some (compileSelect ready exposes)
  | _, _, _, @DOTCapture.Acyclic.GeneralExpression.Term.HasType.app _ _
      function argument functionUse argumentUse functionType domain codomain
      functionTyping functionShape domainPlain argumentTyping =>
      match codomainTranslated : Translation.translateTy? context codomain with
      | none => none
      | some codomainTarget => do
          let functionCompiled ← compilePolarizedTerm? ready functionTyping
          let argumentCompiled ← compilePolarizedTerm? ready argumentTyping
          have translatedShape :
              Translation.translateTy? context (.arr domain codomain) =
                some functionCompiled.targetType.stripCapture := by
            have translatedShape := translateTy?_stripCapture
              functionCompiled.typeTranslated
            rw [functionShape] at translatedShape
            exact translatedShape
          have arrowTranslated :
              Translation.translateTy? context (.arr domain codomain) =
                some (.arr argumentCompiled.targetType codomainTarget) := by
            simp [Translation.translateTy?, argumentCompiled.typeTranslated,
              codomainTranslated]
          have functionShapeTarget :=
            StaticTranslation.TranslatesTy.functional translatedShape
              arrowTranslated
          have invocationTranslated :
              Translation.translateCapture? context
                  (.union functionType.outerCapture domain.outerCapture) =
                some (.union functionCompiled.targetType.outerCapture
                  argumentCompiled.targetType.outerCapture) := by
            simp [Translation.translateCapture?,
              translateTy?_outerCapture functionCompiled.typeTranslated,
              translateTy?_outerCapture argumentCompiled.typeTranslated]
          have totalUseTranslated := translateCapture?_seq
            functionCompiled.useTranslated
            (translateCapture?_seq argumentCompiled.useTranslated
              invocationTranslated)
          pure
            { sourceTyping := .app functionCompiled.sourceTyping functionShape
                domainPlain argumentCompiled.sourceTyping
              targetUse := functionCompiled.targetUse.sequence
                (argumentCompiled.targetUse.sequence
                  (.union functionCompiled.targetType.outerCapture
                    argumentCompiled.targetType.outerCapture))
              targetType := codomainTarget
              useTranslated := totalUseTranslated
              typeTranslated := codomainTranslated
              term := .app functionCompiled.term argumentCompiled.term
              typing := .app functionCompiled.typing functionShapeTarget
                argumentCompiled.typing }
  | _, _, _, @DOTCapture.Acyclic.GeneralExpression.Term.HasType.objectApp _ _
      function argument functionUse closure codomain signature functionTyping
      argumentTyping => do
      let interface ← compileObjectSignature? context signature
      let functionCompiled ← compileObjectFunction? ready interface
        functionTyping
      let argumentCompiled ← compilePolarizedObjectArgument? ready interface
        argumentTyping
      let application := compileObjectApplication functionCompiled argumentCompiled
      pure
        { sourceTyping := application.sourceTyping
          targetUse := application.targetUse
          targetType := application.resultType
          useTranslated := application.useTranslated
          typeTranslated := application.resultTranslated
          term := application.term
          typing := application.typing }
  | _, _, _, @DOTCapture.Acyclic.GeneralExpression.Term.HasType.letPlain _ _
      result bound rhs body rhsUse bodyUse bodyOuterUse boundPlain rhsTyping
      bodyTyping discharge =>
      match resultTranslated : Translation.translateTy? context result with
      | none => none
      | some resultTarget =>
          match bodyOuterTranslated :
              Translation.translateCapture? context bodyOuterUse with
          | none => none
          | some bodyOuterTarget => do
              let rhsCompiled ← compilePolarizedTerm? ready rhsTyping
              let bodyReady := ready.extendPlain boundPlain
                rhsCompiled.typeTranslated
              let bodyCompiled ← compilePolarizedTerm? bodyReady bodyTyping
              finishPlainLet? boundPlain discharge resultTranslated
                bodyOuterTranslated rhsCompiled bodyCompiled
  | _, _, _, @DOTCapture.Acyclic.GeneralExpression.Term.HasType.letObject _ _
      signature result rhs rhsUse body bodyUse bodyOuterUse rhsTyping
      bodyTyping discharge =>
      match signatureTranslated :
          Translation.translateObjectSig? context signature with
      | none => none
      | some bounds =>
          match resultTranslated : Translation.translateTy? context result with
          | none => none
          | some resultTarget =>
              match bodyOuterTranslated :
                  Translation.translateCapture? context bodyOuterUse with
              | none => none
              | some bodyOuterTarget => do
                  let rhsCompiled ← compilePolarizedTerm? ready rhsTyping
                  let bodyReady := ready.extendObject signature
                    signatureTranslated
                  let bodyCompiled ← compilePolarizedTerm? bodyReady bodyTyping
                  finishObjectLet? discharge signatureTranslated
                    resultTranslated bodyOuterTranslated rhsCompiled bodyCompiled
  | _, _, _, @DOTCapture.Acyclic.GeneralExpression.Term.HasType.use _ _
      term sourceUse targetUse type termTyping inclusion => do
      let inner ← compilePolarizedTerm? ready termTyping
      compileUse? inner inclusion

@[simp]
noncomputable def compileObjectFunction? {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope}
    (interface : CompiledObjectSignature context signature) :
    {function : Source.Term scope} → {use : Source.Capture scope} →
      {codomain : Source.Ty scope} → {closure : Source.Capture scope} →
      Source.ObjectFunction.HasType context function use signature codomain
        closure →
      Option (CompiledObjectFunction ready interface function use codomain
        closure)
  | _, _, _, _,
      @DOTCapture.Acyclic.GeneralExpression.ObjectFunction.HasType.returned _ _
        _ _ body bodyUse _ bodyTyping captures => do
      let bodyReady := ready.extendObject signature interface.translated
      let bodyCompiled ← compilePolarizedTerm? bodyReady bodyTyping
      let consumer ← finishObjectLambdaCompiled? ready interface bodyTyping
        captures bodyCompiled
      pure consumer.asFunction
  | _, _, _, _,
      @DOTCapture.Acyclic.GeneralExpression.ObjectFunction.HasType.letPlain _ _
        _ _ bound _ _ _ _ _ _ boundPlain rhsTyping bodyTyping discharge => do
      let rhsCompiled ← compilePolarizedTerm? ready rhsTyping
      let bodyReady := ready.extendPlain boundPlain rhsCompiled.typeTranslated
      let bodyBounds := interface.bounds.rename
        (Layout.extendRename context bound)
      have bodyTranslated :
          Translation.translateObjectSig? (context.extendTerm bound)
              signature.weaken =
            some bodyBounds := by
        rw [StaticTranslationMetatheory.translateObjectSig?_weaken,
          interface.translated]
        rfl
      let bodyInterface : CompiledObjectSignature
          (context.extendTerm bound) signature.weaken :=
        { bounds := bodyBounds
          translated := bodyTranslated }
      let bodyCompiled ← compileObjectFunction? bodyReady bodyInterface
        bodyTyping
      finishObjectFunctionLet? ready interface boundPlain rhsTyping bodyTyping
        discharge rhsCompiled bodyInterface rfl bodyCompiled
  | _, _, _, _,
      @DOTCapture.Acyclic.GeneralExpression.ObjectFunction.HasType.use _ _
        _ _ targetUse _ _ _ functionTyping inclusion => do
      let inner ← compileObjectFunction? ready interface functionTyping
      match targetTranslated :
          Translation.translateCapture? context targetUse with
      | none => none
      | some targetUse => do
          let compiled ← compileCaptureInclusion? ready.translated inclusion
            inner.useTranslated targetTranslated
          pure
            { sourceTyping := .use inner.sourceTyping inclusion
              targetUse := targetUse
              useTranslated := targetTranslated
              outerCapture := inner.outerCapture
              outerTranslated := inner.outerTranslated
              resultType := inner.resultType
              resultTranslated := inner.resultTranslated
              term := .use inner.term compiled.evidence
              typing := .use inner.typing compiled.typing }

@[simp]
noncomputable def compilePolarizedObjectArgument? {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope}
    (interface : CompiledObjectSignature context signature) :
    {argument : Source.Term scope} →
      Source.ObjectArgument.HasType context argument signature →
      Option (CompiledObjectArgument ready interface argument)
  | _, @DOTCapture.Acyclic.GeneralExpression.ObjectArgument.HasType.literal
      _ _ available _ typeWitness captureWitness payload payloadType
      typeLower typeUpper captureLower captureUpper payloadTyping payloadShape
      payloadCapture adaptation =>
      match availableTranslated :
          Translation.translateObjectSig? context available with
      | none => none
      | some availableBounds =>
          match typeWitnessTranslated :
              Translation.translateTy? context typeWitness with
          | none => none
          | some typeWitnessTarget =>
              match captureWitnessTranslated :
                  Translation.translateCapture? context captureWitness with
              | none => none
              | some captureWitnessTarget => do
                  let payloadCompiled ← compilePolarizedValue? ready payloadTyping
                  let availableTranslation :=
                    BoundsTranslation.ofTranslated availableTranslated
                  let expectedTranslation :=
                    BoundsTranslation.ofTranslated interface.translated
                  let availableTypeLower ←
                    compileTypeInclusion? ready.translated typeLower
                      availableTranslation.typeLower typeWitnessTranslated
                  let availableTypeUpper ←
                    compileTypeInclusion? ready.translated typeUpper
                      typeWitnessTranslated availableTranslation.typeUpper
                  let availableCaptureLower ←
                    compileCaptureInclusion? ready.translated captureLower
                      availableTranslation.captureLower
                      captureWitnessTranslated
                  let availableCaptureUpper ←
                    compileCaptureInclusion? ready.translated captureUpper
                      captureWitnessTranslated
                      availableTranslation.captureUpper
                  let expectedTypeLower ←
                    compileTypeInclusion? ready.translated adaptation.typeLower
                      expectedTranslation.typeLower
                      availableTranslation.typeLower
                  let expectedTypeUpper ←
                    compileTypeInclusion? ready.translated adaptation.typeUpper
                      availableTranslation.typeUpper
                      expectedTranslation.typeUpper
                  let expectedCaptureLower ←
                    compileCaptureInclusion? ready.translated
                      adaptation.captureLower expectedTranslation.captureLower
                      availableTranslation.captureLower
                  let expectedCaptureUpper ←
                    compileCaptureInclusion? ready.translated
                      adaptation.captureUpper availableTranslation.captureUpper
                      expectedTranslation.captureUpper
                  let payloadShapeCompiled ←
                    compileTypeInclusion? ready.translated payloadShape
                      (translateTy?_stripCapture
                        payloadCompiled.typeTranslated)
                      typeWitnessTranslated
                  let payloadCaptureCompiled ←
                    compileCaptureInclusion? ready.translated payloadCapture
                      (translateTy?_outerCapture
                        payloadCompiled.typeTranslated)
                      captureWitnessTranslated
                  let finalTypeLower : Target.Evidence (.inclusion .type)
                      (Layout.sig context) :=
                    .inclusionTrans expectedTypeLower.evidence
                      availableTypeLower.evidence
                  let finalTypeUpper : Target.Evidence (.inclusion .type)
                      (Layout.sig context) :=
                    .inclusionTrans availableTypeUpper.evidence
                      expectedTypeUpper.evidence
                  let finalCaptureLower :
                      Target.Evidence (.inclusion .capture)
                        (Layout.sig context) :=
                    .inclusionTrans expectedCaptureLower.evidence
                      availableCaptureLower.evidence
                  let finalCaptureUpper :
                      Target.Evidence (.inclusion .capture)
                        (Layout.sig context) :=
                    .inclusionTrans availableCaptureUpper.evidence
                      expectedCaptureUpper.evidence
                  have finalTypeLowerTyping : Target.Evidence.Proves
                      ready.target finalTypeLower
                      (.inclusion (.type interface.bounds.typeLower)
                        (.type typeWitnessTarget)) :=
                    .inclusionTrans expectedTypeLower.typing
                      availableTypeLower.typing
                  have finalTypeUpperTyping : Target.Evidence.Proves
                      ready.target finalTypeUpper
                      (.inclusion (.type typeWitnessTarget)
                        (.type interface.bounds.typeUpper)) :=
                    .inclusionTrans availableTypeUpper.typing
                      expectedTypeUpper.typing
                  have finalCaptureLowerTyping : Target.Evidence.Proves
                      ready.target finalCaptureLower
                      (.inclusion (.capture interface.bounds.captureLower)
                        (.capture captureWitnessTarget)) :=
                    .inclusionTrans expectedCaptureLower.typing
                      availableCaptureLower.typing
                  have finalCaptureUpperTyping : Target.Evidence.Proves
                      ready.target finalCaptureUpper
                      (.inclusion (.capture captureWitnessTarget)
                        (.capture interface.bounds.captureUpper)) :=
                    .inclusionTrans availableCaptureUpper.typing
                      expectedCaptureUpper.typing
                  let retagged := Object.retagPayload payloadCompiled.term
                    payloadCompiled.targetType typeWitnessTarget
                    captureWitnessTarget payloadCaptureCompiled.evidence
                    payloadShapeCompiled.evidence
                  have retaggedTyping : Target.Tm.HasType ready.target
                      retagged .empty
                      (.capturing captureWitnessTarget typeWitnessTarget) := by
                    unfold retagged ObjectEncoding.retagPayload
                    exact .adapt payloadCompiled.isValue payloadCompiled.typing
                      (ManySortedFC.Adapter.HasType.retagCapture
                        payloadCaptureCompiled.typing
                        payloadShapeCompiled.typing)
                  have satisfaction := satisfiesObjectTheory ready.target
                    interface.bounds typeWitnessTarget captureWitnessTarget
                    finalTypeLower finalTypeUpper finalCaptureLower
                    finalCaptureUpper finalTypeLowerTyping finalTypeUpperTyping
                    finalCaptureLowerTyping finalCaptureUpperTyping
                  let targetArgument : Negative.Argument ready.target
                      (Object.theory interface.bounds) Object.payloadType :=
                    { symbols := Object.symbolArguments typeWitnessTarget
                        captureWitnessTarget
                      evidence := Object.evidenceArguments finalTypeLower
                        finalTypeUpper finalCaptureLower finalCaptureUpper
                      satisfies := satisfaction
                      payload := retagged
                      payloadValue := .adapt payloadCompiled.isValue
                      payloadTyping := by
                        simpa [ObjectEncoding.payloadType,
                          ObjectEncoding.symbolArguments,
                          ManySortedFC.Ty.instantiateStatic,
                          ManySortedFC.Ty.substitute,
                          ManySortedFC.StaticSubst.ofSymbolArgs]
                          using retaggedTyping }
                  pure
                    { sourceTyping := .literal typeLower typeUpper captureLower
                        captureUpper payloadTyping payloadShape payloadCapture
                        adaptation
                      typeWitness := typeWitnessTarget
                      captureWitness := captureWitnessTarget
                      target := targetArgument
                      symbolsEquation := rfl
                      captureUpper := finalCaptureUpper
                      captureUpperTyping := finalCaptureUpperTyping }
  | _, @DOTCapture.Acyclic.GeneralExpression.ObjectArgument.HasType.stable
      _ _ name available _ canonical adaptation =>
      compileStableObjectArgument? ready interface canonical adaptation

end

theorem compilePolarizedValue?_var_result {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    (name : Source.Var scope)
    {compiled : CompiledValue ready (.var name) (context.lookup name)}
    (success : compilePolarizedValue? ready
      (DOTCapture.Acyclic.GeneralExpression.Value.HasType.var
        (context := context) (name := name)) =
        some compiled) :
    ∃ core : DOTCaptureToManySortedFC.Acyclic.ValueTranslation.CompiledValue
        ready (.var name) (context.lookup name),
      DOTCaptureToManySortedFC.Acyclic.ValueTranslation.compileValue? ready
          (DOTCapture.Acyclic.Value.HasType.var
            (context := context) (name := name)) = some core ∧
      compiled.term = core.term := by
  unfold compilePolarizedValue? at success
  exact compileValue?_var_result ready name success

theorem compilePolarizedValue?_lam_result {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {domain codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)} {closure : Source.Capture scope}
    (domainPlain : domain.IsPlain)
    (bodyTyping : Source.Term.HasType (context.extendTerm domain) body
      bodyUse codomain.weaken)
    (captures : Source.CaptureIncludes (context.extendTerm domain) bodyUse
      (.union closure.weaken (.singleton (.var .here))))
    {compiled : CompiledValue ready (.lam domain codomain body)
      (.capturing closure (.arr domain codomain))}
    (success : compilePolarizedValue? ready
      (.lam domainPlain bodyTyping captures) = some compiled) :
    ∃ (domainTarget codomainTarget : Target.Ty (Layout.sig context))
        (closureTarget : Target.Capture (Layout.sig context))
        (domainTranslated :
          Translation.translateTy? context domain = some domainTarget)
        (codomainTranslated :
          Translation.translateTy? context codomain = some codomainTarget)
        (closureTranslated :
          Translation.translateCapture? context closure = some closureTarget)
        (bodyCompiled : CompiledTerm
          (ready.extendPlain domainPlain domainTranslated) body bodyUse
            codomain.weaken),
      compilePolarizedTerm?
          (ready.extendPlain domainPlain domainTranslated) bodyTyping =
        some bodyCompiled ∧
      finishLambda? domainPlain captures domainTranslated codomainTranslated
          closureTranslated bodyCompiled = some compiled := by
  unfold compilePolarizedValue? at success
  split at success <;> try contradiction
  rename_i domainTarget domainTranslated
  split at success <;> try contradiction
  rename_i codomainTarget codomainTranslated
  split at success <;> try contradiction
  rename_i closureTarget closureTranslated
  change (do
    let bodyCompiled ← compilePolarizedTerm?
      (ready.extendPlain domainPlain domainTranslated) bodyTyping
    finishLambda? domainPlain captures domainTranslated codomainTranslated
      closureTranslated bodyCompiled) = some compiled at success
  generalize bodyEquation :
    compilePolarizedTerm? (ready.extendPlain domainPlain domainTranslated)
      bodyTyping = bodyResult at success ⊢
  cases bodyResult with
  | none => simp at success
  | some bodyCompiled =>
      exact ⟨domainTarget, codomainTarget, closureTarget, domainTranslated,
        codomainTranslated, closureTranslated, bodyCompiled, bodyEquation,
        success⟩

theorem compilePolarizedTerm?_letPlain_result {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {result bound : Source.Ty scope} {rhs : Source.Term scope}
    {body : Source.Term (scope + 1)} {rhsUse : Source.Capture scope}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (boundPlain : bound.IsPlain)
    (rhsTyping : Source.Term.HasType context rhs rhsUse bound)
    (bodyTyping : Source.Term.HasType (context.extendTerm bound) body
      bodyUse result.weaken)
    (discharge : Source.CaptureIncludes (context.extendTerm bound) bodyUse
      bodyOuterUse.weaken)
    {compiled : CompiledTerm ready (.let' result rhs body)
      (.union rhsUse bodyOuterUse) result}
    (success : compilePolarizedTerm? ready
      (.letPlain boundPlain rhsTyping bodyTyping discharge) = some compiled) :
    ∃ (resultTarget : Target.Ty (Layout.sig context))
        (bodyOuterTarget : Target.Capture (Layout.sig context))
        (resultTranslated :
          Translation.translateTy? context result = some resultTarget)
        (bodyOuterTranslated :
          Translation.translateCapture? context bodyOuterUse =
            some bodyOuterTarget)
        (rhsCompiled : CompiledTerm ready rhs rhsUse bound)
        (bodyCompiled : CompiledTerm
          (ready.extendPlain boundPlain rhsCompiled.typeTranslated) body
            bodyUse result.weaken),
      compilePolarizedTerm? ready rhsTyping = some rhsCompiled ∧
      compilePolarizedTerm?
          (ready.extendPlain boundPlain rhsCompiled.typeTranslated)
          bodyTyping = some bodyCompiled ∧
      finishPlainLet? boundPlain discharge resultTranslated
          bodyOuterTranslated rhsCompiled bodyCompiled = some compiled := by
  unfold compilePolarizedTerm? at success
  split at success <;> try contradiction
  rename_i resultTarget resultTranslated
  split at success <;> try contradiction
  rename_i bodyOuterTarget bodyOuterTranslated
  change (do
    let rhsCompiled ← compilePolarizedTerm? ready rhsTyping
    let bodyCompiled ← compilePolarizedTerm?
      (ready.extendPlain boundPlain rhsCompiled.typeTranslated) bodyTyping
    finishPlainLet? boundPlain discharge resultTranslated
      bodyOuterTranslated rhsCompiled bodyCompiled) = some compiled at success
  generalize rhsEquation :
    compilePolarizedTerm? ready rhsTyping = rhsResult at success
  cases rhsResult with
  | none => simp at success
  | some rhsCompiled =>
      change (do
        let bodyCompiled ← compilePolarizedTerm?
          (ready.extendPlain boundPlain rhsCompiled.typeTranslated) bodyTyping
        finishPlainLet? boundPlain discharge resultTranslated
          bodyOuterTranslated rhsCompiled bodyCompiled) = some compiled
        at success
      generalize bodyEquation :
        compilePolarizedTerm?
            (ready.extendPlain boundPlain rhsCompiled.typeTranslated)
            bodyTyping = bodyResult at success
      cases bodyResult with
      | none => simp at success
      | some bodyCompiled =>
          exact ⟨resultTarget, bodyOuterTarget, resultTranslated,
            bodyOuterTranslated, rhsCompiled, bodyCompiled, rfl,
            bodyEquation, success⟩

theorem compilePolarizedTerm?_letObject_result {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope} {result : Source.Ty scope}
    {rhs : Source.Term scope} {rhsUse : Source.Capture scope}
    {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (rhsTyping : Source.Term.HasType context rhs rhsUse
      (.capturing signature.captureUpper (.object signature)))
    (bodyTyping : Source.Term.HasType
      (context.extendTerm
        (.capturing signature.captureUpper (.object signature)))
      body bodyUse result.weaken)
    (discharge : Source.CaptureIncludes
      (context.extendTerm
        (.capturing signature.captureUpper (.object signature))) bodyUse
      (.union bodyOuterUse.weaken (.singleton (.var .here))))
    {compiled : CompiledTerm ready (.let' result rhs body)
      (DOTCapture.Acyclic.GeneralExpression.Capture.seq rhsUse
        (.union signature.captureUpper bodyOuterUse)) result}
    (success : compilePolarizedTerm? ready
      (.letObject rhsTyping bodyTyping discharge) = some compiled) :
    ∃ (bounds : Object.Bounds (Layout.sig context))
        (resultTarget : Target.Ty (Layout.sig context))
        (bodyOuterTarget : Target.Capture (Layout.sig context))
        (signatureTranslated :
          Translation.translateObjectSig? context signature = some bounds)
        (resultTranslated :
          Translation.translateTy? context result = some resultTarget)
        (bodyOuterTranslated :
          Translation.translateCapture? context bodyOuterUse =
            some bodyOuterTarget)
        (rhsCompiled : CompiledTerm ready rhs rhsUse
          (.capturing signature.captureUpper (.object signature)))
        (bodyCompiled : CompiledTerm
          (ready.extendObject signature signatureTranslated) body bodyUse
            result.weaken),
      compilePolarizedTerm? ready rhsTyping = some rhsCompiled ∧
      compilePolarizedTerm? (ready.extendObject signature signatureTranslated)
          bodyTyping = some bodyCompiled ∧
      finishObjectLet? discharge signatureTranslated resultTranslated
          bodyOuterTranslated rhsCompiled bodyCompiled = some compiled := by
  unfold compilePolarizedTerm? at success
  split at success <;> try contradiction
  rename_i bounds signatureTranslated
  split at success <;> try contradiction
  rename_i resultTarget resultTranslated
  split at success <;> try contradiction
  rename_i bodyOuterTarget bodyOuterTranslated
  change (do
    let rhsCompiled ← compilePolarizedTerm? ready rhsTyping
    let bodyCompiled ← compilePolarizedTerm?
      (ready.extendObject signature signatureTranslated) bodyTyping
    finishObjectLet? discharge signatureTranslated resultTranslated
      bodyOuterTranslated rhsCompiled bodyCompiled) = some compiled at success
  generalize rhsEquation :
    compilePolarizedTerm? ready rhsTyping = rhsResult at success
  cases rhsResult with
  | none => simp at success
  | some rhsCompiled =>
      change (do
        let bodyCompiled ← compilePolarizedTerm?
          (ready.extendObject signature signatureTranslated) bodyTyping
        finishObjectLet? discharge signatureTranslated resultTranslated
          bodyOuterTranslated rhsCompiled bodyCompiled) = some compiled
        at success
      generalize bodyEquation :
        compilePolarizedTerm? (ready.extendObject signature signatureTranslated)
          bodyTyping = bodyResult at success
      cases bodyResult with
      | none => simp at success
      | some bodyCompiled =>
          exact ⟨bounds, resultTarget, bodyOuterTarget,
            signatureTranslated, resultTranslated, bodyOuterTranslated,
            rhsCompiled, bodyCompiled, rfl, bodyEquation, success⟩

theorem compilePolarizedTerm?_objectApp_result {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {function argument : Source.Term scope}
    {functionUse closure : Source.Capture scope}
    {codomain : Source.Ty scope} {signature : Source.ObjectSig scope}
    (functionTyping : Source.ObjectFunction.HasType context function
      functionUse signature codomain closure)
    (argumentTyping : Source.ObjectArgument.HasType context argument signature)
    {compiled : CompiledTerm ready (.app function argument)
      (DOTCapture.Acyclic.GeneralExpression.Capture.seq functionUse
        (.union closure signature.captureUpper)) codomain}
    (success : compilePolarizedTerm? ready
      (.objectApp functionTyping argumentTyping) = some compiled) :
    ∃ (interface : CompiledObjectSignature context signature)
        (functionCompiled : CompiledObjectFunction ready interface function
          functionUse codomain closure)
        (argumentCompiled : CompiledObjectArgument ready interface argument),
      compileObjectSignature? context signature = some interface ∧
      compileObjectFunction? ready interface functionTyping =
        some functionCompiled ∧
      compilePolarizedObjectArgument? ready interface argumentTyping =
        some argumentCompiled ∧
      compiled.term =
        (compileObjectApplication functionCompiled argumentCompiled).term := by
  unfold compilePolarizedTerm? at success
  generalize interfaceEquation :
    compileObjectSignature? context signature = interfaceResult at success
  cases interfaceResult with
  | none => simp at success
  | some interface =>
      simp only [Bind.bind, Option.bind] at success
      generalize functionEquation :
        compileObjectFunction? ready interface functionTyping = functionResult
          at success
      cases functionResult with
      | none => simp at success
      | some functionCompiled =>
          generalize argumentEquation :
            compilePolarizedObjectArgument? ready interface argumentTyping =
              argumentResult at success
          cases argumentResult with
          | none => simp at success
          | some argumentCompiled =>
              cases success
              exact ⟨interface, functionCompiled, argumentCompiled,
                rfl, functionEquation, argumentEquation, rfl⟩

theorem compileObjectFunction?_returned_result {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope}
    (interface : CompiledObjectSignature context signature)
    {codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)} {closure : Source.Capture scope}
    (bodyTyping : Source.Term.HasType
      (context.extendTerm signature.formedType) body bodyUse codomain.weaken)
    (captures : Source.CaptureIncludes
      (context.extendTerm signature.formedType) bodyUse
      (.union closure.weaken (.singleton (.var .here))))
    {compiled : CompiledObjectFunction ready interface
      (.ret (.lam signature.formedType codomain body)) .empty codomain closure}
    (success : compileObjectFunction? ready interface
      (.returned bodyTyping captures) = some compiled) :
    ∃ (bodyCompiled : CompiledTerm
          (ready.extendObject signature interface.translated) body bodyUse
            codomain.weaken)
        (consumer : CompiledObjectConsumer ready interface codomain body
          bodyUse closure),
      compilePolarizedTerm? (ready.extendObject signature interface.translated)
          bodyTyping = some bodyCompiled ∧
      compiled.term = consumer.term ∧
      consumer.bodyCompiled.term = bodyCompiled.term := by
  unfold compileObjectFunction? at success
  change (do
    let bodyCompiled ← compilePolarizedTerm?
      (ready.extendObject signature interface.translated) bodyTyping
    let consumer ← finishObjectLambdaCompiled? ready interface bodyTyping
      captures bodyCompiled
    pure consumer.asFunction) = some compiled at success
  generalize bodyEquation :
    compilePolarizedTerm? (ready.extendObject signature interface.translated)
      bodyTyping = bodyResult at success
  cases bodyResult with
  | none => simp at success
  | some bodyCompiled =>
      change (do
        let consumer ← finishObjectLambdaCompiled? ready interface
          bodyTyping captures bodyCompiled
        pure consumer.asFunction) = some compiled at success
      generalize consumerEquation :
        finishObjectLambdaCompiled? ready interface bodyTyping captures
          bodyCompiled = consumerResult at success
      cases consumerResult with
      | none => simp at success
      | some consumer =>
          cases success
          have bodyTermEquation :
              consumer.bodyCompiled.term = bodyCompiled.term := by
            unfold finishObjectLambdaCompiled? at consumerEquation
            split at consumerEquation <;> try contradiction
            split at consumerEquation <;> try contradiction
            simp only [Bind.bind, Option.bind] at consumerEquation
            split at consumerEquation <;> try contradiction
            cases consumerEquation
            rfl
          exact ⟨bodyCompiled, consumer, rfl, rfl,
            bodyTermEquation⟩

set_option maxHeartbeats 8000000 in
theorem compileObjectFunction?_letPlain_result {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope}
    (interface : CompiledObjectSignature context signature)
    {codomain bound : Source.Ty scope} {closure : Source.Capture scope}
    {rhs : Source.Term scope} {body : Source.Term (scope + 1)}
    {rhsUse : Source.Capture scope} {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (boundPlain : bound.IsPlain)
    (rhsTyping : Source.Term.HasType context rhs rhsUse bound)
    (bodyTyping : Source.ObjectFunction.HasType (context.extendTerm bound)
      body bodyUse signature.weaken codomain.weaken closure.weaken)
    (discharge : Source.CaptureIncludes (context.extendTerm bound) bodyUse
      bodyOuterUse.weaken)
    {compiled : CompiledObjectFunction ready interface
      (.let' (.capturing closure (.arr signature.formedType codomain)) rhs body)
      (.union rhsUse bodyOuterUse) codomain closure}
    (success : compileObjectFunction? ready interface
      (.letPlain boundPlain rhsTyping bodyTyping discharge) = some compiled) :
    ∃ (rhsCompiled : CompiledTerm ready rhs rhsUse bound)
        (bodyInterface : CompiledObjectSignature (context.extendTerm bound)
          signature.weaken)
        (bodyBounds : bodyInterface.bounds = interface.bounds.rename
          (Layout.extendRename context bound))
        (bodyCompiled : CompiledObjectFunction
          (ready.extendPlain boundPlain rhsCompiled.typeTranslated)
          bodyInterface body bodyUse codomain.weaken closure.weaken),
      compilePolarizedTerm? ready rhsTyping = some rhsCompiled ∧
      compileObjectFunction?
          (ready.extendPlain boundPlain rhsCompiled.typeTranslated)
          bodyInterface bodyTyping = some bodyCompiled ∧
      finishObjectFunctionLet? ready interface boundPlain rhsTyping bodyTyping
          discharge rhsCompiled bodyInterface bodyBounds bodyCompiled =
        some compiled := by
  unfold compileObjectFunction? at success
  generalize rhsEquation :
    compilePolarizedTerm? ready rhsTyping = rhsResult at success
  cases rhsResult with
  | none => simp at success
  | some rhsCompiled =>
      let bodyBounds := interface.bounds.rename
        (Layout.extendRename context bound)
      have bodyTranslated :
          Translation.translateObjectSig? (context.extendTerm bound)
              signature.weaken = some bodyBounds := by
        rw [StaticTranslationMetatheory.translateObjectSig?_weaken,
          interface.translated]
        rfl
      let bodyInterface : CompiledObjectSignature
          (context.extendTerm bound) signature.weaken :=
        { bounds := bodyBounds, translated := bodyTranslated }
      change (do
        let bodyCompiled ← compileObjectFunction?
          (ready.extendPlain boundPlain rhsCompiled.typeTranslated)
          bodyInterface bodyTyping
        finishObjectFunctionLet? ready interface boundPlain rhsTyping
          bodyTyping discharge rhsCompiled bodyInterface rfl bodyCompiled) =
        some compiled at success
      generalize bodyEquation :
        compileObjectFunction?
            (ready.extendPlain boundPlain rhsCompiled.typeTranslated)
            bodyInterface bodyTyping = bodyResult at success
      cases bodyResult with
      | none => simp at success
      | some bodyCompiled =>
          exact ⟨rhsCompiled, bodyInterface, rfl, bodyCompiled, rfl,
            bodyEquation, success⟩

theorem compilePolarizedValue?_adapt_term {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {value : Source.Value scope} {source target : Source.Ty scope}
    (valueTyping : Source.Value.HasType context value source)
    (inclusion : Source.TypeIncludes context source target)
    {compiled : CompiledValue ready value target}
    (success : compilePolarizedValue? ready (.adapt valueTyping inclusion) =
      some compiled) :
    ∃ inner evidence,
      compilePolarizedValue? ready valueTyping = some inner ∧
      compiled.term = .adapt inner.term (.cast evidence) := by
  unfold compilePolarizedValue? at success
  split at success <;> try contradiction
  rename_i targetType targetTranslated
  generalize innerEquation :
    compilePolarizedValue? ready valueTyping = innerResult at success
  cases innerResult with
  | none => simp at success
  | some inner =>
      change compileAdapt? inner inclusion targetTranslated = some compiled
        at success
      unfold compileAdapt? at success
      generalize evidenceEquation :
        compileTypeInclusion? ready.translated inclusion inner.typeTranslated
          targetTranslated = evidenceResult at success
      cases evidenceResult with
      | none => simp at success
      | some evidence =>
          cases success
          exact ⟨inner, evidence.evidence, rfl, rfl⟩

theorem compilePolarizedTerm?_use_term {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {term : Source.Term scope} {sourceUse targetUse : Source.Capture scope}
    {type : Source.Ty scope}
    (termTyping : Source.Term.HasType context term sourceUse type)
    (inclusion : Source.CaptureIncludes context sourceUse targetUse)
    {compiled : CompiledTerm ready term targetUse type}
    (success : compilePolarizedTerm? ready (.use termTyping inclusion) =
      some compiled) :
    ∃ inner evidence,
      compilePolarizedTerm? ready termTyping = some inner ∧
      compiled.term = .use inner.term evidence := by
  unfold compilePolarizedTerm? at success
  generalize innerEquation :
    compilePolarizedTerm? ready termTyping = innerResult at success
  cases innerResult with
  | none => simp at success
  | some inner =>
      change compileUse? inner inclusion = some compiled at success
      unfold compileUse? at success
      split at success <;> try contradiction
      rename_i targetTarget targetTranslated
      generalize evidenceEquation :
        compileCaptureInclusion? ready.translated inclusion
          inner.useTranslated targetTranslated = evidenceResult at success
      cases evidenceResult with
      | none => simp at success
      | some evidence =>
          cases success
          exact ⟨inner, evidence.evidence, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- A successful negative-function let contributes exactly one runtime let;
all static interface data and capture evidence erase. -/
theorem finishObjectFunctionLet?_erase {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope}
    (interface : CompiledObjectSignature context signature)
    {codomain bound : Source.Ty scope} {closure : Source.Capture scope}
    {rhs : Source.Term scope} {body : Source.Term (scope + 1)}
    {rhsUse : Source.Capture scope} {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (boundPlain : bound.IsPlain)
    (rhsTyping : Source.Term.HasType context rhs rhsUse bound)
    (bodyTyping : Source.ObjectFunction.HasType (context.extendTerm bound)
      body bodyUse signature.weaken codomain.weaken closure.weaken)
    (discharge : Source.CaptureIncludes (context.extendTerm bound) bodyUse
      bodyOuterUse.weaken)
    (rhsCompiled : CompiledTerm ready rhs rhsUse bound)
    (bodyInterface : CompiledObjectSignature (context.extendTerm bound)
      signature.weaken)
    (bodyBounds : bodyInterface.bounds = interface.bounds.rename
      (Layout.extendRename context bound))
    (bodyCompiled : CompiledObjectFunction
      (ready.extendPlain boundPlain rhsCompiled.typeTranslated) bodyInterface
      body bodyUse codomain.weaken closure.weaken)
    {compiled : CompiledObjectFunction ready interface
      (.let' (.capturing closure (.arr signature.formedType codomain)) rhs body)
      (.union rhsUse bodyOuterUse) codomain closure}
    (success : finishObjectFunctionLet? ready interface boundPlain rhsTyping
      bodyTyping discharge rhsCompiled bodyInterface bodyBounds bodyCompiled =
        some compiled) :
    ∃ erasedBody : ManySortedFC.Runtime.Tm
        ((Layout.sig context).termCount + 1),
      HEq bodyCompiled.term.erase erasedBody ∧
      compiled.term.erase = .let' rhsCompiled.term.erase erasedBody := by
  cases bound with
  | object signature =>
      simp [DOTCapture.Acyclic.Ty.IsPlain,
        DOTCapture.Acyclic.Ty.objectSignature?,
        DOTCapture.Acyclic.Ty.stripCapture] at boundPlain
  | capturing retained shape =>
      cases shape with
      | object signature =>
          simp [DOTCapture.Acyclic.Ty.IsPlain,
            DOTCapture.Acyclic.Ty.objectSignature?,
            DOTCapture.Acyclic.Ty.stripCapture] at boundPlain
      | top | bot | one | ref | arr | capturing =>
          unfold finishObjectFunctionLet? at success
          split at success <;> try contradiction
          split at success <;> try contradiction
          split at success <;> try contradiction
          simp only [Bind.bind, Option.bind] at success
          split at success <;> try contradiction
          cases success
          exact ⟨erasePlainBody boundPlain bodyCompiled.term,
            erasePlainBody_heq boundPlain bodyCompiled.term, by
              rw [ManySortedFC.Tm.erase_let]
              congr 1⟩
  | top | bot | one | ref | arr =>
      unfold finishObjectFunctionLet? at success
      split at success <;> try contradiction
      split at success <;> try contradiction
      split at success <;> try contradiction
      simp only [Bind.bind, Option.bind] at success
      split at success <;> try contradiction
      cases success
      exact ⟨erasePlainBody boundPlain bodyCompiled.term,
        erasePlainBody_heq boundPlain bodyCompiled.term, by
          rw [ManySortedFC.Tm.erase_let]
          congr 1⟩

end DOTCaptureToManySortedFC.Acyclic.GeneralExpression.Compiler
