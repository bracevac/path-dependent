import Coercions.Translation.ManySorted.Acyclic.RuntimeContext
import Coercions.Translation.ManySorted.Acyclic.EvidenceTranslation
import Coercions.Translation.ManySorted.BinderOnly.StaticInstantiation

/-!
# Certified translation of acyclic DOT values

Executable source contexts contain only ordinary bindings and canonically
formed object bindings.  Ordinary variables translate to their target term
coordinate, with an explicit capture retag when their stored type is
capturing.  An object variable denotes an already-open payload in the target
context, so returning it as a first-class value repackages that same payload
with the two shared witnesses and exactly four stored assumptions.
-/

namespace DOTCaptureToManySortedFC.Acyclic.ValueTranslation

namespace Source

export DOTCapture.Acyclic
  (Scope StaticSort Var Path Capture Ty ObjectSig StaticExpr Ctx Value Term
    TypeIncludes CaptureIncludes)

namespace Value
export DOTCapture.Acyclic.Value (HasType)
end Value

namespace ObjectSig
export DOTCapture.Acyclic.ObjectSig
  (typeLower typeUpper captureLower captureUpper)
end ObjectSig

namespace Ty
export DOTCapture.Acyclic.Ty (stripCapture outerCapture)
end Ty

namespace Ctx
export DOTCapture.Acyclic.Ctx (nil)
end Ctx

end Source

namespace Target

export ManySortedFC
  (StaticExpr Capture Ty Binding Ctx Evidence Adapter Theory Tm)

namespace Tm
export ManySortedFC.Tm (HasType IsValue synth)
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
  (Ready PlainVariable ObjectVariable Variable resolveVariable nil)

end Runtime

namespace Object

export ObjectEncoding
  (Bounds symbols relations theory payloadType existentialShape objectType
    symbolWeakening alphaSymbol chiSymbol symbolArguments evidenceArguments
    retagPayload pack payloadTypeOpened exactBounds)

end Object

/-! ## Proof-carrying result -/

/-- A target value with the exact translation of its source result type. -/
structure CompiledValue {scope : Source.Scope} {context : Source.Ctx scope}
    (ready : Runtime.Ready context) (value : Source.Value scope)
    (type : Source.Ty scope) where
  targetType : Target.Ty (Layout.sig context)
  typeTranslated :
    Translation.translateTy? context type = some targetType
  term : Target.Tm (Layout.sig context)
  isValue : Target.Tm.IsValue term
  typing : Target.Tm.HasType ready.target term .empty targetType

/-! ## Translation projections and exact evidence alignment -/

private structure BoundsTranslation {scope : Source.Scope}
    {context : Source.Ctx scope} (signature : Source.ObjectSig scope)
    (bounds : Object.Bounds (Layout.sig context)) where
  typeLower : Translation.translateTy? context signature.typeLower =
    some bounds.typeLower
  typeUpper : Translation.translateTy? context signature.typeUpper =
    some bounds.typeUpper
  captureLower :
    Translation.translateCapture? context signature.captureLower =
      some bounds.captureLower
  captureUpper :
    Translation.translateCapture? context signature.captureUpper =
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
      generalize typeLowerEquation :
        Translation.translateTy? context typeLower = typeLowerResult
          at translated
      cases typeLowerResult with
      | none => simp at translated
      | some translatedTypeLower =>
          generalize typeUpperEquation :
            Translation.translateTy? context typeUpper = typeUpperResult
              at translated
          cases typeUpperResult with
          | none => simp at translated
          | some translatedTypeUpper =>
              generalize captureLowerEquation :
                Translation.translateCapture? context captureLower =
                  captureLowerResult at translated
              cases captureLowerResult with
              | none => simp at translated
              | some translatedCaptureLower =>
                  generalize captureUpperEquation :
                    Translation.translateCapture? context captureUpper =
                      captureUpperResult at translated
                  cases captureUpperResult with
                  | none => simp at translated
                  | some translatedCaptureUpper =>
                      simp at translated
                      subst bounds
                      exact
                        { typeLower := typeLowerEquation
                          typeUpper := typeUpperEquation
                          captureLower := captureLowerEquation
                          captureUpper := captureUpperEquation }

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
    (translated :
      Translation.translateCapture? context source = some target) :
    Translation.translateExpr? context (.capture source) =
      some (.capture target) := by
  simp [Translation.translateExpr?, translated]

/-- A compiled inclusion whose target endpoints have been fixed by the value
compiler's already chosen translations. -/
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
    {sort : Source.StaticSort}
    {source target : Source.StaticExpr sort scope}
    (compiled : EvidenceTranslation.CompiledInclusion translatedContext
      source target)
    {sourceTarget targetTarget :
      Target.StaticExpr (Layout.translateSort sort) (Layout.sig context)}
    (sourceTranslated :
      Translation.translateExpr? context source = some sourceTarget)
    (targetTranslated :
      Translation.translateExpr? context target = some targetTarget) :
    ExactInclusion translatedContext sourceTarget targetTarget := by
  have sourceEquality := StaticTranslation.TranslatesExpr.functional
    compiled.sourceTranslated sourceTranslated
  have targetEquality := StaticTranslation.TranslatesExpr.functional
    compiled.targetTranslated targetTranslated
  cases sourceEquality
  cases targetEquality
  exact ⟨compiled.evidence, compiled.typing⟩

private noncomputable def compileTypeInclusion? {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translatedContext : ExposureTranslation.TranslatedContext context)
    {source target : Source.Ty scope}
    (derivation : Source.TypeIncludes context source target)
    {sourceTarget targetTarget : Target.Ty (Layout.sig context)}
    (sourceTranslated :
      Translation.translateTy? context source = some sourceTarget)
    (targetTranslated :
      Translation.translateTy? context target = some targetTarget) :
    Option (ExactInclusion (sort := .type) translatedContext
      (.type sourceTarget) (.type targetTarget)) := do
  let compiled ← EvidenceTranslation.compileIncludes?
    translatedContext derivation
  pure (ExactInclusion.align compiled
    (translatedTypeExpression sourceTranslated)
    (translatedTypeExpression targetTranslated))

private noncomputable def compileCaptureInclusion? {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translatedContext : ExposureTranslation.TranslatedContext context)
    {source target : Source.Capture scope}
    (derivation : Source.CaptureIncludes context source target)
    {sourceTarget targetTarget : Target.Capture (Layout.sig context)}
    (sourceTranslated :
      Translation.translateCapture? context source = some sourceTarget)
    (targetTranslated :
      Translation.translateCapture? context target = some targetTarget) :
    Option (ExactInclusion (sort := .capture) translatedContext
      (.capture sourceTarget) (.capture targetTarget)) := do
  let compiled ← EvidenceTranslation.compileIncludes?
    translatedContext derivation
  pure (ExactInclusion.align compiled
    (translatedCaptureExpression sourceTranslated)
    (translatedCaptureExpression targetTranslated))

/-! The capture and shape projections used by object-payload premises are
determined by a successful whole-type translation. -/

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
  | capturing captures shape =>
      unfold StaticTranslation.translateTy? at translated
      generalize captureEquation :
        Translation.translateCapture? context captures = captureResult
          at translated
      cases captureResult with
      | none => contradiction
      | some captureTarget =>
          generalize shapeEquation :
            Translation.translateTy? context shape = shapeResult
              at translated
          cases shapeResult with
          | none => contradiction
          | some shapeTarget =>
              cases translated
              exact captureEquation
  | object signature =>
      unfold StaticTranslation.translateTy? at translated
      generalize signatureEquation :
        Translation.translateObjectSig? context signature = signatureResult
          at translated
      cases signatureResult with
      | none => contradiction
      | some bounds =>
          cases translated
          rfl

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
  | capturing captures shape =>
      unfold StaticTranslation.translateTy? at translated
      generalize captureEquation :
        Translation.translateCapture? context captures = captureResult
          at translated
      cases captureResult with
      | none => contradiction
      | some captureTarget =>
          generalize shapeEquation :
            Translation.translateTy? context shape = shapeResult
              at translated
          cases shapeResult with
          | none => contradiction
          | some shapeTarget =>
              cases translated
              exact shapeEquation
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

/-! ## Exact four-assumption object models -/

private def symbolInstantiationCancels {scope : ManySortedFC.Sig}
    (typeWitness : Target.Ty scope)
    (captureWitness : Target.Capture scope) :
    BinderOnly.TargetStaticInstantiation.Cancels
      (ObjectEncoding.symbolWeakening (scope := scope))
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
    (expression.rename ObjectEncoding.symbolWeakening).substitute
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
        ObjectEncoding.symbolWeakening)
      (ObjectEncoding.alphaSymbol (scope := scope))).instantiateSymbols
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
      (ObjectEncoding.alphaSymbol (scope := scope))
      (((.type bounds.typeUpper : Target.StaticExpr .type scope)).rename
        ObjectEncoding.symbolWeakening)).instantiateSymbols
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
        ObjectEncoding.symbolWeakening)
      (ObjectEncoding.chiSymbol (scope := scope))).instantiateSymbols
        (Object.symbolArguments typeWitness captureWitness) =
      .inclusion (.capture bounds.captureLower)
        (.capture captureWitness) := by
  unfold ManySortedFC.Proposition.instantiateSymbols
    ManySortedFC.Proposition.substitute
  congr 1
  exact ambientExpression_instantiates
    (.capture bounds.captureLower) typeWitness captureWitness

private theorem captureUpperInstance {scope : ManySortedFC.Sig}
    (bounds : Object.Bounds scope) (typeWitness : Target.Ty scope)
    (captureWitness : Target.Capture scope) :
    (ManySortedFC.Proposition.inclusion
      (ObjectEncoding.chiSymbol (scope := scope))
      (((.capture bounds.captureUpper : Target.StaticExpr .capture scope)).rename
        ObjectEncoding.symbolWeakening)).instantiateSymbols
        (Object.symbolArguments typeWitness captureWitness) =
      .inclusion (.capture captureWitness)
        (.capture bounds.captureUpper) := by
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
          ObjectEncoding.symbolWeakening)
        ObjectEncoding.alphaSymbol).instantiateSymbols
          (Object.symbolArguments typeWitness captureWitness))
    rw [typeLowerInstance]
    exact typeLowerTyping
  · change Target.Evidence.Proves context typeUpper
      ((ManySortedFC.Proposition.inclusion ObjectEncoding.alphaSymbol
        (((.type bounds.typeUpper : Target.StaticExpr .type scope)).rename
          ObjectEncoding.symbolWeakening)).instantiateSymbols
          (Object.symbolArguments typeWitness captureWitness))
    rw [typeUpperInstance]
    exact typeUpperTyping
  · change Target.Evidence.Proves context captureLower
      ((ManySortedFC.Proposition.inclusion
        (((.capture bounds.captureLower : Target.StaticExpr .capture scope)).rename
          ObjectEncoding.symbolWeakening)
        ObjectEncoding.chiSymbol).instantiateSymbols
          (Object.symbolArguments typeWitness captureWitness))
    rw [captureLowerInstance]
    exact captureLowerTyping
  · change Target.Evidence.Proves context captureUpper
      ((ManySortedFC.Proposition.inclusion ObjectEncoding.chiSymbol
        (((.capture bounds.captureUpper : Target.StaticExpr .capture scope)).rename
          ObjectEncoding.symbolWeakening)).instantiateSymbols
          (Object.symbolArguments typeWitness captureWitness))
    rw [captureUpperInstance]
    exact captureUpperTyping

/-! ## Variable compilation -/

private def rawVariableTyping {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {name : Source.Var scope}
    (facts : Runtime.PlainVariable ready.translated name) :
    Target.Tm.HasType ready.target
      (.var (Layout.termVar context name)) .empty
      (ManySortedFC.Ty.precise
        (Layout.termVar context name) facts.targetType) := by
  have typing := ManySortedFC.Tm.HasType.var
    (context := ready.target) (Layout.termVar context name)
  have targetLookup := facts.targetLookup
  change ready.target.lookup (Layout.termVar context name) = _
    at targetLookup
  rw [targetLookup] at typing
  exact typing

private noncomputable def compilePlainVariable {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {name : Source.Var scope}
    (facts : Runtime.PlainVariable ready.translated name) :
    CompiledValue ready (.var name) (context.lookup name) := by
  let coordinate := Layout.termVar context name
  have rawTyping := rawVariableTyping facts
  cases targetEquation : facts.targetType with
  | top =>
      exact
        { targetType := .top
          typeTranslated := by simpa [targetEquation] using facts.typeTranslated
          term := .var coordinate
          isValue := .var
          typing := by simpa [coordinate, targetEquation] using rawTyping }
  | bot =>
      exact
        { targetType := .bot
          typeTranslated := by simpa [targetEquation] using facts.typeTranslated
          term := .var coordinate
          isValue := .var
          typing := by simpa [coordinate, targetEquation] using rawTyping }
  | one =>
      exact
        { targetType := .one
          typeTranslated := by simpa [targetEquation] using facts.typeTranslated
          term := .var coordinate
          isValue := .var
          typing := by simpa [coordinate, targetEquation] using rawTyping }
  | tvar name =>
      exact
        { targetType := .tvar name
          typeTranslated := by simpa [targetEquation] using facts.typeTranslated
          term := .var coordinate
          isValue := .var
          typing := by simpa [coordinate, targetEquation] using rawTyping }
  | capturing captures shape =>
      let sourceType : Target.Ty (Layout.sig context) :=
        .capturing (.singleton coordinate) shape
      let adapter : Target.Adapter (Layout.sig context) :=
        .retagCapture sourceType captures shape
          (.captureVariable coordinate)
          (.inclusionRefl (.type shape))
      have capturesTyping : Target.Evidence.Proves ready.target
          (.captureVariable coordinate)
          (.inclusion (.capture (.singleton coordinate))
            (.capture captures)) := by
        apply ManySortedFC.Evidence.Proves.captureVariable
        change ready.target.lookup coordinate =
          ManySortedFC.Binding.term (.capturing captures shape)
        simpa [coordinate, targetEquation] using facts.targetLookup
      have adapterTyping : Target.Adapter.HasType ready.target adapter
          sourceType (.capturing captures shape) := by
        apply ManySortedFC.Adapter.HasType.retagCapture capturesTyping
        exact .inclusionRefl (.type shape)
      exact
        { targetType := .capturing captures shape
          typeTranslated := by simpa [targetEquation] using facts.typeTranslated
          term := .adapt (.var coordinate) adapter
          isValue := .adapt .var
          typing := by
            apply ManySortedFC.Tm.HasType.adapt (.var) ?_ adapterTyping
            simpa [coordinate, sourceType, targetEquation] using rawTyping }
  | arr domain codomain =>
      exact
        { targetType := .arr domain codomain
          typeTranslated := by simpa [targetEquation] using facts.typeTranslated
          term := .var coordinate
          isValue := .var
          typing := by simpa [coordinate, targetEquation] using rawTyping }
  | forallT theory body =>
      exact
        { targetType := .forallT theory body
          typeTranslated := by simpa [targetEquation] using facts.typeTranslated
          term := .var coordinate
          isValue := .var
          typing := by simpa [coordinate, targetEquation] using rawTyping }
  | existsT theory payload =>
      exact
        { targetType := .existsT theory payload
          typeTranslated := by simpa [targetEquation] using facts.typeTranslated
          term := .var coordinate
          isValue := .var
          typing := by simpa [coordinate, targetEquation] using rawTyping }

private noncomputable def compileObjectVariable {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {name : Source.Var scope}
    (facts : Runtime.ObjectVariable ready.translated name) :
    CompiledValue ready (.var name) (context.lookup name) := by
  let resolved := facts.resolved
  let bounds := resolved.bounds
  let slot := resolved.slot
  let alpha : Target.Ty (Layout.sig context) := .tvar slot.alpha.name
  let chi : Target.Capture (Layout.sig context) := .cvar slot.chi.name
  let payloadRoot : Target.Capture (Layout.sig context) :=
    .singleton slot.payload
  let payloadSourceType : Target.Ty (Layout.sig context) :=
    .capturing payloadRoot alpha
  let typeLower : Target.Evidence (.inclusion .type)
      (Layout.sig context) := .var resolved.facts.typeLower
  let typeUpper : Target.Evidence (.inclusion .type)
      (Layout.sig context) := .var resolved.facts.typeUpper
  let captureLower : Target.Evidence (.inclusion .capture)
      (Layout.sig context) := .var resolved.facts.captureLower
  let captureUpper : Target.Evidence (.inclusion .capture)
      (Layout.sig context) := .var resolved.facts.captureUpper
  let payloadCaptures : Target.Evidence (.inclusion .capture)
      (Layout.sig context) := .captureVariable slot.payload
  let payloadShape : Target.Evidence (.inclusion .type)
      (Layout.sig context) := .inclusionRefl (.type alpha)
  let term := Object.pack bounds alpha chi typeLower typeUpper
    captureLower captureUpper (.var slot.payload) payloadSourceType
    payloadCaptures payloadShape
  have rawPayloadTyping := ManySortedFC.Tm.HasType.var
    (context := ready.target) slot.payload
  have payloadLookup := resolved.facts.payloadLookup
  change ready.target.lookup slot.payload = _ at payloadLookup
  rw [payloadLookup] at rawPayloadTyping
  have payloadCapturesTyping : Target.Evidence.Proves ready.target
      payloadCaptures
      (.inclusion (.capture payloadRoot) (.capture chi)) := by
    exact .captureVariable resolved.facts.payloadLookup
  have payloadShapeTyping : Target.Evidence.Proves ready.target
      payloadShape (.inclusion (.type alpha) (.type alpha)) :=
    .inclusionRefl (.type alpha)
  have adaptedPayloadTyping : Target.Tm.HasType ready.target
      (Object.retagPayload (.var slot.payload) payloadSourceType alpha chi
        payloadCaptures payloadShape)
      .empty (.capturing chi alpha) := by
    unfold ObjectEncoding.retagPayload
    apply ManySortedFC.Tm.HasType.adapt (.var) ?_
        (ManySortedFC.Adapter.HasType.retagCapture
          payloadCapturesTyping payloadShapeTyping)
    simpa [payloadSourceType, payloadRoot, alpha, chi] using rawPayloadTyping
  have typeLowerTyping : Target.Evidence.Proves ready.target typeLower
      (.inclusion (.type bounds.typeLower) (.type alpha)) := by
    simpa [typeLower, bounds, alpha, resolved,
      ManySortedTranslation.StaticSlot.expression]
      using ManySortedFC.Evidence.Proves.var
        resolved.facts.typeLowerLookup
  have typeUpperTyping : Target.Evidence.Proves ready.target typeUpper
      (.inclusion (.type alpha) (.type bounds.typeUpper)) := by
    simpa [typeUpper, bounds, alpha, resolved,
      ManySortedTranslation.StaticSlot.expression]
      using ManySortedFC.Evidence.Proves.var
        resolved.facts.typeUpperLookup
  have captureLowerTyping : Target.Evidence.Proves ready.target captureLower
      (.inclusion (.capture bounds.captureLower) (.capture chi)) := by
    simpa [captureLower, bounds, chi, resolved,
      ManySortedTranslation.StaticSlot.expression]
      using ManySortedFC.Evidence.Proves.var
        resolved.facts.captureLowerLookup
  have captureUpperTyping : Target.Evidence.Proves ready.target captureUpper
      (.inclusion (.capture chi) (.capture bounds.captureUpper)) := by
    simpa [captureUpper, bounds, chi, resolved,
      ManySortedTranslation.StaticSlot.expression]
      using ManySortedFC.Evidence.Proves.var
        resolved.facts.captureUpperLookup
  have satisfaction := satisfiesObjectTheory ready.target bounds alpha chi
    typeLower typeUpper captureLower captureUpper typeLowerTyping
      typeUpperTyping captureLowerTyping captureUpperTyping
  have termTyping : Target.Tm.HasType ready.target term .empty
      (Object.objectType bounds) := by
    unfold term ObjectEncoding.pack
    apply ManySortedFC.Tm.HasType.pack satisfaction
    · exact .adapt .var
    · exact adaptedPayloadTyping
    · exact captureUpperTyping
  exact
    { targetType := Object.objectType bounds
      typeTranslated := by simpa [bounds, resolved] using facts.typeTranslated
      term := term
      isValue := by
        unfold term ObjectEncoding.pack
        exact .pack (.adapt .var)
      typing := termTyping }

/-! ## Derivation-directed value compiler -/

/-- Compile a source value derivation.  The compiler is total on variable
and unit rules under `Runtime.Ready`; object construction remains partial
exactly where one of its ambient source endpoints cannot be translated.
Every successful object result contains two witnesses and four interval
certificates, with the declared capture upper bound reused as its package
closure rather than represented by a fifth premise. -/
noncomputable def compileValue? {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context) :
    {value : Source.Value scope} → {type : Source.Ty scope} →
      Source.Value.HasType context value type →
        Option (CompiledValue ready value type)
  | _, _, @DOTCapture.Acyclic.Value.HasType.var _ _ name =>
      match Runtime.resolveVariable ready name with
      | .plain facts => some (compilePlainVariable ready facts)
      | .object facts => some (compileObjectVariable ready facts)
  | _, _, .unit =>
      some
        { targetType := .one
          typeTranslated := rfl
          term := .unit
          isValue := .unit
          typing := .unit }
  | _, _, @DOTCapture.Acyclic.Value.HasType.object _ _ signature
      typeWitness captureWitness payload payloadType typeLower typeUpper
      captureLower captureUpper payloadTyping payloadShape payloadCapture =>
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
                    typeUpperCompiled.evidence
                    captureLowerCompiled.evidence
                    captureUpperCompiled.evidence payloadCompiled.term
                    payloadCompiled.targetType
                    payloadCaptureCompiled.evidence
                    payloadShapeCompiled.evidence
                  have satisfaction := satisfiesObjectTheory ready.target
                    bounds typeWitnessTarget captureWitnessTarget
                    typeLowerCompiled.evidence typeUpperCompiled.evidence
                    captureLowerCompiled.evidence
                    captureUpperCompiled.evidence
                    typeLowerCompiled.typing typeUpperCompiled.typing
                    captureLowerCompiled.typing
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

/-! ## Decisive executable regressions -/

namespace Regression

namespace SourceExamples

export DOTCapture.Acyclic.Examples
  (exactObject exactObjectTyping exactContext exactValueMemberTyping
    receiver)

end SourceExamples

/-- The closed `A = One`, `C = ∅` source object compiles to the exact
source-independent two-symbol/four-proof package fixed by ObjectEncoding. -/
noncomputable def exactObjectCompiled? :=
  compileValue? Runtime.nil SourceExamples.exactObjectTyping

/-- The source payload-capture premise is reflexivity, so the generated
certificate is `refl(∅)` (extensionally interchangeable with the
`captureEmpty` certificate used by ObjectEncoding's older checker example). -/
def exactCompiledPackage : Target.Tm [] :=
  Object.pack Object.exactBounds .one .empty
    (.inclusionRefl (.type .one))
    (.inclusionRefl (.type .one))
    (.inclusionRefl (.capture .empty))
    (.inclusionRefl (.capture .empty))
    .unit .one
    (.inclusionRefl (.capture .empty))
    (.inclusionRefl (.type .one))

theorem exact_object_compiles_to_expected_package :
    exactObjectCompiled?.map (fun compiled => compiled.term) =
      some exactCompiledPackage := by
  rfl

theorem exact_object_compiles_to_exact_type :
    exactObjectCompiled?.map (fun compiled => compiled.targetType) =
      some (Object.objectType ObjectEncoding.exactBounds) := by
  rfl

theorem exact_object_compiled_package_is_accepted :
    exactObjectCompiled?.bind (fun compiled =>
      Target.Tm.synth Runtime.nil.target compiled.term) =
        some (.empty, Object.objectType ObjectEncoding.exactBounds) := by
  have compiledTerm := exact_object_compiles_to_expected_package
  generalize resultEquation : exactObjectCompiled? = result
    at compiledTerm ⊢
  cases result with
  | none => simp at compiledTerm
  | some compiled =>
      simp only [Option.map_some, Option.bind_some] at compiledTerm ⊢
      have termEquality := Option.some.inj compiledTerm
      rw [termEquality]
      native_decide

/-- Returning a canonical source object variable is executable even though
its target binding stores only the opened payload: the value compiler
repackages that payload with its shared `α`/`χ` slots and four facts. -/
def returnedObjectTyping : Source.Value.HasType
    StaticTranslation.exactSourceContext
    (.var (.here : Source.Var 1))
    (StaticTranslation.exactSourceContext.lookup .here) :=
  .var

noncomputable def returnedObjectCompiled? :=
  compileValue? RuntimeContext.exactObjectReady returnedObjectTyping

theorem returned_object_variable_compiles :
    returnedObjectCompiled?.isSome = true := by
  rfl

/-! The next executable context makes the selected value-member type itself
an ordinary binding.  Its source annotation is genuinely `(x.A)^{x.C}`;
neither selection is represented by the runtime singleton `{x}`. -/

def selectedMemberSourceContext : Source.Ctx 2 :=
  StaticTranslation.exactSourceContext.extendTerm
    StaticTranslation.exactReceiver.valueMemberType

def selectedMemberTargetContext :
    Target.Ctx (Layout.sig selectedMemberSourceContext) :=
  StaticTranslation.exactTargetContext.extendTerm Object.payloadTypeOpened

theorem selected_member_context_translates :
    StaticTranslation.translateContext? selectedMemberSourceContext =
      some selectedMemberTargetContext := by
  rfl

def selectedMemberReady : Runtime.Ready selectedMemberSourceContext where
  translated :=
    ⟨selectedMemberTargetContext, selected_member_context_translates⟩
  executable :=
    .plain RuntimeContext.exactObjectReady.executable
      StaticTranslation.exactReceiver.valueMemberType (by rfl)

def selectedReceiver : Source.Path 2 :=
  StaticTranslation.exactReceiver.weaken

abbrev selectedReceiverSlot :=
  (Layout.newestReceiverSlot []).rename
    (ManySortedFC.Rename.succ (kind := .term))

theorem genuine_xA_reuses_renamed_alpha :
    Translation.translateTy? selectedMemberSourceContext
        selectedReceiver.selectedType =
      some (.tvar selectedReceiverSlot.alpha.name) := by
  rfl

theorem genuine_xC_reuses_renamed_chi :
    Translation.translateCapture? selectedMemberSourceContext
        selectedReceiver.selectedCapture =
      some (.cvar selectedReceiverSlot.chi.name) := by
  rfl

theorem genuine_selected_payload_type_translates :
    Translation.translateTy? selectedMemberSourceContext
        selectedReceiver.valueMemberType =
      some (.capturing (.cvar selectedReceiverSlot.chi.name)
        (.tvar selectedReceiverSlot.alpha.name)) := by
  rfl

def selectedPayloadTyping : Source.Value.HasType
    selectedMemberSourceContext (.var (.here : Source.Var 2))
      selectedReceiver.valueMemberType := by
  exact .var

noncomputable def selectedPayloadCompiled? :=
  compileValue? selectedMemberReady selectedPayloadTyping

theorem selected_xA_xC_variable_compiles :
    selectedPayloadCompiled?.isSome = true := by
  rfl

/-- `x.v` belongs to the source computation layer, but its returned source
type is the same genuine selected `(x.A)^{x.C}` exercised above.  This pins
the handoff expected by the separate term/selection compiler. -/
def genuine_x_v_typing : DOTCapture.Acyclic.Term.HasType
    SourceExamples.exactContext
    (.select SourceExamples.receiver .v)
    SourceExamples.receiver.selectedCapture
    SourceExamples.receiver.valueMemberType :=
  SourceExamples.exactValueMemberTyping

theorem genuine_x_v_result_type_translates :
    Translation.translateTy? SourceExamples.exactContext
        SourceExamples.receiver.valueMemberType =
      some Object.payloadTypeOpened := by
  rfl

end Regression

end DOTCaptureToManySortedFC.Acyclic.ValueTranslation
