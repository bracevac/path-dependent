import Coercions.Translation.ManySorted.Acyclic.RuntimeContext
import Coercions.Translation.ManySorted.Acyclic.EvidenceTranslation
import Coercions.Translation.ManySorted.Acyclic.SelectionTranslation
import Coercions.Translation.ManySorted.BinderOnly.StaticInstantiation
import Coercions.ManySortedFC.Erasure

/-!
# Certified compiler core for acyclic captured DOT

The end-to-end source language is the **closed, acyclic, value-MNF
captured-DOT compiler case-study core**.  Its acceptance regressions are
closed, while the underlying compiler API is parameterized by an arbitrary
executable `Ready` context.
Applications take values.  Object-opening lets require a canonical object
value RHS, and object bindings compile through the many-sorted FC target's
FCsub-style existential opening (`ManySortedFC.Tm.open`).
Lambda domains are classified by `Ty.IsPlain`, so object-typed parameters are
not part of this compiler slice.

Executable contexts contain ordinary bindings and canonically formed object
bindings.  Ordinary variables translate to their target term coordinate, with
an explicit capture retag when needed.  An already-open object variable is
repackaged with two witnesses and four interval assumptions when returned as a
first-class value.  Recursive objects, full DOT, general non-MNF terms,
intersections, arbitrary member labels, structural arrow adaptation, and the
negative/universal object interface are outside this fragment.
-/

namespace DOTCaptureToManySortedFC.Acyclic.ValueTranslation

namespace Source

export DOTCapture.Acyclic
  (Scope StaticSort Var Path Capture Ty ObjectSig StaticExpr Ctx Value Term
    ExposesObject TypeIncludes CaptureIncludes)

namespace Value
export DOTCapture.Acyclic.Value (HasType)
end Value

namespace Term
export DOTCapture.Acyclic.Term (HasType)
end Term

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
  (Ready PlainVariable ObjectVariable Variable resolveVariable nil)

end Runtime

namespace Selection

export DOTCaptureToManySortedFC.Acyclic.SelectionTranslation
  (Result selectedPayloadType term compile)

end Selection

namespace Object

export ObjectEncoding
  (Bounds symbols relations theory payloadType existentialShape objectType
    symbolWeakening alphaSymbol chiSymbol symbolArguments evidenceArguments
    retagPayload pack openOnce payloadTypeOpened exactBounds staticWeakening)

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

/-- A target computation with exact translations of both source typing
indices.  It lives beside `CompiledValue` so the two derivation-directed
compilers can recurse mutually without introducing a module cycle. -/
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
  | modal requirements body =>
      exact
        { targetType := .modal requirements body
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
  | recProj bodies index =>
      exact
        { targetType := .recProj bodies index
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

/-! ## Computational translation helpers -/

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

/-- View the erased body of a plain source binder at the canonical one-term
runtime extension of the ambient target scope. -/
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
        ObjectEncoding.symbols ObjectEncoding.relations =
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
          ObjectEncoding.symbols ObjectEncoding.relations) =
      body.erase := by
  unfold ManySortedFC.Tm.erase
  rw [payloadRenamingIdentity]
  rfl

private theorem objectSig {scope : Source.Scope}
    (context : Source.Ctx scope) (signature : Source.ObjectSig scope) :
    Layout.sig (context.extendTerm
      (.capturing signature.captureUpper (.object signature))) =
        ObjectEncoding.PayloadScope (Layout.sig context) := rfl

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

/-- Primitive member selection is total in a ready runtime context. -/
private noncomputable def compileSelect {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (exposes : Source.ExposesObject context receiver signature) :
    CompiledTerm ready (.select receiver .v) (.singleton receiver)
      receiver.valueMemberType := by
  let selected := Selection.compile ready.translated exposes
  exact
    { sourceTyping := selected.sourceTyping
      targetUse := .singleton selected.resolved.slot.payload
      targetType := Selection.selectedPayloadType selected.resolved
      useTranslated := selected.useTranslated
      typeTranslated := selected.typeTranslated
      term := Selection.term selected.resolved
      typing := selected.targetTyping }

/-- Compile one immediate-use widening after its inner computation has
already been translated. -/
private noncomputable def compileUseTerm? {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {term : Source.Term scope} {sourceUse targetUse : Source.Capture scope}
    {type : Source.Ty scope}
    (inner : CompiledTerm ready term sourceUse type)
    (inclusion : Source.CaptureIncludes context sourceUse targetUse) :
    Option (CompiledTerm ready term targetUse type) :=
  match targetTranslated : Translation.translateCapture? context targetUse with
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

/-- Finish one logical source adaptation after compiling its value child. -/
noncomputable def compileAdapt? {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {value : Source.Value scope} {source target : Source.Ty scope}
    (inner : CompiledValue ready value source)
    (inclusion : Source.TypeIncludes context source target)
    {targetType : Target.Ty (Layout.sig context)}
    (targetTranslated : Translation.translateTy? context target =
      some targetType) : Option (CompiledValue ready value target) := do
  let inclusionCompiled ← compileTypeInclusion? ready.translated inclusion
    inner.typeTranslated targetTranslated
  pure
    { targetType := targetType
      typeTranslated := targetTranslated
      term := .adapt inner.term (.cast inclusionCompiled.evidence)
      isValue := .adapt inner.isValue
      typing := .adapt inner.isValue inner.typing
        (.cast inclusionCompiled.typing) }

/-- A finished lambda packages the compiled target value together with the
runtime constructor equation that downstream erasure proofs consume. -/
structure FinishedLambda {scope : Source.Scope}
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

/-- Finish a source lambda after its body has already been compiled.  Keeping
the dependent `IsPlain` case split here makes recursive compilation visible to
clients while containing the target-scope alignment in one semantic helper. -/
noncomputable def finishLambda? {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {domain codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)} {closure : Source.Capture scope}
    (domainPlain : domain.IsPlain)
    (captures : Source.CaptureIncludes (context.extendTerm domain) bodyUse
      (.union closure.weaken (.singleton (.var .here))))
    {domainTarget codomainTarget : Target.Ty (Layout.sig context)}
    {closureTarget : Target.Capture (Layout.sig context)}
    (domainTranslated : Translation.translateTy? context domain =
      some domainTarget)
    (codomainTranslated : Translation.translateTy? context codomain =
      some codomainTarget)
    (closureTranslated : Translation.translateCapture? context closure =
      some closureTarget)
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
          Translation.translateTy? (context.extendTerm binding) codomain.weaken =
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

/-- A finished plain let packages its proof-carrying target term and exact
runtime let spine. -/
structure FinishedPlainLet {scope : Source.Scope}
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

/-- Finish a plain let after compiling both recursive computations. -/
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
    (resultTranslated : Translation.translateTy? context result =
      some resultTarget)
    (bodyOuterTranslated : Translation.translateCapture? context bodyOuterUse =
      some bodyOuterTarget)
    (rhsCompiled : CompiledTerm ready rhs rhsUse bound)
    (bodyCompiled : CompiledTerm
      (ready.extendPlain boundPlain rhsCompiled.typeTranslated) body bodyUse
        result.weaken) : Option (@FinishedPlainLet scope context ready result
          bound rhs body rhsUse bodyUse bodyOuterUse boundPlain rhsCompiled
          bodyCompiled) := by
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
          Translation.translateTy? (context.extendTerm binding) result.weaken =
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
              simp [Translation.translateCapture?, rhsCompiled.useTranslated,
                bodyOuterTranslated]
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

/-- A finished object let retains the target `open` statically and exposes
its single runtime let after the fixed object telescope is erased. -/
structure FinishedObjectLet {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {signature : Source.ObjectSig scope} {result : Source.Ty scope}
    {rhs : Source.Value scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    {bounds : Object.Bounds (Layout.sig context)}
    {signatureTranslated : Translation.translateObjectSig? context signature =
      some bounds}
    (rhsCompiled : CompiledValue ready rhs
      (.capturing signature.captureUpper (.object signature)))
    (bodyCompiled : CompiledTerm
      (ready.extendObject signature signatureTranslated) body bodyUse
        result.weaken) where
  compiled : CompiledTerm ready (.let' result (.ret rhs) body)
    (.union signature.captureUpper bodyOuterUse) result
  erasedBody : ManySortedFC.Runtime.Tm
    ((Layout.sig context).termCount + 1)
  bodyErases : HEq bodyCompiled.term.erase erasedBody
  compiledErases : compiled.term.erase =
    ManySortedFC.Runtime.Tm.let' rhsCompiled.term.erase erasedBody

/-- Finish an object let as one target `open`, never as an ordinary target
let over the expanded static telescope. -/
noncomputable def finishObjectLet? {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {signature : Source.ObjectSig scope} {result : Source.Ty scope}
    {rhs : Source.Value scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (discharge : Source.CaptureIncludes
      (context.extendTerm
        (.capturing signature.captureUpper (.object signature))) bodyUse
      (.union bodyOuterUse.weaken (.singleton (.var .here))))
    {bounds : Object.Bounds (Layout.sig context)}
    {resultTarget : Target.Ty (Layout.sig context)}
    {bodyOuterTarget : Target.Capture (Layout.sig context)}
    (signatureTranslated : Translation.translateObjectSig? context signature =
      some bounds)
    (resultTranslated : Translation.translateTy? context result =
      some resultTarget)
    (bodyOuterTranslated : Translation.translateCapture? context bodyOuterUse =
      some bodyOuterTarget)
    (rhsTyping : Source.Value.HasType context rhs
      (.capturing signature.captureUpper (.object signature)))
    (rhsCompiled : CompiledValue ready rhs
      (.capturing signature.captureUpper (.object signature)))
    (bodyCompiled : CompiledTerm
      (ready.extendObject signature signatureTranslated) body bodyUse
        result.weaken) : Option (@FinishedObjectLet scope context ready
          signature result rhs body bodyUse bodyOuterUse bounds
          signatureTranslated rhsCompiled bodyCompiled) := do
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
  have rhsTargetTyping : Target.Tm.HasType ready.target rhsCompiled.term .empty
      (Object.objectType bounds) := by
    simpa [rhsTypeEquality] using rhsCompiled.typing
  have packageShape : (Object.objectType bounds).stripCapture =
      Object.existentialShape bounds := rfl
  let compiled : CompiledTerm ready (.let' result (.ret rhs) body)
      (.union signature.captureUpper bodyOuterUse) result :=
    { sourceTyping := .letObject rhsTyping
        bodyCompiled.sourceTyping discharge
      targetUse := .union bounds.captureUpper bodyOuterTarget
      targetType := resultTarget
      useTranslated := by
        have boundsTranslation :=
          BoundsTranslation.ofTranslated signatureTranslated
        simp [Translation.translateCapture?, boundsTranslation.captureUpper,
          bodyOuterTranslated]
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

/-! ## Mutually derivation-directed compiler -/

mutual

/-- Compile a source value derivation.  The compiler is total on variable
and unit rules under `Runtime.Ready`; object construction remains partial
exactly where one of its ambient source endpoints cannot be translated.
Every successful object result contains two witnesses and four interval
certificates, with the declared capture upper bound reused as its package
closure rather than represented by a fifth premise. -/

@[simp]
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
  | _, _, @DOTCapture.Acyclic.Value.HasType.lam _ _ domain codomain body
      bodyUse closure domainPlain bodyTyping captures =>
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
                  let finished ← finishLambda? domainPlain captures
                    domainTranslated codomainTranslated closureTranslated
                    bodyCompiled
                  pure finished.compiled
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
  | _, _, @DOTCapture.Acyclic.Value.HasType.adapt _ _ value source target
      valueTyping inclusion =>
      match targetTranslated : Translation.translateTy? context target with
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
  | _, _, _, @DOTCapture.Acyclic.Term.HasType.ret _ _ value type
      valueTyping => do
      let valueCompiled ← compileValue? ready valueTyping
      pure
        { sourceTyping := .ret valueTyping
          targetUse := .empty
          targetType := valueCompiled.targetType
          useTranslated := rfl
          typeTranslated := valueCompiled.typeTranslated
          term := valueCompiled.term
          typing := valueCompiled.typing }
  | _, _, _, @DOTCapture.Acyclic.Term.HasType.select _ _ receiver signature
      exposes =>
      some (compileSelect ready exposes)
  | _, _, _, @DOTCapture.Acyclic.Term.HasType.app _ _ function argument
      functionType domain codomain functionTyping functionShape
      domainPlain argumentTyping =>
      match codomainTranslated : Translation.translateTy? context codomain with
      | none => none
      | some codomainTarget => do
          let functionCompiled ← compileValue? ready functionTyping
          let argumentCompiled ← compileValue? ready argumentTyping
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
          pure
            { sourceTyping := .app functionTyping functionShape domainPlain
                argumentTyping
              targetUse := .union functionCompiled.targetType.outerCapture
                argumentCompiled.targetType.outerCapture
              targetType := codomainTarget
              useTranslated := by
                simp [Translation.translateCapture?,
                  functionOuterTranslated, argumentOuterTranslated]
              typeTranslated := codomainTranslated
              term := .app functionCompiled.term argumentCompiled.term
              typing := .app functionCompiled.typing functionShapeTarget
                argumentCompiled.typing }
  | _, _, _, @DOTCapture.Acyclic.Term.HasType.letPlain _ _ result bound rhs
      body rhsUse bodyUse bodyOuterUse boundPlain rhsTyping bodyTyping
      discharge =>
      match resultTranslated : Translation.translateTy? context result with
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
              let finished ← finishPlainLet? boundPlain discharge
                resultTranslated bodyOuterTranslated rhsCompiled bodyCompiled
              pure finished.compiled
  | _, _, _, @DOTCapture.Acyclic.Term.HasType.letObject _ _ signature result
      rhs body bodyUse bodyOuterUse rhsTyping bodyTyping discharge =>
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
                  let rhsCompiled ← compileValue? ready rhsTyping
                  let bodyReady := ready.extendObject signature
                    signatureTranslated
                  let bodyCompiled ← compileTerm? bodyReady bodyTyping
                  let finished ← finishObjectLet? discharge
                    signatureTranslated resultTranslated bodyOuterTranslated
                    rhsTyping rhsCompiled bodyCompiled
                  pure finished.compiled
  | _, _, _, @DOTCapture.Acyclic.Term.HasType.use _ _ term sourceUse
      targetUse type termTyping inclusion => do
      let inner ← compileTerm? ready termTyping
      compileUseTerm? inner inclusion

end

/-! ## Erasure-facing successful constructor shapes -/

/-- Successful application compilation exposes an actual target application,
independently of the endpoint-alignment proofs stored in the result. -/
theorem compileTerm?_app_term {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {function argument : Source.Value scope}
    {functionType domain codomain : Source.Ty scope}
    (functionTyping : Source.Value.HasType context function functionType)
    (functionShape : functionType.stripCapture = .arr domain codomain)
    (domainPlain : domain.IsPlain)
    (argumentTyping : Source.Value.HasType context argument domain)
    {compiled : CompiledTerm ready (.app function argument)
      (.union functionType.outerCapture domain.outerCapture) codomain}
    (success : compileTerm? ready
      (.app functionTyping functionShape domainPlain argumentTyping) =
        some compiled) :
    ∃ targetFunction targetArgument,
      compiled.term = .app targetFunction targetArgument := by
  unfold compileTerm? at success
  split at success
  · contradiction
  · generalize functionEquation :
      compileValue? ready functionTyping = functionResult at success
    cases functionResult with
    | none => contradiction
    | some functionCompiled =>
        generalize argumentEquation :
          compileValue? ready argumentTyping = argumentResult at success
        cases argumentResult with
        | none => contradiction
        | some argumentCompiled =>
            cases success
            exact ⟨functionCompiled.term, argumentCompiled.term, rfl⟩

/-- Logical source adaptation compiles to a runtime-transparent target cast,
never to a structural function adapter. -/
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
  split at success
  · contradiction
  · generalize innerEquation :
      compileValue? ready valueTyping = innerResult at success
    cases innerResult with
    | none => contradiction
    | some inner =>
        change compileAdapt? inner inclusion (by assumption) =
          some compiled at success
        unfold compileAdapt? at success
        generalize evidenceEquation :
          compileTypeInclusion? ready.translated inclusion
            inner.typeTranslated (by assumption) = evidenceResult at success
        cases evidenceResult with
        | none => contradiction
        | some generated =>
            cases success
            exact ⟨inner, generated.evidence, rfl, rfl⟩

/-- The lambda finisher changes no runtime structure beyond adding one
lambda node.  `HEq` records the harmless scope identification justified by
the source `IsPlain` premise. -/
theorem finishLambda?_erase {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {domain codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)} {closure : Source.Capture scope}
    (domainPlain : domain.IsPlain)
    (captures : Source.CaptureIncludes (context.extendTerm domain) bodyUse
      (.union closure.weaken (.singleton (.var .here))))
    {domainTarget codomainTarget : Target.Ty (Layout.sig context)}
    {closureTarget : Target.Capture (Layout.sig context)}
    (domainTranslated : Translation.translateTy? context domain =
      some domainTarget)
    (codomainTranslated : Translation.translateTy? context codomain =
      some codomainTarget)
    (closureTranslated : Translation.translateCapture? context closure =
      some closureTarget)
    (bodyCompiled : CompiledTerm
      (ready.extendPlain domainPlain domainTranslated) body bodyUse
        codomain.weaken)
    {finished : FinishedLambda bodyCompiled}
    (_success : finishLambda? domainPlain captures domainTranslated
      codomainTranslated closureTranslated bodyCompiled = some finished) :
    ∃ erasedBody : ManySortedFC.Runtime.Tm
        ((Layout.sig context).termCount + 1),
      HEq bodyCompiled.term.erase erasedBody ∧
      finished.compiled.term.erase =
        ManySortedFC.Runtime.Tm.lam erasedBody := by
  exact ⟨finished.erasedBody, finished.bodyErases,
    finished.compiledErases⟩

/-- Successful lambda compilation exposes the recursively compiled body and
its exact runtime lambda spine. -/
theorem compileValue?_lam_erase {scope : Source.Scope}
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
    ∃ (bodyReady : Runtime.Ready (context.extendTerm domain))
      (bodyCompiled : CompiledTerm bodyReady body bodyUse codomain.weaken)
      (erasedBody : ManySortedFC.Runtime.Tm
        ((Layout.sig context).termCount + 1)),
      compileTerm? bodyReady bodyTyping = some bodyCompiled ∧
      HEq bodyCompiled.term.erase erasedBody ∧
      compiled.term.erase = ManySortedFC.Runtime.Tm.lam erasedBody := by
  unfold compileValue? at success
  split at success
  · contradiction
  · rename_i domainTarget domainTranslated
    split at success
    · contradiction
    · rename_i codomainTarget codomainTranslated
      split at success
      · contradiction
      · rename_i closureTarget closureTranslated
        let bodyReady := ready.extendPlain domainPlain domainTranslated
        change (do
          let bodyCompiled ← compileTerm? bodyReady bodyTyping
          let finished ← finishLambda? domainPlain captures
            domainTranslated codomainTranslated closureTranslated bodyCompiled
          pure finished.compiled) =
              some compiled at success
        generalize bodyEquation :
          compileTerm? bodyReady bodyTyping = bodyResult at success
        cases bodyResult with
        | none => simp at success
        | some bodyCompiled =>
            change (do
              let finished ← finishLambda? domainPlain captures
                domainTranslated codomainTranslated closureTranslated
                bodyCompiled
              pure finished.compiled) = some compiled at success
            generalize finishEquation : finishLambda? domainPlain captures
              domainTranslated codomainTranslated closureTranslated
              bodyCompiled = finishResult at success
            cases finishResult with
            | none => simp at success
            | some finished =>
                have erased := finishLambda?_erase domainPlain captures
                  domainTranslated codomainTranslated closureTranslated
                  bodyCompiled finishEquation
                cases success
                obtain ⟨erasedBody, bodyErases, resultErases⟩ := erased
                exact ⟨bodyReady, bodyCompiled, erasedBody, bodyEquation,
                  bodyErases, resultErases⟩

/-- Successful plain-let finishing exposes its exact runtime let spine. -/
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
    (resultTranslated : Translation.translateTy? context result =
      some resultTarget)
    (bodyOuterTranslated : Translation.translateCapture? context bodyOuterUse =
      some bodyOuterTarget)
    (rhsCompiled : CompiledTerm ready rhs rhsUse bound)
    (bodyCompiled : CompiledTerm
      (ready.extendPlain boundPlain rhsCompiled.typeTranslated) body bodyUse
        result.weaken)
    {finished : FinishedPlainLet rhsCompiled bodyCompiled}
    (_success : finishPlainLet? boundPlain discharge resultTranslated
      bodyOuterTranslated rhsCompiled bodyCompiled = some finished) :
    ∃ erasedBody : ManySortedFC.Runtime.Tm
        ((Layout.sig context).termCount + 1),
      HEq bodyCompiled.term.erase erasedBody ∧
      finished.compiled.term.erase =
        ManySortedFC.Runtime.Tm.let' rhsCompiled.term.erase erasedBody := by
  exact ⟨finished.erasedBody, finished.bodyErases,
    finished.compiledErases⟩

/-- Successful plain-let compilation exposes both recursive compilations and
one runtime let. -/
theorem compileTerm?_letPlain_erase {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {result bound : Source.Ty scope} {rhs : Source.Term scope}
    {body : Source.Term (scope + 1)} {rhsUse : Source.Capture scope}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (boundPlain : bound.IsPlain)
    (rhsTyping : Source.Term.HasType context rhs rhsUse bound)
    (bodyTyping : Source.Term.HasType (context.extendTerm bound) body bodyUse
      result.weaken)
    (discharge : Source.CaptureIncludes (context.extendTerm bound) bodyUse
      bodyOuterUse.weaken)
    {compiled : CompiledTerm ready (.let' result rhs body)
      (.union rhsUse bodyOuterUse) result}
    (success : compileTerm? ready
      (.letPlain boundPlain rhsTyping bodyTyping discharge) = some compiled) :
    ∃ (rhsCompiled : CompiledTerm ready rhs rhsUse bound)
      (bodyReady : Runtime.Ready (context.extendTerm bound))
      (bodyCompiled : CompiledTerm bodyReady body bodyUse result.weaken)
      (erasedBody : ManySortedFC.Runtime.Tm
        ((Layout.sig context).termCount + 1)),
      compileTerm? ready rhsTyping = some rhsCompiled ∧
      compileTerm? bodyReady bodyTyping = some bodyCompiled ∧
      HEq bodyCompiled.term.erase erasedBody ∧
      compiled.term.erase = ManySortedFC.Runtime.Tm.let'
        rhsCompiled.term.erase erasedBody := by
  unfold compileTerm? at success
  split at success
  · contradiction
  · rename_i resultTarget resultTranslated
    split at success
    · contradiction
    · rename_i bodyOuterTarget bodyOuterTranslated
      change (do
        let rhsCompiled ← compileTerm? ready rhsTyping
        let bodyReady := ready.extendPlain boundPlain
          rhsCompiled.typeTranslated
        let bodyCompiled ← compileTerm? bodyReady bodyTyping
        let finished ← finishPlainLet? boundPlain discharge
          resultTranslated bodyOuterTranslated rhsCompiled bodyCompiled
        pure finished.compiled) = some compiled at success
      generalize rhsEquation :
        compileTerm? ready rhsTyping = rhsResult at success
      cases rhsResult with
      | none => simp at success
      | some rhsCompiled =>
          let bodyReady := ready.extendPlain boundPlain
            rhsCompiled.typeTranslated
          change (do
            let bodyCompiled ← compileTerm? bodyReady bodyTyping
            let finished ← finishPlainLet? boundPlain discharge
              resultTranslated bodyOuterTranslated rhsCompiled bodyCompiled
            pure finished.compiled) = some compiled at success
          generalize bodyEquation :
            compileTerm? bodyReady bodyTyping = bodyResult at success
          cases bodyResult with
          | none => simp at success
          | some bodyCompiled =>
              change (do
                let finished ← finishPlainLet? boundPlain discharge
                  resultTranslated bodyOuterTranslated rhsCompiled
                  bodyCompiled
                pure finished.compiled) = some compiled at success
              generalize finishEquation : finishPlainLet? boundPlain discharge
                resultTranslated bodyOuterTranslated rhsCompiled bodyCompiled =
                  finishResult at success
              cases finishResult with
              | none => simp at success
              | some finished =>
                  have erased := finishPlainLet?_erase boundPlain discharge
                    resultTranslated bodyOuterTranslated rhsCompiled
                    bodyCompiled finishEquation
                  cases success
                  obtain ⟨erasedBody, bodyErases, resultErases⟩ := erased
                  exact ⟨rhsCompiled, bodyReady, bodyCompiled, erasedBody,
                    rfl, bodyEquation, bodyErases, resultErases⟩

/-- Successful object-let finishing exposes the exact runtime let obtained by
erasing one target `open`. -/
theorem finishObjectLet?_erase {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {signature : Source.ObjectSig scope} {result : Source.Ty scope}
    {rhs : Source.Value scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (discharge : Source.CaptureIncludes
      (context.extendTerm
        (.capturing signature.captureUpper (.object signature))) bodyUse
      (.union bodyOuterUse.weaken (.singleton (.var .here))))
    {bounds : Object.Bounds (Layout.sig context)}
    {resultTarget : Target.Ty (Layout.sig context)}
    {bodyOuterTarget : Target.Capture (Layout.sig context)}
    (signatureTranslated : Translation.translateObjectSig? context signature =
      some bounds)
    (resultTranslated : Translation.translateTy? context result =
      some resultTarget)
    (bodyOuterTranslated : Translation.translateCapture? context bodyOuterUse =
      some bodyOuterTarget)
    (rhsTyping : Source.Value.HasType context rhs
      (.capturing signature.captureUpper (.object signature)))
    (rhsCompiled : CompiledValue ready rhs
      (.capturing signature.captureUpper (.object signature)))
    (bodyCompiled : CompiledTerm
      (ready.extendObject signature signatureTranslated) body bodyUse
        result.weaken)
    {finished : FinishedObjectLet rhsCompiled bodyCompiled}
    (_success : finishObjectLet? discharge signatureTranslated
      resultTranslated bodyOuterTranslated rhsTyping rhsCompiled bodyCompiled =
        some finished) :
    ∃ erasedBody : ManySortedFC.Runtime.Tm
        ((Layout.sig context).termCount + 1),
      HEq bodyCompiled.term.erase erasedBody ∧
      finished.compiled.term.erase = ManySortedFC.Runtime.Tm.let'
        rhsCompiled.term.erase erasedBody := by
  exact ⟨finished.erasedBody, finished.bodyErases,
    finished.compiledErases⟩

/-- Successful object-let compilation exposes the compiled package and body,
and erases the mandatory target `open` to one runtime let. -/
theorem compileTerm?_letObject_erase {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {signature : Source.ObjectSig scope} {result : Source.Ty scope}
    {rhs : Source.Value scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)}
    {bodyOuterUse : Source.Capture scope}
    (rhsTyping : Source.Value.HasType context rhs
      (.capturing signature.captureUpper (.object signature)))
    (bodyTyping : Source.Term.HasType
      (context.extendTerm
        (.capturing signature.captureUpper (.object signature))) body bodyUse
      result.weaken)
    (discharge : Source.CaptureIncludes
      (context.extendTerm
        (.capturing signature.captureUpper (.object signature))) bodyUse
      (.union bodyOuterUse.weaken (.singleton (.var .here))))
    {compiled : CompiledTerm ready (.let' result (.ret rhs) body)
      (.union signature.captureUpper bodyOuterUse) result}
    (success : compileTerm? ready
      (.letObject rhsTyping bodyTyping discharge) = some compiled) :
    ∃ (rhsCompiled : CompiledValue ready rhs
        (.capturing signature.captureUpper (.object signature)))
      (bodyReady : Runtime.Ready (context.extendTerm
        (.capturing signature.captureUpper (.object signature))))
      (bodyCompiled : CompiledTerm bodyReady body bodyUse result.weaken)
      (erasedBody : ManySortedFC.Runtime.Tm
        ((Layout.sig context).termCount + 1)),
      compileValue? ready rhsTyping = some rhsCompiled ∧
      compileTerm? bodyReady bodyTyping = some bodyCompiled ∧
      HEq bodyCompiled.term.erase erasedBody ∧
      compiled.term.erase = ManySortedFC.Runtime.Tm.let'
        rhsCompiled.term.erase erasedBody := by
  unfold compileTerm? at success
  split at success
  · contradiction
  · rename_i bounds signatureTranslated
    split at success
    · contradiction
    · rename_i resultTarget resultTranslated
      split at success
      · contradiction
      · rename_i bodyOuterTarget bodyOuterTranslated
        change (do
          let rhsCompiled ← compileValue? ready rhsTyping
          let bodyReady := ready.extendObject signature signatureTranslated
          let bodyCompiled ← compileTerm? bodyReady bodyTyping
          let finished ← finishObjectLet? discharge signatureTranslated
            resultTranslated bodyOuterTranslated rhsTyping rhsCompiled
            bodyCompiled
          pure finished.compiled) = some compiled at success
        generalize rhsEquation :
          compileValue? ready rhsTyping = rhsResult at success
        cases rhsResult with
        | none => simp at success
        | some rhsCompiled =>
            let bodyReady := ready.extendObject signature signatureTranslated
            change (do
              let bodyCompiled ← compileTerm? bodyReady bodyTyping
              let finished ← finishObjectLet? discharge
                signatureTranslated resultTranslated bodyOuterTranslated
                rhsTyping rhsCompiled bodyCompiled
              pure finished.compiled) = some compiled at success
            generalize bodyEquation :
              compileTerm? bodyReady bodyTyping = bodyResult at success
            cases bodyResult with
            | none => simp at success
            | some bodyCompiled =>
                change (do
                  let finished ← finishObjectLet? discharge
                    signatureTranslated resultTranslated bodyOuterTranslated
                    rhsTyping rhsCompiled bodyCompiled
                  pure finished.compiled) = some compiled at success
                generalize finishEquation : finishObjectLet? discharge
                  signatureTranslated resultTranslated bodyOuterTranslated
                  rhsTyping rhsCompiled bodyCompiled = finishResult at success
                cases finishResult with
                | none => simp at success
                | some finished =>
                    have erased := finishObjectLet?_erase discharge
                      signatureTranslated resultTranslated bodyOuterTranslated
                      rhsTyping rhsCompiled bodyCompiled finishEquation
                    cases success
                    obtain ⟨erasedBody, bodyErases, resultErases⟩ := erased
                    exact ⟨rhsCompiled, bodyReady, bodyCompiled, erasedBody,
                      rfl, bodyEquation, bodyErases, resultErases⟩

/-- A successfully compiled source `use` contains the successfully compiled
inner computation under exactly one target `Tm.use` node. -/
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
  generalize innerEquation : compileTerm? ready termTyping = innerResult
    at success
  cases innerResult with
  | none => simp at success
  | some inner =>
      change compileUseTerm? inner inclusion = some compiled at success
      unfold compileUseTerm? at success
      split at success
      · contradiction
      · rename_i target
        generalize compiledEvidenceEquation :
          compileCaptureInclusion? ready.translated inclusion
            inner.useTranslated (by assumption) = evidenceResult at success
        cases evidenceResult with
        | none => contradiction
        | some generated =>
            cases success
            exact ⟨inner, generated.evidence, rfl, rfl⟩

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
  unfold exactObjectCompiled?
  unfold SourceExamples.exactObjectTyping SourceExamples.exactObject
    DOTCapture.Acyclic.Examples.exactSignature
  unfold compileValue?
  unfold compileValue?
  rfl

theorem exact_object_compiles_to_exact_type :
    exactObjectCompiled?.map (fun compiled => compiled.targetType) =
      some (Object.objectType ObjectEncoding.exactBounds) := by
  unfold exactObjectCompiled?
  unfold SourceExamples.exactObjectTyping SourceExamples.exactObject
    DOTCapture.Acyclic.Examples.exactSignature
  unfold compileValue?
  unfold compileValue?
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
  unfold returnedObjectCompiled? returnedObjectTyping
  unfold compileValue?
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
  unfold selectedPayloadCompiled? selectedPayloadTyping
  unfold compileValue?
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
