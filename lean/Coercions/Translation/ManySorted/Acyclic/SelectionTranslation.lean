import Coercions.Translation.ManySorted.Acyclic.ExposureTranslation
import Coercions.DOT.Captures.Acyclic.ObjectTyping
import Coercions.ManySortedFC.TermChecker

/-!
# Primitive value-member selection translation

Reading `x.v` is the first runtime operation of the acyclic object encoding.
The target reads the receiver's separate payload coordinate, retags its
precise singleton capture to the shared abstract capture member, and finally
records the primitive receiver use.  This module stops at `{x}`: later source
`Term.HasType.use` derivations are compiled by the evidence layer.
-/

namespace DOTCaptureToManySortedFC.Acyclic.SelectionTranslation

namespace Source

export DOTCapture.Acyclic
  (Scope Path Ctx ObjectSig ExposesObject Capture Term ValueLabel)

namespace Path
export DOTCapture.Acyclic.Path (selectedCapture valueMemberType)
end Path

namespace Term
export DOTCapture.Acyclic.Term (HasType)
end Term

end Source

namespace Target

export ManySortedFC
  (BVar Capture Ty Binding Evidence Adapter Tm Ctx)

namespace Tm
export ManySortedFC.Tm (HasType check checkValue synth)
end Tm

end Target

namespace Static

export DOTCaptureToManySortedFC.Acyclic.StaticTranslation
  (translatePath translateCapture? translateTy?)

end Static

namespace Exposure

export DOTCaptureToManySortedFC.Acyclic.ExposureTranslation
  (TranslatedContext ResolvedExposure SlotFacts resolve)

end Exposure

/-! ## Exact target term -/

/-- The precise type synthesized for the payload variable before retagging. -/
def precisePayloadType {scope : Source.Scope} {context : Source.Ctx scope}
    {translated : Exposure.TranslatedContext context}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (resolved : Exposure.ResolvedExposure translated receiver signature) :
    Target.Ty (Layout.sig context) :=
  .capturing (.singleton resolved.slot.payload)
    (.tvar resolved.slot.alpha.name)

/-- The signature-declared target type of `x.v`. -/
def selectedPayloadType {scope : Source.Scope} {context : Source.Ctx scope}
    {translated : Exposure.TranslatedContext context}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (resolved : Exposure.ResolvedExposure translated receiver signature) :
    Target.Ty (Layout.sig context) :=
  .capturing (.cvar resolved.slot.chi.name)
    (.tvar resolved.slot.alpha.name)

/-- Primitive selection translation:

1. read the separate payload variable `p`, obtaining precise `{p}^alpha`;
2. explicitly retag it to `chi^alpha` using `{p} <= chi` and shape reflexivity;
3. widen the empty value-use prediction to the primitive use `{p}`. -/
def term {scope : Source.Scope} {context : Source.Ctx scope}
    {translated : Exposure.TranslatedContext context}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (resolved : Exposure.ResolvedExposure translated receiver signature) :
    Target.Tm (Layout.sig context) :=
  .use
    (.adapt (.var resolved.slot.payload)
      (.retagCapture (precisePayloadType resolved)
        (.cvar resolved.slot.chi.name) (.tvar resolved.slot.alpha.name)
        (.captureVariable resolved.slot.payload)
        (.inclusionRefl (.type (.tvar resolved.slot.alpha.name)))))
    (.captureEmpty (.singleton resolved.slot.payload))

/-! ## Declarative target typing -/

def term_hasType {scope : Source.Scope} {context : Source.Ctx scope}
    {translated : Exposure.TranslatedContext context}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (resolved : Exposure.ResolvedExposure translated receiver signature) :
    Target.Tm.HasType translated.target (term resolved)
      (.singleton resolved.slot.payload) (selectedPayloadType resolved) := by
  have variableTyping : Target.Tm.HasType translated.target
      (.var resolved.slot.payload) .empty (precisePayloadType resolved) := by
    simpa [precisePayloadType, resolved.facts.payloadLookup,
      ManySortedFC.Binding.termType, ManySortedFC.Ty.precise] using
      (ManySortedFC.Tm.HasType.var (context := translated.target)
        resolved.slot.payload)
  have captureTyping : ManySortedFC.Evidence.Proves translated.target
      (.captureVariable resolved.slot.payload)
      (.inclusion (.capture (.singleton resolved.slot.payload))
        (.capture (.cvar resolved.slot.chi.name))) :=
    .captureVariable resolved.facts.payloadLookup
  have shapeTyping : ManySortedFC.Evidence.Proves translated.target
      (.inclusionRefl (.type (.tvar resolved.slot.alpha.name)))
      (.inclusion (.type (.tvar resolved.slot.alpha.name))
        (.type (.tvar resolved.slot.alpha.name))) :=
    .inclusionRefl _
  have adapterTyping : ManySortedFC.Adapter.HasType translated.target
      (.retagCapture (precisePayloadType resolved)
        (.cvar resolved.slot.chi.name) (.tvar resolved.slot.alpha.name)
        (.captureVariable resolved.slot.payload)
        (.inclusionRefl (.type (.tvar resolved.slot.alpha.name))))
      (precisePayloadType resolved) (selectedPayloadType resolved) :=
    .retagCapture captureTyping shapeTyping
  have adaptedTyping : Target.Tm.HasType translated.target
      (.adapt (.var resolved.slot.payload)
        (.retagCapture (precisePayloadType resolved)
          (.cvar resolved.slot.chi.name) (.tvar resolved.slot.alpha.name)
          (.captureVariable resolved.slot.payload)
          (.inclusionRefl (.type (.tvar resolved.slot.alpha.name)))))
      .empty (selectedPayloadType resolved) :=
    .adapt .var variableTyping adapterTyping
  exact .use adaptedTyping (.captureEmpty _)

/-! ## Proof-carrying source-to-target result -/

/-- Translation of one primitive source `.select receiver .v` derivation.
The source use remains its runtime singleton; no selected-capture widening is
performed here. -/
structure Result {scope : Source.Scope} {context : Source.Ctx scope}
    (translated : Exposure.TranslatedContext context)
    (receiver : Source.Path scope) (signature : Source.ObjectSig scope) where
  resolved : Exposure.ResolvedExposure translated receiver signature
  sourceTyping : Source.Term.HasType context (.select receiver .v)
    (.singleton receiver) receiver.valueMemberType
  useTranslated : Static.translateCapture? context (.singleton receiver) =
    some (.singleton resolved.slot.payload)
  typeTranslated : Static.translateTy? context receiver.valueMemberType =
    some (selectedPayloadType resolved)
  targetTyping : Target.Tm.HasType translated.target (term resolved)
    (.singleton resolved.slot.payload) (selectedPayloadType resolved)

/-- Compile the primitive source selection associated with one exposure. -/
noncomputable def compile {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translated : Exposure.TranslatedContext context)
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (exposes : Source.ExposesObject context receiver signature) :
    Result translated receiver signature := by
  let resolved := Exposure.resolve translated exposes
  refine
    { resolved := resolved
      sourceTyping := .select exposes
      useTranslated := ?_
      typeTranslated := resolved.valueMemberTypeTranslated
      targetTyping := term_hasType resolved }
  change some (ManySortedFC.Capture.singleton
    (Static.translatePath context receiver)) =
      some (ManySortedFC.Capture.singleton resolved.slot.payload)
  rw [resolved.payloadIsPath]

/-! ## Executable checker regressions -/

namespace Regression

namespace ExposureRegression

export DOTCaptureToManySortedFC.Acyclic.ExposureTranslation.Regression
  (exactContext exactExposure exactResolved olderExpandedContext
    olderExpandedExposure olderExpandedResolved)

end ExposureRegression

/-- The newest receiver's generated selection is accepted with exactly its
payload singleton as immediate use and its shared `chi^alpha` result type. -/
theorem newest_check_accepts :
    (Target.Tm.check ExposureRegression.exactContext.target
      (term ExposureRegression.exactResolved)).isSome = true := by
  rfl

theorem newest_synthesizes_exact_indices :
    Target.Tm.synth ExposureRegression.exactContext.target
        (term ExposureRegression.exactResolved) =
      some (.singleton ExposureRegression.exactResolved.slot.payload,
        selectedPayloadType ExposureRegression.exactResolved) := by
  rfl

/-- Selection of an older receiver still checks after traversing a complete
newer object expansion (two symbols, four evidence coordinates, payload). -/
theorem older_through_object_check_accepts :
    (Target.Tm.check ExposureRegression.olderExpandedContext.target
      (term ExposureRegression.olderExpandedResolved)).isSome = true := by
  rfl

theorem older_through_object_synthesizes_exact_indices :
    Target.Tm.synth ExposureRegression.olderExpandedContext.target
        (term ExposureRegression.olderExpandedResolved) =
      some (.singleton ExposureRegression.olderExpandedResolved.slot.payload,
        selectedPayloadType ExposureRegression.olderExpandedResolved) := by
  rfl

end Regression

end DOTCaptureToManySortedFC.Acyclic.SelectionTranslation
