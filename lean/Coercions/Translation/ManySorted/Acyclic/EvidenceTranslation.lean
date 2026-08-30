import Coercions.Translation.ManySorted.Acyclic.ExposureTranslation
import Coercions.DOT.Captures.Acyclic.Examples
import Coercions.ManySortedFC.EvidenceChecker

/-!
# Evidence translation for acyclic DOT objects with captures

Source inclusion derivations compile directly to many-sorted FC evidence.
The raw source syntax is intentionally partial: a result exists only when
both source endpoints translate through the canonical receiver layout.  Each
successful result records those endpoint translations together with the
exact target `Evidence.Proves` derivation.
-/

namespace DOTCaptureToManySortedFC.Acyclic.EvidenceTranslation

namespace Source

export DOTCapture.Acyclic
  (Scope StaticSort Path StaticRef Capture Ty ObjectSig StaticExpr Ctx
    ExposesObject HasLower HasUpper Includes TypeIncludes CaptureIncludes)

namespace Path
export DOTCapture.Acyclic.Path
  (selectedType selectedCapture typeMember captureMember)
end Path

namespace StaticRef
export DOTCapture.Acyclic.StaticRef (expression)
end StaticRef

namespace ObjectSig
export DOTCapture.Acyclic.ObjectSig
  (typeLower typeUpper captureLower captureUpper)
end ObjectSig

namespace Ctx
export DOTCapture.Acyclic.Ctx (nil)
end Ctx

end Source

namespace Target

export ManySortedFC
  (StaticSort Relation StaticExpr Capture Ty Proposition Binding Ctx Evidence)

namespace Evidence
export ManySortedFC.Evidence (Proves Checked check)
end Evidence

namespace Ctx
export ManySortedFC.Ctx (nil extendTerm)
end Ctx

end Target

namespace Translation

export DOTCaptureToManySortedFC.Acyclic.StaticTranslation
  (translatePath translateCapture? translateTy? translateExpr?
    TranslatesExpr)

end Translation

namespace Exposure

export DOTCaptureToManySortedFC.Acyclic.ExposureTranslation
  (TranslatedContext ResolvedExposure resolve)

namespace ResolvedExposure
export DOTCaptureToManySortedFC.Acyclic.ExposureTranslation.ResolvedExposure
  (typeLowerTranslated typeUpperTranslated captureLowerTranslated
    captureUpperTranslated)
end ResolvedExposure

end Exposure

/-! ## Proof-carrying result -/

/-- One target certificate for the exact translations of two source
endpoints. -/
structure CompiledInclusion {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translatedContext : Exposure.TranslatedContext context)
    {sort : Source.StaticSort}
    (source target : Source.StaticExpr sort scope) where
  sourceTarget :
    Target.StaticExpr (Layout.translateSort sort) (Layout.sig context)
  targetTarget :
    Target.StaticExpr (Layout.translateSort sort) (Layout.sig context)
  sourceTranslated :
    Translation.translateExpr? context source = some sourceTarget
  targetTranslated :
    Translation.translateExpr? context target = some targetTarget
  evidence : Target.Evidence (.inclusion (Layout.translateSort sort))
    (Layout.sig context)
  typing : Target.Evidence.Proves translatedContext.target evidence
    (.inclusion sourceTarget targetTarget)

/-- Internal result once both translated endpoints have already been fixed. -/
private structure CompiledAt {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translatedContext : Exposure.TranslatedContext context)
    {sort : Source.StaticSort}
    (source target :
      Target.StaticExpr (Layout.translateSort sort) (Layout.sig context)) where
  evidence : Target.Evidence (.inclusion (Layout.translateSort sort))
    (Layout.sig context)
  typing : Target.Evidence.Proves translatedContext.target evidence
    (.inclusion source target)

private theorem translateTypeExpression {scope : Source.Scope}
    {context : Source.Ctx scope} {source : Source.Ty scope}
    {target : Target.Ty (Layout.sig context)}
    (translated : Translation.translateTy? context source = some target) :
    Translation.translateExpr? context (.type source) =
      some (.type target) := by
  simp [Translation.translateExpr?, translated]

private theorem translateCaptureExpression {scope : Source.Scope}
    {context : Source.Ctx scope} {source : Source.Capture scope}
    {target : Target.Capture (Layout.sig context)}
    (translated :
      Translation.translateCapture? context source = some target) :
    Translation.translateExpr? context (.capture source) =
      some (.capture target) := by
  simp [Translation.translateExpr?, translated]

private theorem translatedExpression_unique {scope : Source.Scope}
    {context : Source.Ctx scope} {sort : Source.StaticSort}
    {source : Source.StaticExpr sort scope}
    {first second : Target.StaticExpr (Layout.translateSort sort)
      (Layout.sig context)}
    (firstTranslated :
      Translation.translateExpr? context source = some first)
    (secondTranslated :
      Translation.translateExpr? context source = some second) :
    first = second :=
  StaticTranslation.TranslatesExpr.functional
    firstTranslated secondTranslated

/-! ## Resolved member assumptions -/

private noncomputable def compileLower {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translatedContext : Exposure.TranslatedContext context)
    {sort : Source.StaticSort} {reference : Source.StaticRef sort scope}
    {endpoint : Source.StaticExpr sort scope}
    (bound : Source.HasLower context reference endpoint)
    {sourceTarget targetTarget :
      Target.StaticExpr (Layout.translateSort sort) (Layout.sig context)}
    (sourceTranslated :
      Translation.translateExpr? context endpoint = some sourceTarget)
    (targetTranslated :
      Translation.translateExpr? context reference.expression =
        some targetTarget) :
    CompiledAt translatedContext sourceTarget targetTarget := by
  cases bound with
  | typeMember exposes =>
      let resolved := Exposure.resolve translatedContext exposes
      have expectedSource := translateTypeExpression
        (Exposure.ResolvedExposure.typeLowerTranslated resolved)
      have expectedTarget := translateTypeExpression
        resolved.selectedTypeTranslated
      have sourceEquality := translatedExpression_unique
        sourceTranslated expectedSource
      have targetEquality := translatedExpression_unique
        targetTranslated expectedTarget
      cases sourceEquality
      cases targetEquality
      exact
        { evidence := .var resolved.facts.typeLower
          typing := .var resolved.facts.typeLowerLookup }
  | captureMember exposes =>
      let resolved := Exposure.resolve translatedContext exposes
      have expectedSource := translateCaptureExpression
        (Exposure.ResolvedExposure.captureLowerTranslated resolved)
      have expectedTarget := translateCaptureExpression
        resolved.selectedCaptureTranslated
      have sourceEquality := translatedExpression_unique
        sourceTranslated expectedSource
      have targetEquality := translatedExpression_unique
        targetTranslated expectedTarget
      cases sourceEquality
      cases targetEquality
      exact
        { evidence := .var resolved.facts.captureLower
          typing := .var resolved.facts.captureLowerLookup }

private noncomputable def compileUpper {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translatedContext : Exposure.TranslatedContext context)
    {sort : Source.StaticSort} {reference : Source.StaticRef sort scope}
    {endpoint : Source.StaticExpr sort scope}
    (bound : Source.HasUpper context reference endpoint)
    {sourceTarget targetTarget :
      Target.StaticExpr (Layout.translateSort sort) (Layout.sig context)}
    (sourceTranslated :
      Translation.translateExpr? context reference.expression =
        some sourceTarget)
    (targetTranslated :
      Translation.translateExpr? context endpoint = some targetTarget) :
    CompiledAt translatedContext sourceTarget targetTarget := by
  cases bound with
  | typeMember exposes =>
      let resolved := Exposure.resolve translatedContext exposes
      have expectedSource := translateTypeExpression
        resolved.selectedTypeTranslated
      have expectedTarget := translateTypeExpression
        (Exposure.ResolvedExposure.typeUpperTranslated resolved)
      have sourceEquality := translatedExpression_unique
        sourceTranslated expectedSource
      have targetEquality := translatedExpression_unique
        targetTranslated expectedTarget
      cases sourceEquality
      cases targetEquality
      exact
        { evidence := .var resolved.facts.typeUpper
          typing := .var resolved.facts.typeUpperLookup }
  | captureMember exposes =>
      let resolved := Exposure.resolve translatedContext exposes
      have expectedSource := translateCaptureExpression
        resolved.selectedCaptureTranslated
      have expectedTarget := translateCaptureExpression
        (Exposure.ResolvedExposure.captureUpperTranslated resolved)
      have sourceEquality := translatedExpression_unique
        sourceTranslated expectedSource
      have targetEquality := translatedExpression_unique
        targetTranslated expectedTarget
      cases sourceEquality
      cases targetEquality
      exact
        { evidence := .var resolved.facts.captureUpper
          typing := .var resolved.facts.captureUpperLookup }

private noncomputable def compilePayloadRoot {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translatedContext : Exposure.TranslatedContext context)
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (exposes : Source.ExposesObject context receiver signature)
    {sourceTarget targetTarget : Target.StaticExpr .capture
      (Layout.sig context)}
    (sourceTranslated : Translation.translateExpr? context
      (.capture (.singleton receiver)) = some sourceTarget)
    (targetTranslated : Translation.translateExpr? context
      (.capture receiver.selectedCapture) = some targetTarget) :
    CompiledAt (sort := .capture) translatedContext sourceTarget
      targetTarget := by
  let resolved := Exposure.resolve translatedContext exposes
  have singletonTranslated : Translation.translateExpr? context
      (.capture (.singleton receiver)) =
        some (.capture (.singleton resolved.slot.payload)) := by
    simp only [Translation.translateExpr?, Translation.translateCapture?,
      Option.map_some]
    rw [resolved.payloadIsPath]
  have selectedTranslated := translateCaptureExpression
    resolved.selectedCaptureTranslated
  have sourceEquality := translatedExpression_unique
    sourceTranslated singletonTranslated
  have targetEquality := translatedExpression_unique
    targetTranslated selectedTranslated
  cases sourceEquality
  cases targetEquality
  exact
    { evidence := .captureVariable resolved.slot.payload
      typing := .captureVariable resolved.facts.payloadLookup }

/-! ## Derivation-directed structural compiler -/

private noncomputable def compileAt? {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translatedContext : Exposure.TranslatedContext context) :
    {sort : Source.StaticSort} →
    {source target : Source.StaticExpr sort scope} →
    (derivation : Source.Includes context source target) →
    {sourceTarget targetTarget :
      Target.StaticExpr (Layout.translateSort sort) (Layout.sig context)} →
    (sourceTranslated :
      Translation.translateExpr? context source = some sourceTarget) →
    (targetTranslated :
      Translation.translateExpr? context target = some targetTarget) →
    Option (CompiledAt translatedContext sourceTarget targetTarget)
  | _, _, _, .refl, sourceTarget, targetTarget, sourceTranslated,
      targetTranslated =>
      have equality := translatedExpression_unique
        sourceTranslated targetTranslated
      equality ▸ some
        { evidence := .inclusionRefl sourceTarget
          typing := .inclusionRefl sourceTarget }
  | _, _, _, @DOTCapture.Acyclic.Includes.trans _ _ _ _ middle _ first second,
      sourceTarget, targetTarget, sourceTranslated, targetTranslated =>
      match middleTranslated : Translation.translateExpr? context middle with
      | none => none
      | some middleTarget => do
          let firstCompiled ← compileAt? translatedContext first
            sourceTranslated middleTranslated
          let secondCompiled ← compileAt? translatedContext second
            middleTranslated targetTranslated
          pure
            { evidence := .inclusionTrans firstCompiled.evidence
                secondCompiled.evidence
              typing := .inclusionTrans firstCompiled.typing
                secondCompiled.typing }
  | _, _, _, .lower bound, sourceTarget, targetTarget, sourceTranslated,
      targetTranslated =>
      some (compileLower translatedContext bound sourceTranslated
        targetTranslated)
  | _, _, _, .upper bound, sourceTarget, targetTarget, sourceTranslated,
      targetTranslated =>
      some (compileUpper translatedContext bound sourceTranslated
        targetTranslated)
  | _, _, _, @DOTCapture.Acyclic.Includes.typeTop _ _ type,
      sourceTarget, targetTarget, sourceTranslated, targetTranslated =>
      have expectedTarget : Translation.translateExpr? context
          (.type (.top : Source.Ty scope)) =
            some (.type (.top : Target.Ty (Layout.sig context))) := rfl
      have targetEquality := translatedExpression_unique
        targetTranslated expectedTarget
      targetEquality ▸
        match sourceTarget with
        | .type sourceType => some
            { evidence := .typeTop sourceType
              typing := .typeTop sourceType }
  | _, _, _, @DOTCapture.Acyclic.Includes.typeBottom _ _ type,
      sourceTarget, targetTarget, sourceTranslated, targetTranslated =>
      have expectedSource : Translation.translateExpr? context
          (.type (.bot : Source.Ty scope)) =
            some (.type (.bot : Target.Ty (Layout.sig context))) := rfl
      have sourceEquality := translatedExpression_unique
        sourceTranslated expectedSource
      sourceEquality ▸
        match targetTarget with
        | .type targetType => some
            { evidence := .typeBottom targetType
              typing := .typeBottom targetType }
  | _, _, _, @DOTCapture.Acyclic.Includes.typeCapturing _ _ sourceCaptures
      targetCaptures sourceShape targetShape captures shape,
      sourceTarget, targetTarget, sourceTranslated, targetTranslated =>
      match sourceCapturesTranslated :
          Translation.translateCapture? context sourceCaptures with
      | none => none
      | some sourceCapturesTarget =>
          match targetCapturesTranslated :
              Translation.translateCapture? context targetCaptures with
          | none => none
          | some targetCapturesTarget =>
              match sourceShapeTranslated :
                  Translation.translateTy? context sourceShape with
              | none => none
              | some sourceShapeTarget =>
                  match targetShapeTranslated :
                      Translation.translateTy? context targetShape with
                  | none => none
                  | some targetShapeTarget => do
                      let capturesCompiled ← compileAt? translatedContext
                        captures
                        (translateCaptureExpression
                          sourceCapturesTranslated)
                        (translateCaptureExpression
                          targetCapturesTranslated)
                      let shapeCompiled ← compileAt? translatedContext shape
                        (translateTypeExpression sourceShapeTranslated)
                        (translateTypeExpression targetShapeTranslated)
                      have expectedSource : Translation.translateExpr? context
                          (.type (.capturing sourceCaptures sourceShape)) =
                            some (.type (.capturing sourceCapturesTarget
                              sourceShapeTarget)) := by
                        simp [Translation.translateExpr?,
                          Translation.translateTy?,
                          sourceCapturesTranslated, sourceShapeTranslated]
                      have expectedTarget : Translation.translateExpr? context
                          (.type (.capturing targetCaptures targetShape)) =
                            some (.type (.capturing targetCapturesTarget
                              targetShapeTarget)) := by
                        simp [Translation.translateExpr?,
                          Translation.translateTy?,
                          targetCapturesTranslated, targetShapeTranslated]
                      have sourceEquality := translatedExpression_unique
                        sourceTranslated expectedSource
                      have targetEquality := translatedExpression_unique
                        targetTranslated expectedTarget
                      sourceEquality ▸ targetEquality ▸ pure
                        { evidence := .typeCapturing
                            capturesCompiled.evidence shapeCompiled.evidence
                          typing := .typeCapturing capturesCompiled.typing
                            shapeCompiled.typing }
  | _, _, _, @DOTCapture.Acyclic.Includes.captureEmpty _ _ captures,
      sourceTarget, targetTarget, sourceTranslated, targetTranslated =>
      have expectedSource : Translation.translateExpr? context
          (.capture (.empty : Source.Capture scope)) =
            some (.capture (.empty : Target.Capture
              (Layout.sig context))) := rfl
      have sourceEquality := translatedExpression_unique
        sourceTranslated expectedSource
      sourceEquality ▸
        match targetTarget with
        | .capture targetCapture => some
            { evidence := .captureEmpty targetCapture
              typing := .captureEmpty targetCapture }
  | _, _, _, @DOTCapture.Acyclic.Includes.captureUnionLeft _ _ left right,
      sourceTarget, targetTarget, sourceTranslated, targetTranslated =>
      match leftTranslated : Translation.translateCapture? context left with
      | none => none
      | some leftTarget =>
          match rightTranslated : Translation.translateCapture? context right with
          | none => none
          | some rightTarget =>
              have expectedSource :=
                translateCaptureExpression leftTranslated
              have expectedTarget : Translation.translateExpr? context
                  (.capture (.union left right)) =
                    some (.capture (.union leftTarget rightTarget)) := by
                simp [Translation.translateExpr?,
                  Translation.translateCapture?, leftTranslated,
                  rightTranslated]
              have sourceEquality := translatedExpression_unique
                sourceTranslated expectedSource
              have targetEquality := translatedExpression_unique
                targetTranslated expectedTarget
              sourceEquality ▸ targetEquality ▸ some
                { evidence := .captureUnionLeft leftTarget rightTarget
                  typing := .captureUnionLeft leftTarget rightTarget }
  | _, _, _, @DOTCapture.Acyclic.Includes.captureUnionRight _ _ left right,
      sourceTarget, targetTarget, sourceTranslated, targetTranslated =>
      match leftTranslated : Translation.translateCapture? context left with
      | none => none
      | some leftTarget =>
          match rightTranslated : Translation.translateCapture? context right with
          | none => none
          | some rightTarget =>
              have expectedSource :=
                translateCaptureExpression rightTranslated
              have expectedTarget : Translation.translateExpr? context
                  (.capture (.union left right)) =
                    some (.capture (.union leftTarget rightTarget)) := by
                simp [Translation.translateExpr?,
                  Translation.translateCapture?, leftTranslated,
                  rightTranslated]
              have sourceEquality := translatedExpression_unique
                sourceTranslated expectedSource
              have targetEquality := translatedExpression_unique
                targetTranslated expectedTarget
              sourceEquality ▸ targetEquality ▸ some
                { evidence := .captureUnionRight leftTarget rightTarget
                  typing := .captureUnionRight leftTarget rightTarget }
  | _, _, _, @DOTCapture.Acyclic.Includes.captureUnionElim _ _ left right target
      fromLeft fromRight, sourceTarget, .capture targetTarget, sourceTranslated,
      targetTranslated =>
      match leftTranslated : Translation.translateCapture? context left with
      | none => none
      | some leftTarget =>
          match rightTranslated : Translation.translateCapture? context right with
          | none => none
          | some rightTarget => do
              let fromLeftCompiled ← compileAt? translatedContext fromLeft
                (translateCaptureExpression leftTranslated) targetTranslated
              let fromRightCompiled ← compileAt? translatedContext fromRight
                (translateCaptureExpression rightTranslated) targetTranslated
              have expectedSource : Translation.translateExpr? context
                  (.capture (.union left right)) =
                    some (.capture (.union leftTarget rightTarget)) := by
                simp [Translation.translateExpr?,
                  Translation.translateCapture?, leftTranslated,
                  rightTranslated]
              have sourceEquality := translatedExpression_unique
                sourceTranslated expectedSource
              sourceEquality ▸ pure
                { evidence := .captureUnionElim fromLeftCompiled.evidence
                    fromRightCompiled.evidence
                  typing := .captureUnionElim fromLeftCompiled.typing
                    fromRightCompiled.typing }
  | _, _, _, .payloadRoot exposes, sourceTarget, targetTarget,
      sourceTranslated, targetTranslated =>
      some (compilePayloadRoot translatedContext exposes sourceTranslated
        targetTranslated)

/-- Compile a source inclusion without proof search.  Failure means that at
least one raw source endpoint did not translate through the current layout. -/
noncomputable def compileIncludes? {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translatedContext : Exposure.TranslatedContext context)
    {sort : Source.StaticSort}
    {source target : Source.StaticExpr sort scope}
    (derivation : Source.Includes context source target) :
    Option (CompiledInclusion translatedContext source target) :=
  match sourceTranslated : Translation.translateExpr? context source,
      targetTranslated : Translation.translateExpr? context target with
  | some sourceTarget, some targetTarget =>
      match compileAt? translatedContext derivation sourceTranslated
          targetTranslated with
      | none => none
      | some compiled => some
          { sourceTarget := sourceTarget
            targetTarget := targetTarget
            sourceTranslated := sourceTranslated
            targetTranslated := targetTranslated
            evidence := compiled.evidence
            typing := compiled.typing }
  | _, _ => none

/-! ## Checker-facing execution -/

/-- Run the target structural checker on a successfully compiled source
derivation and retain only its synthesized proposition. -/
noncomputable def compileAndCheck? {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translatedContext : Exposure.TranslatedContext context)
    {sort : Source.StaticSort}
    {source target : Source.StaticExpr sort scope}
    (derivation : Source.Includes context source target) :
    Option (Target.Proposition
      (.inclusion (Layout.translateSort sort)) (Layout.sig context)) := do
  let compiled ← compileIncludes? translatedContext derivation
  let checked ← Target.Evidence.check translatedContext.target
    compiled.evidence
  pure checked.proposition

/-! ## Decisive checker regressions -/

namespace Regression

namespace ExposureRegression

export DOTCaptureToManySortedFC.Acyclic.ExposureTranslation.Regression
  (ExactSignature ExactSourceContext ExactTargetContext exactContext
    exactExposure)

end ExposureRegression

def exactTypeLower : Source.TypeIncludes
    ExposureRegression.ExactSourceContext .one
      StaticTranslation.exactReceiver.selectedType :=
  ExposureRegression.exactExposure.typeLower

def exactTypeUpper : Source.TypeIncludes
    ExposureRegression.ExactSourceContext
      StaticTranslation.exactReceiver.selectedType .one :=
  ExposureRegression.exactExposure.typeUpper

def exactCaptureLower : Source.CaptureIncludes
    ExposureRegression.ExactSourceContext .empty
      StaticTranslation.exactReceiver.selectedCapture :=
  ExposureRegression.exactExposure.captureLower

def exactCaptureUpper : Source.CaptureIncludes
    ExposureRegression.ExactSourceContext
      StaticTranslation.exactReceiver.selectedCapture .empty :=
  ExposureRegression.exactExposure.captureUpper

def exactPayloadRoot : Source.CaptureIncludes
    ExposureRegression.ExactSourceContext
      (.singleton StaticTranslation.exactReceiver)
      StaticTranslation.exactReceiver.selectedCapture :=
  ExposureRegression.exactExposure.payloadRoot

abbrev exactSlot := Layout.newestReceiverSlot []

theorem exact_type_lower_checker_accepted :
    compileAndCheck? ExposureRegression.exactContext exactTypeLower =
      some (.inclusion (.type .one) exactSlot.alpha.expression) := by
  rfl

theorem exact_type_upper_checker_accepted :
    compileAndCheck? ExposureRegression.exactContext exactTypeUpper =
      some (.inclusion exactSlot.alpha.expression (.type .one)) := by
  rfl

theorem exact_capture_lower_checker_accepted :
    compileAndCheck? ExposureRegression.exactContext exactCaptureLower =
      some (.inclusion (.capture .empty) exactSlot.chi.expression) := by
  rfl

theorem exact_capture_upper_checker_accepted :
    compileAndCheck? ExposureRegression.exactContext exactCaptureUpper =
      some (.inclusion exactSlot.chi.expression (.capture .empty)) := by
  rfl

theorem exact_payload_root_checker_accepted :
    compileAndCheck? ExposureRegression.exactContext exactPayloadRoot =
      some (.inclusion
        (.capture (.singleton exactSlot.payload))
        (.capture (.cvar exactSlot.chi.name))) := by
  rfl

namespace SourceExamples

export DOTCapture.Acyclic.Examples
  (badOpenContext topIncludesBottom capabilityIncludesEmpty)

end SourceExamples

abbrev BadOuterScope : ManySortedFC.Sig := ([] : ManySortedFC.Sig) ▹ .term

def badOuterTargetContext : Target.Ctx BadOuterScope :=
  Target.Ctx.nil.extendTerm (.capturing .empty .one)

def badBounds : ObjectEncoding.Bounds BadOuterScope where
  typeLower := .top
  typeUpper := .bot
  captureLower := .singleton .here
  captureUpper := .empty

def badTargetContext :
    Target.Ctx (Layout.sig SourceExamples.badOpenContext) :=
  ObjectEncoding.openedContext badOuterTargetContext badBounds

theorem bad_context_translates :
    StaticTranslation.translateContext? SourceExamples.badOpenContext =
      some badTargetContext := by
  native_decide

def badContext : Exposure.TranslatedContext SourceExamples.badOpenContext :=
  ⟨badTargetContext, bad_context_translates⟩

theorem bad_type_chain_checker_accepted :
    compileAndCheck? badContext SourceExamples.topIncludesBottom =
      some (.inclusion (.type .top) (.type .bot)) := by
  rfl

def badCapabilityTarget : ManySortedFC.BVar
    (Layout.sig SourceExamples.badOpenContext) .term :=
  ObjectEncoding.payloadWeakening.var (.here :
    ManySortedFC.BVar BadOuterScope .term)

theorem bad_capture_chain_checker_accepted :
    compileAndCheck? badContext SourceExamples.capabilityIncludesEmpty =
      some (.inclusion
        (.capture (.singleton badCapabilityTarget))
        (.capture .empty)) := by
  rfl

def invalidContext : Exposure.TranslatedContext
    StaticTranslation.plainSourceContext :=
  ⟨Target.Ctx.nil.extendTerm .one, rfl⟩

def invalidSelectionRefl : Source.TypeIncludes
    StaticTranslation.plainSourceContext
      StaticTranslation.invalidTypeSelection
      StaticTranslation.invalidTypeSelection :=
  .refl

/-- Raw source syntax can form reflexivity at an invalid selection, but the
partial compiler does not invent a target member coordinate for it. -/
theorem invalid_member_selection_is_rejected :
    compileIncludes? invalidContext invalidSelectionRefl = none := by
  rfl

end Regression

end DOTCaptureToManySortedFC.Acyclic.EvidenceTranslation
