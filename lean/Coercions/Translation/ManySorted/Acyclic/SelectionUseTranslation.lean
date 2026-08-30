import Coercions.Translation.ManySorted.Acyclic.SelectionTranslation
import Coercions.Translation.ManySorted.Acyclic.EvidenceTranslation

/-!
# Capture-use translation for selected object payloads

Primitive selection exposes the runtime singleton `{x}`.  A source
`Term.HasType.use` derivation is compiled separately: its supplied capture
inclusion becomes one target `Tm.use`, preserving the selected value type and
changing only the immediate-use index.
-/

namespace DOTCaptureToManySortedFC.Acyclic.SelectionUseTranslation

namespace Source

export DOTCapture.Acyclic
  (Scope Path Capture Ty ObjectSig StaticExpr Ctx ExposesObject Includes
    CaptureIncludes Term)

namespace Path
export DOTCapture.Acyclic.Path (selectedCapture valueMemberType)
end Path

namespace ObjectSig
export DOTCapture.Acyclic.ObjectSig (captureUpper)
end ObjectSig

namespace ExposesObject
export DOTCapture.Acyclic.ExposesObject
  (payloadRoot captureUpper valueMember)
end ExposesObject

namespace Term
export DOTCapture.Acyclic.Term (HasType)
end Term

end Source

namespace Target

export ManySortedFC
  (Capture Ty StaticExpr Proposition Evidence Tm)

namespace Evidence
export ManySortedFC.Evidence (Proves)
end Evidence

namespace Tm
export ManySortedFC.Tm (HasType check synth)
end Tm

end Target

namespace Static

export DOTCaptureToManySortedFC.Acyclic.StaticTranslation
  (translateCapture? translateTy? translateExpr?)

end Static

namespace Exposure

export DOTCaptureToManySortedFC.Acyclic.ExposureTranslation
  (TranslatedContext ResolvedExposure)

namespace ResolvedExposure
export DOTCaptureToManySortedFC.Acyclic.ExposureTranslation.ResolvedExposure
  (captureUpperTranslated)
end ResolvedExposure

end Exposure

namespace Primitive

export DOTCaptureToManySortedFC.Acyclic.SelectionTranslation
  (Result term selectedPayloadType compile)

end Primitive

namespace Logical

export DOTCaptureToManySortedFC.Acyclic.EvidenceTranslation
  (CompiledInclusion compileIncludes?)

end Logical

private theorem translateCaptureExpression {scope : Source.Scope}
    {context : Source.Ctx scope} {source : Source.Capture scope}
    {target : Target.Capture (Layout.sig context)}
    (translated : Static.translateCapture? context source = some target) :
    Static.translateExpr? context (.capture source) =
      some (.capture target) := by
  simp [Static.translateExpr?, translated]

private theorem ofTranslateCaptureExpression {scope : Source.Scope}
    {context : Source.Ctx scope} {source : Source.Capture scope}
    {target : Target.Capture (Layout.sig context)}
    (translated : Static.translateExpr? context (.capture source) =
      some (.capture target)) :
    Static.translateCapture? context source = some target := by
  unfold Static.translateExpr? at translated
  obtain ⟨found, foundTranslated, foundEquality⟩ :=
    Option.map_eq_some_iff.mp translated
  have equality : found = target := by
    injection foundEquality
  subst target
  exact foundTranslated

private theorem translatedExpression_unique {scope : Source.Scope}
    {context : Source.Ctx scope} {source : Source.StaticExpr .capture scope}
    {first second : Target.StaticExpr .capture (Layout.sig context)}
    (firstTranslated : Static.translateExpr? context source = some first)
    (secondTranslated : Static.translateExpr? context source = some second) :
    first = second :=
  StaticTranslation.TranslatesExpr.functional
    firstTranslated secondTranslated

/-! ## One explicit source use -/

/-- Proof-carrying composition of primitive selection with one supplied
source capture widening. -/
structure Result {scope : Source.Scope} {context : Source.Ctx scope}
    {translated : Exposure.TranslatedContext context}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (primitive : Primitive.Result translated receiver signature)
    (sourceTargetUse : Source.Capture scope) where
  inclusion : Source.CaptureIncludes context (.singleton receiver)
    sourceTargetUse
  sourceTyping : Source.Term.HasType context (.select receiver .v)
    sourceTargetUse receiver.valueMemberType
  targetUse : Target.Capture (Layout.sig context)
  targetUseTranslated :
    Static.translateCapture? context sourceTargetUse = some targetUse
  typeTranslated : Static.translateTy? context receiver.valueMemberType =
    some (Primitive.selectedPayloadType primitive.resolved)
  evidence : Target.Evidence (.inclusion .capture) (Layout.sig context)
  evidenceTyping : Target.Evidence.Proves translated.target evidence
    (.inclusion
      (.capture (.singleton primitive.resolved.slot.payload))
      (.capture targetUse))
  targetTyping : Target.Tm.HasType translated.target
    (.use (Primitive.term primitive.resolved) evidence)
    targetUse (Primitive.selectedPayloadType primitive.resolved)

/-- The target term produced by one successful use compilation. -/
def Result.term {scope : Source.Scope} {context : Source.Ctx scope}
    {translated : Exposure.TranslatedContext context}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    {primitive : Primitive.Result translated receiver signature}
    {targetUse : Source.Capture scope}
    (result : Result primitive targetUse) : Target.Tm (Layout.sig context) :=
  .use (Primitive.term primitive.resolved) result.evidence

/-- Compile exactly the inclusion supplied by a source `use` rule.  The
compiler remains partial because raw source endpoints may contain unresolved
member selections. -/
noncomputable def compile? {scope : Source.Scope}
    {context : Source.Ctx scope}
    {translated : Exposure.TranslatedContext context}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (primitive : Primitive.Result translated receiver signature)
    {targetUse : Source.Capture scope}
    (inclusion : Source.CaptureIncludes context
      (.singleton receiver) targetUse) :
    Option (Result primitive targetUse) := by
  generalize compiledEquation :
    Logical.compileIncludes? translated inclusion = compiledResult
  cases compiledResult with
  | none => exact none
  | some compiled =>
      rcases compiled with
        ⟨sourceTarget, targetTarget, sourceTranslated, targetTranslated,
          evidence, evidenceTyping⟩
      cases sourceTarget with
      | capture compiledSource =>
          cases targetTarget with
          | capture compiledTarget =>
              have expectedSource := translateCaptureExpression
                primitive.useTranslated
              have sourceEquality := translatedExpression_unique
                sourceTranslated expectedSource
              cases sourceEquality
              have targetUseTranslated :=
                ofTranslateCaptureExpression targetTranslated
              exact some
                { inclusion := inclusion
                  sourceTyping := .use primitive.sourceTyping inclusion
                  targetUse := compiledTarget
                  targetUseTranslated := targetUseTranslated
                  typeTranslated := primitive.typeTranslated
                  evidence := evidence
                  evidenceTyping := evidenceTyping
                  targetTyping := .use primitive.targetTyping
                    evidenceTyping }

/-! ## Total canonical selected-member use -/

/-- The canonical target term for `ExposesObject.valueMember`: primitive
selection followed by the warranted one-way `{x} <= x.C` contraction. -/
def valueMemberTerm {scope : Source.Scope} {context : Source.Ctx scope}
    {translated : Exposure.TranslatedContext context}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (primitive : Primitive.Result translated receiver signature) :
    Target.Tm (Layout.sig context) :=
  .use (Primitive.term primitive.resolved)
    (.captureVariable primitive.resolved.slot.payload)

/-- Total proof-carrying translation of the canonical source
`ExposesObject.valueMember` derivation. -/
structure ValueMemberResult {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translated : Exposure.TranslatedContext context)
    (receiver : Source.Path scope) (signature : Source.ObjectSig scope) where
  primitive : Primitive.Result translated receiver signature
  sourceTyping : Source.Term.HasType context (.select receiver .v)
    receiver.selectedCapture receiver.valueMemberType
  useTranslated : Static.translateCapture? context receiver.selectedCapture =
    some (.cvar primitive.resolved.slot.chi.name)
  typeTranslated : Static.translateTy? context receiver.valueMemberType =
    some (Primitive.selectedPayloadType primitive.resolved)
  evidenceTyping : Target.Evidence.Proves translated.target
    (.captureVariable primitive.resolved.slot.payload)
    (.inclusion
      (.capture (.singleton primitive.resolved.slot.payload))
      (.capture (.cvar primitive.resolved.slot.chi.name)))
  targetTyping : Target.Tm.HasType translated.target
    (valueMemberTerm primitive)
    (.cvar primitive.resolved.slot.chi.name)
    (Primitive.selectedPayloadType primitive.resolved)

/-- Compile `ExposesObject.valueMember` without an optional fallback.  Its
only logical step is exactly `captureVariable` at the receiver payload. -/
noncomputable def compileValueMember {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translated : Exposure.TranslatedContext context)
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (exposes : Source.ExposesObject context receiver signature) :
    ValueMemberResult translated receiver signature := by
  let primitive := Primitive.compile translated exposes
  have evidenceTyping : Target.Evidence.Proves translated.target
      (.captureVariable primitive.resolved.slot.payload)
      (.inclusion
        (.capture (.singleton primitive.resolved.slot.payload))
        (.capture (.cvar primitive.resolved.slot.chi.name))) :=
    .captureVariable primitive.resolved.facts.payloadLookup
  exact
    { primitive := primitive
      sourceTyping := exposes.valueMember
      useTranslated := primitive.resolved.selectedCaptureTranslated
      typeTranslated := primitive.typeTranslated
      evidenceTyping := evidenceTyping
      targetTyping := .use primitive.targetTyping evidenceTyping }

/-! ## Optional widening through the declared upper endpoint -/

/-- Target term for `{x} <= x.C <= E`, retaining both explicit source proof
steps as two target `Tm.use` nodes. -/
def upperBoundTerm {scope : Source.Scope} {context : Source.Ctx scope}
    {translated : Exposure.TranslatedContext context}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (result : ValueMemberResult translated receiver signature) :
    Target.Tm (Layout.sig context) :=
  .use (valueMemberTerm result.primitive)
    (.var result.primitive.resolved.facts.captureUpper)

structure UpperBoundResult {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translated : Exposure.TranslatedContext context)
    (receiver : Source.Path scope) (signature : Source.ObjectSig scope) where
  valueMember : ValueMemberResult translated receiver signature
  sourceTyping : Source.Term.HasType context (.select receiver .v)
    signature.captureUpper receiver.valueMemberType
  useTranslated : Static.translateCapture? context signature.captureUpper =
    some valueMember.primitive.resolved.bounds.captureUpper
  targetTyping : Target.Tm.HasType translated.target
    (upperBoundTerm valueMember)
    valueMember.primitive.resolved.bounds.captureUpper
    (Primitive.selectedPayloadType valueMember.primitive.resolved)

noncomputable def compileUpperBound {scope : Source.Scope}
    {context : Source.Ctx scope}
    (translated : Exposure.TranslatedContext context)
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (exposes : Source.ExposesObject context receiver signature) :
    UpperBoundResult translated receiver signature := by
  let valueMember := compileValueMember translated exposes
  have upperTyping : Target.Evidence.Proves translated.target
      (.var valueMember.primitive.resolved.facts.captureUpper)
      (.inclusion
        (.capture (.cvar valueMember.primitive.resolved.slot.chi.name))
        (.capture valueMember.primitive.resolved.bounds.captureUpper)) :=
    .var valueMember.primitive.resolved.facts.captureUpperLookup
  exact
    { valueMember := valueMember
      sourceTyping := .use (.select exposes)
        (.trans exposes.payloadRoot exposes.captureUpper)
      useTranslated :=
        Exposure.ResolvedExposure.captureUpperTranslated
          valueMember.primitive.resolved
      targetTyping := .use valueMember.targetTyping upperTyping }

/-! ## Executable checker regressions -/

namespace Regression

namespace ExposureRegression

export DOTCaptureToManySortedFC.Acyclic.ExposureTranslation.Regression
  (exactContext exactExposure exactResolved)

end ExposureRegression

noncomputable def exactValueMember :=
  compileValueMember ExposureRegression.exactContext
    ExposureRegression.exactExposure

theorem exact_payload_root_use_compiles :
    (compile? exactValueMember.primitive
      ExposureRegression.exactExposure.payloadRoot).isSome = true := by
  rfl

theorem exact_upper_bound_use_compiles :
    (compile? exactValueMember.primitive
      (.trans ExposureRegression.exactExposure.payloadRoot
        ExposureRegression.exactExposure.captureUpper)).isSome = true := by
  rfl

noncomputable def exact_value_member_has_selected_indices :
    Target.Tm.HasType ExposureRegression.exactContext.target
      (valueMemberTerm exactValueMember.primitive)
      (.cvar exactValueMember.primitive.resolved.slot.chi.name)
      (Primitive.selectedPayloadType
        exactValueMember.primitive.resolved) :=
  exactValueMember.targetTyping

theorem exact_value_member_check_accepts :
    (Target.Tm.check ExposureRegression.exactContext.target
      (valueMemberTerm exactValueMember.primitive)).isSome = true := by
  rfl

theorem exact_value_member_synthesizes_chi :
    Target.Tm.synth ExposureRegression.exactContext.target
        (valueMemberTerm exactValueMember.primitive) =
      some
        (.cvar exactValueMember.primitive.resolved.slot.chi.name,
          Primitive.selectedPayloadType
            exactValueMember.primitive.resolved) := by
  rfl

noncomputable def exactUpperBound :=
  compileUpperBound ExposureRegression.exactContext
    ExposureRegression.exactExposure

theorem exact_upper_bound_check_accepts :
    (Target.Tm.check ExposureRegression.exactContext.target
      (upperBoundTerm exactUpperBound.valueMember)).isSome = true := by
  rfl

theorem exact_upper_bound_synthesizes_E :
    Target.Tm.synth ExposureRegression.exactContext.target
        (upperBoundTerm exactUpperBound.valueMember) =
      some
        (exactUpperBound.valueMember.primitive.resolved.bounds.captureUpper,
          Primitive.selectedPayloadType
            exactUpperBound.valueMember.primitive.resolved) := by
  rfl

end Regression

end DOTCaptureToManySortedFC.Acyclic.SelectionUseTranslation
