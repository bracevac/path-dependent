import Coercions.Translation.ManySorted.Acyclic.ValueTranslation
import Coercions.Translation.ManySorted.Acyclic.SelectionTranslation
import Coercions.Translation.ManySorted.Acyclic.EvidenceTranslation

/-!
# Captured-DOT term translation

The acyclic source has three derivation forms.  Returning a value contributes
no target marker, primitive `x.v` selection uses the receiver's resolved
payload coordinate, and each source capture-use rule contributes exactly one
explicit target `Tm.use` node carrying the translated inclusion evidence.
-/

namespace DOTCaptureToManySortedFC.Acyclic.TermTranslation

namespace Source

export DOTCapture.Acyclic
  (Scope Path Capture Ty StaticExpr Ctx Value Term ObjectSig ExposesObject
    CaptureIncludes)

namespace Path
export DOTCapture.Acyclic.Path (selectedType selectedCapture valueMemberType)
end Path

namespace Term
export DOTCapture.Acyclic.Term (HasType)
end Term

end Source

namespace Target

export ManySortedFC
  (Capture Ty StaticExpr Evidence Tm)

namespace Evidence
export ManySortedFC.Evidence (Proves)
end Evidence

namespace Tm
export ManySortedFC.Tm (HasType check synth)
end Tm

end Target

namespace Context

export DOTCaptureToManySortedFC.Acyclic.RuntimeContext
  (Ready)

end Context

namespace Static

export DOTCaptureToManySortedFC.Acyclic.StaticTranslation
  (translateCapture? translateTy? translateExpr?)

end Static

namespace Values

export DOTCaptureToManySortedFC.Acyclic.ValueTranslation
  (CompiledValue compileValue?)

end Values

namespace Selection

export DOTCaptureToManySortedFC.Acyclic.SelectionTranslation
  (Result selectedPayloadType term compile)

end Selection

namespace Logical

export DOTCaptureToManySortedFC.Acyclic.EvidenceTranslation
  (CompiledInclusion compileIncludes?)

end Logical

/-! ## Proof-carrying result -/

/-- A target term together with exact translations of both source typing
indices and its declarative many-sorted FC typing derivation. -/
structure CompiledTerm {scope : Source.Scope} {context : Source.Ctx scope}
    (ready : Context.Ready context) (sourceTerm : Source.Term scope)
    (sourceUse : Source.Capture scope) (sourceType : Source.Ty scope) where
  sourceTyping : Source.Term.HasType context sourceTerm sourceUse sourceType
  targetUse : Target.Capture (Layout.sig context)
  targetType : Target.Ty (Layout.sig context)
  useTranslated :
    Static.translateCapture? context sourceUse = some targetUse
  typeTranslated :
    Static.translateTy? context sourceType = some targetType
  term : Target.Tm (Layout.sig context)
  typing : Target.Tm.HasType ready.target term targetUse targetType

/-! ## Exact endpoint alignment -/

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
    {context : Source.Ctx scope}
    {source : Source.StaticExpr .capture scope}
    {first second : Target.StaticExpr .capture (Layout.sig context)}
    (firstTranslated : Static.translateExpr? context source = some first)
    (secondTranslated : Static.translateExpr? context source = some second) :
    first = second :=
  StaticTranslation.TranslatesExpr.functional
    firstTranslated secondTranslated

/-! ## Individual source rules -/

/-- Primitive selection is total once its source exposure and translated
runtime context are available. -/
noncomputable def compileSelect {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Context.Ready context)
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

/-- Add exactly one target `Tm.use` for one source capture-use rule.  Failure
can only come from translating or resolving one of the raw source inclusion
endpoints. -/
noncomputable def compileUse? {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Context.Ready context}
    {sourceTerm : Source.Term scope}
    {sourceUse targetUse : Source.Capture scope}
    {sourceType : Source.Ty scope}
    (inner : CompiledTerm ready sourceTerm sourceUse sourceType)
    (inclusion : Source.CaptureIncludes context sourceUse targetUse) :
    Option (CompiledTerm ready sourceTerm targetUse sourceType) := by
  generalize compiledEquation :
    Logical.compileIncludes? ready.translated inclusion = compiledResult
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
              have expectedSource :=
                translateCaptureExpression inner.useTranslated
              have sourceEquality := translatedExpression_unique
                sourceTranslated expectedSource
              cases sourceEquality
              have targetUseTranslated :=
                ofTranslateCaptureExpression targetTranslated
              exact some
                { sourceTyping := .use inner.sourceTyping inclusion
                  targetUse := compiledTarget
                  targetType := inner.targetType
                  useTranslated := targetUseTranslated
                  typeTranslated := inner.typeTranslated
                  term := .use inner.term evidence
                  typing := .use inner.typing evidenceTyping }

/-! ## Derivation-directed compiler -/

/-- Translate captured-DOT term typing derivations without proof search.
The only optional branches are inherited from raw source endpoint
translation in value construction and capture-use evidence compilation. -/
noncomputable def compileTerm? {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Context.Ready context)
    {sourceTerm : Source.Term scope} {sourceUse : Source.Capture scope}
    {sourceType : Source.Ty scope}
    (derivation : Source.Term.HasType context sourceTerm sourceUse sourceType) :
    Option (CompiledTerm ready sourceTerm sourceUse sourceType) := by
  induction derivation with
  | ret valueTyping =>
      exact (Values.compileValue? ready valueTyping).map fun valueCompiled =>
        { sourceTyping := .ret valueTyping
          targetUse := .empty
          targetType := valueCompiled.targetType
          useTranslated := rfl
          typeTranslated := valueCompiled.typeTranslated
          term := valueCompiled.term
          typing := valueCompiled.typing }
  | select exposes =>
      exact some (compileSelect ready exposes)
  | use termTyping inclusion induction =>
      exact do
        let inner ← induction
        compileUse? inner inclusion

/-! ## Exact-object regressions -/

namespace Regression

namespace RuntimeRegression

export DOTCaptureToManySortedFC.Acyclic.RuntimeContext
  (nil exactObjectReady)

end RuntimeRegression

namespace ExposureRegression

export DOTCaptureToManySortedFC.Acyclic.ExposureTranslation.Regression
  (ExactSignature ExactSourceContext exactExposure)

end ExposureRegression

namespace SourceExamples

export DOTCapture.Acyclic.Examples
  (exactSignature exactObject exactObjectTyping)

end SourceExamples

abbrev exactReceiver := StaticTranslation.exactReceiver
abbrev exactSlot := Layout.newestReceiverSlot []

/-! ### Return-marker erasure -/

def unitReturnTyping : Source.Term.HasType (.nil : Source.Ctx 0)
    (.ret .unit) .empty .one :=
  .ret .unit

theorem unit_return_compiles :
    (compileTerm? RuntimeRegression.nil unitReturnTyping).isSome = true := by
  rfl

noncomputable def unitReturnResult :=
  (compileTerm? RuntimeRegression.nil unitReturnTyping).get
    unit_return_compiles

theorem unit_return_has_no_target_marker :
    unitReturnResult.term = (.unit : Target.Tm []) := by
  rfl

/-- Returning a formed captured-DOT object delegates to value compilation;
the source `ret` marker adds no wrapper around the generated package. -/
def exactObjectReturnTyping : Source.Term.HasType (.nil : Source.Ctx 0)
    (.ret SourceExamples.exactObject) .empty
    (.capturing .empty (.object SourceExamples.exactSignature)) :=
  .ret SourceExamples.exactObjectTyping

theorem exact_object_return_compiles :
    (compileTerm? RuntimeRegression.nil
      exactObjectReturnTyping).isSome = true := by
  rfl

noncomputable def exactObjectReturnResult :=
  (compileTerm? RuntimeRegression.nil exactObjectReturnTyping).get
    exact_object_return_compiles

theorem exact_object_return_has_exact_package_type :
    exactObjectReturnResult.targetUse =
        (.empty : Target.Capture []) ∧
      exactObjectReturnResult.targetType =
        ObjectEncoding.objectType ObjectEncoding.exactBounds := by
  constructor <;> rfl

theorem exact_object_return_checker_accepts :
    (Target.Tm.check RuntimeRegression.nil.target
      exactObjectReturnResult.term).isSome = true := by
  rfl

theorem exact_object_return_synthesizes_package_type :
    Target.Tm.synth RuntimeRegression.nil.target
        exactObjectReturnResult.term =
      some
        ((.empty : Target.Capture []),
          ObjectEncoding.objectType ObjectEncoding.exactBounds) := by
  rfl

/-! ### Genuine `x.A`, `x.C`, and `x.v` selection -/

def exactPrimitiveTyping : Source.Term.HasType
    ExposureRegression.ExactSourceContext
    (.select exactReceiver .v) (.singleton exactReceiver)
    exactReceiver.valueMemberType :=
  .select ExposureRegression.exactExposure

theorem exact_primitive_compiles :
    (compileTerm? RuntimeRegression.exactObjectReady
      exactPrimitiveTyping).isSome = true := by
  rfl

noncomputable def exactPrimitiveResult :=
  (compileTerm? RuntimeRegression.exactObjectReady
    exactPrimitiveTyping).get exact_primitive_compiles

/-- The primitive read charges the receiver payload root and returns exactly
`(x.A)^{x.C}` translated through the receiver's shared alpha/chi slot. -/
theorem exact_primitive_has_xA_xC_xv_indices :
    exactPrimitiveResult.targetUse =
        (.singleton exactSlot.payload : Target.Capture _) ∧
      exactPrimitiveResult.targetType =
        (.capturing (.cvar exactSlot.chi.name)
          (.tvar exactSlot.alpha.name) : Target.Ty _) := by
  constructor <;> rfl

theorem exact_primitive_checker_accepts :
    (Target.Tm.check RuntimeRegression.exactObjectReady.target
      exactPrimitiveResult.term).isSome = true := by
  rfl

theorem exact_primitive_synthesizes_xA_xC :
    Target.Tm.synth RuntimeRegression.exactObjectReady.target
        exactPrimitiveResult.term =
      some
        ((.singleton exactSlot.payload : Target.Capture _),
          (.capturing (.cvar exactSlot.chi.name)
            (.tvar exactSlot.alpha.name) : Target.Ty _)) := by
  rfl

/-! ### One source use becomes one additional target use -/

def exactSelectedUseTyping : Source.Term.HasType
    ExposureRegression.ExactSourceContext
    (.select exactReceiver .v) exactReceiver.selectedCapture
    exactReceiver.valueMemberType :=
  .use (.select ExposureRegression.exactExposure)
    ExposureRegression.exactExposure.payloadRoot

theorem exact_selected_use_compiles :
    (compileTerm? RuntimeRegression.exactObjectReady
      exactSelectedUseTyping).isSome = true := by
  rfl

noncomputable def exactSelectedUseResult :=
  (compileTerm? RuntimeRegression.exactObjectReady
    exactSelectedUseTyping).get exact_selected_use_compiles

noncomputable def exactSelection :=
  Selection.compile RuntimeRegression.exactObjectReady.translated
    ExposureRegression.exactExposure

theorem exact_selected_use_is_one_explicit_widening :
    exactSelectedUseResult.term =
      .use (Selection.term exactSelection.resolved)
        (.captureVariable exactSelection.resolved.slot.payload) := by
  rfl

theorem exact_selected_use_has_xA_xC_xv_indices :
    exactSelectedUseResult.targetUse =
        (.cvar exactSlot.chi.name : Target.Capture _) ∧
      exactSelectedUseResult.targetType =
        (.capturing (.cvar exactSlot.chi.name)
          (.tvar exactSlot.alpha.name) : Target.Ty _) := by
  constructor <;> rfl

theorem exact_selected_use_checker_accepts :
    (Target.Tm.check RuntimeRegression.exactObjectReady.target
      exactSelectedUseResult.term).isSome = true := by
  rfl

theorem exact_selected_use_synthesizes_xC :
    Target.Tm.synth RuntimeRegression.exactObjectReady.target
        exactSelectedUseResult.term =
      some
        ((.cvar exactSlot.chi.name : Target.Capture _),
          (.capturing (.cvar exactSlot.chi.name)
            (.tvar exactSlot.alpha.name) : Target.Ty _)) := by
  rfl

/-! A transitive source inclusion is retained inside the one new evidence
tree; it does not introduce one target term node per logical sub-proof. -/

def exactUpperUseTyping : Source.Term.HasType
    ExposureRegression.ExactSourceContext
    (.select exactReceiver .v)
    ExposureRegression.ExactSignature.weaken.captureUpper
    exactReceiver.valueMemberType :=
  .use (.select ExposureRegression.exactExposure)
    (.trans ExposureRegression.exactExposure.payloadRoot
      ExposureRegression.exactExposure.captureUpper)

theorem exact_upper_use_compiles :
    (compileTerm? RuntimeRegression.exactObjectReady
      exactUpperUseTyping).isSome = true := by
  rfl

noncomputable def exactUpperUseResult :=
  (compileTerm? RuntimeRegression.exactObjectReady
    exactUpperUseTyping).get exact_upper_use_compiles

theorem exact_upper_use_is_one_explicit_widening :
    exactUpperUseResult.term =
      .use (Selection.term exactSelection.resolved)
        (.inclusionTrans
          (.captureVariable exactSelection.resolved.slot.payload)
          (.var exactSelection.resolved.facts.captureUpper)) := by
  rfl

/-! Two nested source rules recurse to two additional term nodes.  This is
distinct from the prior regression, whose one source rule contains a
transitive logical certificate but still adds only one term node. -/

def exactNestedUseTyping : Source.Term.HasType
    ExposureRegression.ExactSourceContext
    (.select exactReceiver .v)
    ExposureRegression.ExactSignature.weaken.captureUpper
    exactReceiver.valueMemberType :=
  .use exactSelectedUseTyping ExposureRegression.exactExposure.captureUpper

theorem exact_nested_use_compiles :
    (compileTerm? RuntimeRegression.exactObjectReady
      exactNestedUseTyping).isSome = true := by
  rfl

noncomputable def exactNestedUseResult :=
  (compileTerm? RuntimeRegression.exactObjectReady
    exactNestedUseTyping).get exact_nested_use_compiles

theorem exact_nested_use_has_two_explicit_widenings :
    exactNestedUseResult.term =
      .use
        (.use (Selection.term exactSelection.resolved)
          (.captureVariable exactSelection.resolved.slot.payload))
        (.var exactSelection.resolved.facts.captureUpper) := by
  rfl

theorem exact_nested_use_synthesizes_empty :
    Target.Tm.synth RuntimeRegression.exactObjectReady.target
        exactNestedUseResult.term =
      some
        ((.empty : Target.Capture _),
          (.capturing (.cvar exactSlot.chi.name)
            (.tvar exactSlot.alpha.name) : Target.Ty _)) := by
  rfl

end Regression

end DOTCaptureToManySortedFC.Acyclic.TermTranslation
