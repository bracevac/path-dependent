import Coercions.DOT.Captures.BinderOnly.Typing
import Coercions.ManySortedFC.TermChecker
import Coercions.Translation.ManySorted.BinderOnly.AdapterElaboration
import Coercions.Translation.ManySorted.BinderOnly.LayoutMetatheory
import Coercions.Translation.ManySorted.BinderOnly.ModelElaboration
import Coercions.Translation.ManySorted.BinderOnly.StaticSubstitutionMetatheory

/-!
# Certified term elaboration for binder-only DOT captures

Elaboration follows the supplied source typing derivation.  It never searches
for subtyping, subcapturing, adapters, or interval models: every source
inclusion is compiled to evidence, every source adaptation is compiled to an
explicit adapter, and every source interval realization is compiled to an
explicit target model.

Values and computations retain the source calculus's capture-predictive split.
Every compiled value is a target value with empty immediate use; every
compiled computation has exactly the translation of both its source use and
its source result type.
-/

namespace DOTCaptureToManySortedFC.BinderOnly

/-- A source value elaborated to a target value at its exact translated type. -/
structure CompiledValue
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (value : DOTCapture.BinderOnly.Value scope)
    (type : DOTCapture.BinderOnly.Ty scope) where
  term : ManySortedFC.Tm (sig context)
  isValue : ManySortedFC.Tm.IsValue term
  typing : ManySortedFC.Tm.HasType (translateContext context) term
    .empty (translateTy context type)

/-- A source computation elaborated at its exact translated use and type. -/
structure CompiledTerm
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (term : DOTCapture.BinderOnly.Term scope)
    (use : DOTCapture.BinderOnly.Capture scope)
    (type : DOTCapture.BinderOnly.Ty scope) where
  term : ManySortedFC.Tm (sig context)
  typing : ManySortedFC.Tm.HasType (translateContext context) term
    (translateCapture context use) (translateTy context type)

private theorem translateTy_termWeaken
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (bound type : DOTCapture.BinderOnly.Ty scope) :
    translateTy (context.extendTerm bound)
        (type.weaken (kind := .term)) =
      (translateTy context type).weaken := by
  change
    translateTy (.extend context (.term bound)) type.weaken =
      (translateTy context type).rename ManySortedFC.Rename.succ
  exact translateTy_weaken context (.term bound) type

private theorem translateCapture_termWeaken
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    (bound : DOTCapture.BinderOnly.Ty scope)
    (capture : DOTCapture.BinderOnly.Capture scope) :
    translateCapture (context.extendTerm bound)
        (capture.weaken (kind := .term)) =
      (translateCapture context capture).weaken := by
  change
    translateCapture (.extend context (.term bound)) capture.weaken =
      (translateCapture context capture).rename ManySortedFC.Rename.succ
  exact translateCapture_weaken context (.term bound) capture

private theorem translateTy_staticWeaken
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (interval : DOTCapture.BinderOnly.Interval sort scope)
    (type : DOTCapture.BinderOnly.Ty scope) :
    translateTy (context.extendStatic interval)
        (type.weaken (kind := .static sort)) =
      (translateTy context type).rename
        (ManySortedFC.Rename.weakenStatic [translateSort sort]
          (intervalRelations interval)) := by
  change
    translateTy (.extend context (.static interval)) type.weaken =
      (translateTy context type).rename
        (ManySortedFC.Rename.weakenStatic [translateSort sort]
          (intervalRelations interval))
  exact translateTy_weaken context (.static interval) type

private theorem translateCapture_staticWeaken
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (interval : DOTCapture.BinderOnly.Interval sort scope)
    (capture : DOTCapture.BinderOnly.Capture scope) :
    translateCapture (context.extendStatic interval)
        (capture.weaken (kind := .static sort)) =
      (translateCapture context capture).rename
        (ManySortedFC.Rename.weakenStatic [translateSort sort]
          (intervalRelations interval)) := by
  change
    translateCapture (.extend context (.static interval)) capture.weaken =
      (translateCapture context capture).rename
        (ManySortedFC.Rename.weakenStatic [translateSort sort]
          (intervalRelations interval))
  exact translateCapture_weaken context (.static interval) capture

mutual

/-- Total derivation-directed value elaboration. -/
def compileValue
    {scope : DOTCapture.BinderOnly.Sig}
    {context : DOTCapture.BinderOnly.Ctx scope}
    {value : DOTCapture.BinderOnly.Value scope}
    {type : DOTCapture.BinderOnly.Ty scope}
    (typing : DOTCapture.BinderOnly.Value.HasType context value type) :
    CompiledValue context value type :=
  match typing with
  | @DOTCapture.BinderOnly.Value.HasType.var _ context name => by
      let targetName := termVar context name
      have targetTyping :=
        ManySortedFC.Tm.HasType.var
          (context := translateContext context) targetName
      have lookup := translate_lookupTerm context name
      change
        (translateContext context).lookup targetName =
          ManySortedFC.Binding.term
            (translateTy context (context.lookupTerm name)) at lookup
      refine
        { term := .var targetName
          isValue := .var
          typing := ?_ }
      rw [lookup] at targetTyping
      simpa [targetName, translatePath] using targetTyping

  | @DOTCapture.BinderOnly.Value.HasType.unit _ _ =>
      { term := .unit
        isValue := .unit
        typing := .unit }

  | @DOTCapture.BinderOnly.Value.HasType.lam _ context domain codomain
      body bodyUse closure bodyTyping captures => by
      let compiledBody := compileTerm bodyTyping
      let compiledCaptures := compileIncludesTotal captures
      let targetBodyTyping : ManySortedFC.Tm.HasType
          ((translateContext context).extendTerm (translateTy context domain))
          compiledBody.term (translateCapture (context.extendTerm domain) bodyUse)
          (translateTy context codomain).weaken := by
        have translated := compiledBody.typing
        rw [translateTy_termWeaken context domain codomain] at translated
        exact translated
      let targetCapturesTyping : ManySortedFC.Evidence.Proves
          ((translateContext context).extendTerm (translateTy context domain))
          compiledCaptures.evidence
          (.inclusion
            (.capture (translateCapture (context.extendTerm domain) bodyUse))
            (.capture
              (.union (translateCapture context closure).weaken
                (.singleton .here)))) := by
        have translated := compiledCaptures.typing
        simp only [translateExpr, translateCapture, translatePath]
          at translated
        rw [translateCapture_termWeaken context domain closure] at translated
        exact translated
      exact
        { term := .lam (translateTy context domain)
            (translateTy context codomain) (translateCapture context closure)
            compiledBody.term compiledCaptures.evidence
          isValue := .lam
          typing := .lam targetBodyTyping targetCapturesTyping }

  | @DOTCapture.BinderOnly.Value.HasType.staticLam _ context sort interval
      body bodyType closure bodyTyping captures => by
      let compiledBody := compileValue bodyTyping
      let compiledCaptures := compileIncludesTotal captures
      let targetCapturesTyping : ManySortedFC.Evidence.Proves
          ((translateContext context).extendTheory
            (translateInterval context interval))
          compiledCaptures.evidence
          (.inclusion
            (.capture
              (translateTy (context.extendStatic interval) bodyType).outerCapture)
            (.capture
              ((translateCapture context closure).rename
                (ManySortedFC.Rename.weakenStatic [translateSort sort]
                  (intervalRelations interval))))) := by
        have translated := compiledCaptures.typing
        simp only [translateExpr] at translated
        rw [← translateTy_outerCapture] at translated
        rw [translateCapture_staticWeaken context interval closure] at translated
        exact translated
      exact
        { term := .slam (translateInterval context interval)
            (translateCapture context closure) compiledBody.term
            compiledCaptures.evidence
          isValue := .slam compiledBody.isValue
          typing := .slam compiledBody.isValue compiledBody.typing
            targetCapturesTyping }

  | @DOTCapture.BinderOnly.Value.HasType.pack _ context sort interval
      payloadType witness payload closure satisfaction payloadTyping
      captures => by
      let compiledModel := compileModelTotal satisfaction
      let compiledPayload := compileValue payloadTyping
      let compiledCaptures := compileIncludesTotal captures
      let targetSymbols :=
        TargetIntervalModel.symbols (translateExpr context witness)
      have instantiation :=
        translateTy_instantiateStatic context interval payloadType witness
      let targetPayloadTyping : ManySortedFC.Tm.HasType
          (translateContext context) compiledPayload.term .empty
          ((translateTy (context.extendStatic interval) payloadType).instantiateStatic
            targetSymbols) := by
        rw [instantiation]
        exact compiledPayload.typing
      let targetCapturesTyping : ManySortedFC.Evidence.Proves
          (translateContext context) compiledCaptures.evidence
          (.inclusion
            (.capture
              ((translateTy (context.extendStatic interval) payloadType).instantiateStatic
                targetSymbols).outerCapture)
            (.capture (translateCapture context closure))) := by
        rw [instantiation, translateTy_outerCapture]
        simpa [translateExpr] using compiledCaptures.typing
      exact
        { term := .pack (translateInterval context interval)
            (translateTy (context.extendStatic interval) payloadType)
            (translateCapture context closure) targetSymbols
            compiledModel.evidence compiledPayload.term
            compiledCaptures.evidence
          isValue := .pack compiledPayload.isValue
          typing := .pack compiledModel.satisfies compiledPayload.isValue
            targetPayloadTyping targetCapturesTyping }

  | @DOTCapture.BinderOnly.Value.HasType.adapt _ context value source target
      valueTyping adaptation => by
      let compiledValue := compileValue valueTyping
      let compiledAdapter := compileAdapts adaptation
      exact
        { term := .adapt compiledValue.term compiledAdapter.adapter
          isValue := .adapt compiledValue.isValue
          typing := .adapt compiledValue.isValue compiledValue.typing
            compiledAdapter.typing }

/-- Total derivation-directed computation elaboration. -/
def compileTerm
    {scope : DOTCapture.BinderOnly.Sig}
    {context : DOTCapture.BinderOnly.Ctx scope}
    {term : DOTCapture.BinderOnly.Term scope}
    {use : DOTCapture.BinderOnly.Capture scope}
    {type : DOTCapture.BinderOnly.Ty scope}
    (typing : DOTCapture.BinderOnly.Term.HasType context term use type) :
    CompiledTerm context term use type :=
  match typing with
  | @DOTCapture.BinderOnly.Term.HasType.ret _ _ value type valueTyping => by
      let compiledValue := compileValue valueTyping
      exact
        { term := compiledValue.term
          typing := compiledValue.typing }

  | @DOTCapture.BinderOnly.Term.HasType.app _ context function argument
      functionType domain codomain functionTyping functionShape
      argumentTyping => by
      let compiledFunction := compileValue functionTyping
      let compiledArgument := compileValue argumentTyping
      have targetShape :
          (translateTy context functionType).stripCapture =
            .arr (translateTy context domain) (translateTy context codomain) := by
        rw [translateTy_stripCapture]
        exact congrArg (translateTy context) functionShape
      let targetTyping : ManySortedFC.Tm.HasType
          (translateContext context)
          (.app compiledFunction.term compiledArgument.term)
          (.union (translateTy context functionType).outerCapture
            (translateTy context domain).outerCapture)
          (translateTy context codomain) :=
        .app compiledFunction.typing targetShape compiledArgument.typing
      exact
        { term := .app compiledFunction.term compiledArgument.term
          typing := by
            simpa only [translateCapture, translateTy_outerCapture] using
              targetTyping }

  | @DOTCapture.BinderOnly.Term.HasType.let' _ context result bound rhs body
      rhsUse bodyUse bodyOuterUse rhsTyping bodyTyping discharge => by
      let compiledRhs := compileTerm rhsTyping
      let compiledBody := compileTerm bodyTyping
      let compiledDischarge := compileIncludesTotal discharge
      let targetBodyTyping : ManySortedFC.Tm.HasType
          ((translateContext context).extendTerm (translateTy context bound))
          compiledBody.term (translateCapture (context.extendTerm bound) bodyUse)
          (translateTy context result).weaken := by
        have translated := compiledBody.typing
        rw [translateTy_termWeaken context bound result] at translated
        exact translated
      let targetDischargeTyping : ManySortedFC.Evidence.Proves
          ((translateContext context).extendTerm (translateTy context bound))
          compiledDischarge.evidence
          (.inclusion
            (.capture (translateCapture (context.extendTerm bound) bodyUse))
            (.capture (translateCapture context bodyOuterUse).weaken)) := by
        have translated := compiledDischarge.typing
        simp only [translateExpr] at translated
        rw [translateCapture_termWeaken context bound bodyOuterUse] at translated
        exact translated
      exact
        { term := .let' (translateTy context result)
            (translateCapture context bodyOuterUse) compiledRhs.term
            compiledBody.term compiledDischarge.evidence
          typing := .let' compiledRhs.typing targetBodyTyping
            targetDischargeTyping }

  | @DOTCapture.BinderOnly.Term.HasType.staticApp _ context sort interval
      function argument functionType bodyType functionTyping functionShape
      satisfaction => by
      let compiledFunction := compileValue functionTyping
      let compiledModel := compileModelTotal satisfaction
      let targetSymbols :=
        TargetIntervalModel.symbols (translateExpr context argument)
      have targetShape :
          (translateTy context functionType).stripCapture =
            .forallT (translateInterval context interval)
              (translateTy (context.extendStatic interval) bodyType) := by
        rw [translateTy_stripCapture]
        exact congrArg (translateTy context) functionShape
      have instantiation :=
        translateTy_instantiateStatic context interval bodyType argument
      let targetTyping : ManySortedFC.Tm.HasType
          (translateContext context)
          (.sapp (translateInterval context interval) compiledFunction.term
            targetSymbols compiledModel.evidence)
          (translateTy context functionType).outerCapture
          ((translateTy (context.extendStatic interval) bodyType).instantiateStatic
            targetSymbols) :=
        .sapp compiledFunction.typing targetShape compiledModel.satisfies
      exact
        { term := .sapp (translateInterval context interval)
            compiledFunction.term targetSymbols compiledModel.evidence
          typing := by
            rw [instantiation] at targetTyping
            simpa only [translateTy_outerCapture] using targetTyping }

  | @DOTCapture.BinderOnly.Term.HasType.«open» _ context sort interval
      payloadType result package body packageType bodyUse bodyOuterUse
      packageTyping packageShape bodyTyping discharge => by
      let compiledPackage := compileValue packageTyping
      let compiledBody := compileTerm bodyTyping
      let compiledDischarge := compileIncludesTotal discharge
      have targetShape :
          (translateTy context packageType).stripCapture =
            .existsT (translateInterval context interval)
              (translateTy (context.extendStatic interval) payloadType) := by
        rw [translateTy_stripCapture]
        exact congrArg (translateTy context) packageShape
      let targetBodyTyping : ManySortedFC.Tm.HasType
          (((translateContext context).extendTheory
              (translateInterval context interval)).extendTerm
            (translateTy (context.extendStatic interval) payloadType))
          compiledBody.term
          (translateCapture
            ((context.extendStatic interval).extendTerm payloadType) bodyUse)
          (((translateTy context result).rename
            (ManySortedFC.Rename.weakenStatic [translateSort sort]
              (intervalRelations interval))).weaken) := by
        have translated := compiledBody.typing
        rw [translateTy_termWeaken (context.extendStatic interval)
          payloadType (result.weaken (kind := .static sort))] at translated
        rw [translateTy_staticWeaken context interval result] at translated
        exact translated
      let targetDischargeTyping : ManySortedFC.Evidence.Proves
          (((translateContext context).extendTheory
              (translateInterval context interval)).extendTerm
            (translateTy (context.extendStatic interval) payloadType))
          compiledDischarge.evidence
          (.inclusion
            (.capture
              (translateCapture
                ((context.extendStatic interval).extendTerm payloadType)
                bodyUse))
            (.capture
              (.union
                ((translateCapture context bodyOuterUse).rename
                  (ManySortedFC.Rename.weakenStatic [translateSort sort]
                    (intervalRelations interval))).weaken
                (.singleton .here)))) := by
        have translated := compiledDischarge.typing
        simp only [translateExpr, translateCapture, translatePath]
          at translated
        rw [translateCapture_termWeaken (context.extendStatic interval)
          payloadType (bodyOuterUse.weaken (kind := .static sort))] at translated
        rw [translateCapture_staticWeaken context interval bodyOuterUse] at translated
        exact translated
      exact
        { term := .«open» (translateInterval context interval)
            (translateTy (context.extendStatic interval) payloadType)
            (translateTy context result) (translateCapture context bodyOuterUse)
            compiledPackage.term compiledBody.term compiledDischarge.evidence
          typing := by
            have targetTyping :=
              ManySortedFC.Tm.HasType.«open» compiledPackage.typing
                targetShape targetBodyTyping targetDischargeTyping
            simpa only [translateCapture, translateTy_outerCapture] using
              targetTyping }

  | @DOTCapture.BinderOnly.Term.HasType.use _ context term sourceUse
      targetUse type termTyping inclusion => by
      let compiledTerm := compileTerm termTyping
      let compiledInclusion := compileIncludesTotal inclusion
      exact
        { term := .use compiledTerm.term compiledInclusion.evidence
          typing := .use compiledTerm.typing compiledInclusion.typing }

end

namespace TermElaborationExamples

open DOTCapture.BinderOnly.TypingExamples

/-- Closed identity: ordinary closure capture and body-use discharge. -/
def compiledIdentity := compileValue identityTyping

/-- A free function is let-bound and its local use is discharged back to the
free capability retained by the binding. -/
def compiledLetBoundCall := compileTerm letBoundCallTyping

/-- Invoking a function parameter is discharged to the parameter singleton,
so the enclosing lambda retains no ambient closure. -/
def compiledCallsParameter := compileValue callsParameterTyping

/-- Applying that closure-empty lambda still charges the capture retained by
its function-typed argument. -/
def compiledCallsParameterApplication :=
  compileTerm callsParameterApplicationChargesDomain

/-- Static application whose result genuinely substitutes the abstract type
name rather than returning a vacuous body type. -/
def compiledStaticAbstractOne := compileTerm applyStaticAbstractOneTyping

/-- Capture polymorphism substitutes through both capturing annotations of
the function domain and codomain. -/
def compiledCaptureIdentity := compileTerm applyCaptureIdentityTyping

/-- Existential opening exposes a hidden abstract type, adapts the payload by
its upper evidence, and discharges the local body use. -/
def compiledPackageOpen := compileTerm openPackedAbstractOneTyping

/-- The simplest generated target syntax is accepted by the structural target
checker at exactly its certified capture and type. -/
@[simp]
theorem identity_checker_accepts :
    ManySortedFC.Tm.synth ManySortedFC.Ctx.nil
        compiledIdentity.term =
      some (.empty,
        translateTy DOTCapture.BinderOnly.Ctx.nil
          (.capturing .empty (.arr .one .one))) := by
  rfl

@[simp]
theorem let_bound_call_checker_accepts :
    ManySortedFC.Tm.synth
        (translateContext
          (DOTCapture.BinderOnly.Ctx.nil.extendTerm closedUnaryType))
        compiledLetBoundCall.term =
      some
        (translateCapture
          (DOTCapture.BinderOnly.Ctx.nil.extendTerm closedUnaryType)
          (.singleton (.var .here)),
        translateTy
          (DOTCapture.BinderOnly.Ctx.nil.extendTerm closedUnaryType) .one) := by
  rfl

@[simp]
theorem calls_parameter_checker_accepts :
    ManySortedFC.Tm.synth (translateContext outerCapabilityContext)
        compiledCallsParameter.term =
      some (.empty,
        .capturing .empty
          (.arr
            (.capturing (.singleton .here) (.arr .one .one))
            .one)) := by
  rfl

@[simp]
theorem calls_parameter_application_checker_accepts :
    ManySortedFC.Tm.synth (translateContext outerCapabilityContext)
        compiledCallsParameterApplication.term =
      some (.singleton .here, .one) := by
  rfl

@[simp]
theorem static_abstract_one_checker_accepts :
    ManySortedFC.Tm.synth ManySortedFC.Ctx.nil
        compiledStaticAbstractOne.term =
      some (.empty, .one) := by
  rfl

@[simp]
theorem capture_identity_checker_accepts :
    ManySortedFC.Tm.synth ManySortedFC.Ctx.nil
        compiledCaptureIdentity.term =
      some (.empty,
        .capturing .empty
          (.arr (.capturing .empty .one) (.capturing .empty .one))) := by
  rfl

@[simp]
theorem package_open_checker_accepts :
    ManySortedFC.Tm.synth ManySortedFC.Ctx.nil
        compiledPackageOpen.term =
      some (.empty, .one) := by
  rfl

end TermElaborationExamples

end DOTCaptureToManySortedFC.BinderOnly
