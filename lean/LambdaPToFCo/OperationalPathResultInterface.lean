import LambdaPToFCo.OperationalExpectedResult
import LambdaPToFCo.OperationalLexicalFunctionCompatibility
import LambdaPToFCo.OperationalApplicationPathCoherence
import LambdaPToFCo.OperationalTypedPathCoherence

/-!
# Complete result interfaces for resolved source paths

Non-function paths obtain their result interface from the generated raw
ordinary slot.  Function paths additionally consume the current lexical
function provenance: the retained native closure is wrapped by exactly the
structural arrow casts described by `FunctionPathSpine` and re-exposed at the
final typed-path endpoint.

This module is deliberately independent of recursive store coherence.  A
higher environment theorem supplies the base `FunctionResultProvenance`;
the definitions below perform only target-facing adaptation.
-/

namespace LambdaPToFCo
namespace OperationalPathResultInterface

open SystemFCo
open StaticTranslation
open OperationalEnvironment
open OperationalBindingView
open OperationalApplicationSpine
open OperationalStoreEnvironment
open OperationalPathCoherence
open OperationalPathCoherenceGenerated
open OperationalFunctionPathSpine
open OperationalTypedPathView
open OperationalTypedPathCoherence
open OperationalLexicalFunctionCompatibility
open OperationalFunctionResultProvenance
open OperationalExpectedResult

private def sourceDomain : LambdaPFC.Ty n -> LambdaPFC.Ty n
  | .Fun domain _ => domain
  | _ => .Top

/-- Complete interface for a generated noncanonical path endpoint. -/
noncomputable def ofNonCanonical
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path path) sourceType}
    (admissible : OperationalAdmissibility.OperationallyAdmissible typing)
    (shape : NonCanonicalResultShape sourceType)
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : StorePathCoherence store) :
    ResultInterface
      (sourceBoundary scope typing.typeWf closing (storeArguments store)) :=
  let target := OperationalTypedPathView.build admissible store coherent
  { view := target.view
    accepted :=
      SourceResultAcceptance.ofNonCanonical scope typing.typeWf shape closing
        target.view (storeArguments store)
        (OperationalTypedPathCoherence.build_rawSlot admissible store
          coherent) }

@[simp] theorem ofNonCanonical_argument
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path path) sourceType}
    (admissible : OperationalAdmissibility.OperationallyAdmissible typing)
    (shape : NonCanonicalResultShape sourceType)
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : StorePathCoherence store) :
    (ofNonCanonical admissible shape store coherent).view.argument =
      (OperationalTypedPathView.build admissible store coherent).view.argument :=
  rfl

/-- A function result retained at the base lexical slot is transported
through the exact function-path cast spine to the final generated path view.
The source closure and body remain unchanged; only its wrapper-aware target
image is replaced. -/
noncomputable def ofFunctionPath
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {domain codomain : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path path)
      (.Fun domain codomain.weaken)}
    (spine : FunctionPathSpine typing)
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : StorePathCoherence store)
    (base : FunctionResultProvenance scope spine.baseDomainWf closing
      (store.lookup (typedPathReferent typing)).slot.behavior) :
    ResultInterface
      (sourceBoundary scope typing.typeWf closing (storeArguments store)) := by
  let target := OperationalTypedPathView.buildFunctionPath spine store coherent
  let compatible : LexicalFunctionCompatibility store spine :=
    { image := base.closure.image
      domainPlan_eq := base.domainPlan_eq }
  let endpoint := compatible.endpointImage coherent target
  have compatibleBaseRaw :
      {outerPlan : Interface.BinderPlan []} ->
      (outer : EliminationView outerPlan) ->
      (outerPlan_eq :
        outerPlan = closedPlan scope closing spine.baseDomainWf) ->
      RawSlot outer ->
      RawSlot
        ((compatible.baseEvidence outer
          outerPlan_eq).toArgumentView.elimination) := by
    intro outerPlan outer outerPlan_eq outerRaw
    exact base.closure.argumentRaw outer
      (outerPlan_eq.trans compatible.domainPlan_eq) outerRaw
  have endpointArgumentRaw :
      {outerPlan : Interface.BinderPlan []} ->
      (outer : EliminationView outerPlan) ->
      (outerPlan_eq : outerPlan = endpoint.domainPlan) ->
      RawSlot outer ->
      RawSlot
        ((endpoint.argumentEvidence outer
          outerPlan_eq).toArgumentView.elimination) := by
    intro outerPlan outer outerPlan_eq outerRaw
    simpa only [endpoint,
      LexicalFunctionCompatibility.endpointImage] using
      (OperationalApplicationPathCoherence.FunctionPathSpine.argumentEvidence_rawSlot
        spine scope closing compatible.image.value compatible.baseEvidence
        compatibleBaseRaw outer outerPlan_eq outerRaw)
  let closure := base.closure.withImage endpoint rfl HEq.rfl
    endpointArgumentRaw
  let final : FunctionResultProvenance scope spine.domainWf closing
      target.view :=
    { closure := closure
      domainPlan_eq := rfl }
  exact
    { view := target.view
      accepted :=
        { paths :=
            { raw :=
                OperationalTypedPathCoherence.buildFunctionPath_rawSlot spine
                  store coherent
              payload :=
                newPayloadAgreement_ofOrdinary scope typing.typeWf .arrow
                  closing target.view (storeArguments store) }
          function := by
            intro otherDomain otherCodomain type_eq
            have domain_eq : domain = otherDomain :=
              congrArg sourceDomain type_eq
            cases domain_eq
            exact ⟨⟨spine.domainWf, final⟩⟩ } }

@[simp] theorem ofFunctionPath_argument
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {domain codomain : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path path)
      (.Fun domain codomain.weaken)}
    (spine : FunctionPathSpine typing)
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : StorePathCoherence store)
    (base : FunctionResultProvenance scope spine.baseDomainWf closing
      (store.lookup (typedPathReferent typing)).slot.behavior) :
    (ofFunctionPath spine store coherent base).view.argument =
      (OperationalTypedPathView.buildFunctionPath spine store coherent).view.argument :=
  rfl

end OperationalPathResultInterface
end LambdaPToFCo
