import LambdaPToFCo.OperationalFunctionResultProvenance
import LambdaPToFCo.OperationalMachineImage
import LambdaPToFCo.OperationalEnvironmentCoherence
import LambdaPToFCo.OperationalApplicationStore
import LambdaPToFCo.OperationalFunctionEnvironmentCoherence

/-!
# Function provenance for a directly allocated binding

This module is deliberately separate from the machine image.  It turns the
function witness carried by a result boundary into the source-closure witness
needed by the application-side store interface.
-/

namespace LambdaPToFCo
namespace OperationalDirectFunctionBinding

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalEnvironment
open OperationalBindingView
open OperationalApplication
open OperationalApplicationTranslation
open OperationalApplicationSpine
open OperationalValueEvidence
open OperationalAdmissibility
open OperationalStoreEnvironment
open OperationalEnvironmentCoherence
open OperationalMachineImage
open OperationalApplicationStore
open OperationalFunctionResultProvenance
open OperationalFunctionEnvironmentCoherence
open OperationalPathCoherence
open OperationalPathCoherenceGenerated

private def sourceDomain : LambdaPFC.Ty n -> LambdaPFC.Ty n
  | .Fun domain _ => domain
  | _ => .Top

namespace DirectCodeEnvironment

/-- An untruncated direct function witness.  The structural alignment retains
the definitional native origin needed when a higher store invariant installs
the value as the newest physical binding; the heterogeneous projections remain
available to lower clients which only need individual endpoint equalities. -/
structure DirectFunctionWitness
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    (valuation : SourceValuation n current)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (closing : ClosingEnv sig [])
    (nativeEnvironment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (runtimeValue : LambdaPFC.Tm current)
    {plan : Interface.BinderPlan []} (view : EliminationView plan)
    (domain : LambdaPFC.Ty n) : Type where
  domainWf : Fragment.Wf sourceContext domain
  provenance : FunctionResultProvenance scope domainWf closing view
  sourceStore_heq : HEq provenance.closure.sourceStore sourceStore
  runtimeValue_heq : HEq provenance.closure.runtimeValue runtimeValue
  nativeEnvironment_heq :
    HEq provenance.closure.nativeEnvironment nativeEnvironment
  alignment : FunctionClosureAlignment provenance.closure sourceStore
    runtimeValue nativeEnvironment

namespace DirectFunctionWitness

/-- Forget the direct-code packaging while retaining precisely the
wrapper-aware witness consumed by recursive function-environment coherence. -/
noncomputable def toFunctionBindingWitness
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    {nativeEnvironment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    {runtimeValue : LambdaPFC.Tm current}
    {plan : Interface.BinderPlan []} {view : EliminationView plan}
    {domain : LambdaPFC.Ty n}
    (witness : DirectFunctionWitness valuation scope closing nativeEnvironment
      runtimeValue view domain) :
    FunctionBindingWitness scope closing view domain sourceStore runtimeValue
      nativeEnvironment where
  domainWf := witness.domainWf
  provenance := witness.provenance
  alignment := witness.alignment

end DirectFunctionWitness

/-- Closed readiness follows from the ready lexical arguments retained by
recursive environment coherence. -/
private noncomputable def closedReadyOfArguments
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext term sourceType}
    (evidence : ApplicationValueEvidence typing)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (closing : ClosingEnv sig [])
    (arguments : ClosedArguments n)
    (agreement : ClosedPathAgreement scope closing arguments)
    (ready : forall index, Exp.IsValue (arguments index)) :
    evidence.ClosedReady scope closing := by
  cases evidence with
  | function _ => trivial
  | @package first _ _ _ _ _ =>
      change Exp.IsValue
        (closing.closeExp
          (translatePath scope
            (Fragment.PathTy.var
              (Γ := sourceContext) (x := first))).expression)
      rw [agreement (Fragment.PathTy.var
        (Γ := sourceContext) (x := first))]
      exact ready first

/-- The readiness proof used by the function-aware direct result boundary.
-/
noncomputable def acceptedClosedReady
    (code : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (coherent : EnvironmentCoherence code.environment) :
    (code.valueEvidence runtimeReady).ClosedReady code.scope code.closing :=
  closedReadyOfArguments (code.valueEvidence runtimeReady) code.scope
    code.closing (storeArguments code.environment) coherent.pathCoherence
    (fun index => (code.environment.lookup index).slot.behavior.ready)

/-- Canonical result view used by the function-aware source boundary. -/
noncomputable def acceptedClosedView
    (code : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (coherent : EnvironmentCoherence code.environment) :
    OperationalPackageBehavior.ClosedView code.scope code.original.typing
      code.closing :=
  (code.valueEvidence runtimeReady).closedView code.scope code.closing
    (acceptedClosedReady code runtimeReady coherent)

/-- Source-level value inversion plus deterministic target normalization
constructs the function witness for the canonical direct result view. -/
@[implicit_reducible] private noncomputable def functionWitnessOfValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceTerm : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext sourceTerm sourceType}
    (admissible : OperationallyAdmissible typing)
    (sourceReady : sourceTerm.IsValue)
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    (valuation : SourceValuation n current)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (closing : ClosingEnv sig [])
    (nativeEnvironment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue)
    (runtime_eq : runtimeValue = sourceTerm.rename valuation)
    (ready : (admissible.valueEvidence sourceReady).ClosedReady scope closing)
    {domain codomain : LambdaPFC.Ty n}
    (type_eq : sourceType = .Fun domain codomain.weaken) :
    Nonempty
      (DirectFunctionWitness valuation scope closing nativeEnvironment
        runtimeValue
        ((admissible.valueEvidence sourceReady).closedView scope closing
          ready).view domain) := by
  cases sourceReady with
  | abs =>
    cases admissible with
    | @function _ _ nativeDomain sourceDomain sourceCodomain sourceBody typing
        spine bodyAdmissible =>
      have domain_eq : sourceDomain = domain :=
        congrArg OperationalDirectFunctionBinding.sourceDomain type_eq
      cases domain_eq
      let selected :=
        (OperationallyAdmissible.valueEvidence
          (.function spine bodyAdmissible) (.abs)).closedView scope closing ready
      let canonicalReady :
          (ApplicationValueEvidence.function spine).ClosedReady scope closing :=
        True.intro
      let canonical :=
        (ApplicationValueEvidence.function spine).closedView scope closing
          canonicalReady
      have behavior_eq : canonical.view.argument = selected.view.argument := by
        exact OperationalApplicationStore.value_endpoint_unique
          canonical.normalizes selected.normalizes canonical.view.ready
            selected.view.ready
      exact
        ⟨{
          domainWf := spine.domainWf
          provenance :=
            { closure :=
                SourceFunctionClosure.ofApplicationSpine spine
                  bodyAdmissible valuation scope closing nativeEnvironment
                  runtimeValue runtimeReady runtime_eq canonicalReady
                  selected.view.argument behavior_eq
              domainPlan_eq := rfl }
          sourceStore_heq := HEq.rfl
          runtimeValue_heq := HEq.rfl
          nativeEnvironment_heq := HEq.rfl
          alignment := .direct _
        }⟩
    | neutralSub neutral _ _ _ => cases neutral
  | pair =>
    cases admissible with
    | package spine =>
      rw [spine.sourceType_eq] at type_eq
      cases type_eq
    | neutralSub neutral _ _ _ => cases neutral

/-- A direct arrow-valued computation exports function provenance at the
exact canonical view already used as its result interface.  This construction
uses the function spine retained by admissibility, not proof reconstruction
from the runtime store. -/
noncomputable def functionWitness
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeValue : LambdaPFC.Tm current}
    (code : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (coherent : EnvironmentCoherence code.environment)
    {domain codomain : LambdaPFC.Ty code.original.arity}
    (type_eq : code.original.resultType =
      .Fun domain codomain.weaken) :
    DirectFunctionWitness code.valuation code.scope code.closing
      code.environment runtimeValue
      (acceptedClosedView code runtimeReady coherent).view domain :=
  Classical.choice
    (functionWitnessOfValue code.admissible (code.sourceReady runtimeReady)
      code.valuation code.scope code.closing code.environment runtimeValue
      runtimeReady code.runtime_eq
      (acceptedClosedReady code runtimeReady coherent) type_eq)

/-- Direct allocation witness at the canonical input behavior.  Structural
native alignment is retained before the source-value inversion witness is
selected.  A result adapter which changes the advertised behavior must carry
this alignment to its mapped output explicitly before environment extension.
-/
noncomputable def functionBindingWitness
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeValue : LambdaPFC.Tm current}
    (code : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (coherent : EnvironmentCoherence code.environment)
    {domain codomain : LambdaPFC.Ty code.original.arity}
    (type_eq : code.original.resultType =
      .Fun domain codomain.weaken) :
    FunctionBindingWitness code.scope code.closing
      (acceptedClosedView code runtimeReady coherent).view domain sourceStore
      runtimeValue code.environment :=
  (functionWitness code runtimeReady coherent type_eq).toFunctionBindingWitness

/-- Logically truncated canonical-input binding witness.  This is a newest
callback for `FunctionEnvironmentCoherence.extend` only when its installed
behavior is definitionally this direct input view. -/
@[implicit_reducible] noncomputable def functionBinding
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeValue : LambdaPFC.Tm current}
    (code : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (coherent : EnvironmentCoherence code.environment)
    {domain codomain : LambdaPFC.Ty code.original.arity}
    (type_eq : code.original.resultType =
      .Fun domain codomain.weaken) :
    Nonempty
      (FunctionBindingWitness code.scope code.closing
        (acceptedClosedView code runtimeReady coherent).view domain sourceStore
        runtimeValue code.environment) :=
  ⟨functionBindingWitness code runtimeReady coherent type_eq⟩

/-- Logically truncated form stored by a universe-zero result boundary. -/
@[implicit_reducible] noncomputable def functionProvenance
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeValue : LambdaPFC.Tm current}
    (code : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (coherent : EnvironmentCoherence code.environment)
    {domain codomain : LambdaPFC.Ty code.original.arity}
    (type_eq : code.original.resultType =
      .Fun domain codomain.weaken) :
    Nonempty
      (Sigma fun domainWf : Fragment.Wf code.original.context domain =>
        FunctionResultProvenance code.scope domainWf code.closing
          (acceptedClosedView code runtimeReady coherent).view) :=
  let witness := functionWitness code runtimeReady coherent type_eq
  ⟨⟨witness.domainWf, witness.provenance⟩⟩

/-- Complete Prop-valued acceptance for a direct source value.  Function
provenance remains hidden under `Nonempty`, keeping the result boundary in
universe zero. -/
@[implicit_reducible] noncomputable def sourceAcceptance
    (code : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (coherent : EnvironmentCoherence code.environment) :
    SourceResultAcceptance code.scope code.original.typing.typeWf code.closing
      (acceptedClosedView code runtimeReady coherent).view
      (storeArguments code.environment) where
  paths := BehaviorPathCoherence.ofApplicationValueEvidence
    (code.valueEvidence runtimeReady) code.scope code.closing
    (acceptedClosedReady code runtimeReady coherent)
    (storeArguments code.environment) coherent.pathCoherence
  function := fun type_eq =>
    functionProvenance code runtimeReady coherent type_eq

end DirectCodeEnvironment

end OperationalDirectFunctionBinding
end LambdaPToFCo
