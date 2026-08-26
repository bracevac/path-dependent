import LambdaPToFCo.OperationalClosedPlanWeakening
import LambdaPToFCo.OperationalFunctionEnvironmentCoherence
import LambdaPToFCo.OperationalFunctionPathSpine

/-!
# Function provenance in the current lexical context

`FunctionEnvironmentCoherence` stores a function witness at the lexical
scope in which a slot was introduced.  A later source context may have
crossed arbitrarily many ordinary binder extensions.  This module transports
the retained domain plan through those extensions and repackages the same
source closure as provenance for the current scope.

The result is the store-independent input expected by function-path result
interfaces.  Physical closure alignment is retained alongside the
current-scoped provenance for application consumers.
-/

namespace LambdaPToFCo
namespace OperationalCurrentFunctionProvenance

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalBindingView
open OperationalEnvironment
open OperationalStoreEnvironment
open OperationalApplicationSpine
open OperationalFunctionPathSpine
open OperationalFunctionResultProvenance
open OperationalFunctionEnvironmentCoherence
open OperationalClosedPlanWeakening

private def sourceDomain : LambdaPFC.Ty n -> LambdaPFC.Ty n
  | .Fun domain _ => domain
  | _ => .Top

/-- Invert an arrow observed after weakening without eliminating the
well-formedness proof on which a compiled binder may depend. -/
private structure WeakenedArrowView
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceType : LambdaPFC.Ty lexical}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    {domain codomain : LambdaPFC.Ty (lexical + 1)}
    (type_eq : sourceType.weaken = .Fun domain codomain.weaken) : Type where
  originalDomain : LambdaPFC.Ty lexical
  originalCodomain : LambdaPFC.Ty lexical
  sourceType_eq : sourceType =
    .Fun originalDomain originalCodomain.weaken
  originalDomainWf : Fragment.Wf sourceContext originalDomain
  originalCodomainWf : Fragment.Wf sourceContext originalCodomain
  domain_eq : originalDomain.weaken = domain

private def weakenedArrowView
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceType : LambdaPFC.Ty lexical}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    {domain codomain : LambdaPFC.Ty (lexical + 1)}
    (type_eq : sourceType.weaken = .Fun domain codomain.weaken) :
    WeakenedArrowView sourceWf type_eq := by
  cases sourceWf with
  | top => cases type_eq
  | singleton _ => cases type_eq
  | selection _ _ => cases type_eq
  | memberPackage _ _ _ => cases type_eq
  | arrow domainWf codomainWf =>
      exact
        { originalDomain := _
          originalCodomain := _
          sourceType_eq := rfl
          originalDomainWf := domainWf
          originalCodomainWf := codomainWf
          domain_eq := congrArg sourceDomain type_eq }

/-- Removing one weakening from a well-formed ordinary type preserves its
ordinary representation shape.  The dependent member-package case is
excluded by the shape premise. -/
private def ordinaryShape_unweaken
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceType : LambdaPFC.Ty lexical}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (shape : OrdinaryShape sourceType.weaken) : OrdinaryShape sourceType := by
  cases sourceWf with
  | top => exact .top
  | singleton _ => exact .singleton
  | selection _ _ => exact .selection
  | memberPackage _ _ _ => cases shape
  | arrow _ _ => exact .arrow

private def ordinaryShape_unweaken_of_eq
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceType : LambdaPFC.Ty lexical}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    {domain : LambdaPFC.Ty (lexical + 1)}
    (domain_eq : sourceType.weaken = domain)
    (shape : OrdinaryShape domain) : OrdinaryShape sourceType := by
  cases domain_eq
  exact ordinaryShape_unweaken sourceWf shape

/-- Static bridge between a domain in the current context and the retained
domain owned by the selected lexical slot. -/
structure CurrentSlotFunctionPlan
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (index : Fin lexical)
    {domain : LambdaPFC.Ty lexical}
    (domainWf : Fragment.Wf sourceContext domain) : Type where
  slotDomain : LambdaPFC.Ty (environment.lookup index).slot.arity
  slotCodomain : LambdaPFC.Ty (environment.lookup index).slot.arity
  slotType_eq : (environment.lookup index).slot.sourceType =
    .Fun slotDomain slotCodomain.weaken
  slotDomainWf : Fragment.Wf
    (environment.lookup index).slot.context slotDomain
  slotDomainShape : OrdinaryShape slotDomain
  closedPlan_eq : closedPlan scope closing domainWf =
    closedPlan (environment.lookup index).slot.scope
      (environment.lookup index).slot.environment slotDomainWf

private theorem closedPlan_step
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceType oldDomain : LambdaPFC.Ty lexical}
    {domain : LambdaPFC.Ty (lexical + 1)}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (oldDomainWf : Fragment.Wf sourceContext oldDomain)
    (oldDomainShape : OrdinaryShape oldDomain)
    (closing : ClosingEnv sig [])
    (view : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        closing.substitution))
    (domainWf : Fragment.Wf (sourceContext.snoc sourceType) domain)
    (domainShape : OrdinaryShape domain)
    (domain_eq : oldDomain.weaken = domain) :
    closedPlan (TermTranslation.compileBinder scope sourceWf).extended
        (extendClosing closing
          (TermTranslation.compileBinder scope sourceWf).plan view)
        domainWf =
      closedPlan scope closing oldDomainWf := by
  cases domain_eq
  exact
    (closedPlan_irrel_of_ordinary
      (TermTranslation.compileBinder scope sourceWf).extended
      (extendClosing closing
        (TermTranslation.compileBinder scope sourceWf).plan view)
      domainWf (oldDomainWf.weaken sourceType) domainShape).trans
      (closedPlan_weaken scope sourceWf oldDomainWf oldDomainShape closing
        view)

private theorem currentSlotFunctionPlan
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (index : Fin lexical)
    {domain codomain : LambdaPFC.Ty lexical}
    (type_eq : sourceContext.lookup index = .Fun domain codomain.weaken)
    (domainWf : Fragment.Wf sourceContext domain)
    (domainShape : OrdinaryShape domain) :
    Nonempty (CurrentSlotFunctionPlan environment index domainWf) := by
  induction environment with
  | empty => exact Fin.elim0 index
  | nativeWeaken older runtimeValue runtimeReady ih =>
      rcases ih index type_eq domainWf domainShape with ⟨olderPlan⟩
      exact ⟨
        { slotDomain := olderPlan.slotDomain
          slotCodomain := olderPlan.slotCodomain
          slotType_eq := olderPlan.slotType_eq
          slotDomainWf := olderPlan.slotDomainWf
          slotDomainShape := olderPlan.slotDomainShape
          closedPlan_eq := olderPlan.closedPlan_eq }⟩
  | extend older typing native nativeValuation nativeAdmissible nativeEvidence
      nativeEnvironment nativeReady runtimeReady runtime_eq memberCell
      functionCell behavior normalizes ih =>
      cases index using Fin.cases with
      | zero =>
          let arrow := weakenedArrowView typing.typeWf type_eq
          have sourceDomainShape : OrdinaryShape arrow.originalDomain :=
            ordinaryShape_unweaken_of_eq arrow.originalDomainWf
              arrow.domain_eq domainShape
          exact ⟨
            { slotDomain := arrow.originalDomain
              slotCodomain := arrow.originalCodomain
              slotType_eq := arrow.sourceType_eq
              slotDomainWf := arrow.originalDomainWf
              slotDomainShape := sourceDomainShape
              closedPlan_eq := closedPlan_step _ typing.typeWf
                arrow.originalDomainWf sourceDomainShape older.closing
                behavior domainWf domainShape arrow.domain_eq }⟩
      | succ olderIndex =>
          let olderWf := older.coherent.lookup_wf olderIndex
          let arrow := weakenedArrowView olderWf type_eq
          have sourceDomainShape : OrdinaryShape arrow.originalDomain :=
            ordinaryShape_unweaken_of_eq arrow.originalDomainWf
              arrow.domain_eq domainShape
          rcases ih olderIndex arrow.sourceType_eq arrow.originalDomainWf
              sourceDomainShape with ⟨olderPlan⟩
          exact ⟨
            { slotDomain := olderPlan.slotDomain
              slotCodomain := olderPlan.slotCodomain
              slotType_eq := olderPlan.slotType_eq
              slotDomainWf := olderPlan.slotDomainWf
              slotDomainShape := olderPlan.slotDomainShape
              closedPlan_eq :=
                (closedPlan_step _ typing.typeWf
                  arrow.originalDomainWf sourceDomainShape older.closing
                  behavior domainWf domainShape arrow.domain_eq).trans
                  olderPlan.closedPlan_eq }⟩
  | alias older typing memberCell functionCell behavior normalizes ih =>
      cases index using Fin.cases with
      | zero =>
          let arrow := weakenedArrowView typing.typeWf type_eq
          have sourceDomainShape : OrdinaryShape arrow.originalDomain :=
            ordinaryShape_unweaken_of_eq arrow.originalDomainWf
              arrow.domain_eq domainShape
          exact ⟨
            { slotDomain := arrow.originalDomain
              slotCodomain := arrow.originalCodomain
              slotType_eq := arrow.sourceType_eq
              slotDomainWf := arrow.originalDomainWf
              slotDomainShape := sourceDomainShape
              closedPlan_eq := closedPlan_step _ typing.typeWf
                arrow.originalDomainWf sourceDomainShape older.closing
                behavior domainWf domainShape arrow.domain_eq }⟩
      | succ olderIndex =>
          let olderWf := older.coherent.lookup_wf olderIndex
          let arrow := weakenedArrowView olderWf type_eq
          have sourceDomainShape : OrdinaryShape arrow.originalDomain :=
            ordinaryShape_unweaken_of_eq arrow.originalDomainWf
              arrow.domain_eq domainShape
          rcases ih olderIndex arrow.sourceType_eq arrow.originalDomainWf
              sourceDomainShape with ⟨olderPlan⟩
          exact ⟨
            { slotDomain := olderPlan.slotDomain
              slotCodomain := olderPlan.slotCodomain
              slotType_eq := olderPlan.slotType_eq
              slotDomainWf := olderPlan.slotDomainWf
              slotDomainShape := olderPlan.slotDomainShape
              closedPlan_eq :=
                (closedPlan_step _ typing.typeWf
                  arrow.originalDomainWf sourceDomainShape older.closing
                  behavior domainWf domainShape arrow.domain_eq).trans
                  olderPlan.closedPlan_eq }⟩
  | bindLocation older sourceWf location binds compiled nativeEnvironment
      memberCell functionCell behavior ih =>
      cases index using Fin.cases with
      | zero =>
          let arrow := weakenedArrowView sourceWf type_eq
          have sourceDomainShape : OrdinaryShape arrow.originalDomain :=
            ordinaryShape_unweaken_of_eq arrow.originalDomainWf
              arrow.domain_eq domainShape
          exact ⟨
            { slotDomain := arrow.originalDomain
              slotCodomain := arrow.originalCodomain
              slotType_eq := arrow.sourceType_eq
              slotDomainWf := arrow.originalDomainWf
              slotDomainShape := sourceDomainShape
              closedPlan_eq := closedPlan_step _ sourceWf
                arrow.originalDomainWf sourceDomainShape older.closing
                behavior domainWf domainShape arrow.domain_eq }⟩
      | succ olderIndex =>
          let olderWf := older.coherent.lookup_wf olderIndex
          let arrow := weakenedArrowView olderWf type_eq
          have sourceDomainShape : OrdinaryShape arrow.originalDomain :=
            ordinaryShape_unweaken_of_eq arrow.originalDomainWf
              arrow.domain_eq domainShape
          rcases ih olderIndex arrow.sourceType_eq arrow.originalDomainWf
              sourceDomainShape with ⟨olderPlan⟩
          exact ⟨
            { slotDomain := olderPlan.slotDomain
              slotCodomain := olderPlan.slotCodomain
              slotType_eq := olderPlan.slotType_eq
              slotDomainWf := olderPlan.slotDomainWf
              slotDomainShape := olderPlan.slotDomainShape
              closedPlan_eq :=
                (closedPlan_step _ sourceWf arrow.originalDomainWf
                  sourceDomainShape older.closing behavior domainWf
                  domainShape arrow.domain_eq).trans
                  olderPlan.closedPlan_eq }⟩

/-- Function provenance reindexed from a retained lexical slot to the
current source scope. -/
structure CurrentFunctionWitness
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (index : Fin lexical)
    {domain : LambdaPFC.Ty lexical}
    (domainWf : Fragment.Wf sourceContext domain) : Type where
  provenance : FunctionResultProvenance scope domainWf closing
    (environment.lookup index).slot.behavior
  alignment : FunctionClosureAlignment provenance.closure sourceStore
    (environment.lookup index).runtimeValue
    (environment.lookup index).nativeEnvironment

end OperationalCurrentFunctionProvenance

namespace OperationalFunctionEnvironmentCoherence
namespace FunctionEnvironmentCoherence

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalBindingView
open OperationalEnvironment
open OperationalStoreEnvironment
open OperationalApplicationSpine
open OperationalFunctionPathSpine
open OperationalFunctionResultProvenance
open OperationalCurrentFunctionProvenance

private theorem pathLookup_eq
    {sourceContext : LambdaPFC.Ctx lexical}
    {path : LambdaPFC.Path lexical}
    {sourceType : LambdaPFC.Ty lexical}
    {domain codomain : LambdaPFC.Ty lexical}
    (typing : Fragment.PathTy sourceContext path sourceType)
    (type_eq : sourceType = .Fun domain codomain.weaken) :
    sourceContext.lookup (pathReferentIndex typing) =
      .Fun domain codomain.weaken := by
  cases typing with
  | var => exact type_eq
  | exactFst _ => cases type_eq

/-- Recover function provenance at the current lexical scope, transporting
the closed domain binder plan through every intervening source binder. -/
theorem lookupCurrent
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    {environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    (coherent : FunctionEnvironmentCoherence environment)
    (index : Fin lexical)
    {domain codomain : LambdaPFC.Ty lexical}
    (type_eq : sourceContext.lookup index = .Fun domain codomain.weaken)
    (domainWf : Fragment.Wf sourceContext domain)
    (domainShape : OrdinaryShape domain) :
    Nonempty (CurrentFunctionWitness environment index domainWf) := by
  rcases currentSlotFunctionPlan environment index type_eq domainWf
      domainShape with ⟨plan⟩
  rcases coherent.lookupFunction index plan.slotType_eq with ⟨binding⟩
  let slotPlanProofEq := closedPlan_irrel_of_ordinary
    (environment.lookup index).slot.scope
    (environment.lookup index).slot.environment plan.slotDomainWf
    binding.domainWf plan.slotDomainShape
  let currentPlanEq := plan.closedPlan_eq.trans
    (slotPlanProofEq.trans binding.provenance.domainPlan_eq)
  exact ⟨
    { provenance :=
        { closure := binding.provenance.closure
          domainPlan_eq := currentPlanEq }
      alignment := binding.alignment }⟩

/-- A function-path spine identifies an arrow variable in the current source
context; lookup returns exactly the base provenance consumed by path result
interfaces. -/
theorem lookupFunctionPath
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    {environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    (coherent : FunctionEnvironmentCoherence environment)
    {path : LambdaPFC.Path lexical}
    {domain codomain : LambdaPFC.Ty lexical}
    {typing : Fragment.HasType sourceContext (.path path)
      (.Fun domain codomain.weaken)}
    (spine : FunctionPathSpine typing) :
    Nonempty (CurrentFunctionWitness environment
      (typedPathReferent typing) spine.baseDomainWf) := by
  induction spine with
  | widen pathTyping domainWf codomainWf domainShape =>
      simpa only [typedPathReferent_sub, typedPathReferent_path,
        FunctionPathSpine.baseDomainWf] using
        coherent.lookupCurrent (pathReferentIndex pathTyping)
          (pathLookup_eq pathTyping rfl) domainWf domainShape
  | sub inner coercion ih =>
      simpa only [typedPathReferent_sub, FunctionPathSpine.baseDomainWf] using
        ih

/-- The projection used by path result-interface construction. -/
theorem functionPathProvenance
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    {environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    (coherent : FunctionEnvironmentCoherence environment)
    {path : LambdaPFC.Path lexical}
    {domain codomain : LambdaPFC.Ty lexical}
    {typing : Fragment.HasType sourceContext (.path path)
      (.Fun domain codomain.weaken)}
    (spine : FunctionPathSpine typing) :
    Nonempty (FunctionResultProvenance scope spine.baseDomainWf closing
      (environment.lookup (typedPathReferent typing)).slot.behavior) := by
  rcases coherent.lookupFunctionPath spine with ⟨witness⟩
  exact ⟨witness.provenance⟩

end FunctionEnvironmentCoherence

end OperationalFunctionEnvironmentCoherence
end LambdaPToFCo
