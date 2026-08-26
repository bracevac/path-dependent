import LambdaPToFCo.OperationalPathCoherenceGenerated
import LambdaPToFCo.OperationalFunctionPathSpine

/-!
# Raw-slot coherence for generated application evidence

`ArgumentEvidence` itself intentionally accepts an arbitrary
`AdaptedArgument`; in particular, `AdaptedArgument.ofView` may install a view
with an arbitrary substitution.  Therefore `RawSlot outer` does *not* imply
`RawSlot evidence.toArgumentView.elimination` for an arbitrary evidence term.

The source-generated evidence is narrower.  `ApplicationFunctionCo` and
`ApplicationSpine` use only reflexive passage and the direct ordinary
adapter, both of which preserve or establish `RawSlot`.  The lemmas below
retain that construction provenance and prove exactly the property needed by
the direct application successor.  The final helpers combine any such raw
elimination with an ordinary or noncanonical source result shape to build the
full `BehaviorPathCoherence` required by `bindLocation`.
-/

namespace LambdaPToFCo
namespace OperationalApplicationPathCoherence

open SystemFCo
open StaticTranslation
open OperationalEnvironment
open OperationalBindingView
open OperationalApplication
open OperationalApplicationTranslation
open OperationalApplicationSpine
open OperationalPathCoherence
open OperationalPathCoherenceGenerated
open OperationalFunctionPathSpine

private theorem rawSlot_argumentEvidence_transport
    {plan : Interface.BinderPlan []} {result : Ty []}
    {body : Exp plan.scope}
    {first second : FunctionValue plan result body}
    {outerPlan : Interface.BinderPlan []}
    {outer : EliminationView outerPlan}
    (valueEqual : first = second)
    (typeEqual : ArgumentEvidence second outer = ArgumentEvidence first outer)
    (evidence : ArgumentEvidence first outer)
    (raw : RawSlot evidence.toArgumentView.elimination) :
    RawSlot ((Eq.mpr typeEqual evidence).toArgumentView.elimination) := by
  cases valueEqual
  have proofEqual : typeEqual = rfl := Subsingleton.elim _ _
  cases proofEqual
  exact raw

namespace ApplicationFunctionCo

/-- Generated function-coercion argument evidence preserves a raw base slot,
provided the recursively supplied inner evidence does so. -/
theorem argumentEvidence_rawSlot
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceDomain sourceCodomain targetDomain targetCodomain : LambdaPFC.Ty n}
    {subtype : Fragment.Sub sourceContext
      (.Fun sourceDomain sourceCodomain.weaken)
      (.Fun targetDomain targetCodomain.weaken)}
    {shape : FragmentFunctionCo subtype}
    (coercion : ApplicationFunctionCo shape)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    {plan : Interface.BinderPlan []} {result : Ty []}
    {body : Exp plan.scope}
    (function : FunctionValue plan result body)
    (sourceEvidence :
      {outerPlan : Interface.BinderPlan []} ->
      (outer : EliminationView outerPlan) ->
      outerPlan = closedPlan scope environment coercion.sourceDomainWf ->
      ArgumentEvidence function outer)
    (sourceRaw :
      {outerPlan : Interface.BinderPlan []} ->
      (outer : EliminationView outerPlan) ->
      (outerPlan_eq :
        outerPlan = closedPlan scope environment coercion.sourceDomainWf) ->
      RawSlot outer ->
      RawSlot
        ((sourceEvidence outer outerPlan_eq).toArgumentView.elimination))
    {outerPlan : Interface.BinderPlan []}
    (outer : EliminationView outerPlan)
    (outerPlan_eq :
      outerPlan = closedPlan scope environment coercion.targetDomainWf)
    (outerRaw : RawSlot outer) :
    RawSlot
      ((coercion.argumentEvidence scope environment function sourceEvidence
        outer outerPlan_eq).toArgumentView.elimination) := by
  induction coercion generalizing plan result body outerPlan with
  | refl domainWf codomainWf domainShape =>
      exact sourceRaw outer outerPlan_eq outerRaw
  | @trans sourceDomain sourceCodomain middleDomain middleCodomain
      targetDomain targetCodomain firstSubtype secondSubtype firstShape
      secondShape first second firstIH secondIH =>
      let firstNormalization :=
        (firstShape.close scope environment).normalize function
      let middleEvidence :
          {middlePlan : Interface.BinderPlan []} ->
          (middle : EliminationView middlePlan) ->
          middlePlan = closedPlan scope environment second.sourceDomainWf ->
          ArgumentEvidence firstNormalization.value middle :=
        fun middle middlePlan_eq =>
          first.argumentEvidence scope environment function sourceEvidence
            middle
            (middlePlan_eq.trans
              (closedPlan_irrel_of_ordinary scope environment
                second.sourceDomainWf first.targetDomainWf
                second.sourceDomainShape))
      apply secondIH firstNormalization.value middleEvidence
      · intro middlePlan middle middlePlan_eq middleRaw
        apply firstIH function sourceEvidence sourceRaw middle
          (middlePlan_eq.trans
            (closedPlan_irrel_of_ordinary scope environment
              second.sourceDomainWf first.targetDomainWf
              second.sourceDomainShape))
        exact middleRaw
      · exact outerRaw
  | @arrow sourceDomain sourceCodomain targetDomain targetCodomain domain codomain
      sourceShape targetShape =>
      let raw := AdaptedArgument.ordinary outer
        (environment.closeCo
          (CoercionTranslation.elaborateSub scope domain))
        (environment.closeTy
          (translateType scope domain.targetWf))
      have rawPlan_eq :
          raw.plan = closedPlan scope environment domain.targetWf := by
        dsimp [raw, AdaptedArgument.ordinary, closedPlan]
        rw [OperationalValueEvidence.compileBinder_plan_ordinary scope
          domain.targetWf sourceShape]
        change Interface.BinderPlan.ordinary
            ((translateType scope domain.targetWf).subst
              environment.substitution) = _
        rfl
      change RawSlot
        ((sourceEvidence raw.view rawPlan_eq).toArgumentView.elimination)
      apply sourceRaw raw.view rawPlan_eq
      exact rawSlot_adaptedOrdinary outer _ _

end ApplicationFunctionCo

namespace FunctionPathSpine

/-- Generated operator-path coercions preserve a raw argument projection when
the retained lexical base function supplies the same law.  This is the
wrapper-aware counterpart of `ApplicationSpine.argumentEvidence_rawSlot`:
the base image may differ from the physical canonical endpoint, so its raw law
must be carried explicitly. -/
theorem argumentEvidence_rawSlot
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {functionPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken)}
    (spine : FunctionPathSpine typing)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    {plan : Interface.BinderPlan []} {result : Ty []}
    {body : Exp plan.scope}
    (base : FunctionValue plan result body)
    (baseEvidence :
      {outerPlan : Interface.BinderPlan []} ->
      (outer : EliminationView outerPlan) ->
      outerPlan = closedPlan scope environment spine.baseDomainWf ->
      ArgumentEvidence base outer)
    (baseRaw :
      {outerPlan : Interface.BinderPlan []} ->
      (outer : EliminationView outerPlan) ->
      (outerPlan_eq :
        outerPlan = closedPlan scope environment spine.baseDomainWf) ->
      RawSlot outer ->
      RawSlot
        ((baseEvidence outer outerPlan_eq).toArgumentView.elimination))
    {outerPlan : Interface.BinderPlan []}
    (outer : EliminationView outerPlan)
    (outerPlan_eq :
      outerPlan = closedPlan scope environment spine.domainWf)
    (outerRaw : RawSlot outer) :
    RawSlot
      ((spine.argumentEvidence scope environment base baseEvidence outer
        outerPlan_eq).toArgumentView.elimination) := by
  induction spine generalizing outerPlan with
  | widen pathTyping domainWf codomainWf domainShape =>
      simp only [OperationalFunctionPathSpine.FunctionPathSpine.argumentEvidence,
        OperationalFunctionPathSpine.FunctionPathSpine.closedView,
        FunctionView.normalize, FunctionCo.normalize]
      apply rawSlot_argumentEvidence_transport
      · exact
          (OperationalFunctionPathSpine.FunctionPathSpine.canonicalView_normalize_value
            base).symm
      exact baseRaw outer outerPlan_eq outerRaw
  | @sub sourceDomain sourceCodomain targetDomain targetCodomain innerTyping
      subtype shape inner coercion ih =>
      let sourceEvidence :
          {sourcePlan : Interface.BinderPlan []} ->
          (source : EliminationView sourcePlan) ->
          sourcePlan = closedPlan scope environment coercion.sourceDomainWf ->
          ArgumentEvidence
            (inner.closedView scope environment base).normalize.value source :=
        fun source sourcePlan_eq =>
          inner.argumentEvidence scope environment base baseEvidence source
            (sourcePlan_eq.trans
              (closedPlan_irrel_of_ordinary scope environment
                coercion.sourceDomainWf inner.domainWf
                coercion.sourceDomainShape))
      apply
        OperationalApplicationPathCoherence.ApplicationFunctionCo.argumentEvidence_rawSlot
          coercion scope environment
          (inner.closedView scope environment base).normalize.value
          sourceEvidence
      · intro sourcePlan source sourcePlan_eq sourceRaw
        apply ih baseEvidence baseRaw source
          (sourcePlan_eq.trans
            (closedPlan_irrel_of_ordinary scope environment
              coercion.sourceDomainWf inner.domainWf
              coercion.sourceDomainShape))
        exact sourceRaw
      · exact outerRaw

end FunctionPathSpine

namespace ApplicationSpine

/-- The argument evidence generated by a native application spine maps the
base binder's raw projection back to its behavioral argument. -/
theorem argumentEvidence_rawSlot
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {nativeDomain domain codomain : LambdaPFC.Ty n}
    {sourceBody : LambdaPFC.Tm (n + 1)}
    {typing : Fragment.HasType sourceContext (.abs nativeDomain sourceBody)
      (.Fun domain codomain.weaken)}
    (spine : ApplicationSpine typing)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    {outerPlan : Interface.BinderPlan []}
    (outer : EliminationView outerPlan)
    (outerPlan_eq : outerPlan = closedPlan scope environment spine.domainWf)
    (outerRaw : RawSlot outer) :
    RawSlot
      ((spine.argumentEvidence scope environment outer
        outerPlan_eq).toArgumentView.elimination) := by
  induction spine generalizing outerPlan with
  | abs bodyTyping domainWf codomainWf domainShape =>
      cases outerPlan_eq
      exact outerRaw
  | @sub sourceDomain sourceCodomain targetDomain targetCodomain innerTyping
      subtype shape inner coercion ih =>
      let sourceEvidence :
          {sourcePlan : Interface.BinderPlan []} ->
          (source : EliminationView sourcePlan) ->
          sourcePlan = closedPlan scope environment coercion.sourceDomainWf ->
          ArgumentEvidence
            (inner.functionSpine.close scope environment).image.view.normalize.value
            source :=
        fun source sourcePlan_eq =>
          inner.argumentEvidence scope environment source
            (sourcePlan_eq.trans
              (closedPlan_irrel_of_ordinary scope environment
                coercion.sourceDomainWf inner.domainWf
                coercion.sourceDomainShape))
      apply
        OperationalApplicationPathCoherence.ApplicationFunctionCo.argumentEvidence_rawSlot
          coercion scope environment
          (inner.functionSpine.close scope environment).image.view.normalize.value
          sourceEvidence
      · intro sourcePlan source sourcePlan_eq sourceRaw
        apply ih source
          (sourcePlan_eq.trans
            (closedPlan_irrel_of_ordinary scope environment
              coercion.sourceDomainWf inner.domainWf
              coercion.sourceDomainShape))
        exact sourceRaw
      · exact outerRaw

end ApplicationSpine

namespace NativeFunctionImage

/-- The erased native image built from an `ApplicationSpine` retains the
same raw-slot guarantee through its exported argument-evidence callback. -/
theorem ofApplicationSpine_argumentEvidence_rawSlot
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {nativeDomain domain codomain : LambdaPFC.Ty n}
    {sourceBody : LambdaPFC.Tm (n + 1)}
    {typing : Fragment.HasType sourceContext (.abs nativeDomain sourceBody)
      (.Fun domain codomain.weaken)}
    (spine : ApplicationSpine typing)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (ready :
      (ApplicationValueEvidence.function spine).ClosedReady scope environment)
    (behavior : Exp [])
    (behavior_eq :
      ((ApplicationValueEvidence.function spine).closedView scope environment
        ready).view.argument = behavior)
    {outerPlan : Interface.BinderPlan []}
    (outer : EliminationView outerPlan)
    (outerPlan_eq : outerPlan =
      (NativeFunctionImage.ofApplicationSpine spine scope environment ready
        behavior behavior_eq).domainPlan)
    (outerRaw : RawSlot outer) :
    RawSlot
      ((((NativeFunctionImage.ofApplicationSpine spine scope environment ready
        behavior behavior_eq).argumentEvidence outer
          outerPlan_eq).toArgumentView.elimination)) := by
  apply
    OperationalApplicationPathCoherence.ApplicationSpine.argumentEvidence_rawSlot
      spine scope environment outer
  · exact outerRaw

end NativeFunctionImage

namespace BehaviorPathCoherence

/-- For an ordinary source binder, `RawSlot` is the only non-vacuous local
path-coherence obligation. -/
theorem ofRawOrdinary
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (shape : OrdinaryShape sourceType)
    (environment : ClosingEnv sig [])
    (behavior : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        environment.substitution))
    (arguments : OperationalPathCoherence.ClosedArguments n)
    (raw : RawSlot behavior) :
    BehaviorPathCoherence scope sourceWf environment behavior arguments where
  raw := raw
  payload := newPayloadAgreement_ofOrdinary scope sourceWf shape environment
    behavior arguments

/-- Application result shapes are ordinary, so their payload obligation is
vacuous once the base elimination satisfies `RawSlot`. -/
theorem ofRawNonCanonical
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (shape : NonCanonicalResultShape sourceType)
    (environment : ClosingEnv sig [])
    (behavior : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        environment.substitution))
    (arguments : OperationalPathCoherence.ClosedArguments n)
    (raw : RawSlot behavior) :
    BehaviorPathCoherence scope sourceWf environment behavior arguments :=
  ofRawOrdinary scope sourceWf shape.ordinary environment behavior arguments
    raw

end BehaviorPathCoherence

end OperationalApplicationPathCoherence
end LambdaPToFCo
