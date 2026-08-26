import LambdaPToFCo.OperationalApplicationPathCoherence

/-!
# Function provenance retained by source result interfaces

Source result boundaries stay in universe zero.  Their acceptance proposition
retains rich native function/source-body provenance only under `Nonempty`;
application may recover the Type-valued witness noncomputably.
-/

namespace LambdaPToFCo
namespace OperationalFunctionResultProvenance

open SystemFCo
open StaticTranslation
open OperationalEnvironment
open OperationalBindingView
open OperationalApplication
open OperationalApplicationTranslation
open OperationalApplicationSpine
open OperationalValueEvidence
open OperationalAdmissibility
open OperationalPathCoherence
open OperationalPathCoherenceGenerated
open OperationalFunctionPathSpine

/-- A native source abstraction and the wrapper-aware target function image
currently advertised for it.  Wrappers may change the image's value, but not
the retained source body. -/
structure SourceFunctionClosure (behavior : Exp []) : Type where
  sourceArity : Nat
  sourceContext : LambdaPFC.Ctx sourceArity
  nativeDomain : LambdaPFC.Ty sourceArity
  domain : LambdaPFC.Ty sourceArity
  codomain : LambdaPFC.Ty sourceArity
  sourceBody : LambdaPFC.Tm (sourceArity + 1)
  typing : Fragment.HasType sourceContext
    (.abs nativeDomain sourceBody) (.Fun domain codomain.weaken)
  spine : ApplicationSpine typing
  bodyAdmissible :
    OperationallyAdmissible spine.functionSpine.bodyTyping.2
  current : Nat
  sourceStore : LambdaPFC.Store current
  valuation : OperationalCode.SourceValuation sourceArity current
  targetSig : Sig
  targetContext : Ctx targetSig
  scope : Scope sourceContext targetContext
  closing : ClosingEnv targetSig []
  nativeEnvironment : OperationalStoreEnvironment.StoreEnvironment
    sourceContext sourceStore valuation targetContext scope closing
  runtimeValue : LambdaPFC.Tm current
  runtimeReady : runtimeValue.IsValue
  runtime_eq : runtimeValue =
    (LambdaPFC.Tm.abs nativeDomain sourceBody).rename valuation
  ready :
    (ApplicationValueEvidence.function spine).ClosedReady scope closing
  image : NativeFunctionImage behavior
  plan_eq : image.plan =
    (spine.functionSpine.close scope closing).image.plan
  body_heq : HEq image.body
    (spine.functionSpine.close scope closing).image.body
  argumentRaw :
    {outerPlan : Interface.BinderPlan []} ->
    (outer : EliminationView outerPlan) ->
    (outerPlan_eq : outerPlan = image.domainPlan) ->
    RawSlot outer ->
    RawSlot
      ((image.argumentEvidence outer outerPlan_eq).toArgumentView.elimination)

namespace SourceFunctionClosure

/-- The independently compiled base function evidence. -/
noncomputable def baseEvidence
    (closure : SourceFunctionClosure behavior) :
    ClosedFunctionEvidence closure.scope closure.closing closure.typing :=
  closure.spine.functionSpine.close closure.scope closure.closing

/-- Canonical function expression selected by the native source closure. -/
noncomputable def baseCanonical
    (closure : SourceFunctionClosure behavior) : Exp [] :=
  closure.baseEvidence.image.view.normalize.value.expression

/-- Direct admissible abstractions generate native function provenance. -/
noncomputable def ofApplicationSpine
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {nativeDomain domain codomain : LambdaPFC.Ty n}
    {sourceBody : LambdaPFC.Tm (n + 1)}
    {typing : Fragment.HasType sourceContext (.abs nativeDomain sourceBody)
      (.Fun domain codomain.weaken)}
    (spine : ApplicationSpine typing)
    (bodyAdmissible :
      OperationallyAdmissible spine.functionSpine.bodyTyping.2)
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    (valuation : OperationalCode.SourceValuation n current)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (closing : ClosingEnv sig [])
    (nativeEnvironment : OperationalStoreEnvironment.StoreEnvironment
      sourceContext sourceStore valuation targetContext scope closing)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue)
    (runtime_eq : runtimeValue =
      (LambdaPFC.Tm.abs nativeDomain sourceBody).rename valuation)
    (ready :
      (ApplicationValueEvidence.function spine).ClosedReady scope closing)
    (behavior : Exp [])
    (behavior_eq :
      ((ApplicationValueEvidence.function spine).closedView scope closing
        ready).view.argument = behavior) :
    SourceFunctionClosure behavior where
  sourceArity := n
  sourceContext := sourceContext
  nativeDomain := nativeDomain
  domain := domain
  codomain := codomain
  sourceBody := sourceBody
  typing := typing
  spine := spine
  bodyAdmissible := bodyAdmissible
  current := current
  sourceStore := sourceStore
  valuation := valuation
  targetSig := sig
  targetContext := targetContext
  scope := scope
  closing := closing
  nativeEnvironment := nativeEnvironment
  runtimeValue := runtimeValue
  runtimeReady := runtimeReady
  runtime_eq := runtime_eq
  ready := ready
  image := NativeFunctionImage.ofApplicationSpine spine scope closing ready
    behavior behavior_eq
  plan_eq := rfl
  body_heq := HEq.rfl
  argumentRaw := by
    intro outerPlan outer outerPlan_eq outerRaw
    exact
      OperationalApplicationPathCoherence.NativeFunctionImage.ofApplicationSpine_argumentEvidence_rawSlot
        spine scope closing ready behavior behavior_eq outer outerPlan_eq
        outerRaw

/-- Change only the wrapper-aware endpoint while retaining the source
closure and compiled body. -/
noncomputable def withImage
    (closure : SourceFunctionClosure oldBehavior)
    (image : NativeFunctionImage newBehavior)
    (plan_eq : image.plan = closure.image.plan)
    (body_heq : HEq image.body closure.image.body)
    (argumentRaw :
      {outerPlan : Interface.BinderPlan []} ->
      (outer : EliminationView outerPlan) ->
      (outerPlan_eq : outerPlan = image.domainPlan) ->
      RawSlot outer ->
      RawSlot
        ((image.argumentEvidence outer outerPlan_eq).toArgumentView.elimination)) :
    SourceFunctionClosure newBehavior where
  sourceArity := closure.sourceArity
  sourceContext := closure.sourceContext
  nativeDomain := closure.nativeDomain
  domain := closure.domain
  codomain := closure.codomain
  sourceBody := closure.sourceBody
  typing := closure.typing
  spine := closure.spine
  bodyAdmissible := closure.bodyAdmissible
  current := closure.current
  sourceStore := closure.sourceStore
  valuation := closure.valuation
  targetSig := closure.targetSig
  targetContext := closure.targetContext
  scope := closure.scope
  closing := closure.closing
  nativeEnvironment := closure.nativeEnvironment
  runtimeValue := closure.runtimeValue
  runtimeReady := closure.runtimeReady
  runtime_eq := closure.runtime_eq
  ready := closure.ready
  image := image
  plan_eq := plan_eq.trans closure.plan_eq
  body_heq := body_heq.trans closure.body_heq
  argumentRaw := argumentRaw

private def sourceReadyWeaken
    {storeArity : Nat} {term : LambdaPFC.Tm storeArity}
    (ready : term.IsValue) :
    term.weaken.IsValue := by
  cases ready with
  | abs => exact .abs
  | pair => exact .pair

/-- A retained native closure crosses an unrelated physical allocation.
The wrapper-aware target endpoint and compiled source body are unchanged. -/
noncomputable def nativeWeaken
    (closure : SourceFunctionClosure behavior)
    (allocatedValue : LambdaPFC.Tm closure.current)
    (allocatedReady : allocatedValue.IsValue) :
    SourceFunctionClosure behavior where
  sourceArity := closure.sourceArity
  sourceContext := closure.sourceContext
  nativeDomain := closure.nativeDomain
  domain := closure.domain
  codomain := closure.codomain
  sourceBody := closure.sourceBody
  typing := closure.typing
  spine := closure.spine
  bodyAdmissible := closure.bodyAdmissible
  current := closure.current + 1
  sourceStore := .val closure.sourceStore allocatedValue allocatedReady
  valuation := closure.valuation.weaken
  targetSig := closure.targetSig
  targetContext := closure.targetContext
  scope := closure.scope
  closing := closure.closing
  nativeEnvironment := closure.nativeEnvironment.nativeWeaken allocatedValue
    allocatedReady
  runtimeValue := closure.runtimeValue.weaken
  runtimeReady := sourceReadyWeaken closure.runtimeReady
  runtime_eq := by
    calc
      closure.runtimeValue.weaken =
          ((LambdaPFC.Tm.abs closure.nativeDomain closure.sourceBody).rename
            closure.valuation).weaken :=
        congrArg LambdaPFC.Tm.weaken closure.runtime_eq
      _ = (LambdaPFC.Tm.abs closure.nativeDomain closure.sourceBody).rename
          closure.valuation.weaken :=
        OperationalCode.SourceValuation.rename_weaken _ _
  ready := closure.ready
  image := closure.image
  plan_eq := closure.plan_eq
  body_heq := closure.body_heq
  argumentRaw := closure.argumentRaw

end SourceFunctionClosure

/-- Rich function provenance at one advertised source arrow domain. -/
structure FunctionResultProvenance
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {domain : LambdaPFC.Ty n}
    (domainWf : Fragment.Wf sourceContext domain)
    (closing : ClosingEnv sig [])
    {plan : Interface.BinderPlan []}
    (view : EliminationView plan) : Type where
  closure : SourceFunctionClosure view.argument
  domainPlan_eq :
    closedPlan scope closing domainWf = closure.image.domainPlan

/-- Path coherence plus a logically truncated conditional function witness.
The complete acceptance remains a proposition. -/
structure SourceResultAcceptance
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (closing : ClosingEnv sig [])
    (view : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        closing.substitution))
    (arguments : ClosedArguments n) : Prop where
  paths : BehaviorPathCoherence scope sourceWf closing view arguments
  function :
    {domain codomain : LambdaPFC.Ty n} ->
    (type_eq : sourceType = .Fun domain codomain.weaken) ->
    Nonempty
      (Sigma fun domainWf : Fragment.Wf sourceContext domain =>
        FunctionResultProvenance scope domainWf closing view)

namespace SourceResultAcceptance

/-- Recover the rich closure noncomputably from its logical truncation. -/
noncomputable def chooseFunction
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n}
    {sourceWf : Fragment.Wf sourceContext sourceType}
    {closing : ClosingEnv sig []}
    {view : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        closing.substitution)}
    {arguments : ClosedArguments n}
    (accepted : SourceResultAcceptance scope sourceWf closing view arguments)
    {domain codomain : LambdaPFC.Ty n}
    (type_eq : sourceType = .Fun domain codomain.weaken) :
    Sigma fun domainWf : Fragment.Wf sourceContext domain =>
      FunctionResultProvenance scope domainWf closing view :=
  Classical.choice (accepted.function type_eq)

private def sourceDomain : LambdaPFC.Ty n -> LambdaPFC.Ty n
  | .Fun domain _ => domain
  | _ => .Top

/-- Direct abstraction acceptance. -/
noncomputable def ofFunction
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {nativeDomain domain codomain : LambdaPFC.Ty n}
    {sourceBody : LambdaPFC.Tm (n + 1)}
    {typing : Fragment.HasType sourceContext (.abs nativeDomain sourceBody)
      (.Fun domain codomain.weaken)}
    (spine : ApplicationSpine typing)
    (bodyAdmissible :
      OperationallyAdmissible spine.functionSpine.bodyTyping.2)
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    (valuation : OperationalCode.SourceValuation n current)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (closing : ClosingEnv sig [])
    (nativeEnvironment : OperationalStoreEnvironment.StoreEnvironment
      sourceContext sourceStore valuation targetContext scope closing)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue)
    (runtime_eq : runtimeValue =
      (LambdaPFC.Tm.abs nativeDomain sourceBody).rename valuation)
    (ready :
      (ApplicationValueEvidence.function spine).ClosedReady scope closing)
    (arguments : ClosedArguments n)
    (agreement : ClosedPathAgreement scope closing arguments) :
    SourceResultAcceptance scope typing.typeWf closing
      ((ApplicationValueEvidence.function spine).closedView scope closing
        ready).view arguments where
  paths := BehaviorPathCoherence.ofApplicationValueEvidence
    (ApplicationValueEvidence.function spine) scope closing ready arguments
    agreement
  function := by
    intro otherDomain otherCodomain type_eq
    have domain_eq : domain = otherDomain :=
      congrArg sourceDomain type_eq
    cases domain_eq
    exact
      ⟨⟨spine.domainWf,
        { closure := SourceFunctionClosure.ofApplicationSpine spine
            bodyAdmissible valuation scope closing nativeEnvironment
            runtimeValue runtimeReady runtime_eq ready _ rfl
          domainPlan_eq := rfl }⟩⟩

/-- A noncanonical ordinary result has no arrow case. -/
noncomputable def ofNonCanonical
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (sourceWf : Fragment.Wf sourceContext sourceType)
    (shape : NonCanonicalResultShape sourceType)
    (closing : ClosingEnv sig [])
    (view : EliminationView
      ((TermTranslation.compileBinder scope sourceWf).plan.subst
        closing.substitution))
    (arguments : ClosedArguments n)
    (raw : RawSlot view) :
    SourceResultAcceptance scope sourceWf closing view arguments where
  paths :=
    OperationalApplicationPathCoherence.BehaviorPathCoherence.ofRawNonCanonical
      scope sourceWf shape closing view arguments raw
  function := by
    intro domain codomain type_eq
    exact (shape.notArrow
      { domain := domain
        codomain := codomain.weaken
        equality := type_eq }).elim

end SourceResultAcceptance

end OperationalFunctionResultProvenance
end LambdaPToFCo
