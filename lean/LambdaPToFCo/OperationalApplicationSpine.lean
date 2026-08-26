import LambdaPToFCo.OperationalValueEvidence
import LambdaPToFCo.StaticTranslationIrrel

/-!
# Source application spines and closed argument evidence

`FunctionSpine` identifies the source abstraction and the supported coercions
surrounding it.  Application needs one additional invariant: the base binder
and every intermediate function domain exposed by reflexivity, transitivity,
or arrow subtyping must use an ordinary binder plan.

`ApplicationFunctionCo` and `ApplicationSpine` record exactly that source-only
invariant.  Their closed interpretation constructs the layer-by-layer
`ArgumentEvidence` consumed by the target application theorem.  The outer
argument remains an arbitrary `EliminationView`; the only static connection
required here is equality between its plan and the plan compiled for the
advertised source domain.

This module does not interpret source stores and does not identify a lexical
function slot with a physical heap cell.  That separate lookup premise must
relate the normalized function exposed by an application spine to the current
lexical function behavior.
-/

namespace LambdaPToFCo
namespace OperationalApplicationSpine

open SystemFCo
open StaticTranslation
open OperationalBindingView
open OperationalEnvironment
open OperationalApplication
open OperationalApplicationTranslation
open OperationalValueEvidence

/-! ## Noncanonical executable shapes -/

/-- Source types whose values cannot already be canonical abstraction or
member-package heads.  Native function binders in the executable core use
exactly these shapes, so beta never has to invent canonical-head provenance
for the physical argument location. -/
inductive NonCanonicalResultShape : LambdaPFC.Ty n -> Type where
  | top : NonCanonicalResultShape .Top
  | singleton : NonCanonicalResultShape (.Single path)
  | selection : NonCanonicalResultShape (.TSel path label)

namespace NonCanonicalResultShape

def ordinary : NonCanonicalResultShape sourceType -> OrdinaryShape sourceType
  | .top => .top
  | .singleton => .singleton
  | .selection => .selection

/-- Syntactic evidence that a source type is an arrow. -/
structure ArrowShape (sourceType : LambdaPFC.Ty n) : Type where
  domain : LambdaPFC.Ty n
  codomain : LambdaPFC.Ty (n + 1)
  equality : sourceType = .Fun domain codomain

def NotArrow (sourceType : LambdaPFC.Ty n) : Type :=
  ArrowShape sourceType -> Empty

def notArrow : NonCanonicalResultShape sourceType -> NotArrow sourceType
  | .top, ⟨_, _, equality⟩ => by cases equality
  | .singleton, ⟨_, _, equality⟩ => by cases equality
  | .selection, ⟨_, _, equality⟩ => by cases equality

def notMember (shape : NonCanonicalResultShape sourceType) :
    NotMember sourceType :=
  shape.ordinary.notMember

end NonCanonicalResultShape

/-! ## Source-only application provenance -/

/-- Function-compatible source subtyping whose source, target, and every
transitive intermediate domain has an ordinary binder representation. -/
inductive ApplicationFunctionCo
    {n : Nat} {sourceContext : LambdaPFC.Ctx n} :
    {sourceDomain sourceCodomain targetDomain targetCodomain : LambdaPFC.Ty n} ->
    {subtype : Fragment.Sub sourceContext
      (.Fun sourceDomain sourceCodomain.weaken)
      (.Fun targetDomain targetCodomain.weaken)} ->
    (shape : FragmentFunctionCo subtype) -> Type where
  | refl
      (domainWf : Fragment.Wf sourceContext domain)
      (codomainWf : Fragment.Wf sourceContext codomain)
      (domainShape : OrdinaryShape domain) :
      ApplicationFunctionCo
        (FragmentFunctionCo.refl (.arrow domainWf codomainWf))
  | trans
      {sourceDomain sourceCodomain middleDomain middleCodomain
        targetDomain targetCodomain : LambdaPFC.Ty n}
      {firstSubtype : Fragment.Sub sourceContext
        (.Fun sourceDomain sourceCodomain.weaken)
        (.Fun middleDomain middleCodomain.weaken)}
      {secondSubtype : Fragment.Sub sourceContext
        (.Fun middleDomain middleCodomain.weaken)
        (.Fun targetDomain targetCodomain.weaken)}
      {firstShape : FragmentFunctionCo firstSubtype}
      {secondShape : FragmentFunctionCo secondSubtype}
      (first : ApplicationFunctionCo firstShape)
      (second : ApplicationFunctionCo secondShape) :
      ApplicationFunctionCo (.trans firstShape secondShape)
  | arrow
      {sourceDomain sourceCodomain targetDomain targetCodomain : LambdaPFC.Ty n}
      (domain : Fragment.Sub sourceContext targetDomain sourceDomain)
      (codomain : Fragment.Sub sourceContext sourceCodomain targetCodomain)
      (sourceDomainShape : OrdinaryShape sourceDomain)
      (targetDomainShape : OrdinaryShape targetDomain) :
      ApplicationFunctionCo (FragmentFunctionCo.arrow domain codomain)

namespace ApplicationFunctionCo

/-- Forget the strengthened domain invariant and recover the original
function-coercion provenance. -/
def fragment {shape : FragmentFunctionCo subtype}
    (_ : ApplicationFunctionCo shape) : FragmentFunctionCo subtype :=
  shape

def sourceDomainWf :
    ApplicationFunctionCo (n := n) (sourceContext := sourceContext)
      (sourceDomain := sourceDomain) (sourceCodomain := sourceCodomain)
      (targetDomain := targetDomain) (targetCodomain := targetCodomain)
      shape ->
    Fragment.Wf sourceContext sourceDomain
  | .refl domainWf _ _ => domainWf
  | .trans first _ => first.sourceDomainWf
  | .arrow domain _ _ _ => domain.targetWf

def targetDomainWf :
    ApplicationFunctionCo (n := n) (sourceContext := sourceContext)
      (sourceDomain := sourceDomain) (sourceCodomain := sourceCodomain)
      (targetDomain := targetDomain) (targetCodomain := targetCodomain)
      shape ->
    Fragment.Wf sourceContext targetDomain
  | .refl domainWf _ _ => domainWf
  | .trans _ second => second.targetDomainWf
  | .arrow domain _ _ _ => domain.sourceWf

def sourceDomainShape :
    ApplicationFunctionCo (n := n) (sourceContext := sourceContext)
      (sourceDomain := sourceDomain) (sourceCodomain := sourceCodomain)
      (targetDomain := targetDomain) (targetCodomain := targetCodomain)
      shape ->
    OrdinaryShape sourceDomain
  | .refl _ _ domainShape => domainShape
  | .trans first _ => first.sourceDomainShape
  | .arrow _ _ sourceShape _ => sourceShape

def targetDomainShape :
    ApplicationFunctionCo (n := n) (sourceContext := sourceContext)
      (sourceDomain := sourceDomain) (sourceCodomain := sourceCodomain)
      (targetDomain := targetDomain) (targetCodomain := targetCodomain)
      shape ->
    OrdinaryShape targetDomain
  | .refl _ _ domainShape => domainShape
  | .trans _ second => second.targetDomainShape
  | .arrow _ _ _ targetShape => targetShape

end ApplicationFunctionCo

/-- A native abstraction spine strengthened with ordinary-domain evidence at
the base abstraction and through every surrounding function coercion. -/
inductive ApplicationSpine
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {nativeDomain : LambdaPFC.Ty n}
    {sourceBody : LambdaPFC.Tm (n + 1)} :
    {domain codomain : LambdaPFC.Ty n} ->
    (typing : Fragment.HasType sourceContext (.abs nativeDomain sourceBody)
      (.Fun domain codomain.weaken)) -> Type where
  | abs
      (bodyTyping : Fragment.HasType (sourceContext.snoc nativeDomain)
        sourceBody nativeCodomain.weaken)
      (domainWf : Fragment.Wf sourceContext nativeDomain)
      (codomainWf : Fragment.Wf sourceContext nativeCodomain)
      (domainShape : NonCanonicalResultShape nativeDomain) :
      ApplicationSpine (.abs bodyTyping domainWf codomainWf)
  | sub
      {sourceDomain sourceCodomain targetDomain targetCodomain : LambdaPFC.Ty n}
      {innerTyping : Fragment.HasType sourceContext
        (.abs nativeDomain sourceBody)
        (.Fun sourceDomain sourceCodomain.weaken)}
      {subtype : Fragment.Sub sourceContext
        (.Fun sourceDomain sourceCodomain.weaken)
        (.Fun targetDomain targetCodomain.weaken)}
      {shape : FragmentFunctionCo subtype}
      (inner : ApplicationSpine innerTyping)
      (coercion : ApplicationFunctionCo shape) :
      ApplicationSpine (.sub innerTyping subtype)

namespace ApplicationSpine

/-- Forget the ordinary-domain strengthening. -/
def functionSpine :
    ApplicationSpine (sourceContext := sourceContext) typing ->
      FunctionSpine typing
  | .abs bodyTyping domainWf codomainWf _ =>
      .abs bodyTyping domainWf codomainWf
  | .sub inner coercion =>
      .sub inner.functionSpine coercion.fragment

/-- Well-formedness of the domain advertised by the outermost function
type. -/
def domainWf :
    ApplicationSpine (sourceContext := sourceContext)
      (domain := domain) (codomain := codomain) typing ->
    Fragment.Wf sourceContext domain
  | .abs _ domainWf _ _ => domainWf
  | .sub _ coercion => coercion.targetDomainWf

/-- The outermost advertised function domain is ordinary. -/
def domainShape :
    ApplicationSpine (sourceContext := sourceContext)
      (domain := domain) (codomain := codomain) typing ->
    OrdinaryShape domain
  | .abs _ _ _ shape => shape.ordinary
  | .sub _ coercion => coercion.targetDomainShape

end ApplicationSpine

/-! ## Heap-storable value evidence -/

/-- Physical values retain the stronger application spine for functions,
while exact packages keep their canonical package spine.  Forgetting this to
plain `ValueEvidence` is always possible; reconstructing it after heap lookup
is not. -/
inductive ApplicationValueEvidence :
    {n : Nat} -> {sourceContext : LambdaPFC.Ctx n} ->
    {term : LambdaPFC.Tm n} -> {sourceType : LambdaPFC.Ty n} ->
    (typing : Fragment.HasType sourceContext term sourceType) -> Type where
  | function
      {n : Nat} {sourceContext : LambdaPFC.Ctx n}
      {nativeDomain domain codomain : LambdaPFC.Ty n}
      {body : LambdaPFC.Tm (n + 1)}
      {typing : Fragment.HasType sourceContext
        (.abs nativeDomain body) (.Fun domain codomain.weaken)}
      (spine : ApplicationSpine typing) : ApplicationValueEvidence typing
  | package
      {typing : Fragment.HasType sourceContext
        (.pair first label (.type witness)) sourceType}
      (spine : ExactPackageSpine typing) : ApplicationValueEvidence typing

namespace ApplicationValueEvidence

/-- Forget application-specific ordinary-domain evidence. -/
def valueEvidence
    {typing : Fragment.HasType sourceContext term sourceType} :
    ApplicationValueEvidence typing -> ValueEvidence typing
  | .function spine => .function spine.functionSpine
  | .package spine => .package spine

def isValue
    {typing : Fragment.HasType sourceContext term sourceType}
    (evidence : ApplicationValueEvidence typing) :
    LambdaPFC.Tm.IsValue term :=
  evidence.valueEvidence.isValue

def ClosedReady
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext term sourceType}
    (evidence : ApplicationValueEvidence typing)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig []) : Prop :=
  evidence.valueEvidence.ClosedReady scope environment

noncomputable def closedView
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext term sourceType}
    (evidence : ApplicationValueEvidence typing)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (ready : evidence.ClosedReady scope environment) :
    OperationalPackageBehavior.ClosedView scope typing environment :=
  evidence.valueEvidence.closedView scope environment ready

end ApplicationValueEvidence

/-! ## Closed binder plans -/

/-- The target binder plan generated for a source type and then closed by a
lexical target environment. -/
noncomputable def closedPlan
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (wf : Fragment.Wf sourceContext sourceType) : Interface.BinderPlan [] :=
  (TermTranslation.compileBinder scope wf).plan.subst
    environment.substitution

/-- Proof choices in source well-formedness do not affect a closed ordinary
binder plan.  This is the only proof-irrelevance transport needed by the
application-spine construction. -/
theorem closedPlan_irrel_of_ordinary
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (left right : Fragment.Wf sourceContext sourceType)
    (shape : OrdinaryShape sourceType) :
    closedPlan scope environment left = closedPlan scope environment right := by
  unfold closedPlan
  rw [OperationalValueEvidence.compileBinder_plan_ordinary scope left shape]
  rw [OperationalValueEvidence.compileBinder_plan_ordinary scope right shape]
  rw [translateType_irrel scope left right]

/-! ## Closed argument evidence -/

namespace ApplicationFunctionCo

/-- Interpret a strengthened source function coercion as the target
argument adaptation it requires.

The source callback handles the already-normalized inner function.  A plan
equality is passed separately so the returned `ArgumentEvidence` remains
indexed by the caller's original view instead of an `Eq.rec`-cast copy. -/
noncomputable def argumentEvidence
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
    {outerPlan : Interface.BinderPlan []}
    (outer : EliminationView outerPlan)
    (outerPlan_eq :
      outerPlan = closedPlan scope environment coercion.targetDomainWf) :
    ArgumentEvidence
      ((shape.close scope environment).normalize function).value outer := by
  induction coercion generalizing plan result body outerPlan with
  | refl domainWf codomainWf domainShape =>
      exact sourceEvidence outer outerPlan_eq
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
          firstIH function sourceEvidence middle
            (middlePlan_eq.trans
              (closedPlan_irrel_of_ordinary scope environment
                second.sourceDomainWf first.targetDomainWf
                second.sourceDomainShape))
      exact secondIH firstNormalization.value middleEvidence outer outerPlan_eq
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
      exact .arrow outer raw (sourceEvidence raw.view rawPlan_eq)

end ApplicationFunctionCo

namespace ApplicationSpine

/-- Construct target argument evidence for a closed native abstraction
spine.  Transitive coercions are traversed from the outermost target domain
back toward the base lambda; each arrow layer uses `AdaptedArgument.ordinary`
to normalize its pushed contravariant cast. -/
noncomputable def argumentEvidence
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
    (outerPlan_eq : outerPlan = closedPlan scope environment spine.domainWf) :
    ArgumentEvidence
      (spine.functionSpine.close scope environment).image.view.normalize.value
      outer := by
  induction spine generalizing outerPlan with
  | abs bodyTyping domainWf codomainWf domainShape =>
      cases outerPlan_eq
      exact .lambda outer
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
          ih source
            (sourcePlan_eq.trans
              (closedPlan_irrel_of_ordinary scope environment
                coercion.sourceDomainWf inner.domainWf
                coercion.sourceDomainShape))
      exact coercion.argumentEvidence scope environment
        (inner.functionSpine.close scope environment).image.view.normalize.value
        sourceEvidence outer outerPlan_eq

end ApplicationSpine

end OperationalApplicationSpine
end LambdaPToFCo
