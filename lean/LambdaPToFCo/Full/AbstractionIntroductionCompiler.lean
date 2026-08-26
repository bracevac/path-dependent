import LambdaPToFCo.Full.IntroductionCompiler
import LambdaPToFCo.Full.NormalizedTermCompilation

/-!
# Certified direct abstraction introduction

This high leaf connects the local abstraction kernel to exact source-term
certificates.  A demand-local `WfPlan.Proper` fixes the domain interface, and
an already certified body package is sealed at one positive codomain plan.
The leaf invokes `IntroductionCompiler.abstraction` internally and returns
the direct value producer together with its `NormalizedTermCompilation`.

It does not compile the body, choose a codomain plan, adapt a subtyping suffix,
or claim total term compilation.  No raw package, adapter, or callback enters
the interface.
-/

namespace LambdaPToFCo.Full.AbstractionIntroductionCompiler

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

/-- One exact body compilation at the positive codomain plan consumed by the
abstraction kernel.  The current `TermCompilation` hides its plan behind the
indexed producer, so this wrapper seals the sole required equality and exposes
only the transported certified package. -/
structure BodyCompilationAtPositivePlan
    (scope : ScopeModel sourceContext targetContext)
    {domain : LambdaPFC.Ty n}
    (domainResult : WfPlan.Proper sourceContext targetContext scope domain)
    {body : LambdaPFC.Tm (n + 1)} {codomain : LambdaPFC.Ty (n + 1)}
    (bodyTyping : Tm.Ty (sourceContext.snoc domain) body codomain)
    (codomainResult : PositivePlan (sourceContext.snoc domain)
      (domainResult.plan.context targetContext)
      (scope.bindBidirectional domainResult.model).view codomain) : Type where
  producer : ProperProducer (sourceContext.snoc domain)
    (domainResult.plan.context targetContext)
    (scope.bindBidirectional domainResult.model) codomain
  compilation : TermCompilation bodyTyping
    (scope.bindBidirectional domainResult.model) producer
  plan_eq : compilation.plan = codomainResult.plan

namespace BodyCompilationAtPositivePlan

/-- The exact certified package expected by the low abstraction compiler. -/
noncomputable def package
    {scope : ScopeModel sourceContext targetContext}
    {domain : LambdaPFC.Ty n}
    {domainResult : WfPlan.Proper sourceContext targetContext scope domain}
    {body : LambdaPFC.Tm (n + 1)} {codomain : LambdaPFC.Ty (n + 1)}
    {bodyTyping : Tm.Ty (sourceContext.snoc domain) body codomain}
    {codomainResult : PositivePlan (sourceContext.snoc domain)
      (domainResult.plan.context targetContext)
      (scope.bindBidirectional domainResult.model).view codomain}
    (compiled : BodyCompilationAtPositivePlan scope domainResult bodyTyping
      codomainResult) :
    CompiledPackage (domainResult.plan.context targetContext)
      codomainResult.plan := by
  rw [← compiled.plan_eq]
  exact compiled.compilation.package

end BodyCompilationAtPositivePlan

/-- The exact direct abstraction typing introduced by this leaf. -/
def sourceTyping
    {scope : ScopeModel sourceContext targetContext}
    {domain : LambdaPFC.Ty n}
    {body : LambdaPFC.Tm (n + 1)} {codomain : LambdaPFC.Ty (n + 1)}
    (bodyTyping : Tm.Ty (sourceContext.snoc domain) body codomain)
    (domainResult : WfPlan.Proper sourceContext targetContext scope domain) :
    Tm.Ty sourceContext (.abs domain body) (.Fun domain codomain) :=
  .abs bodyTyping domainResult.wf

/-- Invoke the sealed abstraction kernel and retain its exact direct value
origin. -/
noncomputable def producer
    {scope : ScopeModel sourceContext targetContext}
    {domain : LambdaPFC.Ty n}
    (domainResult : WfPlan.Proper sourceContext targetContext scope domain)
    {body : LambdaPFC.Tm (n + 1)} {codomain : LambdaPFC.Ty (n + 1)}
    (bodyTyping : Tm.Ty (sourceContext.snoc domain) body codomain)
    (codomainResult : PositivePlan (sourceContext.snoc domain)
      (domainResult.plan.context targetContext)
      (scope.bindBidirectional domainResult.model).view codomain)
    (compiledBody : BodyCompilationAtPositivePlan scope domainResult
      bodyTyping codomainResult) :
    OrdinaryProducer sourceContext targetContext scope (.Fun domain codomain) :=
  IntroductionCompiler.abstraction scope bodyTyping domainResult
    codomainResult compiledBody.package

/-- Package the computed direct abstraction at the normalized introduction
boundary.  Any outer accumulated suffix remains a separate exact
`NormalizedTermCompilation.finish` step. -/
noncomputable def compile
    {scope : ScopeModel sourceContext targetContext}
    {domain : LambdaPFC.Ty n}
    (domainResult : WfPlan.Proper sourceContext targetContext scope domain)
    {body : LambdaPFC.Tm (n + 1)} {codomain : LambdaPFC.Ty (n + 1)}
    (bodyTyping : Tm.Ty (sourceContext.snoc domain) body codomain)
    (codomainResult : PositivePlan (sourceContext.snoc domain)
      (domainResult.plan.context targetContext)
      (scope.bindBidirectional domainResult.model).view codomain)
    (compiledBody : BodyCompilationAtPositivePlan scope domainResult
      bodyTyping codomainResult) :
    NormalizedTermCompilation (sourceTyping bodyTyping domainResult) scope
      (.ordinary (producer domainResult bodyTyping codomainResult
        compiledBody)) where
  root_origin_eq := rfl

end LambdaPToFCo.Full.AbstractionIntroductionCompiler
