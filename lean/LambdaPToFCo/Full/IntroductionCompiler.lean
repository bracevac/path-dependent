import LambdaPToFCo.Full.WfPlan

/-!
# Full term-introduction compilation

This module starts the syntax-directed term layer with constructors whose
static inputs are already sealed by the full interface development.  In
particular, dependent abstraction uses the exact positive codomain plan
produced by compiling its body; it does not ask for a `Tau.Wf` derivation of
the codomain, which full `LambdaPFC` typing does not provide in general.
-/

namespace LambdaPToFCo.Full.IntroductionCompiler

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

/-- Compile a source abstraction from a bidirectional domain model and the
compiled body package under that exact opened domain. -/
noncomputable def abstraction
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {domain : LambdaPFC.Ty n} {body : LambdaPFC.Tm (n + 1)}
    {codomain : LambdaPFC.Ty (n + 1)}
    (bodyTyping : LambdaPFC.Tm.Ty (sourceContext.snoc domain) body codomain)
    (domainResult : WfPlan.Proper sourceContext targetContext scope domain)
    (codomainResult : PositivePlan (sourceContext.snoc domain)
      (domainResult.plan.context targetContext)
      (scope.bindBidirectional domainResult.model).view codomain)
    (compiledBody : CompiledPackage
      (domainResult.plan.context targetContext) codomainResult.plan) :
    OrdinaryProducer sourceContext targetContext scope
      (.Fun domain codomain) where
  origin := .value (.abs bodyTyping domainResult.wf) .abs
  model :=
    ⟨Function.plan domainResult.plan codomainResult.plan,
      .function domainResult.model codomainResult.modeled⟩
  package :=
    { expression := Function.exactAbstractionPackage domainResult.plan
        codomainResult.plan compiledBody.expression compiledBody.typing
      typing := Function.exactAbstractionPackage_hasType domainResult.plan
        codomainResult.plan compiledBody.expression compiledBody.typing }

end LambdaPToFCo.Full.IntroductionCompiler
