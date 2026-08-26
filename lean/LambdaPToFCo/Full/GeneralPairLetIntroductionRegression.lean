import LambdaPToFCo.Full.LetIntroductionCompiler
import LambdaPToFCo.Full.GeneralPairClosedStaticRegression
import LambdaPToFCo.Full.NormalizedTermCompilationRegression

/-!
# Generic let-introduction regression for GeneralPair

This leaf rebuilds the final GeneralPair Church closure through the generic
let-introduction compiler.  Both subterms enter as exact `TermCompilation`
certificates: the bound abstraction is the canonical normalized result, and
the body producer reuses the already sealed two-step interval adaptation at
the exact demand-local body plan.

The output is the direct `.letResult` producer and its normalized direct-let
certificate.  The single body-plan bridge is reflexivity; no root resolver,
package, adapter, or plan choice is supplied.
-/

namespace LambdaPToFCo.Full.GeneralPairLetIntroductionRegression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

noncomputable section

noncomputable def bound :=
  NormalizedTermCompilationRegression.normalized.finishedProducer
    NormalizedTermCompilationRegression.adaptation
    GeneralPairLetPlanningRegression.domainResult.model.producer

noncomputable def boundCompilation : TermCompilation
    GeneralPairLetPlanningRegression.boundSourceTyping
    GeneralPairLetPlanningRegression.rootScope (.ordinary bound) :=
  NormalizedTermCompilationRegression.compilation

/-- Rebuild the exact two source subsumptions from the same public derivations
consumed by the two sealed interval-pair adaptations. -/
def bodyTyping : Tm.Ty (LambdaPFC.Ctx.nil.snoc .Top)
    GeneralPairIntroductionStaticRegression.exactBody
    LambdaPFC.GeneralPairRegression.intervalTarget.weaken :=
  .sub
    (.sub GeneralPairIntroductionStaticRegression.exactBodySourceTyping
      GeneralPairObservedIntervalSubtypingRegression.pairSubtyping
      GeneralPairObservedIntervalSubtypingRegression.targetResult.wf)
    GeneralPairCanonicalIntervalSubtypingRegression.pairSubtyping
    GeneralPairCanonicalIntervalSubtypingRegression.targetResult.wf

noncomputable def bodyScope :=
  LetPlanning.bodyScope GeneralPairLetPlanningRegression.rootScope bound

theorem bodyScope_eq :
    bodyScope = GeneralPairIntroductionStaticRegression.bodyScope := by
  rfl

/-- Canonical body producer at the exact plan chosen by the generic let
planner. -/
noncomputable def bodyProducer : OrdinaryProducer
    (LambdaPFC.Ctx.nil.snoc .Top)
    (bound.plan.context SystemFCoExt.Ctx.empty) bodyScope
    LambdaPFC.GeneralPairRegression.intervalTarget.weaken where
  origin := ProducerOrigin.ofTyping bodyTyping
  model :=
    ⟨(LetPlanning.bodyDemand GeneralPairLetPlanningRegression.rootScope
      bound GeneralPairLetPlanningRegression.rootResult).plan,
      GeneralPairCanonicalIntervalSubtypingRegression.pushed.modeled⟩
  package := GeneralPairClosedStaticRegression.bodyPackage

noncomputable def bodyCompilation : TermCompilation bodyTyping bodyScope
    (.ordinary bodyProducer) where
  origin_eq := rfl

noncomputable def bodyAtDemand :
    LetIntroductionCompiler.BodyCompilationAtDemand
      GeneralPairLetPlanningRegression.rootScope bound
      GeneralPairLetPlanningRegression.rootResult bodyTyping where
  producer := .ordinary bodyProducer
  compilation := bodyCompilation
  plan_eq := rfl

/-- Generic direct-let compilation of the complete closed regression. -/
noncomputable def normalized :=
  LetIntroductionCompiler.compile
    GeneralPairLetPlanningRegression.boundSourceTyping boundCompilation
    GeneralPairLetPlanningRegression.rootResult bodyTyping bodyAtDemand

noncomputable def compiledProducer :=
  LetIntroductionCompiler.producer
    GeneralPairLetPlanningRegression.boundSourceTyping boundCompilation
    GeneralPairLetPlanningRegression.rootResult bodyTyping bodyAtDemand

noncomputable def targetTerm_hasType :
    Exp.HasType SystemFCoExt.Ctx.empty
      compiledProducer.package.expression compiledProducer.plan.inputTy :=
  compiledProducer.package.typing

end

end LambdaPToFCo.Full.GeneralPairLetIntroductionRegression
