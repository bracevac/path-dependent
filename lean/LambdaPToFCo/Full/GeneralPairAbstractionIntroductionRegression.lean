import LambdaPToFCo.Full.AbstractionIntroductionCompiler
import LambdaPToFCo.Full.GeneralPairLetPlanningRegression

/-!
# Generic abstraction-introduction regression for GeneralPair

The GeneralPair bound begins as the dependent identity abstraction
`fun (x : Top) => x`.  Its body typing widens the singleton path to `Top`, so
the canonical body origin is proof-relevantly the normalized typing origin,
not merely the lower path producer's origin.

This leaf certifies that canonical body package at the exact positive `Top`
codomain plan and rebuilds the abstraction through the generic high compiler.
The resulting producer has the direct `.value (.abs ...)` origin and a
`NormalizedTermCompilation`; no raw body package or plan is supplied.
-/

namespace LambdaPToFCo.Full.GeneralPairAbstractionIntroductionRegression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

noncomputable section

/-- Canonical body producer reusing the already translated variable package. -/
noncomputable def bodyProducer : OrdinaryProducer
    (LambdaPFC.Ctx.nil.snoc .Top)
    (GeneralPairLetPlanningRegression.domainResult.plan.context
      SystemFCoExt.Ctx.empty)
    GeneralPairLetPlanningRegression.functionBodyScope .Top where
  origin := ProducerOrigin.ofTyping
    GeneralPairLetPlanningRegression.functionBodyTyping
  model :=
    ⟨GeneralPairLetPlanningRegression.codomainResult.plan,
      GeneralPairLetPlanningRegression.codomainResult.model.producer⟩
  package := GeneralPairLetPlanningRegression.functionBodyPath.package

noncomputable def bodyCompilation : TermCompilation
    GeneralPairLetPlanningRegression.functionBodyTyping
    GeneralPairLetPlanningRegression.functionBodyScope
    (.ordinary bodyProducer) where
  origin_eq := rfl

noncomputable def bodyAtPositivePlan :
    AbstractionIntroductionCompiler.BodyCompilationAtPositivePlan
      GeneralPairLetPlanningRegression.rootScope
      GeneralPairLetPlanningRegression.domainResult
      GeneralPairLetPlanningRegression.functionBodyTyping
      GeneralPairLetPlanningRegression.codomainResult.positive where
  producer := .ordinary bodyProducer
  compilation := bodyCompilation
  plan_eq := rfl

/-- Generic direct compilation of the exact GeneralPair abstraction. -/
noncomputable def normalized :=
  AbstractionIntroductionCompiler.compile
    GeneralPairLetPlanningRegression.domainResult
    GeneralPairLetPlanningRegression.functionBodyTyping
    GeneralPairLetPlanningRegression.codomainResult.positive
    bodyAtPositivePlan

noncomputable def compiledProducer :=
  AbstractionIntroductionCompiler.producer
    GeneralPairLetPlanningRegression.domainResult
    GeneralPairLetPlanningRegression.functionBodyTyping
    GeneralPairLetPlanningRegression.codomainResult.positive
    bodyAtPositivePlan

theorem origin_eq : compiledProducer.origin =
    ProducerOrigin.value
      (.abs GeneralPairLetPlanningRegression.functionBodyTyping .top) .abs := by
  rfl

noncomputable def targetTerm_hasType :
    Exp.HasType SystemFCoExt.Ctx.empty
      compiledProducer.package.expression compiledProducer.plan.inputTy :=
  compiledProducer.package.typing

end

end LambdaPToFCo.Full.GeneralPairAbstractionIntroductionRegression
