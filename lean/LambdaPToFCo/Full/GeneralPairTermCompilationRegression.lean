import LambdaPToFCo.Full.TermCompilation
import LambdaPToFCo.Full.GeneralPairClosedStaticRegression

/-!
# Exact term-compilation certificate for GeneralPair

This leaf packages the existing closed unrestricted GeneralPair regression in
the generic `TermCompilation` carrier.  Its producer reuses the already
computed root plan, structural model, and closed package; its origin is the
canonical provenance of the existing full source typing derivation.  No new
term compiler, adapter, resolver, or target package is supplied.
-/

namespace LambdaPToFCo.Full.GeneralPairTermCompilationRegression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

noncomputable section

noncomputable def producer : OrdinaryProducer LambdaPFC.Ctx.nil
    SystemFCoExt.Ctx.empty GeneralPairLetPlanningRegression.rootScope
    LambdaPFC.GeneralPairRegression.intervalTarget where
  origin := ProducerOrigin.ofTyping
    GeneralPairClosedStaticRegression.sourceTyping
  model :=
    ⟨GeneralPairLetPlanningRegression.rootResult.plan,
      GeneralPairLetPlanningRegression.rootResult.model.producer⟩
  package := GeneralPairClosedStaticRegression.compiled

/-- The closed GeneralPair target is certified against its exact source
typing and exact indexed producer. -/
noncomputable def compilation : TermCompilation
    GeneralPairClosedStaticRegression.sourceTyping
    GeneralPairLetPlanningRegression.rootScope (.ordinary producer) where
  origin_eq := rfl

noncomputable def compiledPlan : ValuePlan [] :=
  compilation.plan

noncomputable def compiledPackage : CompiledPackage SystemFCoExt.Ctx.empty
    compilation.plan :=
  compilation.package

noncomputable def targetTerm_hasType :
    Exp.HasType SystemFCoExt.Ctx.empty compiledPackage.expression
      compiledPlan.inputTy :=
  compilation.typing

end

end LambdaPToFCo.Full.GeneralPairTermCompilationRegression
