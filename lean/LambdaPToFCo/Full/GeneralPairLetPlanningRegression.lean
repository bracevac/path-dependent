import LambdaPToFCo.Full.GeneralPairIntroductionStaticRegression
import LambdaPToFCo.Full.IntroductionCompiler
import LambdaPToFCo.Full.DemandDirectedSubtyping
import LambdaPToFCo.Full.LetPlanning

/-!
# Closed GeneralPair bound and let-result planning

This leaf compiles the abstraction bound by `GeneralPairRegression.term`,
adapts it to its advertised `Top` type, and constructs the exact root plan for
the final interval-pair result.  The resulting bound scope is definitionally
the scope used by the demand-local body-introduction regression, so the final
body package can be closed through `LetPlanning` without a global resolver or
root-plan factorization.

It deliberately stops before compiling the two body subsumptions; those are
separate derivation-directed bridge obligations.
-/

namespace LambdaPToFCo.Full.GeneralPairLetPlanningRegression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open DemandDirectedSubtyping

noncomputable section

def rootScope := GeneralPairIntroductionStaticRegression.rootScope

def domainResult := WfPlan.Proper.top rootScope

noncomputable def functionBodyScope :=
  rootScope.bindBidirectional domainResult.model

def functionBodyTyping :
    Tm.Ty (LambdaPFC.Ctx.nil.snoc .Top) (.path (.var 0)) .Top :=
  .sub (.path .var) (.widen .var) .top

noncomputable def functionBodyPath :=
  functionBodyScope.variablePath (0 : Fin 1)

noncomputable def codomainResult := WfPlan.Proper.top functionBodyScope

/-- The exact dependent identity function before the source `Top`
subsumption. -/
noncomputable def exactFunction : OrdinaryProducer LambdaPFC.Ctx.nil
    SystemFCoExt.Ctx.empty rootScope (.Fun .Top .Top) :=
  IntroductionCompiler.abstraction rootScope functionBodyTyping domainResult
    codomainResult.positive functionBodyPath.package

def functionSubtyping : Tau.Sub LambdaPFC.Ctx.nil
    (.ty (.Fun .Top .Top)) (.ty .Top) :=
  .top

noncomputable def topDemand := domainResult.demand

noncomputable def boundAdaptation : FusedAdaptation
    (ScopeAlignment.identity rootScope.view) functionSubtyping
    (.ordinary exactFunction) topDemand :=
  FusedAdaptation.toOpaque (ScopeAlignment.identity rootScope.view)
    functionSubtyping (.ordinary exactFunction) (DemandTrace.ofWf .top)

/-- The compiled bound at the exact advertised `Top` plan. -/
noncomputable def bound : OrdinaryProducer LambdaPFC.Ctx.nil
    SystemFCoExt.Ctx.empty rootScope .Top :=
  boundAdaptation.toOrdinary domainResult.model.producer

def boundSourceTyping :
    Tm.Ty LambdaPFC.Ctx.nil
      (.abs .Top (.path (.var 0))) .Top :=
  .sub (.abs functionBodyTyping .top) .top .top

theorem bound_origin_eq : bound.origin =
    ProducerOrigin.push functionSubtyping
      (ProducerOrigin.value (.abs functionBodyTyping .top) .abs) := by
  rfl

noncomputable def rootFirst := WfPlan.Proper.top rootScope

noncomputable def rootMemberScope :=
  rootScope.bindBidirectional rootFirst.model

noncomputable def rootLower := WfPlan.Proper.bottom rootMemberScope
noncomputable def rootUpper := WfPlan.Proper.top rootMemberScope

noncomputable def rootInterval :=
  WfPlan.Interval.bounds rootMemberScope rootLower rootUpper
    (Tau.Sub.bot : Tau.Sub (LambdaPFC.Ctx.nil.snoc .Top)
      (.ty .Bot) (.ty .Top))

/-- Exact root result plan for the closed source regression. -/
noncomputable def rootResult : WfPlan.Proper LambdaPFC.Ctx.nil
    SystemFCoExt.Ctx.empty rootScope
    LambdaPFC.GeneralPairRegression.intervalTarget := by
  simpa [LambdaPFC.GeneralPairRegression.intervalTarget] using
    (WfPlan.Proper.intervalPair
      (label := LambdaPFC.GeneralPairRegression.label)
      rootScope rootFirst rootInterval)

/-- The exact negative interface against which the source let body must be
compiled before Church-package closure. -/
noncomputable def plannedBodyDemand :=
  LetPlanning.bodyDemand rootScope bound rootResult

/-- The compiled bound opens precisely the existing body scope. -/
theorem bodyScope_eq : LetPlanning.bodyScope rootScope bound =
    GeneralPairIntroductionStaticRegression.bodyScope := by
  rfl

end

end LambdaPToFCo.Full.GeneralPairLetPlanningRegression
