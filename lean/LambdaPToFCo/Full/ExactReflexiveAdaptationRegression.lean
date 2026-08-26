import LambdaPToFCo.Full.DemandDirectedSubtyping
import LambdaPToFCo.Full.WfPlan

/-!
# Exact-plan reflexive static adaptation

This focused regression opens one structural `Top` binder, resolves its exact
variable package, and adapts that retained ordinary package along source
`.refl` to a demand definitionally indexed by the same plan.  The sealed
constructor computes stable identity internally: no plan equality, adapter,
coercion, package callback, or path resolver is supplied.
-/

namespace LambdaPToFCo.Full.ExactReflexiveAdaptationRegression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open DemandDirectedSubtyping

noncomputable section

def rootScope : ScopeModel LambdaPFC.Ctx.nil SystemFCoExt.Ctx.empty :=
  ScopeModel.empty SystemFCoExt.Ctx.empty

noncomputable def rootTop := WfPlan.Proper.top rootScope

abbrev SourceContext : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc .Top

abbrev TargetContext :=
  rootTop.plan.context SystemFCoExt.Ctx.empty

noncomputable def scope : ScopeModel SourceContext TargetContext :=
  rootScope.bindBidirectional rootTop.model

def precise : Path.Ty SourceContext (.var 0) (.ty .Top) :=
  .var

noncomputable def translated := scope.variablePath (0 : Fin 1)

/-- The exact variable package, re-exposed at its precise referent type. -/
noncomputable def source : OrdinaryProducer SourceContext TargetContext scope
    .Top :=
  translated.preciseProducer

/-- Negative `Top` evidence transported through the very binder whose
variable package is retained by `source`. -/
noncomputable def demandModel : DemandPlanModel SourceContext TargetContext
    scope.view .Top source.plan := by
  exact .underBinding rootTop.model.producer rootTop.model.demand

noncomputable def demand : ProperDemand SourceContext TargetContext scope
    .Top where
  trace := DemandTrace.ofWf Tau.Wf.top
  model := ⟨source.plan, demandModel⟩

/-- Reflexivity consumes no caller-supplied equality or adapter. -/
noncomputable def adaptation : FusedAdaptation
    (ScopeAlignment.identity scope.view)
    (Tau.Sub.refl (τ := .ty (.Top : LambdaPFC.Ty 1)))
    (.ordinary source) demand :=
  FusedAdaptation.reflExact (ScopeAlignment.identity scope.view) source
    (DemandTrace.ofWf Tau.Wf.top) demandModel

noncomputable def compiled : OrdinaryProducer SourceContext TargetContext
    scope .Top :=
  adaptation.toOrdinary source.modeled

theorem compiled_origin_eq : compiled.origin =
    .push (Tau.Sub.refl (τ := .ty (.Top : LambdaPFC.Ty 1))) source.origin := by
  rfl

noncomputable def targetTerm := compiled.package.expression

noncomputable def targetTerm_hasType :
    Exp.HasType TargetContext targetTerm compiled.plan.inputTy :=
  compiled.package.typing

end

end LambdaPToFCo.Full.ExactReflexiveAdaptationRegression
