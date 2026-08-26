import LambdaPToFCo.Full.SubtypingCompilerCore

/-!
# Closed structural rebase provenance

An arbitrary `ScopeAlignment` preserves stable identity and payload, but does
not remember how either scope was built.  In particular, it cannot be
inverted through `ScopeView.bindPlan`, so it is not sufficient by itself to
transport the `bound` and `underBinding` constructors of
`ProducerPlanModel`.

`ScopeRebase` is the deliberately narrower provenance used by heterogeneous
reflexivity.  Its history is generated only by identity and by opening the
same certified `ValuePlan` on both sides.  The two scope views are therefore
propositionally equal, while their `ScopeModel.slot` proofs may differ.  This
is exactly enough to transport every sealed proper, interval, and
bidirectional plan model without changing its plan.  Consequently the
package adapter exposed to `pushRefl` and `pullRefl` is honest identity.

Differing-plan binders and arbitrary `snocExisting` alignments are excluded:
they require a later common-context open/adapt bridge, not a fabricated
factorization of `ScopeAlignment`.
-/

namespace LambdaPToFCo.Full.TranslationModelRebase

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open SubtypingCompilerCore

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

namespace ScopeAlignment

/-- Opening the same complete value plan on two aligned views preserves the
older alignment under the plan telescope and installs the same canonical
newest interface. -/
noncomputable def bindSamePlan
    {left right : ScopeView n targetContext}
    (alignment : ScopeAlignment left right) (plan : ValuePlan sig) :
    ScopeAlignment (TranslationInterfaces.ScopeView.bindPlan left plan)
      (TranslationInterfaces.ScopeView.bindPlan right plan) :=
  (alignment.rename plan.telescope.weaken
      (plan.telescope.weaken_typed targetContext)).snoc
    (SlotAlignment.identity
      (ValueInterface.ofArguments (plan.rename plan.telescope.weaken)
        (Telescope.Args.identity plan.telescope targetContext)))

end ScopeAlignment

/-! ## Closed construction history -/

/-- Proof-relevant history of the only scope changes whose predecessor can be
recovered structurally.  Both sides of `bind` use the exact same target plan;
the certified positive models may be distinct proofs over the two views. -/
inductive ScopeRebaseHistory :
    (n : Nat) -> (sourceContext : LambdaPFC.Ctx n) ->
    (sig : Sig) -> (targetContext : SystemFCoExt.Ctx sig) ->
    ScopeModel sourceContext targetContext ->
    ScopeModel sourceContext targetContext -> Type where
  | identity
      {n : Nat} {sourceContext : LambdaPFC.Ctx n}
      {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
      (scope : ScopeModel sourceContext targetContext) :
      ScopeRebaseHistory n sourceContext sig targetContext scope scope
  | bind
      {n : Nat} {sourceContext : LambdaPFC.Ctx n}
      {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
      {source target : ScopeModel sourceContext targetContext}
      (older : ScopeRebaseHistory n sourceContext sig targetContext source
        target)
      {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
      (sourceNewest : ProducerPlanModel sourceContext targetContext
        source.view sourceType plan)
      (targetNewest : ProducerPlanModel sourceContext targetContext
        target.view sourceType plan) :
      ScopeRebaseHistory (n + 1) (sourceContext.snoc sourceType) plan.scope
        (plan.context targetContext)
        (source.bind sourceNewest) (target.bind targetNewest)

namespace ScopeRebaseHistory

/-- Closed same-plan history forces equality of the complete scope views.
The equality deliberately says nothing about the proof fields in the two
`ScopeModel` records. -/
noncomputable def view_eq
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {source target : ScopeModel sourceContext targetContext}
    (history : ScopeRebaseHistory n sourceContext sig targetContext source
      target) : source.view = target.view :=
  match history with
  | .identity _ => rfl
  | @ScopeRebaseHistory.bind _ _ _ _ _ _ older _ plan _ _ =>
      congrArg
        (fun view => TranslationInterfaces.ScopeView.bindPlan view plan)
        (view_eq older)

noncomputable def symm
    {source target : ScopeModel sourceContext targetContext}
    (history : ScopeRebaseHistory n sourceContext sig targetContext source
      target) :
    ScopeRebaseHistory n sourceContext sig targetContext target source := by
  induction history with
  | identity => exact .identity _
  | bind older sourceNewest targetNewest ih =>
      exact .bind ih targetNewest sourceNewest

end ScopeRebaseHistory

/-- A supplied stable-field alignment together with closed construction
history for its endpoint scopes.  The alignment remains explicit because it
is the index consumed by the existing subtyping compiler core. -/
structure ScopeRebase
    {source target : ScopeModel sourceContext targetContext}
  (alignment : ScopeAlignment source.view target.view) : Type where
  history : ScopeRebaseHistory n sourceContext sig targetContext source target

namespace ScopeRebase

def identity (scope : ScopeModel sourceContext targetContext) :
    ScopeRebase (ScopeAlignment.identity scope.view) where
  history := .identity scope

/-- Extend closed provenance by opening one identical certified positive
plan on both sides. -/
noncomputable def bind
    {source target : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment source.view target.view}
    (older : ScopeRebase alignment)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (sourceNewest : ProducerPlanModel sourceContext targetContext source.view
      sourceType plan)
    (targetNewest : ProducerPlanModel sourceContext targetContext target.view
      sourceType plan) :
    ScopeRebase (source := source.bind sourceNewest)
      (target := target.bind targetNewest)
      (ScopeAlignment.bindSamePlan alignment plan) where
  history := .bind older.history sourceNewest targetNewest

/-- Binder-facing convenience constructor.  Both polarities are retained by
the caller; scope lookup uses the certified positive projection, exactly as
`ScopeModel.bindBidirectional` does. -/
noncomputable def bindBidirectional
    {source target : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment source.view target.view}
    (older : ScopeRebase alignment)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (sourceNewest : BidirectionalPlanModel sourceContext targetContext
      source.view sourceType plan)
    (targetNewest : BidirectionalPlanModel sourceContext targetContext
      target.view sourceType plan) :
    ScopeRebase
      (source := source.bindBidirectional sourceNewest)
      (target := target.bindBidirectional targetNewest)
      (ScopeAlignment.bindSamePlan alignment plan) :=
  bind older sourceNewest.producer targetNewest.producer

noncomputable def symm
    {source target : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment source.view target.view}
    (rebase : ScopeRebase alignment) : ScopeRebase alignment.symm where
  history := rebase.history.symm

theorem view_eq
    {source target : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment source.view target.view}
    (rebase : ScopeRebase alignment) : source.view = target.view :=
  rebase.history.view_eq

/-! ## Constructor-complete sealed-model transport -/

/-- Transport every positive structural model.  This single equality
transport covers all constructors, notably `bound` and `underBinding`; the
closed history is precisely what justifies that equality. -/
def producerModel
    {source target : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment source.view target.view}
    (rebase : ScopeRebase alignment)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : ProducerPlanModel sourceContext targetContext source.view
      sourceType plan) :
    ProducerPlanModel sourceContext targetContext target.view sourceType
      plan := by
  rw [← rebase.view_eq]
  exact model

/-- Transport every negative structural model at the same plan. -/
def demandModel
    {source target : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment source.view target.view}
    (rebase : ScopeRebase alignment)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : DemandPlanModel sourceContext targetContext source.view
      sourceType plan) :
    DemandPlanModel sourceContext targetContext target.view sourceType plan := by
  rw [← rebase.view_eq]
  exact model

/-- Transport a binder-facing model, preserving both polarities at its exact
plan. -/
def bidirectionalModel
    {source target : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment source.view target.view}
    (rebase : ScopeRebase alignment)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : BidirectionalPlanModel sourceContext targetContext source.view
      sourceType plan) :
    BidirectionalPlanModel sourceContext targetContext target.view sourceType
      plan := by
  rw [← rebase.view_eq]
  exact model

def selectionModel
    {source target : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment source.view target.view}
    (rebase : ScopeRebase alignment)
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {origin : SelectionOrigin sourceContext path label}
    {plan : ValuePlan sig}
    (model : SelectionPlanModel sourceContext targetContext source.view origin
      plan) :
    SelectionPlanModel sourceContext targetContext target.view origin plan := by
  rw [← rebase.view_eq]
  exact model

def intervalProducerModel
    {source target : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment source.view target.view}
    (rebase : ScopeRebase alignment)
    {lower upper : LambdaPFC.Ty n}
    {lowerPlan upperPlan : ValuePlan sig}
    (model : IntervalProducerPlanModel sourceContext targetContext source.view
      lower upper lowerPlan upperPlan) :
    IntervalProducerPlanModel sourceContext targetContext target.view lower
      upper lowerPlan upperPlan := by
  rw [← rebase.view_eq]
  exact model

def intervalDemandModel
    {source target : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment source.view target.view}
    (rebase : ScopeRebase alignment)
    {lower upper : LambdaPFC.Ty n}
    {lowerPlan upperPlan : ValuePlan sig}
    (model : IntervalDemandPlanModel sourceContext targetContext source.view
      lower upper lowerPlan upperPlan) :
    IntervalDemandPlanModel sourceContext targetContext target.view lower upper
      lowerPlan upperPlan := by
  rw [← rebase.view_eq]
  exact model

def intervalBidirectionalModel
    {source target : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment source.view target.view}
    (rebase : ScopeRebase alignment)
    {lower upper : LambdaPFC.Ty n}
    {lowerPlan upperPlan : ValuePlan sig}
    (model : IntervalBidirectionalPlanModel sourceContext targetContext
      source.view lower upper lowerPlan upperPlan) :
    IntervalBidirectionalPlanModel sourceContext targetContext target.view lower
      upper lowerPlan upperPlan := by
  rw [← rebase.view_eq]
  exact model

/-! ## Existing compiler-core witnesses -/

noncomputable def positive
    {source target : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment source.view target.view}
    (rebase : ScopeRebase alignment)
    {sourceType : LambdaPFC.Ty n}
    (endpoint : PositivePlan sourceContext targetContext source.view
      sourceType) : PositiveRebase alignment endpoint where
  target :=
    { model :=
        ⟨endpoint.plan, rebase.producerModel endpoint.modeled⟩ }
  adapter := StableIdentity.Adapter.identity targetContext endpoint.plan

noncomputable def negative
    {source target : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment source.view target.view}
    (rebase : ScopeRebase alignment)
    {sourceType : LambdaPFC.Ty n}
    (endpoint : NegativePlan sourceContext targetContext target.view
      sourceType) : NegativeRebase alignment endpoint where
  source :=
    { model :=
        ⟨endpoint.plan, rebase.symm.demandModel endpoint.modeled⟩ }
  adapter := StableIdentity.Adapter.identity targetContext endpoint.plan

/-- Reflexive covariance with no caller-supplied model witness. -/
noncomputable def pushRefl
    {source target : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment source.view target.view}
    (rebase : ScopeRebase alignment)
    {sourceType : LambdaPFC.Ty n}
    (producer : ProperProducer sourceContext targetContext source sourceType) :
    ProperPushResult alignment (Tau.Sub.refl (τ := .ty sourceType)) producer :=
  SubtypingCompilerCore.pushRefl alignment producer fun ordinary =>
    rebase.positive ordinary.positivePlan

/-- Reflexive contravariance with no caller-supplied model witness. -/
noncomputable def pullRefl
    {source target : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment source.view target.view}
    (rebase : ScopeRebase alignment)
    {sourceType : LambdaPFC.Ty n}
    (demand : ProperDemand sourceContext targetContext target sourceType) :
    ProperPullResult alignment (Tau.Sub.refl (τ := .ty sourceType)) demand :=
  SubtypingCompilerCore.pullRefl alignment demand (rebase.negative _)

end ScopeRebase

end LambdaPToFCo.Full.TranslationModelRebase
