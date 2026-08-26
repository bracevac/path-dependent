import LambdaPToFCo.Full.IntervalSubtypingCompilerCore
import LambdaPToFCo.Full.WfPlan

namespace LambdaPToFCo.Full.AtomicSubtypingCompiler

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open SubtypingCompilerCore
open IntervalSubtypingCompilerCore

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

/-! ## Exact proper-path rules -/

inductive WidenEvidence
    (scope : ScopeModel sourceContext targetContext)
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    (precise : Path.Ty sourceContext path (.ty referent)) :
    ProperProducer sourceContext targetContext scope (.Single path) -> Type where
  | ordinary
      (source : OrdinaryProducer sourceContext targetContext scope
        (.Single path))
      (resolved : ProperPathPackage sourceContext targetContext scope precise)
      (adapter : StableIdentity.Adapter targetContext source.plan
        resolved.plan) :
      WidenEvidence scope precise (.ordinary source)
  | absurd
      (bottom : BottomProducer sourceContext targetContext) :
      WidenEvidence scope precise (.absurd bottom (.Single path))

noncomputable def pushWiden
    (scope : ScopeModel sourceContext targetContext)
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    (precise : Path.Ty sourceContext path (.ty referent))
    (source : ProperProducer sourceContext targetContext scope (.Single path))
    (evidence : WidenEvidence scope precise source) :
    ProperPushResult (ScopeAlignment.identity scope.view) (.widen precise)
      source := by
  cases evidence with
  | ordinary ordinary resolved adapter =>
      exact ProperPushResult.ordinary (ScopeAlignment.identity scope.view)
        (.widen precise) ordinary resolved.model adapter
  | absurd bottom =>
      exact ProperPushResult.fromAbsurd (ScopeAlignment.identity scope.view)
        (.widen precise) bottom

inductive SymmetryEvidence
    (scope : ScopeModel sourceContext targetContext)
    {path referent : LambdaPFC.Path n}
    (precise : Path.Ty sourceContext path (.ty (.Single referent))) :
    ProperProducer sourceContext targetContext scope (.Single referent) ->
    Type where
  | ordinary
      (source : OrdinaryProducer sourceContext targetContext scope
        (.Single referent))
      (resolved : ProperPathPackage sourceContext targetContext scope precise)
      (adapter : StableIdentity.Adapter targetContext source.plan
        resolved.plan) :
      SymmetryEvidence scope precise (.ordinary source)
  | absurd
      (bottom : BottomProducer sourceContext targetContext) :
      SymmetryEvidence scope precise (.absurd bottom (.Single referent))

noncomputable def pushSymmetry
    (scope : ScopeModel sourceContext targetContext)
    {path referent : LambdaPFC.Path n}
    (precise : Path.Ty sourceContext path (.ty (.Single referent)))
    (source : ProperProducer sourceContext targetContext scope
      (.Single referent))
    (evidence : SymmetryEvidence scope precise source) :
    ProperPushResult (ScopeAlignment.identity scope.view) (.symm precise)
      source := by
  cases evidence with
  | ordinary ordinary resolved adapter =>
      exact ProperPushResult.ordinary (ScopeAlignment.identity scope.view)
        (.symm precise) ordinary
        ⟨resolved.plan, .singleton precise resolved.modeled⟩ adapter
  | absurd bottom =>
      exact ProperPushResult.fromAbsurd (ScopeAlignment.identity scope.view)
        (.symm precise) bottom

/-! ## Exact selection rules -/

def selectionOrigin
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty n}
    (precise : Path.Ty sourceContext (.sel path label) (.intv lower upper))
    (nonempty : Tau.Sub sourceContext (.ty lower) (.ty upper)) :
    SelectionOrigin sourceContext path label where
  lower := lower
  upper := upper
  precise := precise
  nonempty := nonempty

inductive SelectLowerEvidence
    (scope : ScopeModel sourceContext targetContext)
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty n}
    (precise : Path.Ty sourceContext (.sel path label) (.intv lower upper))
    (nonempty : Tau.Sub sourceContext (.ty lower) (.ty upper)) :
    (source : ProperProducer sourceContext targetContext scope lower) ->
    WfPlan.IntervalPathTranslation sourceContext targetContext scope precise ->
    Type where
  | ordinary
      (source : OrdinaryProducer sourceContext targetContext scope lower)
      (lowerPlan upperPlan : ValuePlan sig)
      (lowerModel : BidirectionalPlanModel sourceContext targetContext
        scope.view lower lowerPlan)
      (upperModel : BidirectionalPlanModel sourceContext targetContext
        scope.view upper upperPlan)
      (representation : SystemFCoExt.Ty sig)
      (lowerToSelected : StableIdentity.Adapter targetContext lowerPlan
        (Selection.plan representation))
      (selectedToUpper : StableIdentity.Adapter targetContext
        (Selection.plan representation) upperPlan)
      (sourceToLower : StableIdentity.Adapter targetContext source.plan
        lowerPlan) :
      SelectLowerEvidence scope precise nonempty (.ordinary source)
        (.resolved lowerPlan upperPlan lowerModel upperModel
          (.selected representation lowerToSelected selectedToUpper))
  | absurd
      (bottom : BottomProducer sourceContext targetContext)
      (translation : WfPlan.IntervalPathTranslation sourceContext
        targetContext scope precise) :
      SelectLowerEvidence scope precise nonempty (.absurd bottom lower)
        translation

noncomputable def pushSelectLower
    (scope : ScopeModel sourceContext targetContext)
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty n}
    (precise : Path.Ty sourceContext (.sel path label) (.intv lower upper))
    (nonempty : Tau.Sub sourceContext (.ty lower) (.ty upper))
    (source : ProperProducer sourceContext targetContext scope lower)
    (translation : WfPlan.IntervalPathTranslation sourceContext targetContext
      scope precise)
    (evidence : SelectLowerEvidence scope precise nonempty source translation) :
    ProperPushResult (ScopeAlignment.identity scope.view)
      (.sel_lo precise nonempty) source := by
  cases evidence with
  | ordinary ordinary lowerPlan upperPlan lowerModel upperModel representation
      lowerToSelected selectedToUpper sourceToLower =>
      let origin := selectionOrigin precise nonempty
      let bounds : IntervalDemandPlanModel sourceContext targetContext
          scope.view lower upper lowerPlan upperPlan :=
        .bounds lowerModel.producer upperModel.demand
      let selected : SelectionPlanModel sourceContext targetContext scope.view
          origin (Selection.plan representation) :=
        .between bounds lowerToSelected selectedToUpper
      exact ProperPushResult.ordinary (ScopeAlignment.identity scope.view)
        (.sel_lo precise nonempty) ordinary
        ⟨Selection.plan representation, .selection selected⟩
        (sourceToLower.compose lowerToSelected)
  | absurd bottom translation =>
      exact ProperPushResult.fromAbsurd (ScopeAlignment.identity scope.view)
        (.sel_lo precise nonempty) bottom

inductive SelectUpperEvidence
    (scope : ScopeModel sourceContext targetContext)
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty n}
    (precise : Path.Ty sourceContext (.sel path label) (.intv lower upper))
    (nonempty : Tau.Sub sourceContext (.ty lower) (.ty upper)) :
    (source : ProperProducer sourceContext targetContext scope
      (.TSel path label)) ->
    WfPlan.IntervalPathTranslation sourceContext targetContext scope precise ->
    Type where
  | ordinary
      (source : OrdinaryProducer sourceContext targetContext scope
        (.TSel path label))
      (lowerPlan upperPlan : ValuePlan sig)
      (lowerModel : BidirectionalPlanModel sourceContext targetContext
        scope.view lower lowerPlan)
      (upperModel : BidirectionalPlanModel sourceContext targetContext
        scope.view upper upperPlan)
      (representation : SystemFCoExt.Ty sig)
      (lowerToSelected : StableIdentity.Adapter targetContext lowerPlan
        (Selection.plan representation))
      (selectedToUpper : StableIdentity.Adapter targetContext
        (Selection.plan representation) upperPlan)
      (sourceToSelected : StableIdentity.Adapter targetContext source.plan
        (Selection.plan representation)) :
      SelectUpperEvidence scope precise nonempty (.ordinary source)
        (.resolved lowerPlan upperPlan lowerModel upperModel
          (.selected representation lowerToSelected selectedToUpper))
  | absurd
      (bottom : BottomProducer sourceContext targetContext)
      (translation : WfPlan.IntervalPathTranslation sourceContext
        targetContext scope precise) :
      SelectUpperEvidence scope precise nonempty
        (.absurd bottom (.TSel path label)) translation

noncomputable def pushSelectUpper
    (scope : ScopeModel sourceContext targetContext)
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty n}
    (precise : Path.Ty sourceContext (.sel path label) (.intv lower upper))
    (nonempty : Tau.Sub sourceContext (.ty lower) (.ty upper))
    (source : ProperProducer sourceContext targetContext scope
      (.TSel path label))
    (translation : WfPlan.IntervalPathTranslation sourceContext targetContext
      scope precise)
    (evidence : SelectUpperEvidence scope precise nonempty source translation) :
    ProperPushResult (ScopeAlignment.identity scope.view)
      (.sel_hi precise nonempty) source := by
  cases evidence with
  | ordinary ordinary lowerPlan upperPlan lowerModel upperModel representation
      lowerToSelected selectedToUpper sourceToSelected =>
      exact ProperPushResult.ordinary (ScopeAlignment.identity scope.view)
        (.sel_hi precise nonempty) ordinary
        ⟨upperPlan, upperModel.producer⟩
        (sourceToSelected.compose selectedToUpper)
  | absurd bottom translation =>
      exact ProperPushResult.fromAbsurd (ScopeAlignment.identity scope.view)
        (.sel_hi precise nonempty) bottom

/-! ## Interval bounds -/

noncomputable def pushBounds
    (scope : ScopeModel sourceContext targetContext)
    {sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n}
    (lowerSubtyping : Tau.Sub sourceContext (.ty targetLower) (.ty sourceLower))
    (upperSubtyping : Tau.Sub sourceContext (.ty sourceUpper) (.ty targetUpper))
    (nonempty : Tau.Sub sourceContext (.ty sourceLower) (.ty sourceUpper))
    (source : IntervalProducer sourceContext targetContext scope sourceLower
      sourceUpper)
    (lowerResult : NegativePullResult
      (ScopeAlignment.identity scope.view) lowerSubtyping source.lower)
    (upperResult : PositivePushResult
      (ScopeAlignment.identity scope.view) upperSubtyping source.upper) :
    IntervalPushResult (ScopeAlignment.identity scope.view)
      (.bounds lowerSubtyping upperSubtyping nonempty) source where
  lower := lowerResult.source
  upper := upperResult.target
  lowerAdapter := lowerResult.adapter
  upperAdapter := upperResult.adapter

noncomputable def pullBounds
    (scope : ScopeModel sourceContext targetContext)
    {sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n}
    (lowerSubtyping : Tau.Sub sourceContext (.ty targetLower) (.ty sourceLower))
    (upperSubtyping : Tau.Sub sourceContext (.ty sourceUpper) (.ty targetUpper))
    (nonempty : Tau.Sub sourceContext (.ty sourceLower) (.ty sourceUpper))
    (target : IntervalDemand sourceContext targetContext scope targetLower
      targetUpper)
    (lowerResult : PositivePushResult
      (ScopeAlignment.identity scope.view) lowerSubtyping target.lower)
    (upperResult : NegativePullResult
      (ScopeAlignment.identity scope.view) upperSubtyping target.upper) :
    IntervalPullResult (ScopeAlignment.identity scope.view)
      (.bounds lowerSubtyping upperSubtyping nonempty) target where
  lower := lowerResult.target
  upper := upperResult.source
  lowerAdapter := lowerResult.adapter
  upperAdapter := upperResult.adapter

end LambdaPToFCo.Full.AtomicSubtypingCompiler
