import LambdaPToFCo.Full.ConstructedScopeInstantiation

/-!
# Sealed positive pair-head provenance

A positive pair model can be hidden below `bound`, `underBinding`, and
`targetRename`.  These wrappers are intentionally not equal to a freshly
constructed pair model.  `ProducerPairHead` retains their exact construction
history, while the capability records below expose only the receiver's
current pair/first-field shape.

This leaf does not claim that a dependent member has already been
instantiated.  That requires the separate closed model-instantiation
coherence action used by `sel_r`.
-/

namespace LambdaPToFCo.Full

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

/-- Exact construction history from a direct positive pair model through the
three provenance-retaining positive wrappers. -/
inductive ProducerPairHead :
    {n : Nat} -> {sourceContext : LambdaPFC.Ctx n} ->
    {sig : Sig} -> {targetContext : SystemFCoExt.Ctx sig} ->
    {view : ScopeView n targetContext} ->
    {sourceType : LambdaPFC.Ty n} -> {plan : ValuePlan sig} ->
    (model : ProducerPlanModel sourceContext targetContext view sourceType
      plan) -> Type where
  | proper
      (first : ProducerPlanModel sourceContext targetContext view
        firstType firstPlan)
      (member : ProducerPlanModel (sourceContext.snoc firstType)
        (firstPlan.context targetContext) (ScopeView.bindPlan view firstPlan)
        memberType memberPlan) :
      ProducerPairHead
        (.properPair (label := label) first member)
  | interval
      (first : ProducerPlanModel sourceContext targetContext view
        firstType firstPlan)
      (member : IntervalProducerPlanModel (sourceContext.snoc firstType)
        (firstPlan.context targetContext) (ScopeView.bindPlan view firstPlan)
        lower upper lowerPlan upperPlan) :
      ProducerPairHead
        (.intervalPair (label := label) first member)
  | bound
      (model : ProducerPlanModel sourceContext targetContext view sourceType
        plan)
      (previous : ProducerPairHead model) :
      ProducerPairHead (.bound model)
  | underBinding
      (boundModel : ProducerPlanModel sourceContext targetContext view
        boundType boundPlan)
      (olderModel : ProducerPlanModel sourceContext targetContext view
        olderType olderPlan)
      (previous : ProducerPairHead olderModel) :
      ProducerPairHead (.underBinding boundModel olderModel)
  | targetRename
      {source target : Sig}
      {sourceTargetContext : SystemFCoExt.Ctx source}
      {targetTargetContext : SystemFCoExt.Ctx target}
      {sourceView : ScopeView n sourceTargetContext}
      {sourceType : LambdaPFC.Ty n} {sourcePlan : ValuePlan source}
      (model : ProducerPlanModel sourceContext sourceTargetContext sourceView
        sourceType sourcePlan)
      (previous : ProducerPairHead model)
      (mapping : Rename source target)
      (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
      ProducerPairHead (.targetRename model mapping typed)

/-- Current-focus decomposition of a proper-member pair.  The receiver model
is not equated with a fresh `.properPair`; only its source/plan indices are
identified and its exact wrapper history is retained. -/
structure ProperPairCapability
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : ProducerPlanModel sourceContext targetContext view sourceType
      plan) : Type where
  firstType : LambdaPFC.Ty n
  label : LambdaPFC.Name
  memberType : LambdaPFC.Ty (n + 1)
  source_eq : sourceType = .Pair firstType label (.ty memberType)
  firstPlan : ValuePlan sig
  memberPlan : ValuePlan firstPlan.scope
  plan_eq : plan = Pair.Proper.plan firstPlan memberPlan
  firstModel : ProducerPlanModel sourceContext targetContext view firstType
    firstPlan
  history : ProducerPairHead model

/-- Current-focus decomposition of an interval-member pair.  Its dependent
member remains origin-free and is recovered later from `history`. -/
structure IntervalPairCapability
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : ProducerPlanModel sourceContext targetContext view sourceType
      plan) : Type where
  firstType : LambdaPFC.Ty n
  label : LambdaPFC.Name
  lower : LambdaPFC.Ty (n + 1)
  upper : LambdaPFC.Ty (n + 1)
  source_eq : sourceType = .Pair firstType label (.intv lower upper)
  firstPlan : ValuePlan sig
  lowerPlan : ValuePlan firstPlan.scope
  upperPlan : ValuePlan firstPlan.scope
  plan_eq : plan = Pair.Interval.plan firstPlan lowerPlan.inputTy
    upperPlan.inputTy
  firstModel : ProducerPlanModel sourceContext targetContext view firstType
    firstPlan
  history : ProducerPairHead model

/-- Kind-complete current pair-head capability. -/
inductive ProducerPairProjection
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : ProducerPlanModel sourceContext targetContext view sourceType
      plan) : Type where
  | proper (capability : ProperPairCapability model) :
      ProducerPairProjection model
  | interval (capability : IntervalPairCapability model) :
      ProducerPairProjection model

noncomputable def ProperPairCapability.direct
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext}
    {firstType : LambdaPFC.Ty n} {label : LambdaPFC.Name}
    {memberType : LambdaPFC.Ty (n + 1)}
    {firstPlan : ValuePlan sig} {memberPlan : ValuePlan firstPlan.scope}
    (first : ProducerPlanModel sourceContext targetContext view firstType
      firstPlan)
    (member : ProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context targetContext) (ScopeView.bindPlan view firstPlan)
      memberType memberPlan) :
    ProperPairCapability
      (.properPair (label := label) first member) where
  firstType := firstType
  label := label
  memberType := memberType
  source_eq := rfl
  firstPlan := firstPlan
  memberPlan := memberPlan
  plan_eq := rfl
  firstModel := first
  history := .proper first member

noncomputable def IntervalPairCapability.direct
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext}
    {firstType : LambdaPFC.Ty n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty (n + 1)}
    {firstPlan : ValuePlan sig}
    {lowerPlan upperPlan : ValuePlan firstPlan.scope}
    (first : ProducerPlanModel sourceContext targetContext view firstType
      firstPlan)
    (member : IntervalProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context targetContext) (ScopeView.bindPlan view firstPlan)
      lower upper lowerPlan upperPlan) :
    IntervalPairCapability
      (.intervalPair (label := label) first member) where
  firstType := firstType
  label := label
  lower := lower
  upper := upper
  source_eq := rfl
  firstPlan := firstPlan
  lowerPlan := lowerPlan
  upperPlan := upperPlan
  plan_eq := rfl
  firstModel := first
  history := .interval first member

/-- Normalize the first-field shape through one unrelated source binding.
The dependent member itself is intentionally left in `history`. -/
noncomputable def ProperPairCapability.underBinding
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext}
    {boundType olderType : LambdaPFC.Ty n}
    {boundPlan olderPlan : ValuePlan sig}
    (boundModel : ProducerPlanModel sourceContext targetContext view
      boundType boundPlan)
    (olderModel : ProducerPlanModel sourceContext targetContext view
      olderType olderPlan)
    (older : ProperPairCapability olderModel) :
    ProperPairCapability (.underBinding boundModel olderModel) where
  firstType := older.firstType.weaken
  label := older.label
  memberType := older.memberType.rename FinFun.weaken.ext
  source_eq := by
    calc
      olderType.weaken =
          (LambdaPFC.Ty.Pair older.firstType older.label
            (.ty older.memberType)).weaken :=
        congrArg LambdaPFC.Ty.weaken older.source_eq
      _ = LambdaPFC.Ty.Pair older.firstType.weaken older.label
          (.ty (older.memberType.rename FinFun.weaken.ext)) := rfl
  firstPlan := older.firstPlan.rename boundPlan.telescope.weaken
  memberPlan := Pair.Proper.renameMember older.firstPlan older.memberPlan
    boundPlan.telescope.weaken
  plan_eq := by
    calc
      olderPlan.rename boundPlan.telescope.weaken =
          (Pair.Proper.plan older.firstPlan older.memberPlan).rename
            boundPlan.telescope.weaken :=
        congrArg (fun plan => plan.rename boundPlan.telescope.weaken)
          older.plan_eq
      _ = Pair.Proper.plan
          (older.firstPlan.rename boundPlan.telescope.weaken)
          (Pair.Proper.renameMember older.firstPlan older.memberPlan
            boundPlan.telescope.weaken) :=
        Pair.Proper.plan_rename older.firstPlan older.memberPlan
          boundPlan.telescope.weaken
  firstModel := .underBinding boundModel older.firstModel
  history := .underBinding boundModel olderModel older.history

/-- Normalize the first-field shape of the newly bound pair itself. -/
noncomputable def ProperPairCapability.bound
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : ProducerPlanModel sourceContext targetContext view sourceType
      plan)
    (older : ProperPairCapability model) :
    ProperPairCapability (.bound model) where
  firstType := older.firstType.weaken
  label := older.label
  memberType := older.memberType.rename FinFun.weaken.ext
  source_eq := by
    calc
      sourceType.weaken =
          (LambdaPFC.Ty.Pair older.firstType older.label
            (.ty older.memberType)).weaken :=
        congrArg LambdaPFC.Ty.weaken older.source_eq
      _ = LambdaPFC.Ty.Pair older.firstType.weaken older.label
          (.ty (older.memberType.rename FinFun.weaken.ext)) := rfl
  firstPlan := older.firstPlan.rename plan.telescope.weaken
  memberPlan := Pair.Proper.renameMember older.firstPlan older.memberPlan
    plan.telescope.weaken
  plan_eq := by
    calc
      plan.rename plan.telescope.weaken =
          (Pair.Proper.plan older.firstPlan older.memberPlan).rename
            plan.telescope.weaken :=
        congrArg (fun current => current.rename plan.telescope.weaken)
          older.plan_eq
      _ = Pair.Proper.plan
          (older.firstPlan.rename plan.telescope.weaken)
          (Pair.Proper.renameMember older.firstPlan older.memberPlan
            plan.telescope.weaken) :=
        Pair.Proper.plan_rename older.firstPlan older.memberPlan
          plan.telescope.weaken
  firstModel := .underBinding model older.firstModel
  history := .bound model older.history

end LambdaPToFCo.Full
