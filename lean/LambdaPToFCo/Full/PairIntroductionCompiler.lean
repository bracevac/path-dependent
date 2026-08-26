import LambdaPToFCo.Full.WfPlan
import LambdaPToFCo.Full.ContextWellFormed
import LambdaPToFCo.Full.InterfaceArgumentCancellation

/-!
# Direct full pair introductions

The two source pair values contain only source variables (for a value member)
or one source variable and a well-formed type (for a type member).  Their
target packages are therefore reconstructed from the certified interfaces in
`ScopeModel`; callers cannot install packages or representation adapters.

For value members, the older member interface is renamed below the exact
first-component telescope and then reopened by that telescope's complete
argument spine.  Interface-argument cancellation transports the original
member arguments to the dependent plan expected by `Pair.Proper`.

For type members, `WfPlan` compiles the weakened witness in the exact
singleton-bound scope.  Its opened package type is used as the hidden witness
representation, and the lower/upper package coercions are the canonical
selection wrapper and unwrapper around reflexivity.
-/

namespace LambdaPToFCo.Full.PairIntroductionCompiler

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

/-! ## Direct value-member pairs -/

/-- The exact singleton producer for one certified source variable. -/
noncomputable def variableSingleton
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) (index : Fin n) :
    OrdinaryProducer sourceContext targetContext scope
      (.Single (.var index)) :=
  (scope.variablePath index).singletonProducer

private noncomputable def variableArguments
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) (index : Fin n) :
    Telescope.Args targetContext
      (variableSingleton scope index).plan.telescope := by
  exact (scope.view index).arguments

private noncomputable def dependentMemberArguments
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (first member : Fin n) :
    Telescope.Args targetContext
      (((variableSingleton scope member).plan.rename
          (variableSingleton scope first).plan.telescope.weaken).telescope.subst
        (variableArguments scope first).substitution) := by
  have canceled :
      (((variableSingleton scope member).plan.rename
          (variableSingleton scope first).plan.telescope.weaken).telescope.subst
        (variableArguments scope first).substitution) =
      (variableSingleton scope member).plan.telescope := by
    rw [ValuePlan.telescope_subst]
    exact congrArg ValuePlan.telescope
      (ValuePlan.rename_subst_cancel
        (variableSingleton scope member).plan
        (variableSingleton scope first).plan.telescope.weaken
        (variableArguments scope first).substitution
        (TargetArguments.weaken_comp_substitution
          (variableArguments scope first)))
  exact canceled.symm ▸ variableArguments scope member

/-- Compile the direct value-member pair introduction entirely from the two
certified source-variable interfaces already present in `scope`. -/
noncomputable def valuePair
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (first member : Fin n) (label : LambdaPFC.Name) :
    OrdinaryProducer sourceContext targetContext scope
      (.Pair (.Single (Path.var first)) label
        (.ty (.Single ((Path.var member).weaken)))) where
  origin := .value
    (Tm.Ty.pair (Γ := sourceContext) (y := first) (a := label) (z := member))
    .pair
  model :=
    ⟨Pair.Proper.plan (variableSingleton scope first).plan
        ((variableSingleton scope member).plan.rename
          (variableSingleton scope first).plan.telescope.weaken),
      .properPair (variableSingleton scope first).modeled
        (.underBinding (variableSingleton scope first).modeled
          (variableSingleton scope member).modeled)⟩
  package :=
    { expression := Pair.Proper.exactValuePair
        (variableSingleton scope first).plan
        ((variableSingleton scope member).plan.rename
          (variableSingleton scope first).plan.telescope.weaken)
        (variableArguments scope first)
        (dependentMemberArguments scope first member)
      typing := Pair.Proper.exactValuePair_hasType
        (variableSingleton scope first).plan
        ((variableSingleton scope member).plan.rename
          (variableSingleton scope first).plan.telescope.weaken)
        (variableArguments scope first)
        (dependentMemberArguments scope first member) }

/-! ## Direct type-member pairs -/

/-- Both polarities of the exact singleton plan used as a type-pair first
component. -/
private noncomputable def variableSingletonBidirectional
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) (index : Fin n) :
    BidirectionalPlanModel sourceContext targetContext scope.view
      (.Single (.var index)) (variableSingleton scope index).plan :=
  .both
    (.singleton (.var (x := index)) (scope.slot index))
    (.singleton (.var (x := index)) (scope.slot index))

/-- The exact source/target scope opened below a type-pair's singleton first
component. -/
noncomputable def bindVariableSingleton
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) (index : Fin n) :
    ScopeModel (sourceContext.snoc (.Single (.var index)))
      ((variableSingleton scope index).plan.context targetContext) :=
  scope.bindBidirectional (variableSingletonBidirectional scope index)

/-- Demand-local witness compilation required by a direct type-member pair.
Unlike `WfPlan.Resolver`, this fixes one weakened witness in the exact scope
opened by the pair's singleton first component. -/
abbrev WitnessPlan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) (first : Fin n)
    (witness : LambdaPFC.Ty n) :=
  WfPlan.Proper
    (sourceContext.snoc (.Single (.var first)))
    ((variableSingleton scope first).plan.context targetContext)
    (bindVariableSingleton scope first) witness.weaken

private noncomputable def weakenedWitnessResult
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (resolver : WfPlan.Resolver)
    (scope : ScopeModel sourceContext targetContext) (first : Fin n)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)) :
    WitnessPlan scope first witness :=
  WfPlan.properWithResolver resolver (bindVariableSingleton scope first)
    (TypeWellFormed.weaken witnessWf (.Single (.var first)))

private noncomputable def openedWitnessRepresentation
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) (first : Fin n)
    {witness : LambdaPFC.Ty n}
    (witnessPlan : WitnessPlan scope first witness) :
    SystemFCoExt.Ty sig :=
  witnessPlan.plan.inputTy.subst
    (variableArguments scope first).substitution

private noncomputable def lowerPackageEvidence
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) (first : Fin n)
    {witness : LambdaPFC.Ty n}
    (witnessPlan : WitnessPlan scope first witness) : Co sig :=
  let representation := openedWitnessRepresentation scope first witnessPlan
  Selection.lowerToPackage targetContext representation
    (.refl representation)

private noncomputable def lowerPackageEvidence_hasType
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) (first : Fin n)
    {witness : LambdaPFC.Ty n}
    (witnessPlan : WitnessPlan scope first witness) :
    Co.HasType targetContext
      (lowerPackageEvidence scope first witnessPlan)
      (witnessPlan.plan.inputTy.subst
        (variableArguments scope first).substitution)
      (Selection.plan (openedWitnessRepresentation scope first
        witnessPlan)).inputTy :=
  Selection.lowerToPackage_hasType targetContext
    (openedWitnessRepresentation scope first witnessPlan)
    (openedWitnessRepresentation scope first witnessPlan)
    (.refl (openedWitnessRepresentation scope first witnessPlan))
    Co.HasType.refl

private noncomputable def upperPackageEvidence
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) (first : Fin n)
    {witness : LambdaPFC.Ty n}
    (witnessPlan : WitnessPlan scope first witness) : Co sig :=
  let representation := openedWitnessRepresentation scope first witnessPlan
  Selection.packageToUpper representation (.refl representation)

private noncomputable def upperPackageEvidence_hasType
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) (first : Fin n)
    {witness : LambdaPFC.Ty n}
    (witnessPlan : WitnessPlan scope first witness) :
    Co.HasType targetContext
      (upperPackageEvidence scope first witnessPlan)
      (Selection.plan (openedWitnessRepresentation scope first
        witnessPlan)).inputTy
      (witnessPlan.plan.inputTy.subst
        (variableArguments scope first).substitution) :=
  Selection.packageToUpper_hasType targetContext
    (openedWitnessRepresentation scope first witnessPlan)
    (openedWitnessRepresentation scope first witnessPlan)
    (.refl (openedWitnessRepresentation scope first witnessPlan))
    Co.HasType.refl

/-- Compile a direct type-member pair from the exact already-compiled witness
plan in the singleton-bound scope. Both interval package adapters are computed
as the canonical selection wrapper/unwrapper around reflexivity at its opened
input type; callers supply no representation or coercion. -/
noncomputable def typePairFromWitnessPlan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness))
    (witnessPlan : WitnessPlan scope first witness) :
    OrdinaryProducer sourceContext targetContext scope
      (.Pair (.Single (.var first)) label
        ((Tau.intv witness witness).weaken)) where
  origin := .value (Tm.Ty.tpair (y := first) (A := label) witnessWf) .pair
  model :=
    ⟨Pair.Interval.plan (variableSingleton scope first).plan
        witnessPlan.plan.inputTy witnessPlan.plan.inputTy,
      .intervalPair (variableSingleton scope first).modeled
        (.bounds
          witnessPlan.model.demand witnessPlan.model.producer)⟩
  package :=
    { expression := Pair.Interval.exactTypePair
        (variableSingleton scope first).plan
        witnessPlan.plan.inputTy witnessPlan.plan.inputTy
        (variableArguments scope first)
        (openedWitnessRepresentation scope first witnessPlan)
        (lowerPackageEvidence scope first witnessPlan)
        (lowerPackageEvidence_hasType scope first witnessPlan)
        (upperPackageEvidence scope first witnessPlan)
        (upperPackageEvidence_hasType scope first witnessPlan)
      typing := Pair.Interval.exactTypePair_hasType
        (variableSingleton scope first).plan
        witnessPlan.plan.inputTy witnessPlan.plan.inputTy
        (variableArguments scope first)
        (openedWitnessRepresentation scope first witnessPlan)
        (lowerPackageEvidence scope first witnessPlan)
        (lowerPackageEvidence_hasType scope first witnessPlan)
        (upperPackageEvidence scope first witnessPlan)
        (upperPackageEvidence_hasType scope first witnessPlan) }

/-- Convenience wrapper that obtains the exact demand-local witness plan from
the existing total `WfPlan.Resolver`. -/
noncomputable def typePair
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (resolver : WfPlan.Resolver)
    (scope : ScopeModel sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)) :
    OrdinaryProducer sourceContext targetContext scope
      (.Pair (.Single (.var first)) label
        ((Tau.intv witness witness).weaken)) :=
  typePairFromWitnessPlan scope first label witnessWf
    (weakenedWitnessResult resolver scope first witnessWf)

end LambdaPToFCo.Full.PairIntroductionCompiler
