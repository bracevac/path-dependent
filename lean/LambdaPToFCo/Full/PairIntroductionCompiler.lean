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

private noncomputable def variableSingleton
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

private noncomputable def variableSingletonBidirectional
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) (index : Fin n) :
    BidirectionalPlanModel sourceContext targetContext scope.view
      (.Single (.var index)) (variableSingleton scope index).plan :=
  .both
    (.singleton (.var (x := index)) (scope.slot index))
    (.singleton (.var (x := index)) (scope.slot index))

private noncomputable def bindVariableSingleton
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) (index : Fin n) :
    ScopeModel (sourceContext.snoc (.Single (.var index)))
      ((variableSingleton scope index).plan.context targetContext) :=
  scope.bindBidirectional (variableSingletonBidirectional scope index)

private noncomputable def weakenedWitnessResult
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (resolver : WfPlan.Resolver)
    (scope : ScopeModel sourceContext targetContext) (first : Fin n)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)) :
    WfPlan.Proper
      (sourceContext.snoc (.Single (.var first)))
      ((variableSingleton scope first).plan.context targetContext)
      (bindVariableSingleton scope first) witness.weaken :=
  WfPlan.properWithResolver resolver (bindVariableSingleton scope first)
    (TypeWellFormed.weaken witnessWf (.Single (.var first)))

private noncomputable def openedWitnessRepresentation
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (resolver : WfPlan.Resolver)
    (scope : ScopeModel sourceContext targetContext) (first : Fin n)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)) :
    SystemFCoExt.Ty sig :=
  (weakenedWitnessResult resolver scope first witnessWf).plan.inputTy.subst
    (variableArguments scope first).substitution

private noncomputable def lowerPackageEvidence
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (resolver : WfPlan.Resolver)
    (scope : ScopeModel sourceContext targetContext) (first : Fin n)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)) : Co sig :=
  let representation := openedWitnessRepresentation resolver scope first
    witnessWf
  Selection.lowerToPackage targetContext representation
    (.refl representation)

private noncomputable def lowerPackageEvidence_hasType
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (resolver : WfPlan.Resolver)
    (scope : ScopeModel sourceContext targetContext) (first : Fin n)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)) :
    Co.HasType targetContext
      (lowerPackageEvidence resolver scope first witnessWf)
      ((weakenedWitnessResult resolver scope first witnessWf).plan.inputTy.subst
        (variableArguments scope first).substitution)
      (Selection.plan (openedWitnessRepresentation resolver scope first
        witnessWf)).inputTy :=
  Selection.lowerToPackage_hasType targetContext
    (openedWitnessRepresentation resolver scope first witnessWf)
    (openedWitnessRepresentation resolver scope first witnessWf)
    (.refl (openedWitnessRepresentation resolver scope first witnessWf))
    Co.HasType.refl

private noncomputable def upperPackageEvidence
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (resolver : WfPlan.Resolver)
    (scope : ScopeModel sourceContext targetContext) (first : Fin n)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)) : Co sig :=
  let representation := openedWitnessRepresentation resolver scope first
    witnessWf
  Selection.packageToUpper representation (.refl representation)

private noncomputable def upperPackageEvidence_hasType
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (resolver : WfPlan.Resolver)
    (scope : ScopeModel sourceContext targetContext) (first : Fin n)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)) :
    Co.HasType targetContext
      (upperPackageEvidence resolver scope first witnessWf)
      (Selection.plan (openedWitnessRepresentation resolver scope first
        witnessWf)).inputTy
      ((weakenedWitnessResult resolver scope first witnessWf).plan.inputTy.subst
        (variableArguments scope first).substitution) :=
  Selection.packageToUpper_hasType targetContext
    (openedWitnessRepresentation resolver scope first witnessWf)
    (openedWitnessRepresentation resolver scope first witnessWf)
    (.refl (openedWitnessRepresentation resolver scope first witnessWf))
    Co.HasType.refl

/-- Compile the direct type-member pair.  The resolver is used only through
`WfPlan` after opening the exact singleton first component.  Both interval
package adapters are the canonical selection wrapper/unwrapper around
reflexivity at the resulting opened witness-package type. -/
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
        ((Tau.intv witness witness).weaken)) where
  origin := .value (Tm.Ty.tpair (y := first) (A := label) witnessWf) .pair
  model :=
    ⟨Pair.Interval.plan (variableSingleton scope first).plan
        (weakenedWitnessResult resolver scope first witnessWf).plan.inputTy
        (weakenedWitnessResult resolver scope first witnessWf).plan.inputTy,
      .intervalPair (variableSingleton scope first).modeled
        (.bounds
          (weakenedWitnessResult resolver scope first witnessWf).model.demand
          (weakenedWitnessResult resolver scope first
            witnessWf).model.producer)⟩
  package :=
    { expression := Pair.Interval.exactTypePair
        (variableSingleton scope first).plan
        (weakenedWitnessResult resolver scope first witnessWf).plan.inputTy
        (weakenedWitnessResult resolver scope first witnessWf).plan.inputTy
        (variableArguments scope first)
        (openedWitnessRepresentation resolver scope first witnessWf)
        (lowerPackageEvidence resolver scope first witnessWf)
        (lowerPackageEvidence_hasType resolver scope first witnessWf)
        (upperPackageEvidence resolver scope first witnessWf)
        (upperPackageEvidence_hasType resolver scope first witnessWf)
      typing := Pair.Interval.exactTypePair_hasType
        (variableSingleton scope first).plan
        (weakenedWitnessResult resolver scope first witnessWf).plan.inputTy
        (weakenedWitnessResult resolver scope first witnessWf).plan.inputTy
        (variableArguments scope first)
        (openedWitnessRepresentation resolver scope first witnessWf)
        (lowerPackageEvidence resolver scope first witnessWf)
        (lowerPackageEvidence_hasType resolver scope first witnessWf)
        (upperPackageEvidence resolver scope first witnessWf)
        (upperPackageEvidence_hasType resolver scope first witnessWf) }

end LambdaPToFCo.Full.PairIntroductionCompiler
