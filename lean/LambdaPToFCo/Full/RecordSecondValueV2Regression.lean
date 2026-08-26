import LambdaPToFCo.Full.RecordFirstValueV2WidenRegression

/-!
# Record second-value V2 checkpoint

This regression compiles the existing `RecordRegression.secondValue` after
binding the genuinely widened V2 `firstValue` result at `firstRecord`.

The direct proper-pair package is built only from the bound scope's newest
and older interfaces.  The literal first subtyping leg is sealed to the old
record descriptor's lower adapter; the literal second leg is sealed to its
upper adapter followed by the new record descriptor's lower adapter.  V2
exact intervals select the complete implementation plan, so these adapters
and all three enclosing proper-pair plans are definitionally identical.

The rule-specific carrier and adaptation evidence are private to this
regression.  This module does not claim a V2 `ScopeModel`, a generic V2
subtyping compiler, or any V1 `ProducerPlanModel` evidence.
-/

namespace LambdaPToFCo.Full.RecordSecondValueV2Regression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

noncomputable section

abbrev FirstSourceContext := RecordFirstValueStaticRegression.SourceContext
abbrev FirstTargetContext := RecordFirstValueStaticRegression.TargetContext

abbrev SourceContext :=
  FirstSourceContext.snoc LambdaPFC.RecordRegression.firstRecord

noncomputable def firstValue :=
  RecordFirstValueV2WidenRegression.widened

noncomputable def exactFirstValue := firstValue.exactSource

noncomputable def bound := firstValue.bind

noncomputable abbrev FirstRecordPlan := firstValue.plan

abbrev TargetContext := FirstRecordPlan.context FirstTargetContext

noncomputable abbrev ImplementationPlan :=
  RecordFirstValueStaticRegression.firstPath.plan

/-! ## Retained V2 descriptor through the actual first-value binding -/

/-- Open the exact descriptor with the exact arguments retained across the
first-component widening. -/
noncomputable def openedDescriptor :=
  firstValue.capability.descriptor.subst
    exactFirstValue.firstArguments.substitution
    exactFirstValue.firstArguments.substitution_typed

theorem opened_selected_eq : openedDescriptor.selected =
    ImplementationPlan := by
  rfl

theorem opened_lower_eq : openedDescriptor.lowerAdapter =
    StableIdentity.Adapter.identity FirstTargetContext
      ImplementationPlan := by
  rfl

theorem opened_upper_eq : openedDescriptor.upperAdapter =
    StableIdentity.Adapter.identity FirstTargetContext
      ImplementationPlan := by
  rfl

noncomputable abbrev BoundImplementationPlan :=
  ImplementationPlan.rename FirstRecordPlan.telescope.weaken

noncomputable abbrev BoundFirstRecordPlan :=
  FirstRecordPlan.rename FirstRecordPlan.telescope.weaken

theorem bound_newest_plan_eq : bound.newestInterface.plan =
    BoundFirstRecordPlan := by
  rfl

theorem bound_older_plan_eq :
    (bound.olderSlot (0 : Fin 1)).interface.plan =
      BoundImplementationPlan := by
  rfl

/-- Transport the retained descriptor through the actual first-record
package binding. -/
noncomputable def boundDescriptor :=
  openedDescriptor.subst FirstRecordPlan.telescope.weaken.asSubst
    (TargetModelRenaming.substTyped
      (FirstRecordPlan.telescope.weaken_typed FirstTargetContext))

theorem bound_selected_eq : boundDescriptor.selected =
    BoundImplementationPlan := by
  rfl

theorem bound_lower_eq : boundDescriptor.lowerAdapter =
    StableIdentity.Adapter.identity TargetContext
      BoundImplementationPlan := by
  rfl

theorem bound_upper_eq : boundDescriptor.upperAdapter =
    StableIdentity.Adapter.identity TargetContext
      BoundImplementationPlan := by
  rfl

/-! ## Direct second-value proper package -/

noncomputable abbrev FirstPlan := BoundFirstRecordPlan

noncomputable abbrev MemberPlan :=
  BoundImplementationPlan.rename FirstPlan.telescope.weaken

noncomputable def firstArguments :
    Telescope.Args TargetContext FirstPlan.telescope :=
  bound.newestInterface.arguments

noncomputable def olderArguments :
    Telescope.Args TargetContext BoundImplementationPlan.telescope :=
  (bound.olderSlot (0 : Fin 1)).interface.arguments

/-- Reopen the older implementation package under the exact first-value
interface.  The cancellation proof is the direct value-pair construction,
without pretending the V2 overlay is a V1 `ScopeModel`. -/
noncomputable def memberArguments : Telescope.Args TargetContext
    ((BoundImplementationPlan.rename FirstPlan.telescope.weaken).telescope.subst
      firstArguments.substitution) := by
  have canceled :
      ((BoundImplementationPlan.rename
        FirstPlan.telescope.weaken).telescope.subst
          firstArguments.substitution) =
        BoundImplementationPlan.telescope := by
    rw [ValuePlan.telescope_subst]
    exact congrArg ValuePlan.telescope
      (ValuePlan.rename_subst_cancel BoundImplementationPlan
        FirstPlan.telescope.weaken firstArguments.substitution
        (TargetArguments.weaken_comp_substitution firstArguments))
  exact canceled.symm ▸ olderArguments

noncomputable abbrev ExactPlan :=
  Pair.Proper.plan FirstPlan MemberPlan

/-- The exact target package for the existing direct source pair
`pair 0 valueLabel (val 1)`. -/
noncomputable def exactPackage :
    PathPackageZipper.CompiledPackage TargetContext ExactPlan where
  expression := Pair.Proper.exactValuePair FirstPlan MemberPlan
    firstArguments memberArguments
  typing := Pair.Proper.exactValuePair_hasType FirstPlan MemberPlan
    firstArguments memberArguments

/-! ## Old and new observed selections -/

noncomputable abbrev MemberTargetContext :=
  FirstPlan.context TargetContext

/-- The let-bound first record becomes `var 1` below the enclosing pair's
first binder. -/
noncomputable def oldSelectionDescriptor :=
  boundDescriptor.subst FirstPlan.telescope.weaken.asSubst
    (TargetModelRenaming.substTyped
      (FirstPlan.telescope.weaken_typed TargetContext))

/-- Widening the enclosing singleton first field opens the exact same bound
first-record package as `var 0`; consequently its V2 descriptor follows the
same proof-relevant substitution. -/
noncomputable def newSelectionDescriptor :=
  boundDescriptor.subst FirstPlan.telescope.weaken.asSubst
    (TargetModelRenaming.substTyped
      (FirstPlan.telescope.weaken_typed TargetContext))

theorem old_selected_eq : oldSelectionDescriptor.selected = MemberPlan := by
  rfl

theorem new_selected_eq : newSelectionDescriptor.selected = MemberPlan := by
  rfl

theorem old_lower_eq : oldSelectionDescriptor.lowerAdapter =
    StableIdentity.Adapter.identity MemberTargetContext MemberPlan := by
  rfl

theorem old_upper_eq : oldSelectionDescriptor.upperAdapter =
    StableIdentity.Adapter.identity MemberTargetContext MemberPlan := by
  rfl

theorem new_lower_eq : newSelectionDescriptor.lowerAdapter =
    StableIdentity.Adapter.identity MemberTargetContext MemberPlan := by
  rfl

theorem old_new_descriptor_eq : oldSelectionDescriptor =
    newSelectionDescriptor := by
  rfl

noncomputable abbrev IntermediatePlan :=
  Pair.Proper.plan FirstPlan oldSelectionDescriptor.selected

noncomputable abbrev TargetPlan :=
  Pair.Proper.plan FirstPlan newSelectionDescriptor.selected

theorem exact_to_intermediate_plan_eq : ExactPlan = IntermediatePlan := by
  rfl

theorem intermediate_to_target_plan_eq : IntermediatePlan = TargetPlan := by
  rfl

theorem exact_to_target_plan_eq : ExactPlan = TargetPlan := by
  rfl

/-! ## Literal source derivations -/

abbrev ExactType := RecordIntroductionStaticRegression.Source.exactSecondType

abbrev Intermediate : LambdaPFC.Ty 2 :=
  .Pair LambdaPFC.RecordRegression.firstRecord
    LambdaPFC.RecordRegression.valueLabel
    (.ty (.TSel (.var 1) LambdaPFC.RecordRegression.typeLabel))

def firstPrecise : Path.Ty SourceContext (.var 0)
    (.ty LambdaPFC.RecordRegression.firstRecord) := by
  exact .var

def memberVarPrecise : Path.Ty
    (SourceContext.snoc (.Single (.var 0))) (.var 2)
    (.ty LambdaPFC.RecordRegression.implementationType) := by
  exact .var

def oldSelectionPreciseUnderSourceFirst : Path.Ty
    (SourceContext.snoc (.Single (.var 0)))
    ((Path.var 1).sel LambdaPFC.RecordRegression.typeLabel)
    (.intv LambdaPFC.RecordRegression.implementationType
      LambdaPFC.RecordRegression.implementationType) := by
  exact LambdaPFC.RecordRegression.firstRecord_type
    (.var : Path.Ty (SourceContext.snoc (.Single (.var 0)))
      (.var 1) (.ty LambdaPFC.RecordRegression.firstRecord))

def oldSelectionPrecise : Path.Ty
    (SourceContext.snoc LambdaPFC.RecordRegression.firstRecord)
    ((Path.var 1).sel LambdaPFC.RecordRegression.typeLabel)
    (.intv LambdaPFC.RecordRegression.implementationType
      LambdaPFC.RecordRegression.implementationType) := by
  exact LambdaPFC.RecordRegression.firstRecord_type
    (.var : Path.Ty
      (SourceContext.snoc LambdaPFC.RecordRegression.firstRecord)
      (.var 1) (.ty LambdaPFC.RecordRegression.firstRecord))

def newSelectionPrecise : Path.Ty
    (SourceContext.snoc LambdaPFC.RecordRegression.firstRecord)
    ((Path.var 0).sel LambdaPFC.RecordRegression.typeLabel)
    (.intv LambdaPFC.RecordRegression.implementationType
      LambdaPFC.RecordRegression.implementationType) := by
  exact LambdaPFC.RecordRegression.firstRecord_type
    (.var : Path.Ty
      (SourceContext.snoc LambdaPFC.RecordRegression.firstRecord)
      (.var 0) (.ty LambdaPFC.RecordRegression.firstRecord))

/-- Literal `secondExactToIntermediate`, reconstructed because the source
regression keeps it private. -/
def exactToIntermediate : Tau.Sub SourceContext (.ty ExactType)
    (.ty Intermediate) := by
  apply Tau.Sub.pair
  · exact .widen firstPrecise
  · exact .trans (.widen memberVarPrecise)
      (.sel_lo oldSelectionPreciseUnderSourceFirst .refl)

/-- Literal `secondIntermediateToRecord`, including the observed old upper
and new lower selections. -/
def intermediateToRecord : Tau.Sub SourceContext (.ty Intermediate)
    (.ty LambdaPFC.RecordRegression.secondRecord) := by
  apply Tau.Sub.pair .refl
  exact .trans
    (.sel_hi oldSelectionPrecise .refl)
    (.sel_lo newSelectionPrecise .refl)

def suffix : Tau.Sub SourceContext (.ty ExactType)
    (.ty LambdaPFC.RecordRegression.secondRecord) :=
  .trans exactToIntermediate intermediateToRecord

/-- `TypingView` retains the direct pair's leading reflexivity before the
one accumulated source suffix. -/
def normalizedSuffix : Tau.Sub SourceContext (.ty ExactType)
    (.ty LambdaPFC.RecordRegression.secondRecord) :=
  .trans .refl suffix

def firstRecordWf : Tau.Wf SourceContext
    (.ty LambdaPFC.RecordRegression.firstRecord) := by
  simpa [LambdaPFC.RecordRegression.firstRecord,
    LambdaPFC.RecordRegression.implementationType, LambdaPFC.Tau.weaken,
    LambdaPFC.Ty.weaken, LambdaPFC.Tau.rename, LambdaPFC.Ty.rename] using
    (Tau.Wf.pair
      (LambdaPFC.RecordRegression.implementationTypeWf
        (Gamma := SourceContext))
      (Tau.Wf.bounds_wf
        (LambdaPFC.RecordRegression.implementationTypeWf
          (Gamma := SourceContext.snoc
            LambdaPFC.RecordRegression.implementationType))
        (LambdaPFC.RecordRegression.implementationTypeWf
          (Gamma := SourceContext.snoc
            LambdaPFC.RecordRegression.implementationType))
        Tau.Sub.refl))

def secondRecordWf : Tau.Wf SourceContext
    (.ty LambdaPFC.RecordRegression.secondRecord) := by
  apply Tau.Wf.pair firstRecordWf
  apply Tau.Wf.sel
  · exact LambdaPFC.RecordRegression.firstRecord_type
      (.var : Path.Ty
        (SourceContext.snoc LambdaPFC.RecordRegression.firstRecord)
        (.var 0) (.ty LambdaPFC.RecordRegression.firstRecord))
  · exact .refl

def sourceTyping : Tm.Ty SourceContext
    LambdaPFC.RecordRegression.secondValue
    LambdaPFC.RecordRegression.secondRecord :=
  .sub RecordIntroductionStaticRegression.Source.typing suffix secondRecordWf

def sourceOrigin : ProducerOrigin SourceContext ExactType :=
  .value RecordIntroductionStaticRegression.Source.typing .pair

/-! ## Private, rule-specific same-plan compilation -/

private structure DirectProducer (sourceType : LambdaPFC.Ty 2) : Type where
  mk ::
  origin : ProducerOrigin SourceContext sourceType
  package : PathPackageZipper.CompiledPackage TargetContext ExactPlan

private noncomputable def directSource : DirectProducer ExactType :=
  .mk sourceOrigin exactPackage

/-- The first member rule can only consume the retained old lower adapter. -/
private inductive FirstLegCertificate :
    StableIdentity.Adapter MemberTargetContext MemberPlan MemberPlan ->
    Type where
  | exact : FirstLegCertificate oldSelectionDescriptor.lowerAdapter

/-- The second member rule can only consume old upper followed by new lower. -/
private inductive SecondLegCertificate :
    StableIdentity.Adapter MemberTargetContext MemberPlan MemberPlan ->
    Type where
  | exact : SecondLegCertificate
      (oldSelectionDescriptor.upperAdapter.compose
        newSelectionDescriptor.lowerAdapter)

private inductive AdaptationEvidence :
    {sourceType targetType : LambdaPFC.Ty 2} ->
    (subtyping : Tau.Sub SourceContext (.ty sourceType) (.ty targetType)) ->
    StableIdentity.Adapter TargetContext ExactPlan ExactPlan -> Type where
  | refl (sourceType : LambdaPFC.Ty 2) :
      AdaptationEvidence (.refl (τ := .ty sourceType))
        (StableIdentity.Adapter.identity TargetContext ExactPlan)
  | first (certificate : FirstLegCertificate
      oldSelectionDescriptor.lowerAdapter) :
      AdaptationEvidence exactToIntermediate
        (StableIdentity.Adapter.identity TargetContext ExactPlan)
  | second (certificate : SecondLegCertificate
      (oldSelectionDescriptor.upperAdapter.compose
        newSelectionDescriptor.lowerAdapter)) :
      AdaptationEvidence intermediateToRecord
        (StableIdentity.Adapter.identity TargetContext ExactPlan)
  | trans
      {sourceType middleType targetType : LambdaPFC.Ty 2}
      {first : Tau.Sub SourceContext (.ty sourceType) (.ty middleType)}
      {second : Tau.Sub SourceContext (.ty middleType) (.ty targetType)}
      {firstAdapter secondAdapter : StableIdentity.Adapter TargetContext
        ExactPlan ExactPlan}
      (firstEvidence : AdaptationEvidence first firstAdapter)
      (secondEvidence : AdaptationEvidence second secondAdapter) :
      AdaptationEvidence (.trans first second)
        (firstAdapter.compose secondAdapter)

/-- This carrier has one plan index.  Its private constructor and indexed
evidence prevent a caller from supplying an equality, adapter, or package. -/
private structure StaticRelabel
    {sourceType targetType : LambdaPFC.Ty 2}
    (subtyping : Tau.Sub SourceContext (.ty sourceType) (.ty targetType))
    (source : DirectProducer sourceType) : Type where
  mk ::
  adapter : StableIdentity.Adapter TargetContext ExactPlan ExactPlan
  evidence : AdaptationEvidence subtyping adapter

private noncomputable def staticTarget
    {sourceType targetType : LambdaPFC.Ty 2}
    {subtyping : Tau.Sub SourceContext (.ty sourceType) (.ty targetType)}
    {source : DirectProducer sourceType}
    (adaptation : StaticRelabel subtyping source) :
    DirectProducer targetType :=
  .mk (.push subtyping source.origin)
    (TranslationInterfaces.CompiledPackage.adapt source.package
      adaptation.adapter)

private noncomputable def staticRefl (source : DirectProducer sourceType) :
    StaticRelabel (.refl (τ := .ty sourceType)) source :=
  .mk (StableIdentity.Adapter.identity TargetContext ExactPlan)
    (.refl sourceType)

private noncomputable def staticFirst (source : DirectProducer ExactType) :
    StaticRelabel exactToIntermediate source :=
  .mk (StableIdentity.Adapter.identity TargetContext ExactPlan)
    (.first .exact)

private noncomputable def staticSecond (source : DirectProducer Intermediate) :
    StaticRelabel intermediateToRecord source :=
  .mk (StableIdentity.Adapter.identity TargetContext ExactPlan)
    (.second .exact)

private noncomputable def staticCompose
    {sourceType middleType targetType : LambdaPFC.Ty 2}
    {firstSubtyping : Tau.Sub SourceContext
      (.ty sourceType) (.ty middleType)}
    {secondSubtyping : Tau.Sub SourceContext
      (.ty middleType) (.ty targetType)}
    {source : DirectProducer sourceType}
    (first : StaticRelabel firstSubtyping source)
    (second : StaticRelabel secondSubtyping (staticTarget first)) :
    StaticRelabel (.trans firstSubtyping secondSubtyping) source :=
  .mk (first.adapter.compose second.adapter)
    (.trans first.evidence second.evidence)

private noncomputable def leading :=
  staticRefl directSource

private noncomputable def firstLeg := staticFirst (staticTarget leading)

private noncomputable def secondLeg := staticSecond (staticTarget firstLeg)

/-- First exact composition: the two literal source suffix legs. -/
private noncomputable def suffixAdaptation :=
  staticCompose firstLeg secondLeg

/-- Second exact composition: the direct pair's leading reflexivity followed
by the already composed source suffix. -/
private noncomputable def fullAdaptation :=
  staticCompose leading suffixAdaptation

private noncomputable def compiled :
    DirectProducer LambdaPFC.RecordRegression.secondRecord :=
  staticTarget fullAdaptation

/-! ## Public checkpoint eliminators -/

noncomputable def compiledOrigin : ProducerOrigin SourceContext
    LambdaPFC.RecordRegression.secondRecord :=
  compiled.origin

theorem compiled_origin_eq : compiledOrigin =
    .push normalizedSuffix sourceOrigin := by
  rfl

theorem compiled_origin_canonical_eq : compiledOrigin =
    ProducerOrigin.ofTyping sourceTyping := by
  rfl

noncomputable def targetPackage :
    PathPackageZipper.CompiledPackage TargetContext TargetPlan :=
  compiled.package

noncomputable def targetTerm := targetPackage.expression

/-- Concrete SystemFCoExt typing for the compiled `secondRecord` package. -/
noncomputable def targetTerm_hasType : Exp.HasType TargetContext targetTerm
    TargetPlan.inputTy :=
  targetPackage.typing

end

end LambdaPToFCo.Full.RecordSecondValueV2Regression
