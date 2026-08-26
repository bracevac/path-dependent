import LambdaPToFCo.Full.RecordUseValueV2Regression

/-!
# Sealed binding overlay for the Record use abstraction

The concrete V2 `useValue` result is not a V1 `OrdinaryProducer`, because its
domain plan comes from the retained second-record descriptor rather than a V1
`ScopeModel`.  This leaf records the honest target context obtained by opening
that exact function package and transports the second-record selected alias
through the same telescope.

Construction is closed over `RecordUseValueV2Regression.compiled`.  Callers
cannot install a package, descriptor, adapter, plan equality, or predecessor
view, and no V1 source model is claimed.
-/

namespace LambdaPToFCo.Full.RecordUseValueV2Binding

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

noncomputable section

open RecordUseValueV2Regression

/-- Provenance for the exact compiled abstraction and its selected domain. -/
structure FunctionHead : Type where
  private mk ::
  sealed : Unit

noncomputable def functionHead : FunctionHead :=
  .mk ()

namespace FunctionHead

noncomputable def package (_head : FunctionHead) :
    PathPackageZipper.CompiledPackage Second.Context TargetPlan :=
  compiled.package

noncomputable def selectedAlias (_head : FunctionHead) :=
  compiled.alias

@[simp] theorem package_eq (head : FunctionHead) :
    head.package = compiled.package := by
  rfl

end FunctionHead

abbrev SourceContext :=
  RecordUseValueV2Regression.SourceContext.snoc
    RecordUseValueV2Regression.SourceType

noncomputable abbrev TargetContext :=
  RecordUseValueV2Regression.TargetPlan.context
    RecordUseValueV2Regression.Second.Context

/-- Exact target opening of the compiled use-function package. -/
structure BoundScope : Type where
  private mk ::
  head : FunctionHead

noncomputable def bind : BoundScope :=
  .mk functionHead

namespace BoundScope

noncomputable def view (_bound : BoundScope) : ScopeView 4 TargetContext :=
  ScopeView.bindPlan RecordUseValueV2Regression.Second.view TargetPlan

noncomputable def newestInterface (bound : BoundScope) :
    ValueInterface TargetContext :=
  bound.view 0

noncomputable def newestPackage (bound : BoundScope) :
    PathPackageZipper.CompiledPackage TargetContext
      (TargetPlan.rename TargetPlan.telescope.weaken) := by
  simpa only [newestInterface, view, ScopeView.bindPlan_here,
    TranslationInterfaces.ValueInterface.ofArguments_plan] using
    PathPackageZipper.CompiledPackage.ofInterface bound.newestInterface

def newestTyping (_bound : BoundScope) :
    LambdaPFC.Path.Ty SourceContext (.var 0)
      (.ty RecordUseValueV2Regression.SourceType.weaken) :=
  .var

noncomputable def olderInterface (bound : BoundScope) (index : Fin 3) :
    ValueInterface TargetContext := by
  cases bound
  exact (RecordUseValueV2Regression.Second.view index).rename
    TargetPlan.telescope.weaken
    (TargetPlan.telescope.weaken_typed
      RecordUseValueV2Regression.Second.Context)

@[simp] theorem olderInterface_eq (bound : BoundScope) (index : Fin 3) :
    bound.olderInterface index = bound.view index.succ := by
  rfl

/-- The immediately older receiver is the exact compiled `secondRecord`. -/
noncomputable def secondRecordInterface (bound : BoundScope) :
    ValueInterface TargetContext :=
  bound.olderInterface 0

noncomputable def firstRecordInterface (bound : BoundScope) :
    ValueInterface TargetContext :=
  bound.olderInterface 1

noncomputable def implementationInterface (bound : BoundScope) :
    ValueInterface TargetContext :=
  bound.olderInterface 2

end BoundScope

/-! ## Retained second-record selected alias -/

noncomputable abbrev SelectedPlan : ValuePlan TargetPlan.scope :=
  RecordUseValueV2Regression.SelectedImplementationPlan.rename
    TargetPlan.telescope.weaken

noncomputable def selectedDescriptor :=
  RecordSecondValueV2Binding.selectedDescriptor.subst
    TargetPlan.telescope.weaken.asSubst
    (TargetModelRenaming.substTyped
      (TargetPlan.telescope.weaken_typed
        RecordUseValueV2Regression.Second.Context))

/-- The exact second-record alias after the use-function package has been
opened.  Its constructor cannot be used with another bound receiver. -/
structure SelectedAlias (bound : BoundScope) : Type where
  private mk ::
  head_eq : bound.head = functionHead

noncomputable def selectedAlias (bound : BoundScope) : SelectedAlias bound := by
  cases bound
  exact .mk rfl

namespace SelectedAlias

noncomputable def descriptor
    {bound : BoundScope} (_alias : SelectedAlias bound) :=
  selectedDescriptor

@[simp] theorem selected_eq
    {bound : BoundScope} (alias : SelectedAlias bound) :
    alias.descriptor.selected = SelectedPlan := by
  rfl

@[simp] theorem lower_eq
    {bound : BoundScope} (alias : SelectedAlias bound) :
    alias.descriptor.lowerAdapter =
      StableIdentity.Adapter.identity TargetContext SelectedPlan := by
  rfl

@[simp] theorem upper_eq
    {bound : BoundScope} (alias : SelectedAlias bound) :
    alias.descriptor.upperAdapter =
      StableIdentity.Adapter.identity TargetContext SelectedPlan := by
  rfl

end SelectedAlias

noncomputable abbrev SecondRecordPlan : ValuePlan TargetPlan.scope :=
  (RecordUseValueV2Regression.Second.view 0).plan.rename
    RecordUseValueV2Regression.TargetPlan.telescope.weaken

@[simp] theorem secondRecordInterface_plan (bound : BoundScope) :
    bound.secondRecordInterface.plan = SecondRecordPlan := by
  rfl

@[simp] theorem implementationInterface_plan (bound : BoundScope) :
    bound.implementationInterface.plan =
      RecordSecondValueV2Binding.SelectedPlan.rename
        TargetPlan.telescope.weaken := by
  rfl

noncomputable abbrev BoundUsePlan : ValuePlan TargetPlan.scope :=
  RecordUseValueV2Regression.TargetPlan.rename
    RecordUseValueV2Regression.TargetPlan.telescope.weaken

noncomputable abbrev BoundUseCodomain : ValuePlan SelectedPlan.scope :=
  Top.plan SelectedPlan.scope

@[simp] theorem newestFunctionPlan (bound : BoundScope) :
    bound.newestInterface.plan =
      Function.plan SelectedPlan BoundUseCodomain := by
  rfl

end

end LambdaPToFCo.Full.RecordUseValueV2Binding
