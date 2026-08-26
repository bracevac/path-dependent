import LambdaPToFCo.Full.RecordSecondValueV2Regression

/-!
# Sealed binding overlay for the second Record value

The exact V2 `secondValue` checkpoint is deliberately model-free: its first
component uses `Pair.IntervalV2`, so it cannot inhabit the frozen V1
`ProducerPlanModel` family.  This Record-specific leaf nevertheless records
the honest target binding produced by opening that exact proper-pair package.

The private construction token ties together the already compiled package,
its proper first/member plans and actual argument spines, and the retained V2
descriptor used by both source selections.  `BoundScope` exposes only the
resulting target interfaces and the exact selected implementation alias.  It
does not claim to be a V1 `ScopeModel`, nor does it accept a package,
descriptor, plan equality, or adapter from its caller.
-/

namespace LambdaPToFCo.Full.RecordSecondValueV2Binding

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

noncomputable section

open RecordSecondValueV2Regression

/-! ## Exact proper-head provenance -/

/-- Construction provenance for the one committed Record second-value
package.  The private token is the only root; all data projections below are
computed from `RecordSecondValueV2Regression`. -/
structure ProperHead : Type where
  private mk ::
  sealed : Unit

noncomputable def properHead : ProperHead :=
  .mk ()

namespace ProperHead

noncomputable def firstPlan (_head : ProperHead) :=
  FirstPlan

noncomputable def memberPlan (_head : ProperHead) : ValuePlan FirstPlan.scope :=
  MemberPlan

noncomputable def descriptor (_head : ProperHead) :=
  newSelectionDescriptor

noncomputable def firstArguments (_head : ProperHead) :
    Telescope.Args TargetContext FirstPlan.telescope :=
  RecordSecondValueV2Regression.firstArguments

noncomputable def memberArguments (_head : ProperHead) :
    Telescope.Args TargetContext
      ((BoundImplementationPlan.rename FirstPlan.telescope.weaken).telescope.subst
        RecordSecondValueV2Regression.firstArguments.substitution) :=
  RecordSecondValueV2Regression.memberArguments

noncomputable def package (_head : ProperHead) :
    PathPackageZipper.CompiledPackage TargetContext TargetPlan :=
  targetPackage

@[simp] theorem firstPlan_eq (head : ProperHead) :
    head.firstPlan = FirstPlan := by
  rfl

@[simp] theorem memberPlan_eq (head : ProperHead) :
    head.memberPlan = MemberPlan := by
  rfl

@[simp] theorem package_eq (head : ProperHead) :
    head.package = targetPackage := by
  rfl

end ProperHead

/-! ## Honest target binding -/

abbrev SourceContext :=
  RecordSecondValueV2Regression.SourceContext.snoc
    LambdaPFC.RecordRegression.secondRecord

noncomputable abbrev TargetContext :=
  RecordSecondValueV2Regression.TargetPlan.context
    RecordSecondValueV2Regression.TargetContext

/-- Opening the exact second-value package.  The predecessor is the V2
first-value overlay rather than a V1 source model. -/
structure BoundScope : Type where
  private mk ::
  head : ProperHead

noncomputable def bind : BoundScope :=
  .mk properHead

namespace BoundScope

noncomputable def view (_bound : BoundScope) : ScopeView 3 TargetContext :=
  ScopeView.bindPlan RecordSecondValueV2Regression.bound.view TargetPlan

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
      (.ty LambdaPFC.RecordRegression.secondRecord.weaken) :=
  .var

/-- Older slots retain their actual open interfaces.  There is intentionally
no V1 model field for the extended source context. -/
noncomputable def olderInterface (bound : BoundScope) (index : Fin 2) :
    ValueInterface TargetContext := by
  cases bound
  exact (RecordSecondValueV2Regression.bound.view index).rename
    TargetPlan.telescope.weaken
    (TargetPlan.telescope.weaken_typed
      RecordSecondValueV2Regression.TargetContext)

@[simp] theorem olderInterface_eq (bound : BoundScope) (index : Fin 2) :
    bound.olderInterface index = bound.view index.succ := by
  rfl

noncomputable def firstRecordInterface (bound : BoundScope) :
    ValueInterface TargetContext :=
  bound.olderInterface 0

noncomputable def implementationInterface (bound : BoundScope) :
    ValueInterface TargetContext :=
  bound.olderInterface 1

end BoundScope

/-! ## Exact selected implementation alias -/

/-- Root-scoped implementation plan after the second-value package has been
opened.  This is the only root factorization used by the subsequent concrete
`useValue` checkpoint. -/
noncomputable abbrev SelectedPlan : ValuePlan TargetPlan.scope :=
  BoundImplementationPlan.rename TargetPlan.telescope.weaken

/-- The retained exact V2 descriptor transported through the same package
opening as every older interface. -/
noncomputable def selectedDescriptor :=
  boundDescriptor.subst TargetPlan.telescope.weaken.asSubst
    (TargetModelRenaming.substTyped
      (TargetPlan.telescope.weaken_typed
        RecordSecondValueV2Regression.TargetContext))

/-- Sealed alias certificate.  It exists only for the exact proper head and
descriptor above; callers cannot pair an unrelated descriptor with a bound
receiver. -/
structure SelectedAlias (bound : BoundScope) : Type where
  private mk ::
  head_eq : bound.head = properHead

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

@[simp] theorem implementationInterface_plan (bound : BoundScope) :
    bound.implementationInterface.plan = SelectedPlan := by
  rfl

@[simp] theorem firstRecordInterface_plan (bound : BoundScope) :
    bound.firstRecordInterface.plan =
      FirstPlan.rename TargetPlan.telescope.weaken := by
  rfl

/-- The exact selected alias retains the concrete implementation-function
shape; no path resolver or fresh representation is chosen. -/
noncomputable abbrev ApplicationDomainPlan : ValuePlan TargetPlan.scope :=
  Top.plan TargetPlan.scope

noncomputable abbrev ApplicationCodomainPlan :
    ValuePlan ApplicationDomainPlan.scope :=
  Top.plan ApplicationDomainPlan.scope

@[simp] theorem selectedPlan_function_eq : SelectedPlan =
    Function.plan ApplicationDomainPlan ApplicationCodomainPlan := by
  rfl

end

end LambdaPToFCo.Full.RecordSecondValueV2Binding
