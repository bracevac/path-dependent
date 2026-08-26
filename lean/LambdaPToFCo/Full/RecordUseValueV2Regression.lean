import LambdaPToFCo.Full.RecordSecondValueV2Binding
import LambdaPToFCo.Full.ApplicationCompilerCore
import LambdaPToFCo.Full.PathPackageClosure

/-!
# Executable V2 compilation of the Record use abstraction

This leaf compiles the existing `RecordRegression.useValue` immediately after
the exact V2 `secondValue` package has been bound.  The source annotation
`r2.A` uses only the sealed selected alias retained by
`RecordSecondValueV2Binding`; in this concrete exact interval it is the same
complete plan as the older implementation and is definitionally a
`Top -> Top` function plan.

The body opens the bound parameter interface, adapts the older implementation
package to `Top`, applies the parameter through `ApplicationCompilerCore`,
closes that argument-package focus back to `Top`, and builds the exact
abstraction package.  The result is indexed by the literal source typing and
origin.  No V1 `ScopeModel`, `WfPlan`, resolver, package callback, adapter
input, or target-calculus change is introduced.
-/

namespace LambdaPToFCo.Full.RecordUseValueV2Regression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open RecordSecondValueV2Binding

noncomputable section

/-! ## Exact source derivation -/

abbrev SourceContext := RecordSecondValueV2Binding.SourceContext

abbrev SourceType : LambdaPFC.Ty 3 :=
  .Fun (.TSel (.var 0) LambdaPFC.RecordRegression.typeLabel) .Top

abbrev BodySourceContext :=
  SourceContext.snoc
    (.TSel (.var 0) LambdaPFC.RecordRegression.typeLabel)

def selectionTyping : Path.Ty SourceContext
    ((Path.var 0).sel LambdaPFC.RecordRegression.typeLabel)
    (.intv LambdaPFC.RecordRegression.implementationType
      LambdaPFC.RecordRegression.implementationType) := by
  exact LambdaPFC.RecordRegression.r2_type_selection_typing

def selectionWf : Tau.Wf SourceContext
    (.ty (.TSel (.var 0) LambdaPFC.RecordRegression.typeLabel)) :=
  .sel selectionTyping .refl

def selectedParameterTyping : Tm.Ty BodySourceContext
    (.path (.var 0)) LambdaPFC.RecordRegression.implementationType := by
  apply Tm.Ty.sub (Tm.Ty.path Path.Ty.var)
  · exact .trans (.widen .var)
      (.sel_hi (LambdaPFC.RecordRegression.secondRecord_type .var) .refl)
  · exact LambdaPFC.RecordRegression.implementationTypeWf

def implementationArgumentTyping : Tm.Ty BodySourceContext
    (.path (.var 3)) .Top :=
  .sub (.path .var) .top .top

def bodyTyping : Tm.Ty BodySourceContext
    (.app (.var 0) (.var 3)) .Top :=
  .app selectedParameterTyping implementationArgumentTyping

def sourceTyping : Tm.Ty SourceContext LambdaPFC.RecordRegression.useValue
    SourceType := by
  simpa [LambdaPFC.RecordRegression.useValue] using
    (Tm.Ty.abs bodyTyping selectionWf)

def sourceOrigin : ProducerOrigin SourceContext SourceType :=
  ProducerOrigin.ofTyping sourceTyping

theorem sourceOrigin_eq : sourceOrigin =
    .push (.refl (τ := .ty SourceType)) (.value sourceTyping .abs) := by
  rfl

/-! ## Target plans and opened body interfaces -/

namespace Second

abbrev BaseContext := RecordSecondValueV2Regression.TargetContext

noncomputable abbrev Plan := RecordSecondValueV2Regression.TargetPlan

abbrev Context := Plan.context BaseContext

noncomputable def bound := RecordSecondValueV2Binding.bind

noncomputable def view : ScopeView 3 Context :=
  bound.view

end Second

/-- The annotation plan is selected only through the sealed exact alias. -/
noncomputable def selectedAlias :=
  RecordSecondValueV2Binding.selectedAlias Second.bound

noncomputable abbrev SelectedImplementationPlan : ValuePlan Second.Plan.scope :=
  RecordSecondValueV2Binding.SelectedPlan

@[simp] theorem selected_descriptor_plan : selectedAlias.descriptor.selected =
    SelectedImplementationPlan := by
  rfl

@[simp] theorem selected_implementation_interface :
    Second.bound.implementationInterface.plan =
      SelectedImplementationPlan := by
  rfl

noncomputable abbrev CallDomain : ValuePlan Second.Plan.scope :=
  RecordSecondValueV2Binding.ApplicationDomainPlan

noncomputable abbrev CallCodomain : ValuePlan CallDomain.scope :=
  RecordSecondValueV2Binding.ApplicationCodomainPlan

@[simp] theorem selected_is_function : SelectedImplementationPlan =
    Function.plan CallDomain CallCodomain :=
  RecordSecondValueV2Binding.selectedPlan_function_eq

namespace Body

abbrev Context := SelectedImplementationPlan.context Second.Context

noncomputable def view : ScopeView 4 Context :=
  ScopeView.bindPlan Second.view SelectedImplementationPlan

noncomputable def parameter : ValueInterface Context :=
  view 0

noncomputable def olderImplementation : ValueInterface Context :=
  Second.bound.implementationInterface.rename
    SelectedImplementationPlan.telescope.weaken
    (SelectedImplementationPlan.telescope.weaken_typed Second.Context)

@[simp] theorem older_implementation_view : olderImplementation = view 3 := by
  rfl

theorem parameter_plan : parameter.plan =
    Function.plan
      (CallDomain.rename SelectedImplementationPlan.telescope.weaken)
      (Function.renameCodomain CallDomain CallCodomain
        SelectedImplementationPlan.telescope.weaken) := by
  rw [parameter, view, ScopeView.bindPlan_here,
    TranslationInterfaces.ValueInterface.ofArguments_plan,
    selected_is_function, Function.plan_rename]

noncomputable abbrev ArgumentPlan : ValuePlan
    SelectedImplementationPlan.scope :=
  Top.plan SelectedImplementationPlan.scope

noncomputable abbrev ResultPlan : ValuePlan ArgumentPlan.scope :=
  Top.plan ArgumentPlan.scope

@[simp] theorem parameter_function_plan : parameter.plan =
    Function.plan ArgumentPlan ResultPlan := by
  rw [parameter_plan]
  rfl

noncomputable def functionView :
    FunctionInterface.View Context ArgumentPlan ResultPlan where
  interface := parameter
  plan_eq := parameter_function_plan

noncomputable def olderPackage :
    PathPackageZipper.CompiledPackage Context olderImplementation.plan :=
  PathPackageZipper.CompiledPackage.ofInterface olderImplementation

noncomputable def argumentPackage :
    PathPackageZipper.CompiledPackage Context ArgumentPlan :=
  TranslationInterfaces.CompiledPackage.adapt olderPackage
    (StableIdentity.Adapter.toTop Context olderImplementation.plan)

end Body

/-! ## Exact application and focus closure -/

namespace Argument

abbrev Context := Body.ArgumentPlan.context Body.Context

noncomputable def zipper :
    PathPackageZipper.ResultZipper Body.Context Context :=
  (PathPackageZipper.ResultZipper.root Body.Context).enterPackage
    Body.argumentPackage

noncomputable def interface : ValueInterface Context :=
  PathPackageZipper.openedInterface Body.Context Body.ArgumentPlan

@[simp] theorem interface_plan : interface.plan =
    Body.ArgumentPlan.rename Body.ArgumentPlan.telescope.weaken := by
  rfl

noncomputable def functionView : FunctionInterface.View Context
    (Body.ArgumentPlan.rename Body.ArgumentPlan.telescope.weaken)
    (Function.renameCodomain Body.ArgumentPlan Body.ResultPlan
      Body.ArgumentPlan.telescope.weaken) where
  interface := Body.functionView.interface.rename
    Body.ArgumentPlan.telescope.weaken
    (Body.ArgumentPlan.telescope.weaken_typed Body.Context)
  plan_eq := by
    change Body.functionView.interface.plan.rename
      Body.ArgumentPlan.telescope.weaken = _
    rw [Body.functionView.plan_eq, Function.plan_rename]
    rfl

noncomputable def applied :=
  ApplicationCompilerCore.applyOpened functionView interface interface_plan

end Argument

noncomputable abbrev BodyResultPlan : ValuePlan
    SelectedImplementationPlan.scope :=
  Top.plan SelectedImplementationPlan.scope

namespace Application

noncomputable def result : PathPackageZipper.PathResult Body.Context where
  currentSig := Body.ArgumentPlan.scope
  currentContext := Argument.Context
  zipper := Argument.zipper
  plan := (Function.renameCodomain Body.ArgumentPlan Body.ResultPlan
    Body.ArgumentPlan.telescope.weaken).subst
      Argument.interface.arguments.substitution
  package := Argument.applied

@[simp] theorem close_plan : result.plan =
    BodyResultPlan.rename result.zipper.weakening := by
  rfl

noncomputable def closed :
    PathPackageZipper.CompiledPackage Body.Context BodyResultPlan :=
  result.close BodyResultPlan close_plan

end Application

/-! ## Sealed executable abstraction result -/

noncomputable abbrev TargetPlan : ValuePlan Second.Plan.scope :=
  Function.plan SelectedImplementationPlan BodyResultPlan

private noncomputable def targetPackage :
    PathPackageZipper.CompiledPackage Second.Context TargetPlan where
  expression := Function.exactAbstractionPackage SelectedImplementationPlan
    BodyResultPlan Application.closed.expression Application.closed.typing
  typing := Function.exactAbstractionPackage_hasType
    SelectedImplementationPlan BodyResultPlan Application.closed.expression
    Application.closed.typing

/-- Exact source/target result.  Its private constructor is filled only from
the sealed alias and the internally computed application/abstraction package. -/
structure Result : Type where
  private mk ::
  alias : RecordSecondValueV2Binding.SelectedAlias Second.bound
  package : PathPackageZipper.CompiledPackage Second.Context TargetPlan
  origin : ProducerOrigin SourceContext SourceType

noncomputable def compile : Result where
  alias := selectedAlias
  package := targetPackage
  origin := sourceOrigin

noncomputable def compiled := compile

@[simp] theorem compiled_origin_eq : compiled.origin =
    ProducerOrigin.ofTyping sourceTyping := by
  rfl

noncomputable def targetTerm := compiled.package.expression

noncomputable def targetTerm_hasType : Exp.HasType Second.Context targetTerm
    TargetPlan.inputTy :=
  compiled.package.typing

end

end LambdaPToFCo.Full.RecordUseValueV2Regression
