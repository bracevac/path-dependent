import LambdaPToFCo.Full.IntervalSelectionCapability

/-!
# Package-specific interval selection certificates

`IntervalSelectionCapability` retains the model/action half of an interval
selection.  This leaf adds the corresponding exact-package root.  The package
is constructed from the same action-instantiated positive descriptor and the
same first-field arguments: its hidden witness and both package adapters are
therefore not caller-selected.

This boundary is intentionally conditional.  It does not certify an arbitrary
existing `Pair.Interval` package, nor does it turn the raw coercion fields
obtained by opening such a package into `StableIdentity.Adapter.Law` evidence.
In particular, a compiler introduction/adaptation must retain this certificate
when it constructs the package if later interval selection is required.
-/

namespace LambdaPToFCo.Full.IntervalSelectionPackageCertificate

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open IntervalSelectionCapability

/-- Exact opening action for the interval member through the supplied first
path and the actual first-field arguments. -/
noncomputable def firstOpeningAction
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan}
    (capability : Capability scope model)
    {path : LambdaPFC.Path n}
    (precise : LambdaPFC.Path.Ty sourceContext path
      (.ty capability.firstType))
    (arguments : Telescope.Args targetContext
      capability.firstPlan.telescope) :=
  ModelInstantiation.openAt scope precise capability.first arguments

/-- The proof-relevant model-instantiation certificate paired with the exact
first arguments stored by the package constructor below. -/
abbrev FirstOpeningCertificate
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan}
    (capability : Capability scope model)
    {path : LambdaPFC.Path n}
    (precise : LambdaPFC.Path.Ty sourceContext path
      (.ty capability.firstType))
    (arguments : Telescope.Args targetContext
      capability.firstPlan.telescope) :=
  IntervalProducerInstantiationCoherence.Result
    (firstOpeningAction capability precise arguments)
    capability.member.modeled

/-- The exact descriptor after opening the dependent first binder with the
same arguments later stored in the interval representation. -/
noncomputable def openedMember
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan}
    (capability : Capability scope model)
    {path : LambdaPFC.Path n}
    (precise : LambdaPFC.Path.Ty sourceContext path
      (.ty capability.firstType))
    (arguments : Telescope.Args targetContext
      capability.firstPlan.telescope)
    (certificate : FirstOpeningCertificate capability precise arguments) :
    MemberEvidence sourceContext targetContext scope.view
      (capability.lower.subst (PathSubst.openAt path))
      (capability.upper.subst (PathSubst.openAt path))
      (capability.lowerPlan.subst arguments.substitution)
      (capability.upperPlan.subst arguments.substitution) :=
  let action := firstOpeningAction capability precise arguments
  let target := certificate.instantiated
  MemberEvidence.subst
    (sourceView := ScopeView.bindPlan scope.view capability.firstPlan)
    (targetView := scope.view) action capability.member target

/-- Sealed selected-witness view of one exact opened descriptor.  The private
constructor prevents callers from pairing unrelated adapters with the
capability or the actual first arguments. -/
structure SelectedOpening
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan}
    (capability : Capability scope model)
    {path : LambdaPFC.Path n}
    (precise : LambdaPFC.Path.Ty sourceContext path
      (.ty capability.firstType))
    (arguments : Telescope.Args targetContext
      capability.firstPlan.telescope)
    (certificate : FirstOpeningCertificate capability precise arguments) :
    Type where
  private mk ::
  representation : SystemFCoExt.Ty sig
  lowerToSelected : StableIdentity.Adapter targetContext
    (capability.lowerPlan.subst arguments.substitution)
    (Selection.plan representation)
  selectedToUpper : StableIdentity.Adapter targetContext
    (Selection.plan representation)
    (capability.upperPlan.subst arguments.substitution)

namespace SelectedOpening

/-- Open only the descriptor fixed by the action certificate. -/
noncomputable def ofCertificate
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan}
    (capability : Capability scope model)
    {path : LambdaPFC.Path n}
    (precise : LambdaPFC.Path.Ty sourceContext path
      (.ty capability.firstType))
    (arguments : Telescope.Args targetContext
      capability.firstPlan.telescope)
    (certificate : FirstOpeningCertificate capability precise arguments) :
    SelectedOpening capability precise arguments certificate := by
  cases (openedMember capability precise arguments certificate).descriptor with
  | selected representation lowerToSelected selectedToUpper =>
      exact .mk representation lowerToSelected selectedToUpper

end SelectedOpening

/-- Target-only package constructor isolated from all source/action indices.
Keeping this elaboration boundary small also makes clear that its only input
beyond the actual first arguments is one certified positive descriptor. -/
private noncomputable def exactFromDescriptor
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext}
    {lowerType upperType : LambdaPFC.Ty n}
    (first : ValuePlan sig)
    (lower upper : ValuePlan first.scope)
    (arguments : Telescope.Args targetContext first.telescope)
    (descriptor : TranslationModelCore.IntervalDescriptor sourceContext
      targetContext
      (.negative
        ({ plan := lower.subst arguments.substitution } :
          TranslationModelCore.NegativePlan sourceContext targetContext view
            lowerType))
      (.positive
        ({ plan := upper.subst arguments.substitution } :
          TranslationModelCore.PositivePlan sourceContext targetContext view
            upperType))) :
    PathPackageZipper.CompiledPackage targetContext
      (Pair.Interval.plan first lower.inputTy upper.inputTy) := by
  cases descriptor with
  | selected representation lowerToSelected selectedToUpper =>
      have lowerTyping : Co.HasType targetContext lowerToSelected.coercion
          (lower.inputTy.subst arguments.substitution)
          (Selection.plan representation).inputTy := by
        simpa only [ValuePlan.inputTy_subst] using
          lowerToSelected.coercion_hasType
      have upperTyping : Co.HasType targetContext selectedToUpper.coercion
          (Selection.plan representation).inputTy
          (upper.inputTy.subst arguments.substitution) := by
        simpa only [ValuePlan.inputTy_subst] using
          selectedToUpper.coercion_hasType
      exact
        { expression := Pair.Interval.exactWithAdapters first lower.inputTy
            upper.inputTy arguments representation lowerToSelected.coercion
            lowerTyping selectedToUpper.coercion upperTyping
          typing := Pair.Interval.exactWithAdapters_hasType first lower.inputTy
            upper.inputTy arguments representation lowerToSelected.coercion
            lowerTyping selectedToUpper.coercion upperTyping }

/-- Construct the exact interval-pair package from a sealed selected opening.
Both coercions are merely projections of proof-relevant stable adapters. -/
noncomputable def exactPackage
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan}
    (capability : Capability scope model)
    {path : LambdaPFC.Path n}
    (precise : LambdaPFC.Path.Ty sourceContext path
      (.ty capability.firstType))
    (arguments : Telescope.Args targetContext
      capability.firstPlan.telescope)
    (certificate : FirstOpeningCertificate capability precise arguments) :
    PathPackageZipper.CompiledPackage targetContext
      (Pair.Interval.plan capability.firstPlan capability.lowerPlan.inputTy
        capability.upperPlan.inputTy) := by
  exact exactFromDescriptor capability.firstPlan capability.lowerPlan
    capability.upperPlan arguments
    (openedMember capability precise arguments certificate).descriptor

/-- Package-specific provenance.  Its sole constructor retains the exact
action certificate and actual arguments; `PackageCertificate.package` below
computes the only package exposed by this boundary.  There is deliberately no
field for a caller-supplied package. -/
inductive PackageCertificate
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan}
    (capability : Capability scope model) : Type where
  | exact
      {path : LambdaPFC.Path n}
      (precise : LambdaPFC.Path.Ty sourceContext path
        (.ty capability.firstType))
      (arguments : Telescope.Args targetContext
        capability.firstPlan.telescope)
      (certificate : FirstOpeningCertificate capability precise arguments) :
      PackageCertificate capability

namespace PackageCertificate

/-- The exact package determined by the sealed certificate. -/
noncomputable def package
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan}
    {capability : Capability scope model}
    (certificate : PackageCertificate capability) :
    PathPackageZipper.CompiledPackage targetContext
      (Pair.Interval.plan capability.firstPlan capability.lowerPlan.inputTy
        capability.upperPlan.inputTy) := by
  cases certificate with
  | exact precise arguments opening =>
      exact exactPackage capability precise arguments opening

end PackageCertificate

end LambdaPToFCo.Full.IntervalSelectionPackageCertificate
