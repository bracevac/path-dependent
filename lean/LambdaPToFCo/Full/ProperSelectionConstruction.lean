import LambdaPToFCo.Full.ProperPairMemberPackage
import LambdaPToFCo.Full.FocusedPathTranslationCore
import LambdaPToFCo.Full.ProperMemberTargetRename

/-!
# Provenance-certified dependent proper selection

This leaf composes the two independently sealed halves of a proper `sel_r`:

* `ProperMemberExchangeCertificate` realizes a dependent member through an
  exact compiler-constructed source binding; and
* `ProperPairMemberPackage` opens the receiver's actual Church package and
  constructs the member package at the literal `openAtTargetRename` plan.

`ProperSelectionCapability` is intentionally stronger than
`ProperPairCapability`.  It retains the current dependent member model, and
its private constructor can be reached only by a direct proper pair or by the
closed `underBinding`/`bound` exchange constructors or by an exact
`targetRename` certificate below.  In particular, this module does not claim
a member for an arbitrary raw pair model or an unrelated target rename.

The final constructors derive both focus extensions, both scope alignments,
the actual first arguments, and the member package.  Their only additional
inputs are the two exact model-coherence results for those fixed actions.
This is a narrow provenance-certified selection finisher, not yet a total
path resolver.
-/

namespace LambdaPToFCo.Full.ProperSelectionConstruction

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open ScopedPathResolution

abbrev OuterPlan (first : ValuePlan sig) (member : ValuePlan first.scope) :=
  Pair.Proper.plan first member

abbrev OuterMapping (first : ValuePlan sig)
    (member : ValuePlan first.scope) :
    Rename sig (OuterPlan first member).scope :=
  (OuterPlan first member).telescope.weaken

noncomputable def outerTyped (base : SystemFCoExt.Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :=
  (OuterPlan first member).telescope.weaken_typed base

abbrev OuterFirst (first : ValuePlan sig) (member : ValuePlan first.scope) :=
  first.subst (OuterMapping first member).asSubst

abbrev OuterMember (first : ValuePlan sig) (member : ValuePlan first.scope) :=
  Pair.Proper.substMember first member (OuterMapping first member).asSubst

noncomputable def outerScope
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext base)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :=
  scope.targetRename (OuterMapping first member)
    (outerTyped base first member)

noncomputable def outerConstructed
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext base}
    (constructed : ConstructedScope scope)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :
    ConstructedScope (outerScope scope first member) :=
  .targetRename constructed (OuterMapping first member)
    (outerTyped base first member)

noncomputable def outerFirstModel
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext base}
    {firstType : LambdaPFC.Ty n} {firstPlan : ValuePlan sig}
    (first : ProducerPlanModel sourceContext base scope.view firstType
      firstPlan)
    (memberPlan : ValuePlan firstPlan.scope) :
    ProducerPlanModel sourceContext
      ((OuterPlan firstPlan memberPlan).context base)
      (outerScope scope firstPlan memberPlan).view firstType
      (OuterFirst firstPlan memberPlan) := by
  simpa only [OuterFirst, TargetModelRenaming.plan_rename_asSubst] using
    TargetModelRenaming.producer first (OuterMapping firstPlan memberPlan)
      (outerTyped base firstPlan memberPlan)

noncomputable def outerAction
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext base)
    (constructed : ConstructedScope scope)
    {firstType : LambdaPFC.Ty n} {firstPlan : ValuePlan sig}
    (first : ProducerPlanModel sourceContext base scope.view firstType firstPlan)
    (memberPlan : ValuePlan firstPlan.scope) :=
  ModelInstantiation.lift
    (.targetRenameScope scope constructed (OuterMapping firstPlan memberPlan)
      (outerTyped base firstPlan memberPlan))
    (ModelInstantiation.targetRenameScopeProducerTarget scope constructed
      (OuterMapping firstPlan memberPlan)
      (outerTyped base firstPlan memberPlan) first)

noncomputable def outerMemberModel
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext base)
    (constructed : ConstructedScope scope)
    {firstType : LambdaPFC.Ty n} {firstPlan : ValuePlan sig}
    (first : ProducerPlanModel sourceContext base scope.view firstType firstPlan)
    {memberType : LambdaPFC.Ty (n + 1)}
    {memberPlan : ValuePlan firstPlan.scope}
    (member : ProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context base) (ScopeView.bindPlan scope.view firstPlan)
      memberType memberPlan)
    (certificate : ProducerInstantiationCoherence.Result
      (outerAction scope constructed first memberPlan) member) :
    ProducerPlanModel (sourceContext.snoc firstType)
      ((OuterFirst firstPlan memberPlan).context
        ((OuterPlan firstPlan memberPlan).context base))
      (ScopeView.bindPlan (outerScope scope firstPlan memberPlan).view
        (OuterFirst firstPlan memberPlan)) memberType
      (OuterMember firstPlan memberPlan) := by
  have result := certificate.instantiated
  simpa only [outerAction, OuterMember,
    ModelInstantiation.ProducerTarget, PathSubst.lift_id,
    LambdaPFC.Ty.subst_id] using result

/-- A sealed proper-pair capability whose first and dependent member models
share the exact substitution-normalized plans selected by its provenance. -/
structure ProperSelectionCapability
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {view : ScopeView n base}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : ProducerPlanModel sourceContext base view sourceType plan) : Type where
  private mk ::
  firstType : LambdaPFC.Ty n
  label : LambdaPFC.Name
  memberType : LambdaPFC.Ty (n + 1)
  source_eq : sourceType = .Pair firstType label (.ty memberType)
  firstPlan : ValuePlan sig
  memberPlan : ValuePlan firstPlan.scope
  plan_eq : plan = Pair.Proper.plan firstPlan memberPlan
  first : ProducerPlanModel sourceContext base view firstType firstPlan
  member : ProducerPlanModel (sourceContext.snoc firstType)
    (firstPlan.context base) (ScopeView.bindPlan view firstPlan)
    memberType memberPlan
  history : ProducerPairHead model

namespace ProperSelectionCapability

/-- Direct proper-pair provenance retains its member definitionally. -/
noncomputable def direct
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {view : ScopeView n base}
    {firstType : LambdaPFC.Ty n} {label : LambdaPFC.Name}
    {memberType : LambdaPFC.Ty (n + 1)}
    {firstPlan : ValuePlan sig} {memberPlan : ValuePlan firstPlan.scope}
    (first : ProducerPlanModel sourceContext base view firstType firstPlan)
    (member : ProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context base) (ScopeView.bindPlan view firstPlan)
      memberType memberPlan) :
    ProperSelectionCapability (.properPair (label := label) first member) where
  firstType := firstType
  label := label
  memberType := memberType
  source_eq := rfl
  firstPlan := firstPlan
  memberPlan := memberPlan
  plan_eq := rfl
  first := first
  member := member
  history := .proper first member

/-- Move a retained member through one compiler-constructed source binding.
The output fields use the substitution-normalized plans determined by the
closed exchange action; no rename equality is assumed. -/
noncomputable def underBinding
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext base)
    (constructed : ConstructedScope scope)
    {boundType olderType : LambdaPFC.Ty n}
    {boundPlan olderPlan : ValuePlan sig}
    (bound : ProducerPlanModel sourceContext base scope.view boundType
      boundPlan)
    (olderModel : ProducerPlanModel sourceContext base scope.view olderType
      olderPlan)
    (capability : ProperSelectionCapability olderModel)
    (certificate : ProperMemberExchangeCertificate scope constructed bound
      capability.first capability.member) :
    ProperSelectionCapability (.underBinding bound olderModel) where
  firstType := capability.firstType.subst FinFun.weaken.asSubst
  label := capability.label
  memberType := capability.memberType.subst FinFun.weaken.asSubst.lift
  source_eq := by
    calc
      olderType.weaken =
          (LambdaPFC.Ty.Pair capability.firstType capability.label
            (.ty capability.memberType)).weaken :=
        congrArg LambdaPFC.Ty.weaken capability.source_eq
      _ = (LambdaPFC.Ty.Pair capability.firstType capability.label
            (.ty capability.memberType)).rename FinFun.weaken := rfl
      _ = (LambdaPFC.Ty.Pair capability.firstType capability.label
            (.ty capability.memberType)).subst FinFun.weaken.asSubst :=
        (LambdaPFC.Ty.subst_asSubst _ _).symm
      _ = LambdaPFC.Ty.Pair
          (capability.firstType.subst FinFun.weaken.asSubst)
          capability.label
          (.ty (capability.memberType.subst
            FinFun.weaken.asSubst.lift)) := rfl
  firstPlan := capability.firstPlan.subst
    boundPlan.telescope.weaken.asSubst
  memberPlan := Pair.Proper.substMember capability.firstPlan
    capability.memberPlan boundPlan.telescope.weaken.asSubst
  plan_eq := by
    calc
      olderPlan.rename boundPlan.telescope.weaken =
          (Pair.Proper.plan capability.firstPlan
            capability.memberPlan).rename boundPlan.telescope.weaken :=
        congrArg (fun current => current.rename
          boundPlan.telescope.weaken) capability.plan_eq
      _ = (Pair.Proper.plan capability.firstPlan
            capability.memberPlan).subst
          boundPlan.telescope.weaken.asSubst :=
        TargetModelRenaming.plan_rename_asSubst _ _
      _ = Pair.Proper.plan
          (capability.firstPlan.subst boundPlan.telescope.weaken.asSubst)
          (Pair.Proper.substMember capability.firstPlan
            capability.memberPlan boundPlan.telescope.weaken.asSubst) :=
        Pair.Proper.plan_subst _ _ _
  first := ModelInstantiation.weakenUnderBindingProducerTarget scope
    constructed bound capability.first
  member := certificate.instantiated
  history := .underBinding bound olderModel capability.history

/-- The newly bound pair uses the same closed exchange as `underBinding`, but
retains the exact `.bound` head history. -/
noncomputable def bound
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext base)
    (constructed : ConstructedScope scope)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : ProducerPlanModel sourceContext base scope.view sourceType plan)
    (capability : ProperSelectionCapability model)
    (certificate : ProperMemberExchangeCertificate scope constructed model
      capability.first capability.member) :
    ProperSelectionCapability (.bound model) := by
  let normalized := underBinding scope constructed model model capability
    certificate
  exact
    { firstType := normalized.firstType
      label := normalized.label
      memberType := normalized.memberType
      source_eq := normalized.source_eq
      firstPlan := normalized.firstPlan
      memberPlan := normalized.memberPlan
      plan_eq := normalized.plan_eq
      first := normalized.first
      member := normalized.member
      history := .bound model capability.history }

/-- Move the retained first/member pair through an exact target rename.  Both
plans are substitution-normalized, and the member comes only from the closed
lifted target-rename certificate. -/
noncomputable def targetRename
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx source}
    {targetTargetContext : SystemFCoExt.Ctx target}
    (scope : ScopeModel sourceContext sourceTargetContext)
    (constructed : ConstructedScope scope)
    {sourceType : LambdaPFC.Ty n} {sourcePlan : ValuePlan source}
    (model : ProducerPlanModel sourceContext sourceTargetContext scope.view
      sourceType sourcePlan)
    (capability : ProperSelectionCapability model)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
    (certificate : ProperMemberTargetRenameCertificate scope constructed
      mapping typed capability.first capability.member) :
    ProperSelectionCapability (.targetRename model mapping typed) where
  firstType := capability.firstType
  label := capability.label
  memberType := capability.memberType
  source_eq := capability.source_eq
  firstPlan := capability.firstPlan.subst mapping.asSubst
  memberPlan := Pair.Proper.substMember capability.firstPlan
    capability.memberPlan mapping.asSubst
  plan_eq := by
    calc
      sourcePlan.rename mapping =
          (Pair.Proper.plan capability.firstPlan
            capability.memberPlan).rename mapping :=
        congrArg (fun current => current.rename mapping) capability.plan_eq
      _ = (Pair.Proper.plan capability.firstPlan
            capability.memberPlan).subst mapping.asSubst :=
        TargetModelRenaming.plan_rename_asSubst _ _
      _ = Pair.Proper.plan
          (capability.firstPlan.subst mapping.asSubst)
          (Pair.Proper.substMember capability.firstPlan
            capability.memberPlan mapping.asSubst) :=
        Pair.Proper.plan_subst _ _ _
  first := by
    simpa only [TargetModelRenaming.plan_rename_asSubst] using
      TargetModelRenaming.producer capability.first mapping typed
  member := certificate.instantiated
  history := .targetRename model capability.history mapping typed

end ProperSelectionCapability

/-- Forget the realized member to the existing proper pair-head boundary. -/
noncomputable def ProperSelectionCapability.proper
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {view : ScopeView n base}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base view sourceType plan}
    (capability : ProperSelectionCapability model) :
    ProperPairCapability model where
  firstType := capability.firstType
  label := capability.label
  memberType := capability.memberType
  source_eq := capability.source_eq
  firstPlan := capability.firstPlan
  memberPlan := capability.memberPlan
  plan_eq := capability.plan_eq
  firstModel := capability.first
  history := capability.history

/-- Forget the stronger member realization to the existing kind-complete
pair projection boundary. -/
noncomputable def ProperSelectionCapability.projection
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {view : ScopeView n base}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base view sourceType plan}
    (capability : ProperSelectionCapability model) :
    ProducerPairProjection model :=
  .proper capability.proper

def ProperSelectionCapability.typing
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {view : ScopeView n base}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base view sourceType plan}
    (capability : ProperSelectionCapability model)
    {path : LambdaPFC.Path n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty sourceType)) :
    LambdaPFC.Path.Ty sourceContext path
      (.ty (.Pair capability.firstType capability.label
        (.ty capability.memberType))) :=
  capability.source_eq ▸ typing

noncomputable def ProperSelectionCapability.package
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {view : ScopeView n base}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base view sourceType plan}
    (capability : ProperSelectionCapability model)
    (package : PathPackageZipper.CompiledPackage base plan) :
    PathPackageZipper.CompiledPackage base
      (Pair.Proper.plan capability.firstPlan capability.memberPlan) :=
  capability.plan_eq ▸ package

private noncomputable def openedView (base : SystemFCoExt.Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :
    PairInterface.Proper.View ((OuterPlan first member).context base)
      (OuterFirst first member) (OuterMember first member) where
  interface := PathPackageZipper.openedInterface base (OuterPlan first member)
  plan_eq := by
    rw [PathPackageZipper.openedInterface_plan,
      TargetModelRenaming.plan_rename_asSubst, Pair.Proper.plan_subst]
    rfl

private noncomputable def representationExpression
    (base : SystemFCoExt.Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :
    PathPackageZipper.CompiledExpression
      ((OuterPlan first member).context base)
      (Pair.Proper.representation (OuterFirst first member)
        (OuterMember first member)).existsTy where
  expression := (openedView base first member).pair.asRepresentation
  typing := (openedView base first member).pair.asRepresentation_hasType

/-- Closed target-rename/lift certificate which moves the retained member
into the receiver's opened outer-pair focus. -/
abbrev OuterMemberCertificate
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext base)
    (constructed : ConstructedScope scope)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base scope.view sourceType plan}
    (capability : ProperSelectionCapability model) :=
  ProducerInstantiationCoherence.Result
    (outerAction scope constructed capability.first capability.memberPlan)
    capability.member

/-- Exact opening certificate for the representation-local first arguments.
The target member is determined by `OuterMemberCertificate`. -/
abbrev RepresentationOpeningCertificate
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext base)
    (constructed : ConstructedScope scope)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base scope.view sourceType plan}
    (capability : ProperSelectionCapability model)
    {path : LambdaPFC.Path n}
    (receiverTyping : LambdaPFC.Path.Ty sourceContext path (.ty sourceType))
    (outerCertificate : OuterMemberCertificate scope constructed capability) :=
  ProducerInstantiationCoherence.Result
    (ModelInstantiation.openAtTargetRename
      (outerScope scope capability.firstPlan capability.memberPlan)
      (outerConstructed constructed capability.firstPlan
        capability.memberPlan)
      (ProperPairMemberPackage.Mapping
        (OuterFirst capability.firstPlan capability.memberPlan)
        (OuterMember capability.firstPlan capability.memberPlan))
      ((ProperPairMemberPackage.Representation
        (OuterFirst capability.firstPlan capability.memberPlan)
        (OuterMember capability.firstPlan capability.memberPlan)).weaken_typed
          ((OuterPlan capability.firstPlan capability.memberPlan).context
            base))
      (capability.typing receiverTyping).fst
      (outerFirstModel capability.first capability.memberPlan)
      (ProperPairMemberPackage.firstArguments
        ((OuterPlan capability.firstPlan capability.memberPlan).context base)
        (OuterFirst capability.firstPlan capability.memberPlan)
        (OuterMember capability.firstPlan capability.memberPlan)))
    (outerMemberModel scope constructed capability.first capability.member
      outerCertificate)

private noncomputable def selectRight
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    (rootScope : ScopeModel sourceContext rootContext)
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext base)
    (constructed : ConstructedScope scope)
    (zipper : PathPackageZipper.ResultZipper rootContext base)
    (alignment : ScopeAlignment
      (rootScope.view.rename zipper.weakening zipper.weakeningTyped)
      scope.view)
    {path : LambdaPFC.Path n} {firstType : LambdaPFC.Ty n}
    {label : LambdaPFC.Name} {memberType : LambdaPFC.Ty (n + 1)}
    (receiverTyping : LambdaPFC.Path.Ty sourceContext path
      (.ty (.Pair firstType label (.ty memberType))))
    {firstPlan : ValuePlan sig}
    (first : ProducerPlanModel sourceContext base scope.view firstType firstPlan)
    {memberPlan : ValuePlan firstPlan.scope}
    (member : ProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context base) (ScopeView.bindPlan scope.view firstPlan)
      memberType memberPlan)
    (receiverPackage : PathPackageZipper.CompiledPackage base
      (OuterPlan firstPlan memberPlan))
    (outerCertificate : ProducerInstantiationCoherence.Result
      (outerAction scope constructed first memberPlan) member)
    (openingCertificate : ProducerInstantiationCoherence.Result
      (ModelInstantiation.openAtTargetRename
        (outerScope scope firstPlan memberPlan)
        (outerConstructed constructed firstPlan memberPlan)
        (ProperPairMemberPackage.Mapping
          (OuterFirst firstPlan memberPlan) (OuterMember firstPlan memberPlan))
        ((ProperPairMemberPackage.Representation
          (OuterFirst firstPlan memberPlan)
          (OuterMember firstPlan memberPlan)).weaken_typed
            ((OuterPlan firstPlan memberPlan).context base))
        receiverTyping.fst (outerFirstModel first memberPlan)
        (ProperPairMemberPackage.firstArguments
          ((OuterPlan firstPlan memberPlan).context base)
          (OuterFirst firstPlan memberPlan) (OuterMember firstPlan memberPlan)))
      (outerMemberModel scope constructed first member outerCertificate)) :
    FocusedProperPathPackage sourceContext rootContext rootScope
      receiverTyping.sel_r := by
  let outer := OuterPlan firstPlan memberPlan
  let openedScope := outerScope scope firstPlan memberPlan
  let openedConstructed := outerConstructed constructed firstPlan memberPlan
  let openedFirst := outerFirstModel first memberPlan
  let openedMember := outerMemberModel scope constructed first member
    outerCertificate
  let representation := Pair.Proper.representation
    (OuterFirst firstPlan memberPlan) (OuterMember firstPlan memberPlan)
  let outerZipper := zipper.enterPackage receiverPackage
  let finalZipper := outerZipper.enter representation
    (representationExpression base firstPlan memberPlan)
  let outerAlignment := FocusedPathTranslationCore.ScopeAlignment.enter
    rootScope zipper scope alignment outer.telescope
  let finalAlignment := FocusedPathTranslationCore.ScopeAlignment.enter
    rootScope outerZipper openedScope outerAlignment representation
  let opening := ProperPairMemberPackage.opening openedScope openedConstructed
    receiverTyping.fst openedFirst openedMember openingCertificate
  exact opening.focused rootScope openedScope openedConstructed
    representation.weaken (representation.weaken_typed (outer.context base))
    receiverTyping openedFirst openedMember finalZipper finalAlignment

/-- Consume the proper branch of `ProducerPairProjection` once its hidden
member has been realized by direct or exchange provenance. -/
noncomputable def selectRightCapability
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    (rootScope : ScopeModel sourceContext rootContext)
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext base)
    (constructed : ConstructedScope scope)
    (zipper : PathPackageZipper.ResultZipper rootContext base)
    (alignment : ScopeAlignment
      (rootScope.view.rename zipper.weakening zipper.weakeningTyped)
      scope.view)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : ProducerPlanModel sourceContext base scope.view sourceType plan)
    (capability : ProperSelectionCapability model)
    {path : LambdaPFC.Path n}
    (receiverTyping : LambdaPFC.Path.Ty sourceContext path (.ty sourceType))
    (receiverPackage : PathPackageZipper.CompiledPackage base plan)
    (outerCertificate : OuterMemberCertificate scope constructed capability)
    (openingCertificate : RepresentationOpeningCertificate scope constructed
      capability receiverTyping outerCertificate) :
    FocusedProperPathPackage sourceContext rootContext rootScope
      (capability.typing receiverTyping).sel_r :=
  selectRight rootScope scope constructed zipper alignment
    (capability.typing receiverTyping) capability.first
    capability.member (capability.package receiverPackage)
    outerCertificate openingCertificate

/-- Provenance-certified proper `sel_r` from an existing focused receiver.
The receiver supplies its package, zipper, scope, and alignment; callers
supply only the constructed-scope history and the two closed member-model
certificates. -/
noncomputable def selectRightFocused
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    (rootScope : ScopeModel sourceContext rootContext)
    {sourceType : LambdaPFC.Ty n} {path : LambdaPFC.Path n}
    (receiverTyping : LambdaPFC.Path.Ty sourceContext path (.ty sourceType))
    (receiver : FocusedProperPathPackage sourceContext rootContext rootScope
      receiverTyping)
    (constructed : ConstructedScope receiver.currentScope)
    (capability : ProperSelectionCapability receiver.modeled)
    (outerCertificate : OuterMemberCertificate receiver.currentScope
      constructed capability)
    (openingCertificate : RepresentationOpeningCertificate
      receiver.currentScope constructed capability receiverTyping
      outerCertificate) :
    FocusedProperPathPackage sourceContext rootContext rootScope
      (capability.typing receiverTyping).sel_r :=
  selectRightCapability rootScope receiver.currentScope constructed
    receiver.zipper receiver.scopeAlignment receiver.modeled capability
    receiverTyping receiver.package outerCertificate openingCertificate

end LambdaPToFCo.Full.ProperSelectionConstruction
