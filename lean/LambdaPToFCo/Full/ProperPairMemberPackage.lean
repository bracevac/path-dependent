import LambdaPToFCo.Full.ProperMemberOpening
import LambdaPToFCo.Full.TelescopeArgumentSplit

/-!
# Canonical proper-member packages inside an opened representation

After a proper pair's outer package has been opened, its representation is a
single appended telescope.  This leaf opens that exact representation,
splits its canonical identity arguments, and repackages the suffix at the
literal plan selected by `ModelInstantiation.openAtTargetRename`.

The source-facing constructor still requires the sealed model-coherence
result for that exact action.  It does not accept a member package, plan
equality, representation coercion, or arbitrary replacement model.  This is
therefore the package-construction half of dependent right selection, not a
claim that a receiver path or its outer zipper has already been compiled.
-/

namespace LambdaPToFCo.Full.ProperPairMemberPackage

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

abbrev Representation (first : ValuePlan sig)
    (member : ValuePlan first.scope) : Telescope sig :=
  Pair.Proper.representation first member

abbrev Context (base : SystemFCoExt.Ctx sig) (first : ValuePlan sig)
    (member : ValuePlan first.scope) :
    SystemFCoExt.Ctx (Representation first member).scope :=
  (Representation first member).context base

abbrev Mapping (first : ValuePlan sig) (member : ValuePlan first.scope) :
    Rename sig (Representation first member).scope :=
  (Representation first member).weaken

abbrev RenamedFirst (first : ValuePlan sig)
    (member : ValuePlan first.scope) :
    ValuePlan (Representation first member).scope :=
  first.rename (Mapping first member)

abbrev RenamedMember (first : ValuePlan sig)
    (member : ValuePlan first.scope) :
    ValuePlan (RenamedFirst first member).scope :=
  Pair.Proper.renameMember first member (Mapping first member)

noncomputable def allArguments (base : SystemFCoExt.Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :
    Telescope.Args (Context base first member)
      ((Representation first member).rename (Mapping first member)) :=
  Telescope.Args.identity (Representation first member) base

theorem representation_rename_eq (first : ValuePlan sig)
    (member : ValuePlan first.scope) :
    (Representation first member).rename (Mapping first member) =
      (RenamedFirst first member).telescope.append
        (RenamedMember first member).telescope := by
  exact Pair.Proper.representation_rename first member (Mapping first member)

/-- The proof-relevant split of the opened representation.  The suffix is
indexed by the substitution of the exact first spine returned here. -/
noncomputable def splitArguments (base : SystemFCoExt.Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :
    Sigma fun firstArguments : Telescope.Args (Context base first member)
      (RenamedFirst first member).telescope =>
      Telescope.Args (Context base first member)
        ((RenamedMember first member).telescope.subst
          firstArguments.substitution) := by
  let arguments : Telescope.Args (Context base first member)
      ((RenamedFirst first member).telescope.append
        (RenamedMember first member).telescope) :=
    representation_rename_eq first member ▸ allArguments base first member
  exact TargetArguments.splitAppend (RenamedMember first member).telescope
    arguments

/-- The actual first-field arguments observed in the representation body. -/
noncomputable def firstArguments (base : SystemFCoExt.Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :
    Telescope.Args (Context base first member)
      (RenamedFirst first member).telescope :=
  (splitArguments base first member).1

/-- The literal target plan selected by `openAtTargetRename` for these
first-field arguments. -/
noncomputable def actionPlan (base : SystemFCoExt.Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :
    ValuePlan (Representation first member).scope :=
  member.subst
    ((first.telescope.liftRename (Mapping first member)).asSubst.comp
      (firstArguments base first member).substitution)

/-- The member interface reconstructed from the suffix arguments, available
only inside the opened representation context. -/
noncomputable def interface (base : SystemFCoExt.Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :
    ValueInterface (Context base first member) :=
  ValueInterface.ofArguments
    ((RenamedMember first member).subst
      (firstArguments base first member).substitution)
    (splitArguments base first member).2

theorem interface_plan_eq (base : SystemFCoExt.Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :
    (interface base first member).plan = actionPlan base first member := by
  unfold interface actionPlan RenamedMember Pair.Proper.renameMember
  rw [TranslationInterfaces.ValueInterface.ofArguments_plan,
    TargetModelRenaming.plan_rename_asSubst, ValuePlan.subst_comp]
  rfl

/-- Canonical compiled member package at the exact action plan. -/
noncomputable def package (base : SystemFCoExt.Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :
    PathPackageZipper.CompiledPackage (Context base first member)
      (actionPlan base first member) := by
  rw [← interface_plan_eq base first member]
  exact PathPackageZipper.CompiledPackage.ofInterface
    (interface base first member)

/-- Fill the retained package field of `ProperMemberOpening` canonically,
once coherence for the same action and the same first arguments is known. -/
noncomputable def opening
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext base)
    (constructed : ConstructedScope scope)
    {path : LambdaPFC.Path n} {firstType : LambdaPFC.Ty n}
    (precise : LambdaPFC.Path.Ty sourceContext path (.ty firstType))
    {firstPlan : ValuePlan sig}
    (first : ProducerPlanModel sourceContext base scope.view firstType firstPlan)
    {memberType : LambdaPFC.Ty (n + 1)}
    {memberPlan : ValuePlan firstPlan.scope}
    (member : ProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context base) (ScopeView.bindPlan scope.view firstPlan)
      memberType memberPlan)
    (certificate : ProducerInstantiationCoherence.Result
      (ModelInstantiation.openAtTargetRename scope constructed
        (Mapping firstPlan memberPlan)
        ((Representation firstPlan memberPlan).weaken_typed base)
        precise first (firstArguments base firstPlan memberPlan)) member) :
    ProperMemberOpening scope constructed (Mapping firstPlan memberPlan)
      ((Representation firstPlan memberPlan).weaken_typed base)
      precise first member where
  arguments := firstArguments base firstPlan memberPlan
  certificate := certificate
  package := package base firstPlan memberPlan

end LambdaPToFCo.Full.ProperPairMemberPackage
