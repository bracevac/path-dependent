import LambdaPToFCo.Full.PairStableAdapter

/-!
# Construction of dependent proper-pair representation bridges

This target-only leaf derives a coercion between dependent proper-pair
representations from two exact stable-identity adapters.  It opens the source
representation, adapts and opens the first package, applies the member
adapter in that common opened context, and repacks the target representation.
No representation-level coercion is accepted as an input.

This is deliberately not yet a compiler for the source `Tau.Sub.pair` rule.
A source-level wrapper must separately construct the dependent member adapter
from its synchronized source/target instantiation evidence.  In particular,
the leaf does not store a decorative `PairedInstantiation` disconnected from
the packages it opens.

Interval pairs are not handled here.  Their selected witness representation
is Church-hidden, so an honest interval bridge needs a rank-2 continuation
that constructs endpoint adapters for the witness exposed by `consume`; the
current fixed proper-member adapter is not such evidence.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

namespace PairRepresentationBridgeConstruction

private theorem ofArguments_plan
    {sig : Sig} {base : Ctx sig} (plan : ValuePlan sig)
    (arguments : Telescope.Args base plan.telescope) :
    (ValueInterface.ofArguments plan arguments).plan = plan := by
  cases arguments with
  | tvar identity rest =>
      cases rest with
      | var payload payloadTyping observations => rfl

def sourceFirstAtBinder (first : ValuePlan sig) :
    ValuePlan (sig ,, .var) :=
  first.rename (Rename.weaken .var)

def sourceMemberAtBinder (first : ValuePlan sig)
    (member : ValuePlan first.scope) :
    ValuePlan (sourceFirstAtBinder first).scope :=
  Pair.Proper.renameMember first member (Rename.weaken .var)

def representationAtBinder (first : ValuePlan sig)
    (member : ValuePlan first.scope) : Telescope (sig ,, .var) :=
  Pair.Proper.representation (sourceFirstAtBinder first)
    (sourceMemberAtBinder first member)

theorem representationAtBinder_eq (first : ValuePlan sig)
    (member : ValuePlan first.scope) :
    (Pair.Proper.representation first member).rename (Rename.weaken .var) =
      representationAtBinder first member := by
  exact Pair.Proper.representation_rename first member (Rename.weaken .var)

def sourceOpening (first : ValuePlan sig)
    (member : ValuePlan first.scope) :
    Rename (sig ,, .var) (sourceMemberAtBinder first member).scope :=
  (sourceFirstAtBinder first).telescope.weaken.comp
    (sourceMemberAtBinder first member).telescope.weaken

def sourceOpenedContext (base : Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :
    Ctx (sourceMemberAtBinder first member).scope :=
  (sourceMemberAtBinder first member).context
    ((sourceFirstAtBinder first).context
      (base.bindVar (Pair.Proper.representation first member).existsTy))

noncomputable def sourceFirstInterface (base : Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :
    ValueInterface (sourceOpenedContext base first member) :=
  (ValueInterface.ofArguments
    ((sourceFirstAtBinder first).rename
      (sourceFirstAtBinder first).telescope.weaken)
    (Telescope.Args.identity (sourceFirstAtBinder first).telescope
      (base.bindVar (Pair.Proper.representation first member).existsTy))).rename
        (sourceMemberAtBinder first member).telescope.weaken
        ((sourceMemberAtBinder first member).telescope.weaken_typed
          ((sourceFirstAtBinder first).context
            (base.bindVar
              (Pair.Proper.representation first member).existsTy)))

noncomputable def sourceMemberInterface (base : Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :
    ValueInterface (sourceOpenedContext base first member) :=
  ValueInterface.ofArguments
    ((sourceMemberAtBinder first member).rename
      (sourceMemberAtBinder first member).telescope.weaken)
    (Telescope.Args.identity
      (sourceMemberAtBinder first member).telescope
      ((sourceFirstAtBinder first).context
        (base.bindVar (Pair.Proper.representation first member).existsTy)))

def targetFirstAtSource (sourceFirst : ValuePlan sig)
    (sourceMember : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :
    ValuePlan (sourceMemberAtBinder sourceFirst sourceMember).scope :=
  (targetFirst.rename (Rename.weaken .var)).rename
    (sourceOpening sourceFirst sourceMember)

def targetMemberAtSource (sourceFirst : ValuePlan sig)
    (sourceMember : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) (targetMember : ValuePlan targetFirst.scope) :
    ValuePlan (targetFirstAtSource sourceFirst sourceMember targetFirst).scope :=
  Pair.Proper.renameMember
    (targetFirst.rename (Rename.weaken .var))
    (Pair.Proper.renameMember targetFirst targetMember (Rename.weaken .var))
    (sourceOpening sourceFirst sourceMember)

def targetFirstOpenedContext (base : Ctx sig)
    (sourceFirst : ValuePlan sig)
    (sourceMember : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :
    Ctx (targetFirstAtSource sourceFirst sourceMember targetFirst).scope :=
  (targetFirstAtSource sourceFirst sourceMember targetFirst).context
    (sourceOpenedContext base sourceFirst sourceMember)

noncomputable def sourceMemberAtTargetFirst (base : Ctx sig)
    (sourceFirst : ValuePlan sig)
    (sourceMember : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :
    ValueInterface
      (targetFirstOpenedContext base sourceFirst sourceMember targetFirst) :=
  (sourceMemberInterface base sourceFirst sourceMember).rename
    (targetFirstAtSource sourceFirst sourceMember targetFirst).telescope.weaken
    ((targetFirstAtSource sourceFirst sourceMember targetFirst).telescope.weaken_typed
      (sourceOpenedContext base sourceFirst sourceMember))

/-- The member coercion is indexed by the exact common context obtained by
opening the source representation and then the first package produced by the
first adapter.  Its target remains dependent on those freshly opened target
first fields. -/
structure DependentMemberAdapter (base : Ctx sig)
    (sourceFirst : ValuePlan sig)
    (sourceMember : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig)
    (targetMember : ValuePlan targetFirst.scope) : Type where
  adapter : StableIdentity.Adapter
    (targetFirstOpenedContext base sourceFirst sourceMember targetFirst)
    (sourceMemberAtTargetFirst base sourceFirst sourceMember targetFirst).plan
    (targetMemberAtSource sourceFirst sourceMember targetFirst targetMember)

noncomputable def firstCoercionAtSource
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    (adapter : StableIdentity.Adapter base sourceFirst targetFirst) :
    Co (sourceMemberAtBinder sourceFirst sourceMember).scope :=
  ((adapter.coercion.weaken .var).rename
    (sourceFirstAtBinder sourceFirst).telescope.weaken).rename
      (sourceMemberAtBinder sourceFirst sourceMember).telescope.weaken

noncomputable def firstCoercionAtSource_hasType
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    (adapter : StableIdentity.Adapter base sourceFirst targetFirst) :
    Co.HasType (sourceOpenedContext base sourceFirst sourceMember)
      (firstCoercionAtSource (sourceMember := sourceMember) adapter)
      (sourceFirstInterface base sourceFirst sourceMember).plan.inputTy
      (targetFirstAtSource sourceFirst sourceMember targetFirst).inputTy := by
  have outer := adapter.coercion_hasType.weaken
    (.var (Pair.Proper.representation sourceFirst sourceMember).existsTy)
  have underFirst := weakenCo_hasType
    (sourceFirstAtBinder sourceFirst).telescope outer
  have underMember := weakenCo_hasType
    (sourceMemberAtBinder sourceFirst sourceMember).telescope underFirst
  have sourceRawEq :
      ((sourceFirst.inputTy.weaken .var).rename
          (sourceFirstAtBinder sourceFirst).telescope.weaken).rename
            (sourceMemberAtBinder sourceFirst sourceMember).telescope.weaken =
        (sourceFirstInterface base sourceFirst sourceMember).plan.inputTy := by
    unfold Ty.weaken sourceFirstAtBinder sourceFirstInterface
    rw [ValuePlan.inputTy_rename, ValuePlan.inputTy_rename,
      ValuePlan.inputTy_rename]
    simp only [ValueInterface.rename,
      ofArguments_plan]
    rfl
  have targetRawEq :
      ((targetFirst.inputTy.weaken .var).rename
          (sourceFirstAtBinder sourceFirst).telescope.weaken).rename
            (sourceMemberAtBinder sourceFirst sourceMember).telescope.weaken =
        (targetFirstAtSource sourceFirst sourceMember targetFirst).inputTy := by
    unfold Ty.weaken targetFirstAtSource sourceOpening
    rw [ValuePlan.inputTy_rename, ValuePlan.inputTy_rename,
      ValuePlan.inputTy_rename, ValuePlan.rename_comp]
    rfl
  exact sourceRawEq ▸ targetRawEq ▸ underMember

noncomputable def adaptedFirstPackage
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    (adapter : StableIdentity.Adapter base sourceFirst targetFirst) :
    Exp (sourceMemberAtBinder sourceFirst sourceMember).scope :=
  .cast
    (sourceFirstInterface base sourceFirst sourceMember).package
    (firstCoercionAtSource (sourceMember := sourceMember) adapter)

noncomputable def adaptedFirstPackage_hasType
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    (adapter : StableIdentity.Adapter base sourceFirst targetFirst) :
    Exp.HasType (sourceOpenedContext base sourceFirst sourceMember)
      (adaptedFirstPackage (sourceMember := sourceMember) adapter)
      (targetFirstAtSource sourceFirst sourceMember targetFirst).inputTy :=
  .cast
    (sourceFirstInterface base sourceFirst sourceMember).package_hasType
    (firstCoercionAtSource_hasType
      (sourceMember := sourceMember) adapter)

noncomputable def adaptedMemberPackage
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    {targetMember : ValuePlan targetFirst.scope}
    (bridge : DependentMemberAdapter base sourceFirst sourceMember
      targetFirst targetMember) :
    Exp (targetFirstAtSource sourceFirst sourceMember targetFirst).scope :=
  bridge.adapter.apply
    (sourceMemberAtTargetFirst base sourceFirst sourceMember targetFirst).package

noncomputable def adaptedMemberPackage_hasType
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    {targetMember : ValuePlan targetFirst.scope}
    (bridge : DependentMemberAdapter base sourceFirst sourceMember
      targetFirst targetMember) :
    Exp.HasType
      (targetFirstOpenedContext base sourceFirst sourceMember targetFirst)
      (adaptedMemberPackage bridge)
      (targetMemberAtSource sourceFirst sourceMember targetFirst
        targetMember).inputTy :=
  bridge.adapter.apply_hasType
    (sourceMemberAtTargetFirst base sourceFirst sourceMember
      targetFirst).package_hasType

def targetRepresentationAtSource
    (sourceFirst : ValuePlan sig)
    (sourceMember : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig)
    (targetMember : ValuePlan targetFirst.scope) :
    Telescope (sourceMemberAtBinder sourceFirst sourceMember).scope :=
  Pair.Proper.representation
    (targetFirstAtSource sourceFirst sourceMember targetFirst)
    (targetMemberAtSource sourceFirst sourceMember targetFirst targetMember)

theorem targetRepresentationAtSource_eq
    (sourceFirst : ValuePlan sig)
    (sourceMember : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig)
    (targetMember : ValuePlan targetFirst.scope) :
    (representationAtBinder targetFirst targetMember).rename
        (sourceOpening sourceFirst sourceMember) =
      targetRepresentationAtSource sourceFirst sourceMember targetFirst
        targetMember := by
  exact Pair.Proper.representation_rename
    (sourceFirstAtBinder targetFirst)
    (sourceMemberAtBinder targetFirst targetMember)
    (sourceOpening sourceFirst sourceMember)

private def toSuffixExp (first : Telescope sig)
    (suffix : Telescope first.scope)
    (expression : Exp (first.append suffix).scope) : Exp suffix.scope :=
  cast (congrArg Exp (first.appendScopeEq suffix)) expression

private def toSuffixTy (first : Telescope sig)
    (suffix : Telescope first.scope)
    (type : Ty (first.append suffix).scope) : Ty suffix.scope :=
  cast (congrArg Ty (first.appendScopeEq suffix)) type

private noncomputable def toSuffixExp_hasType
    (first : Telescope sig) (suffix : Telescope first.scope)
    {base : Ctx sig} {expression : Exp (first.append suffix).scope}
    {type : Ty (first.append suffix).scope}
    (typing : Exp.HasType ((first.append suffix).context base)
      expression type) :
    Exp.HasType (suffix.context (first.context base))
      (toSuffixExp first suffix expression)
      (toSuffixTy first suffix type) := by
  induction first with
  | nil => exact typing
  | var parameter tail ih => exact ih suffix typing
  | tvar tail ih => exact ih suffix typing
  | cvar source target tail ih => exact ih suffix typing

private noncomputable def nestedRepresentationPackage
    (base : Ctx sig) (first : ValuePlan sig)
    (member : ValuePlan first.scope) : Exp member.scope :=
  toSuffixExp first.telescope member.telescope
    (((Pair.Proper.representation first member).rename
      (Pair.Proper.representation first member).weaken).pack
      (Telescope.Args.identity
        (Pair.Proper.representation first member) base))

private theorem cast_symm_eq
    {index : Sort u} {family : index → Sort v}
    {firstIndex secondIndex : index} (equal : firstIndex = secondIndex)
    {first : family firstIndex} {second : family secondIndex}
    (forward : cast (congrArg family equal) first = second) :
    cast (congrArg family equal.symm) second = first := by
  cases equal
  exact forward.symm

private theorem toSuffixTy_weaken
    (first : Telescope sig) (suffix : Telescope first.scope)
    (type : Ty sig) :
    toSuffixTy first suffix
        (type.rename (first.append suffix).weaken) =
      (type.rename first.weaken).rename suffix.weaken := by
  unfold toSuffixTy
  exact cast_symm_eq (first.appendScopeEq suffix).symm
    (PairInterface.fromSuffixTy_weaken first suffix type)

private noncomputable def nestedRepresentationPackage_hasType
    (base : Ctx sig) (first : ValuePlan sig)
    (member : ValuePlan first.scope) :
    Exp.HasType (member.context (first.context base))
      (nestedRepresentationPackage base first member)
      (((Pair.Proper.representation first member).existsTy.rename
        first.telescope.weaken).rename member.telescope.weaken) := by
  have packed := Telescope.pack_hasType
    (Telescope.Args.identity
      (Pair.Proper.representation first member) base)
  have transported := toSuffixExp_hasType first.telescope member.telescope
    packed
  rw [← existsTy_rename] at transported
  change Exp.HasType _ _
    (toSuffixTy first.telescope member.telescope
      ((Pair.Proper.representation first member).existsTy.rename
        (first.telescope.append member.telescope).weaken)) at transported
  rw [toSuffixTy_weaken] at transported
  exact transported

noncomputable def eliminateAdaptedMember
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    {targetMember : ValuePlan targetFirst.scope}
    (bridge : DependentMemberAdapter base sourceFirst sourceMember
      targetFirst targetMember) :
    Exp (targetFirstAtSource sourceFirst sourceMember targetFirst).scope :=
  let first := targetFirstAtSource sourceFirst sourceMember targetFirst
  let member := targetMemberAtSource sourceFirst sourceMember targetFirst
    targetMember
  let representation := targetRepresentationAtSource sourceFirst sourceMember
    targetFirst targetMember
  member.unpack (adaptedMemberPackage bridge)
    (representation.existsTy.rename first.telescope.weaken)
    (nestedRepresentationPackage
      (sourceOpenedContext base sourceFirst sourceMember) first member)

noncomputable def eliminateAdaptedMember_hasType
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    {targetMember : ValuePlan targetFirst.scope}
    (bridge : DependentMemberAdapter base sourceFirst sourceMember
      targetFirst targetMember) :
    Exp.HasType
      (targetFirstOpenedContext base sourceFirst sourceMember targetFirst)
      (eliminateAdaptedMember bridge)
      ((targetRepresentationAtSource sourceFirst sourceMember targetFirst
        targetMember).existsTy.rename
          (targetFirstAtSource sourceFirst sourceMember
            targetFirst).telescope.weaken) := by
  exact (targetMemberAtSource sourceFirst sourceMember targetFirst
    targetMember).unpack_hasType (adaptedMemberPackage_hasType bridge)
      (nestedRepresentationPackage_hasType
        (sourceOpenedContext base sourceFirst sourceMember)
        (targetFirstAtSource sourceFirst sourceMember targetFirst)
        (targetMemberAtSource sourceFirst sourceMember targetFirst targetMember))

noncomputable def eliminateAdaptedFirst
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    {targetMember : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (memberBridge : DependentMemberAdapter base sourceFirst sourceMember
      targetFirst targetMember) :
    Exp (sourceMemberAtBinder sourceFirst sourceMember).scope :=
  (targetFirstAtSource sourceFirst sourceMember targetFirst).unpack
    (adaptedFirstPackage (sourceMember := sourceMember) firstAdapter)
    (targetRepresentationAtSource sourceFirst sourceMember targetFirst
      targetMember).existsTy
    (eliminateAdaptedMember memberBridge)

noncomputable def eliminateAdaptedFirst_hasType
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    {targetMember : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (memberBridge : DependentMemberAdapter base sourceFirst sourceMember
      targetFirst targetMember) :
    Exp.HasType (sourceOpenedContext base sourceFirst sourceMember)
      (eliminateAdaptedFirst firstAdapter memberBridge)
      (targetRepresentationAtSource sourceFirst sourceMember targetFirst
        targetMember).existsTy :=
  (targetFirstAtSource sourceFirst sourceMember targetFirst).unpack_hasType
    (adaptedFirstPackage_hasType
      (sourceMember := sourceMember) firstAdapter)
    (eliminateAdaptedMember_hasType memberBridge)

noncomputable def representationVariable_hasType
    (base : Ctx sig) (first : ValuePlan sig)
    (member : ValuePlan first.scope) :
    Exp.HasType
      (base.bindVar (Pair.Proper.representation first member).existsTy)
      (.var .here) (representationAtBinder first member).existsTy := by
  have variableTyping : Exp.HasType
      (base.bindVar (Pair.Proper.representation first member).existsTy)
      (.var .here)
      ((Pair.Proper.representation first member).existsTy.weaken .var) :=
    .var Ctx.Lookup.here
  rw [Ty.weaken, existsTy_rename,
    representationAtBinder_eq] at variableTyping
  exact variableTyping

noncomputable def openedRepresentationBody
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    {targetMember : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (memberBridge : DependentMemberAdapter base sourceFirst sourceMember
      targetFirst targetMember) :
    Exp (representationAtBinder sourceFirst sourceMember).scope :=
  Pair.fromSuffixExp (sourceFirstAtBinder sourceFirst).telescope
    (sourceMemberAtBinder sourceFirst sourceMember).telescope
    (eliminateAdaptedFirst firstAdapter memberBridge)

noncomputable def openedRepresentationBody_hasType
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    {targetMember : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (memberBridge : DependentMemberAdapter base sourceFirst sourceMember
      targetFirst targetMember) :
    Exp.HasType
      ((representationAtBinder sourceFirst sourceMember).context
        (base.bindVar
          (Pair.Proper.representation sourceFirst sourceMember).existsTy))
      (openedRepresentationBody firstAdapter memberBridge)
      ((representationAtBinder targetFirst targetMember).existsTy.rename
        (representationAtBinder sourceFirst sourceMember).weaken) := by
  have inner := eliminateAdaptedFirst_hasType firstAdapter memberBridge
  have targetEq :
      (targetRepresentationAtSource sourceFirst sourceMember targetFirst
        targetMember).existsTy =
      (((representationAtBinder targetFirst targetMember).existsTy.rename
        (sourceFirstAtBinder sourceFirst).telescope.weaken).rename
          (sourceMemberAtBinder sourceFirst sourceMember).telescope.weaken) := by
    rw [← targetRepresentationAtSource_eq]
    rw [← existsTy_rename]
    unfold sourceOpening
    rw [Ty.rename_comp]
    rfl
  rw [targetEq] at inner
  have transported := PairInterface.fromSuffixExp_hasType
    (sourceFirstAtBinder sourceFirst).telescope
    (sourceMemberAtBinder sourceFirst sourceMember).telescope inner
  have typeEq := PairInterface.fromSuffixTy_weaken
    (sourceFirstAtBinder sourceFirst).telescope
    (sourceMemberAtBinder sourceFirst sourceMember).telescope
    (representationAtBinder targetFirst targetMember).existsTy
  exact typeEq ▸ transported

noncomputable def representationBody
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    {targetMember : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (memberBridge : DependentMemberAdapter base sourceFirst sourceMember
      targetFirst targetMember) : Exp (sig ,, .var) :=
  (representationAtBinder sourceFirst sourceMember).unpack (.var .here)
    (representationAtBinder targetFirst targetMember).existsTy
    (openedRepresentationBody firstAdapter memberBridge)

noncomputable def representationBody_hasType
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    {targetMember : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (memberBridge : DependentMemberAdapter base sourceFirst sourceMember
      targetFirst targetMember) :
    Exp.HasType
      (base.bindVar (Pair.Proper.representation sourceFirst sourceMember).existsTy)
      (representationBody firstAdapter memberBridge)
      ((Pair.Proper.representation targetFirst targetMember).existsTy.weaken
        .var) := by
  have result :=
    (representationAtBinder sourceFirst sourceMember).unpack_hasType
      (representationVariable_hasType base sourceFirst sourceMember)
      (openedRepresentationBody_hasType firstAdapter memberBridge)
  rw [Ty.weaken, existsTy_rename, representationAtBinder_eq]
  exact result

/-- The dependent representation coercion assembled from the first and
member adapters.  No representation-level coercion is accepted as input. -/
noncomputable def representationCoercion
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    {targetMember : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (memberBridge : DependentMemberAdapter base sourceFirst sourceMember
      targetFirst targetMember) : Co sig :=
  .adapter (Pair.Proper.representation sourceFirst sourceMember).existsTy
    (representationBody firstAdapter memberBridge)

noncomputable def representationCoercion_hasType
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    {targetMember : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (memberBridge : DependentMemberAdapter base sourceFirst sourceMember
      targetFirst targetMember) :
    Co.HasType base (representationCoercion firstAdapter memberBridge)
      (Pair.Proper.representation sourceFirst sourceMember).existsTy
      (Pair.Proper.representation targetFirst targetMember).existsTy :=
  .adapter (representationBody_hasType firstAdapter memberBridge)

/-- Lift the constructed dependent representation coercion to the complete
stable outer pair packages. -/
noncomputable def adapter
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceMember : ValuePlan sourceFirst.scope}
    {targetMember : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (memberBridge : DependentMemberAdapter base sourceFirst sourceMember
      targetFirst targetMember) :
    StableIdentity.Adapter base
      (Pair.Proper.plan sourceFirst sourceMember)
      (Pair.Proper.plan targetFirst targetMember) :=
  PairStableAdapter.adapter base
    (Pair.Proper.representation sourceFirst sourceMember)
    (Pair.Proper.representation targetFirst targetMember)
    (representationCoercion firstAdapter memberBridge)
    (representationCoercion_hasType firstAdapter memberBridge)

end PairRepresentationBridgeConstruction

end LambdaPToFCo.Full
