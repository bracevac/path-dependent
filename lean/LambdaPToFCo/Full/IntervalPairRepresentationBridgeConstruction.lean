import LambdaPToFCo.Full.PairStableAdapter

/-!
# Construction of dependent interval-pair representation bridges

This target-only leaf opens the source interval representation before it asks
for endpoint adapters.  Consequently the selected representation is a bound
type variable in the adapter context, not a caller-selected index.  The
source pair's stored lower/upper evidence is composed with those adapters and
the target representation wrapper is constructed internally.

This is deliberately not yet a compiler for the source `Tau.Sub.pair` rule.
The source layer must use its exact paired-instantiation evidence to construct
`ScopedEndpointAdapters` in the common opened context.  This leaf does not
accept a decorative source witness, a fixed selected representation, or a
prebuilt representation coercion.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

namespace IntervalPairRepresentationBridgeConstruction

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

def sourceEndpointAtBinder (first : ValuePlan sig)
    (endpoint : ValuePlan first.scope) :
    ValuePlan (sourceFirstAtBinder first).scope :=
  Pair.Proper.renameMember first endpoint (Rename.weaken .var)

def sourceLowerAtBinder (first : ValuePlan sig)
    (lower : ValuePlan first.scope) :=
  sourceEndpointAtBinder first lower

def sourceUpperAtBinder (first : ValuePlan sig)
    (upper : ValuePlan first.scope) :=
  sourceEndpointAtBinder first upper

def sourceMemberAtBinder (first : ValuePlan sig)
    (lower upper : ValuePlan first.scope) :
    Telescope (sourceFirstAtBinder first).scope :=
  Pair.Interval.memberTelescope
    (sourceLowerAtBinder first lower).inputTy
    (sourceUpperAtBinder first upper).inputTy

def representationAtBinder (first : ValuePlan sig)
    (lower upper : ValuePlan first.scope) : Telescope (sig ,, .var) :=
  Pair.Interval.representation (sourceFirstAtBinder first)
    (sourceLowerAtBinder first lower).inputTy
    (sourceUpperAtBinder first upper).inputTy

theorem representationAtBinder_eq (first : ValuePlan sig)
    (lower upper : ValuePlan first.scope) :
    (Pair.Interval.representation first lower.inputTy upper.inputTy).rename
        (Rename.weaken .var) =
      representationAtBinder first lower upper := by
  rw [Pair.Interval.representation_rename]
  unfold representationAtBinder sourceFirstAtBinder sourceLowerAtBinder sourceUpperAtBinder
    sourceEndpointAtBinder Pair.Proper.renameMember
  rw [ValuePlan.inputTy_rename, ValuePlan.inputTy_rename]

def sourceOpening (first : ValuePlan sig)
    (lower upper : ValuePlan first.scope) :
    Rename (sig ,, .var) (sourceMemberAtBinder first lower upper).scope :=
  (sourceFirstAtBinder first).telescope.weaken.comp
    (sourceMemberAtBinder first lower upper).weaken

def sourceOpenedContext (base : Ctx sig)
    (first : ValuePlan sig) (lower upper : ValuePlan first.scope) :
    Ctx (sourceMemberAtBinder first lower upper).scope :=
  (sourceMemberAtBinder first lower upper).context
    ((sourceFirstAtBinder first).context
      (base.bindVar
        (Pair.Interval.representation first lower.inputTy
          upper.inputTy).existsTy))

noncomputable def sourceFirstInterface (base : Ctx sig)
    (first : ValuePlan sig) (lower upper : ValuePlan first.scope) :
    ValueInterface (sourceOpenedContext base first lower upper) :=
  (ValueInterface.ofArguments
    ((sourceFirstAtBinder first).rename
      (sourceFirstAtBinder first).telescope.weaken)
    (Telescope.Args.identity (sourceFirstAtBinder first).telescope
      (base.bindVar
        (Pair.Interval.representation first lower.inputTy
          upper.inputTy).existsTy))).rename
        (sourceMemberAtBinder first lower upper).weaken
        ((sourceMemberAtBinder first lower upper).weaken_typed
          ((sourceFirstAtBinder first).context
            (base.bindVar
              (Pair.Interval.representation first lower.inputTy
                upper.inputTy).existsTy)))

def sourceEndpointAtMember
    (first : ValuePlan sig) (lower upper endpoint : ValuePlan first.scope) :
    ValuePlan (sourceMemberAtBinder first lower upper).scope :=
  (sourceEndpointAtBinder first endpoint).rename
    (sourceMemberAtBinder first lower upper).weaken

def sourceLowerAtMember (first : ValuePlan sig)
    (lower upper : ValuePlan first.scope) :=
  sourceEndpointAtMember first lower upper lower

def sourceUpperAtMember (first : ValuePlan sig)
    (lower upper : ValuePlan first.scope) :=
  sourceEndpointAtMember first lower upper upper

theorem sourceLowerAtMember_inputTy (first : ValuePlan sig)
    (lower upper : ValuePlan first.scope) :
    (sourceLowerAtMember first lower upper).inputTy =
      Pair.Interval.lowerTy
        (sourceLowerAtBinder first lower).inputTy
        (sourceUpperAtBinder first upper).inputTy := by
  unfold sourceLowerAtMember sourceEndpointAtMember sourceLowerAtBinder
    sourceUpperAtBinder sourceMemberAtBinder Pair.Interval.lowerTy
    Pair.Interval.memberTelescope Pair.Interval.memberTail
  rw [← ValuePlan.inputTy_rename]
  simp only [Telescope.weaken, Ty.weaken, Ty.rename_comp,
    Rename.comp_assoc]
  apply congrArg (fun mapping =>
    (sourceEndpointAtBinder first lower).inputTy.rename mapping)
  apply Rename.funext
  intro kind index
  rfl

theorem sourceUpperAtMember_inputTy (first : ValuePlan sig)
    (lower upper : ValuePlan first.scope) :
    (sourceUpperAtMember first lower upper).inputTy =
      Pair.Interval.upperTy
        (sourceLowerAtBinder first lower).inputTy
        (sourceUpperAtBinder first upper).inputTy := by
  unfold sourceUpperAtMember sourceEndpointAtMember sourceLowerAtBinder
    sourceUpperAtBinder sourceMemberAtBinder Pair.Interval.upperTy
    Pair.Interval.memberTelescope Pair.Interval.memberTail
  rw [← ValuePlan.inputTy_rename]
  simp only [Telescope.weaken, Ty.weaken, Ty.rename_comp,
    Rename.comp_assoc]
  apply congrArg (fun mapping =>
    (sourceEndpointAtBinder first upper).inputTy.rename mapping)
  apply Rename.funext
  intro kind index
  rfl

def targetFirstAtSource (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :
    ValuePlan (sourceMemberAtBinder sourceFirst sourceLower sourceUpper).scope :=
  (targetFirst.rename (Rename.weaken .var)).rename
    (sourceOpening sourceFirst sourceLower sourceUpper)

def targetEndpointAtSource
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig)
    (targetEndpoint : ValuePlan targetFirst.scope) :
    ValuePlan
      (targetFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).scope :=
  Pair.Proper.renameMember
    (targetFirst.rename (Rename.weaken .var))
    (Pair.Proper.renameMember targetFirst targetEndpoint (Rename.weaken .var))
    (sourceOpening sourceFirst sourceLower sourceUpper)

def targetLowerAtSource
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig)
    (targetLower : ValuePlan targetFirst.scope) :=
  targetEndpointAtSource sourceFirst sourceLower sourceUpper targetFirst
    targetLower

def targetUpperAtSource
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig)
    (targetUpper : ValuePlan targetFirst.scope) :=
  targetEndpointAtSource sourceFirst sourceLower sourceUpper targetFirst
    targetUpper

def targetFirstOpenedContext (base : Ctx sig)
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :
    Ctx (targetFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).scope :=
  (targetFirstAtSource sourceFirst sourceLower sourceUpper
    targetFirst).context
      (sourceOpenedContext base sourceFirst sourceLower sourceUpper)

def sourceEndpointAtTargetFirst
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper endpoint : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :
    ValuePlan
      (targetFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).scope :=
  (sourceEndpointAtMember sourceFirst sourceLower sourceUpper endpoint).rename
    (targetFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).telescope.weaken

def sourceLowerAtTargetFirst
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :=
  sourceEndpointAtTargetFirst sourceFirst sourceLower sourceUpper sourceLower
    targetFirst

def sourceUpperAtTargetFirst
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :=
  sourceEndpointAtTargetFirst sourceFirst sourceLower sourceUpper sourceUpper
    targetFirst

/-- The endpoints are supplied only after the source interval representation
has been opened.  Its witness representation is therefore abstract in this
record's context. -/
structure ScopedEndpointAdapters (base : Ctx sig)
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig)
    (targetLower targetUpper : ValuePlan targetFirst.scope) : Type where
  lower : StableIdentity.Adapter
    (targetFirstOpenedContext base sourceFirst sourceLower sourceUpper
      targetFirst)
    (targetLowerAtSource sourceFirst sourceLower sourceUpper targetFirst
      targetLower)
    (sourceLowerAtTargetFirst sourceFirst sourceLower sourceUpper targetFirst)
  upper : StableIdentity.Adapter
    (targetFirstOpenedContext base sourceFirst sourceLower sourceUpper
      targetFirst)
    (sourceUpperAtTargetFirst sourceFirst sourceLower sourceUpper targetFirst)
    (targetUpperAtSource sourceFirst sourceLower sourceUpper targetFirst
      targetUpper)

noncomputable def firstCoercionAtSource
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    (adapter : StableIdentity.Adapter base sourceFirst targetFirst) :
    Co (sourceMemberAtBinder sourceFirst sourceLower sourceUpper).scope :=
  ((adapter.coercion.weaken .var).rename
    (sourceFirstAtBinder sourceFirst).telescope.weaken).rename
      (sourceMemberAtBinder sourceFirst sourceLower sourceUpper).weaken

noncomputable def firstCoercionAtSource_hasType
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    (adapter : StableIdentity.Adapter base sourceFirst targetFirst) :
    Co.HasType (sourceOpenedContext base sourceFirst sourceLower sourceUpper)
      (firstCoercionAtSource
        (sourceLower := sourceLower) (sourceUpper := sourceUpper) adapter)
      (sourceFirstInterface base sourceFirst sourceLower sourceUpper).plan.inputTy
      (targetFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).inputTy := by
  have outer := adapter.coercion_hasType.weaken
    (.var (Pair.Interval.representation sourceFirst sourceLower.inputTy
      sourceUpper.inputTy).existsTy)
  have underFirst := weakenCo_hasType
    (sourceFirstAtBinder sourceFirst).telescope outer
  have underMember := weakenCo_hasType
    (sourceMemberAtBinder sourceFirst sourceLower sourceUpper) underFirst
  have sourceRawEq :
      ((sourceFirst.inputTy.weaken .var).rename
          (sourceFirstAtBinder sourceFirst).telescope.weaken).rename
            (sourceMemberAtBinder sourceFirst sourceLower sourceUpper).weaken =
        (sourceFirstInterface base sourceFirst sourceLower
          sourceUpper).plan.inputTy := by
    unfold Ty.weaken sourceFirstAtBinder sourceFirstInterface
    rw [ValuePlan.inputTy_rename, ValuePlan.inputTy_rename,
      ValuePlan.inputTy_rename]
    simp only [ValueInterface.rename, ofArguments_plan]
    rfl
  have targetRawEq :
      ((targetFirst.inputTy.weaken .var).rename
          (sourceFirstAtBinder sourceFirst).telescope.weaken).rename
            (sourceMemberAtBinder sourceFirst sourceLower sourceUpper).weaken =
        (targetFirstAtSource sourceFirst sourceLower sourceUpper
          targetFirst).inputTy := by
    unfold Ty.weaken targetFirstAtSource sourceOpening
    rw [ValuePlan.inputTy_rename, ValuePlan.inputTy_rename,
      ValuePlan.inputTy_rename, ValuePlan.rename_comp]
  exact sourceRawEq ▸ targetRawEq ▸ underMember

noncomputable def adaptedFirstPackage
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    (adapter : StableIdentity.Adapter base sourceFirst targetFirst) :
    Exp (sourceMemberAtBinder sourceFirst sourceLower sourceUpper).scope :=
  .cast
    (sourceFirstInterface base sourceFirst sourceLower sourceUpper).package
    (firstCoercionAtSource
      (sourceLower := sourceLower) (sourceUpper := sourceUpper) adapter)

noncomputable def adaptedFirstPackage_hasType
    {base : Ctx sig} {sourceFirst targetFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    (adapter : StableIdentity.Adapter base sourceFirst targetFirst) :
    Exp.HasType (sourceOpenedContext base sourceFirst sourceLower sourceUpper)
      (adaptedFirstPackage
        (sourceLower := sourceLower) (sourceUpper := sourceUpper) adapter)
      (targetFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).inputTy :=
  .cast
    (sourceFirstInterface base sourceFirst sourceLower sourceUpper).package_hasType
    (firstCoercionAtSource_hasType
      (sourceLower := sourceLower) (sourceUpper := sourceUpper) adapter)

def sourceSelectedAtTargetFirst
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :
    ValuePlan
      (targetFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).scope :=
  (Pair.Interval.selectedPlan
    (sourceLowerAtBinder sourceFirst sourceLower).inputTy
    (sourceUpperAtBinder sourceFirst sourceUpper).inputTy).rename
      (targetFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).telescope.weaken

def sourceWitnessAtTargetFirst
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :
    Ty (targetFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).scope :=
  (Pair.Interval.witnessRepresentation
    (sourceLowerAtBinder sourceFirst sourceLower).inputTy
    (sourceUpperAtBinder sourceFirst sourceUpper).inputTy).rename
      (targetFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).telescope.weaken

theorem sourceSelectedAtTargetFirst_eq
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :
    sourceSelectedAtTargetFirst sourceFirst sourceLower sourceUpper
        targetFirst =
      Selection.plan
        (sourceWitnessAtTargetFirst sourceFirst sourceLower sourceUpper
          targetFirst) := by
  unfold sourceSelectedAtTargetFirst sourceWitnessAtTargetFirst
    Pair.Interval.selectedPlan
  rw [Selection.plan_rename]

noncomputable def storedLowerCoercionAtTargetFirst
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :
    Co (targetFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).scope :=
  (Pair.Interval.lowerAdapter
    (sourceLowerAtBinder sourceFirst sourceLower).inputTy
    (sourceUpperAtBinder sourceFirst sourceUpper).inputTy).rename
      (targetFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).telescope.weaken

noncomputable def storedLowerCoercionAtTargetFirst_hasType
    (base : Ctx sig)
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :
    Co.HasType
      (targetFirstOpenedContext base sourceFirst sourceLower sourceUpper
        targetFirst)
      (storedLowerCoercionAtTargetFirst sourceFirst sourceLower sourceUpper
        targetFirst)
      (sourceLowerAtTargetFirst sourceFirst sourceLower sourceUpper
        targetFirst).inputTy
      (sourceSelectedAtTargetFirst sourceFirst sourceLower sourceUpper
        targetFirst).inputTy := by
  have typed :=
    (Pair.Interval.lowerAdapter_hasType
      ((sourceFirstAtBinder sourceFirst).context
        (base.bindVar
          (Pair.Interval.representation sourceFirst sourceLower.inputTy
            sourceUpper.inputTy).existsTy))
      (sourceLowerAtBinder sourceFirst sourceLower).inputTy
      (sourceUpperAtBinder sourceFirst sourceUpper).inputTy).rename
        ((targetFirstAtSource sourceFirst sourceLower sourceUpper
          targetFirst).telescope.weaken_typed
            (sourceOpenedContext base sourceFirst sourceLower sourceUpper))
  have lowerEq :
      (sourceLowerAtTargetFirst sourceFirst sourceLower sourceUpper
        targetFirst).inputTy =
      (Pair.Interval.lowerTy
        (sourceLowerAtBinder sourceFirst sourceLower).inputTy
        (sourceUpperAtBinder sourceFirst sourceUpper).inputTy).rename
          (targetFirstAtSource sourceFirst sourceLower sourceUpper
            targetFirst).telescope.weaken := by
    unfold sourceLowerAtTargetFirst sourceEndpointAtTargetFirst
    rw [← ValuePlan.inputTy_rename]
    change (sourceLowerAtMember sourceFirst sourceLower sourceUpper).inputTy.rename _ = _
    rw [sourceLowerAtMember_inputTy]
    rfl
  have selectedEq :
      (sourceSelectedAtTargetFirst sourceFirst sourceLower sourceUpper
        targetFirst).inputTy =
      (Pair.Interval.selectedTy
        (sourceLowerAtBinder sourceFirst sourceLower).inputTy
        (sourceUpperAtBinder sourceFirst sourceUpper).inputTy).rename
          (targetFirstAtSource sourceFirst sourceLower sourceUpper
            targetFirst).telescope.weaken := by
    unfold sourceSelectedAtTargetFirst
    rw [← ValuePlan.inputTy_rename,
      Pair.Interval.selectedPlan_inputTy]
    rfl
  simpa only [targetFirstOpenedContext, ValuePlan.context, lowerEq,
    selectedEq] using typed

noncomputable def storedUpperCoercionAtTargetFirst
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :
    Co (targetFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).scope :=
  (Pair.Interval.upperAdapter
    (sourceLowerAtBinder sourceFirst sourceLower).inputTy
    (sourceUpperAtBinder sourceFirst sourceUpper).inputTy).rename
      (targetFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).telescope.weaken

noncomputable def storedUpperCoercionAtTargetFirst_hasType
    (base : Ctx sig)
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :
    Co.HasType
      (targetFirstOpenedContext base sourceFirst sourceLower sourceUpper
        targetFirst)
      (storedUpperCoercionAtTargetFirst sourceFirst sourceLower sourceUpper
        targetFirst)
      (sourceSelectedAtTargetFirst sourceFirst sourceLower sourceUpper
        targetFirst).inputTy
      (sourceUpperAtTargetFirst sourceFirst sourceLower sourceUpper
        targetFirst).inputTy := by
  have typed :=
    (Pair.Interval.upperAdapter_hasType
      ((sourceFirstAtBinder sourceFirst).context
        (base.bindVar
          (Pair.Interval.representation sourceFirst sourceLower.inputTy
            sourceUpper.inputTy).existsTy))
      (sourceLowerAtBinder sourceFirst sourceLower).inputTy
      (sourceUpperAtBinder sourceFirst sourceUpper).inputTy).rename
        ((targetFirstAtSource sourceFirst sourceLower sourceUpper
          targetFirst).telescope.weaken_typed
            (sourceOpenedContext base sourceFirst sourceLower sourceUpper))
  have selectedEq :
      (sourceSelectedAtTargetFirst sourceFirst sourceLower sourceUpper
        targetFirst).inputTy =
      (Pair.Interval.selectedTy
        (sourceLowerAtBinder sourceFirst sourceLower).inputTy
        (sourceUpperAtBinder sourceFirst sourceUpper).inputTy).rename
          (targetFirstAtSource sourceFirst sourceLower sourceUpper
            targetFirst).telescope.weaken := by
    unfold sourceSelectedAtTargetFirst
    rw [← ValuePlan.inputTy_rename,
      Pair.Interval.selectedPlan_inputTy]
    rfl
  have upperEq :
      (sourceUpperAtTargetFirst sourceFirst sourceLower sourceUpper
        targetFirst).inputTy =
      (Pair.Interval.upperTy
        (sourceLowerAtBinder sourceFirst sourceLower).inputTy
        (sourceUpperAtBinder sourceFirst sourceUpper).inputTy).rename
          (targetFirstAtSource sourceFirst sourceLower sourceUpper
            targetFirst).telescope.weaken := by
    unfold sourceUpperAtTargetFirst sourceEndpointAtTargetFirst
    rw [← ValuePlan.inputTy_rename]
    change (sourceUpperAtMember sourceFirst sourceLower sourceUpper).inputTy.rename _ = _
    rw [sourceUpperAtMember_inputTy]
    rfl
  simpa only [targetFirstOpenedContext, ValuePlan.context, selectedEq,
    upperEq] using typed

noncomputable def adaptedLowerCoercion
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    Co (targetFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).scope :=
  .trans bridges.lower.coercion
    (storedLowerCoercionAtTargetFirst sourceFirst sourceLower sourceUpper
      targetFirst)

noncomputable def adaptedLowerCoercion_hasType
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    Co.HasType
      (targetFirstOpenedContext base sourceFirst sourceLower sourceUpper
        targetFirst)
      (adaptedLowerCoercion bridges)
      (targetLowerAtSource sourceFirst sourceLower sourceUpper targetFirst
        targetLower).inputTy
      (sourceSelectedAtTargetFirst sourceFirst sourceLower sourceUpper
        targetFirst).inputTy :=
  .trans bridges.lower.coercion_hasType
    (storedLowerCoercionAtTargetFirst_hasType base sourceFirst sourceLower
      sourceUpper targetFirst)

noncomputable def adaptedUpperCoercion
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    Co (targetFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).scope :=
  .trans
    (storedUpperCoercionAtTargetFirst sourceFirst sourceLower sourceUpper
      targetFirst)
    bridges.upper.coercion

noncomputable def adaptedUpperCoercion_hasType
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    Co.HasType
      (targetFirstOpenedContext base sourceFirst sourceLower sourceUpper
        targetFirst)
      (adaptedUpperCoercion bridges)
      (sourceSelectedAtTargetFirst sourceFirst sourceLower sourceUpper
        targetFirst).inputTy
      (targetUpperAtSource sourceFirst sourceLower sourceUpper targetFirst
        targetUpper).inputTy :=
  .trans
    (storedUpperCoercionAtTargetFirst_hasType base sourceFirst sourceLower
      sourceUpper targetFirst)
    bridges.upper.coercion_hasType

def targetMemberAtSource
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig)
    (targetLower targetUpper : ValuePlan targetFirst.scope) :
    Telescope (targetFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).scope :=
  Pair.Interval.memberTelescope
    (targetLowerAtSource sourceFirst sourceLower sourceUpper targetFirst
      targetLower).inputTy
    (targetUpperAtSource sourceFirst sourceLower sourceUpper targetFirst
      targetUpper).inputTy

noncomputable def targetMemberArguments
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    Telescope.Args
      (targetFirstOpenedContext base sourceFirst sourceLower sourceUpper
        targetFirst)
      (targetMemberAtSource sourceFirst sourceLower sourceUpper targetFirst
        targetLower targetUpper) :=
  Pair.Interval.memberArgumentsWithAdapters
    (targetFirstOpenedContext base sourceFirst sourceLower sourceUpper
      targetFirst)
    (targetLowerAtSource sourceFirst sourceLower sourceUpper targetFirst
      targetLower).inputTy
    (targetUpperAtSource sourceFirst sourceLower sourceUpper targetFirst
      targetUpper).inputTy
    (sourceWitnessAtTargetFirst sourceFirst sourceLower sourceUpper targetFirst)
    (adaptedLowerCoercion bridges)
    (by
      rw [← sourceSelectedAtTargetFirst_eq]
      exact adaptedLowerCoercion_hasType bridges)
    (adaptedUpperCoercion bridges)
    (by
      rw [← sourceSelectedAtTargetFirst_eq]
      exact adaptedUpperCoercion_hasType bridges)

noncomputable def targetMemberPackage
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    Exp (targetFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).scope :=
  (targetMemberAtSource sourceFirst sourceLower sourceUpper targetFirst
    targetLower targetUpper).pack (targetMemberArguments bridges)

noncomputable def targetMemberPackage_hasType
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    Exp.HasType
      (targetFirstOpenedContext base sourceFirst sourceLower sourceUpper
        targetFirst)
      (targetMemberPackage bridges)
      (targetMemberAtSource sourceFirst sourceLower sourceUpper targetFirst
        targetLower targetUpper).existsTy :=
  (targetMemberAtSource sourceFirst sourceLower sourceUpper targetFirst
    targetLower targetUpper).pack_hasType (targetMemberArguments bridges)

def targetRepresentationAtSource
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig)
    (targetLower targetUpper : ValuePlan targetFirst.scope) :
    Telescope (sourceMemberAtBinder sourceFirst sourceLower sourceUpper).scope :=
  Pair.Interval.representation
    (targetFirstAtSource sourceFirst sourceLower sourceUpper targetFirst)
    (targetLowerAtSource sourceFirst sourceLower sourceUpper targetFirst
      targetLower).inputTy
    (targetUpperAtSource sourceFirst sourceLower sourceUpper targetFirst
      targetUpper).inputTy

theorem targetRepresentationAtSource_eq
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig)
    (targetLower targetUpper : ValuePlan targetFirst.scope) :
    (representationAtBinder targetFirst targetLower targetUpper).rename
        (sourceOpening sourceFirst sourceLower sourceUpper) =
      targetRepresentationAtSource sourceFirst sourceLower sourceUpper
        targetFirst targetLower targetUpper := by
  unfold representationAtBinder
  rw [Pair.Interval.representation_rename]
  unfold targetRepresentationAtSource
    targetLowerAtSource targetUpperAtSource targetEndpointAtSource
    targetFirstAtSource sourceFirstAtBinder sourceLowerAtBinder
    sourceUpperAtBinder sourceEndpointAtBinder Pair.Proper.renameMember
  rw [ValuePlan.inputTy_rename, ValuePlan.inputTy_rename]

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
    (suffix : Telescope first.scope) : Exp suffix.scope :=
  toSuffixExp first.telescope suffix
    (((first.telescope.append suffix).rename
      (first.telescope.append suffix).weaken).pack
      (Telescope.Args.identity (first.telescope.append suffix) base))

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
    (suffix : Telescope first.scope) :
    Exp.HasType (suffix.context (first.context base))
      (nestedRepresentationPackage base first suffix)
      ((((first.telescope.append suffix).existsTy.rename
        first.telescope.weaken).rename suffix.weaken)) := by
  have packed := Telescope.pack_hasType
    (Telescope.Args.identity (first.telescope.append suffix) base)
  have transported := toSuffixExp_hasType first.telescope suffix packed
  rw [← existsTy_rename] at transported
  change Exp.HasType _ _
    (toSuffixTy first.telescope suffix
      ((first.telescope.append suffix).existsTy.rename
        (first.telescope.append suffix).weaken)) at transported
  rw [toSuffixTy_weaken] at transported
  exact transported

noncomputable def eliminateTargetMember
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    Exp (targetFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).scope :=
  let first := targetFirstAtSource sourceFirst sourceLower sourceUpper
    targetFirst
  let suffix := targetMemberAtSource sourceFirst sourceLower sourceUpper
    targetFirst targetLower targetUpper
  let representation := targetRepresentationAtSource sourceFirst sourceLower
    sourceUpper targetFirst targetLower targetUpper
  suffix.unpack (targetMemberPackage bridges)
    (representation.existsTy.rename first.telescope.weaken)
    (nestedRepresentationPackage
      (sourceOpenedContext base sourceFirst sourceLower sourceUpper)
      first suffix)

noncomputable def eliminateTargetMember_hasType
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    Exp.HasType
      (targetFirstOpenedContext base sourceFirst sourceLower sourceUpper
        targetFirst)
      (eliminateTargetMember bridges)
      ((targetRepresentationAtSource sourceFirst sourceLower sourceUpper
        targetFirst targetLower targetUpper).existsTy.rename
          (targetFirstAtSource sourceFirst sourceLower sourceUpper
            targetFirst).telescope.weaken) := by
  exact (targetMemberAtSource sourceFirst sourceLower sourceUpper targetFirst
    targetLower targetUpper).unpack_hasType
      (targetMemberPackage_hasType bridges)
      (nestedRepresentationPackage_hasType
        (sourceOpenedContext base sourceFirst sourceLower sourceUpper)
        (targetFirstAtSource sourceFirst sourceLower sourceUpper targetFirst)
        (targetMemberAtSource sourceFirst sourceLower sourceUpper targetFirst
          targetLower targetUpper))

noncomputable def eliminateAdaptedFirst
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    Exp (sourceMemberAtBinder sourceFirst sourceLower sourceUpper).scope :=
  (targetFirstAtSource sourceFirst sourceLower sourceUpper targetFirst).unpack
    (adaptedFirstPackage
      (sourceLower := sourceLower) (sourceUpper := sourceUpper) firstAdapter)
    (targetRepresentationAtSource sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper).existsTy
    (eliminateTargetMember bridges)

noncomputable def eliminateAdaptedFirst_hasType
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    Exp.HasType (sourceOpenedContext base sourceFirst sourceLower sourceUpper)
      (eliminateAdaptedFirst firstAdapter bridges)
      (targetRepresentationAtSource sourceFirst sourceLower sourceUpper
        targetFirst targetLower targetUpper).existsTy :=
  (targetFirstAtSource sourceFirst sourceLower sourceUpper targetFirst).unpack_hasType
    (adaptedFirstPackage_hasType
      (sourceLower := sourceLower) (sourceUpper := sourceUpper) firstAdapter)
    (eliminateTargetMember_hasType bridges)

noncomputable def representationVariable_hasType
    (base : Ctx sig) (first : ValuePlan sig)
    (lower upper : ValuePlan first.scope) :
    Exp.HasType
      (base.bindVar
        (Pair.Interval.representation first lower.inputTy
          upper.inputTy).existsTy)
      (.var .here) (representationAtBinder first lower upper).existsTy := by
  have variableTyping : Exp.HasType
      (base.bindVar
        (Pair.Interval.representation first lower.inputTy
          upper.inputTy).existsTy)
      (.var .here)
      ((Pair.Interval.representation first lower.inputTy
        upper.inputTy).existsTy.weaken .var) :=
    .var Ctx.Lookup.here
  rw [Ty.weaken, existsTy_rename,
    representationAtBinder_eq] at variableTyping
  exact variableTyping

noncomputable def openedRepresentationBody
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    Exp (representationAtBinder sourceFirst sourceLower sourceUpper).scope :=
  Pair.fromSuffixExp (sourceFirstAtBinder sourceFirst).telescope
    (sourceMemberAtBinder sourceFirst sourceLower sourceUpper)
    (eliminateAdaptedFirst firstAdapter bridges)

noncomputable def openedRepresentationBody_hasType
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    Exp.HasType
      ((representationAtBinder sourceFirst sourceLower sourceUpper).context
        (base.bindVar
          (Pair.Interval.representation sourceFirst sourceLower.inputTy
            sourceUpper.inputTy).existsTy))
      (openedRepresentationBody firstAdapter bridges)
      ((representationAtBinder targetFirst targetLower targetUpper).existsTy.rename
        (representationAtBinder sourceFirst sourceLower sourceUpper).weaken) := by
  have inner := eliminateAdaptedFirst_hasType firstAdapter bridges
  have targetEq :
      (targetRepresentationAtSource sourceFirst sourceLower sourceUpper
        targetFirst targetLower targetUpper).existsTy =
      (((representationAtBinder targetFirst targetLower
          targetUpper).existsTy.rename
        (sourceFirstAtBinder sourceFirst).telescope.weaken).rename
          (sourceMemberAtBinder sourceFirst sourceLower
            sourceUpper).weaken) := by
    rw [← targetRepresentationAtSource_eq]
    rw [← existsTy_rename]
    unfold sourceOpening
    rw [Ty.rename_comp]
  rw [targetEq] at inner
  have transported := PairInterface.fromSuffixExp_hasType
    (sourceFirstAtBinder sourceFirst).telescope
    (sourceMemberAtBinder sourceFirst sourceLower sourceUpper) inner
  have typeEq := PairInterface.fromSuffixTy_weaken
    (sourceFirstAtBinder sourceFirst).telescope
    (sourceMemberAtBinder sourceFirst sourceLower sourceUpper)
    (representationAtBinder targetFirst targetLower targetUpper).existsTy
  exact typeEq ▸ transported

noncomputable def representationBody
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) : Exp (sig ,, .var) :=
  (representationAtBinder sourceFirst sourceLower sourceUpper).unpack
    (.var .here)
    (representationAtBinder targetFirst targetLower targetUpper).existsTy
    (openedRepresentationBody firstAdapter bridges)

noncomputable def representationBody_hasType
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    Exp.HasType
      (base.bindVar
        (Pair.Interval.representation sourceFirst sourceLower.inputTy
          sourceUpper.inputTy).existsTy)
      (representationBody firstAdapter bridges)
      ((Pair.Interval.representation targetFirst targetLower.inputTy
        targetUpper.inputTy).existsTy.weaken .var) := by
  have result :=
    (representationAtBinder sourceFirst sourceLower sourceUpper).unpack_hasType
      (representationVariable_hasType base sourceFirst sourceLower sourceUpper)
      (openedRepresentationBody_hasType firstAdapter bridges)
  rw [Ty.weaken, existsTy_rename, representationAtBinder_eq]
  exact result

/-- Representation covariance assembled internally.  The endpoint bridge is
scoped under the source interval's hidden witness and cannot select a witness
representation at the call site. -/
noncomputable def representationCoercion
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) : Co sig :=
  .adapter
    (Pair.Interval.representation sourceFirst sourceLower.inputTy
      sourceUpper.inputTy).existsTy
    (representationBody firstAdapter bridges)

noncomputable def representationCoercion_hasType
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    Co.HasType base (representationCoercion firstAdapter bridges)
      (Pair.Interval.representation sourceFirst sourceLower.inputTy
        sourceUpper.inputTy).existsTy
      (Pair.Interval.representation targetFirst targetLower.inputTy
        targetUpper.inputTy).existsTy :=
  .adapter (representationBody_hasType firstAdapter bridges)

/-- Lift the rank-2 interval representation coercion to complete stable pair
packages. -/
noncomputable def adapter
    {base : Ctx sig}
    {sourceFirst : ValuePlan sig}
    {sourceLower sourceUpper : ValuePlan sourceFirst.scope}
    {targetFirst : ValuePlan sig}
    {targetLower targetUpper : ValuePlan targetFirst.scope}
    (firstAdapter : StableIdentity.Adapter base sourceFirst targetFirst)
    (bridges : ScopedEndpointAdapters base sourceFirst sourceLower sourceUpper
      targetFirst targetLower targetUpper) :
    StableIdentity.Adapter base
      (Pair.Interval.plan sourceFirst sourceLower.inputTy sourceUpper.inputTy)
      (Pair.Interval.plan targetFirst targetLower.inputTy targetUpper.inputTy) :=
  PairStableAdapter.adapter base
    (Pair.Interval.representation sourceFirst sourceLower.inputTy
      sourceUpper.inputTy)
    (Pair.Interval.representation targetFirst targetLower.inputTy
      targetUpper.inputTy)
    (representationCoercion firstAdapter bridges)
    (representationCoercion_hasType firstAdapter bridges)

end IntervalPairRepresentationBridgeConstruction

end LambdaPToFCo.Full
