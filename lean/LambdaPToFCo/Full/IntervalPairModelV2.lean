import LambdaPToFCo.Full.StableIdentitySubstitution
import LambdaPToFCo.Full.PairModel
import LambdaPToFCo.Full.PathPackageZipper

/-!
# Full-plan interval-pair target model (V2)

The original `Pair.Interval` hides a raw witness `X` and stores package
coercions through `Selection.plan X`.  A general reverse stable adapter from
that selection plan to an arbitrary endpoint plan does not exist.  This
independent V2 keeps all existing APIs intact and changes only the new Full
target representation:

* the hidden target type is the selected plan's complete `inputTy`;
* stored coercions map complete lower/selected/upper packages; and
* compiler-side `Descriptor` evidence retains the full selected `ValuePlan`.

Consequently exact `[T,T]` selects the endpoint plan itself and uses identity
stable adapters in both directions.  No `SystemFCoExt` primitive is added or
changed.  Package provenance is construction-directed: `ExactResult.package`
chooses its hidden type and both coercions only from `ExactResult.descriptor`.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

namespace Pair.IntervalV2

/-- Hidden selected package type and complete package coercions. -/
def memberTail (lower upper : Ty sig) : Telescope (sig ,, .tvar) :=
  .cvar (lower.weaken .tvar) (.tvar .here)
    (.cvar ((.tvar .here : Ty (sig ,, .tvar)).weaken .cvar)
      ((upper.weaken .tvar).weaken .cvar) .nil)

def memberTelescope (lower upper : Ty sig) : Telescope sig :=
  .tvar (memberTail lower upper)

def openedMember (lower upper selectedInput : Ty sig) : Telescope sig :=
  .cvar lower selectedInput
    (.cvar (selectedInput.weaken .cvar) (upper.weaken .cvar) .nil)

theorem memberTail_open (lower upper selectedInput : Ty sig) :
    (memberTail lower upper).subst (Subst.openTVar selectedInput) =
      openedMember lower upper selectedInput := by
  unfold memberTail openedMember
  simp only [Telescope.subst]
  rw [lower.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openTVar selectedInput)]
  change Telescope.cvar lower selectedInput
    (Telescope.cvar
      (((.tvar .here : Ty (_ ,, .tvar)).weaken .cvar).subst
        ((Subst.openTVar selectedInput).lift .cvar))
      (((upper.weaken .tvar).weaken .cvar).subst
        ((Subst.openTVar selectedInput).lift .cvar)) .nil) = _
  rw [← Ty.weaken_subst_comm_base]
  rw [← Ty.weaken_subst_comm_base]
  rw [upper.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openTVar selectedInput)]
  rfl

theorem openedTail_open (upper selectedInput : Ty sig)
    (evidence : Co sig) :
    (Telescope.cvar (selectedInput.weaken .cvar) (upper.weaken .cvar)
      .nil).subst (Subst.openCVar evidence) =
      Telescope.cvar selectedInput upper .nil := by
  simp only [Telescope.subst]
  rw [selectedInput.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openCVar evidence)]
  rw [upper.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openCVar evidence)]

theorem memberTelescope_rename (lower upper : Ty source)
    (mapping : Rename source target) :
    (memberTelescope lower upper).rename mapping =
      memberTelescope (lower.rename mapping) (upper.rename mapping) := by
  unfold memberTelescope memberTail
  simp only [Telescope.rename]
  rw [Ty.weaken_rename_comm, Ty.weaken_rename_comm,
    Ty.weaken_rename_comm, Ty.weaken_rename_comm]
  simp only [Ty.rename, Rename.lift_here]

theorem memberTelescope_subst (lower upper : Ty source)
    (substitution : Subst source target) :
    (memberTelescope lower upper).subst substitution =
      memberTelescope (lower.subst substitution) (upper.subst substitution) := by
  unfold memberTelescope memberTail
  simp only [Telescope.subst]
  rw [← Ty.weaken_subst_comm_base, ← Ty.weaken_subst_comm_base,
    ← Ty.weaken_subst_comm_base, ← Ty.weaken_subst_comm_base]
  simp only [Ty.subst, Subst.lift_tvar_here]

def representation (first : ValuePlan sig)
    (lower upper : Ty first.scope) : Telescope sig :=
  first.telescope.append (memberTelescope lower upper)

def plan (first : ValuePlan sig) (lower upper : Ty first.scope) :
    ValuePlan sig :=
  Pair.plan (representation first lower upper)

theorem representation_rename (first : ValuePlan source)
    (lower upper : Ty first.scope) (mapping : Rename source target) :
    (representation first lower upper).rename mapping =
      representation (first.rename mapping)
        (lower.rename (first.telescope.liftRename mapping))
        (upper.rename (first.telescope.liftRename mapping)) := by
  unfold representation
  rw [Telescope.append_rename, memberTelescope_rename]
  rfl

theorem representation_subst (first : ValuePlan source)
    (lower upper : Ty first.scope) (substitution : Subst source target) :
    (representation first lower upper).subst substitution =
      representation (first.subst substitution)
        (lower.subst (first.telescope.liftSubst substitution))
        (upper.subst (first.telescope.liftSubst substitution)) := by
  unfold representation
  rw [Telescope.append_subst, memberTelescope_subst]
  rfl

theorem plan_rename (first : ValuePlan source)
    (lower upper : Ty first.scope) (mapping : Rename source target) :
    (plan first lower upper).rename mapping =
      plan (first.rename mapping)
        (lower.rename (first.telescope.liftRename mapping))
        (upper.rename (first.telescope.liftRename mapping)) := by
  unfold plan
  rw [Pair.plan_rename, representation_rename]

theorem plan_subst (first : ValuePlan source)
    (lower upper : Ty first.scope) (substitution : Subst source target) :
    (plan first lower upper).subst substitution =
      plan (first.subst substitution)
        (lower.subst (first.telescope.liftSubst substitution))
        (upper.subst (first.telescope.liftSubst substitution)) := by
  unfold plan
  rw [Pair.plan_subst, representation_subst]

noncomputable def openedArgumentsWithAdapters
    {sig : Sig} (base : Ctx sig)
    (lower upper selectedInput : Ty sig)
    (lowerEvidence : Co sig)
    (lowerTyping : Co.HasType base lowerEvidence lower selectedInput)
    (upperEvidence : Co sig)
    (upperTyping : Co.HasType base upperEvidence selectedInput upper) :
    Telescope.Args base (openedMember lower upper selectedInput) := by
  refine .cvar lowerEvidence lowerTyping ?_
  exact (openedTail_open upper selectedInput lowerEvidence).symm ▸
    (.cvar upperEvidence upperTyping .nil)

noncomputable def memberArgumentsWithAdapters
    {sig : Sig} (base : Ctx sig)
    (lower upper selectedInput : Ty sig)
    (lowerEvidence : Co sig)
    (lowerTyping : Co.HasType base lowerEvidence lower selectedInput)
    (upperEvidence : Co sig)
    (upperTyping : Co.HasType base upperEvidence selectedInput upper) :
    Telescope.Args base (memberTelescope lower upper) :=
  .tvar selectedInput
    ((memberTail_open lower upper selectedInput).symm ▸
      openedArgumentsWithAdapters base lower upper selectedInput lowerEvidence
        lowerTyping upperEvidence upperTyping)

noncomputable def representationArgumentsWithAdapters
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (lower upper : Ty first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (selectedInput : Ty sig)
    (lowerEvidence : Co sig)
    (lowerTyping : Co.HasType base lowerEvidence
      (lower.subst firstArguments.substitution) selectedInput)
    (upperEvidence : Co sig)
    (upperTyping : Co.HasType base upperEvidence selectedInput
      (upper.subst firstArguments.substitution)) :
    Telescope.Args base (representation first lower upper) := by
  let supplied := memberArgumentsWithAdapters base
    (lower.subst firstArguments.substitution)
    (upper.subst firstArguments.substitution) selectedInput lowerEvidence
    lowerTyping upperEvidence upperTyping
  have reindexed := memberTelescope_subst lower upper
    firstArguments.substitution
  exact firstArguments.append (memberTelescope lower upper)
    (reindexed.symm ▸ supplied)

noncomputable def exactWithAdapters
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (lower upper : Ty first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (selectedInput : Ty sig)
    (lowerEvidence : Co sig)
    (lowerTyping : Co.HasType base lowerEvidence
      (lower.subst firstArguments.substitution) selectedInput)
    (upperEvidence : Co sig)
    (upperTyping : Co.HasType base upperEvidence selectedInput
      (upper.subst firstArguments.substitution)) : Exp sig :=
  Pair.exactPackage (representation first lower upper)
    (representationArgumentsWithAdapters first lower upper firstArguments
      selectedInput lowerEvidence lowerTyping upperEvidence upperTyping)

noncomputable def exactWithAdapters_hasType
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (lower upper : Ty first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (selectedInput : Ty sig)
    (lowerEvidence : Co sig)
    (lowerTyping : Co.HasType base lowerEvidence
      (lower.subst firstArguments.substitution) selectedInput)
    (upperEvidence : Co sig)
    (upperTyping : Co.HasType base upperEvidence selectedInput
      (upper.subst firstArguments.substitution)) :
    Exp.HasType base
      (exactWithAdapters first lower upper firstArguments selectedInput
        lowerEvidence lowerTyping upperEvidence upperTyping)
      (plan first lower upper).inputTy :=
  Pair.exactPackage_hasType (representation first lower upper)
    (representationArgumentsWithAdapters first lower upper firstArguments
      selectedInput lowerEvidence lowerTyping upperEvidence upperTyping)

end Pair.IntervalV2

namespace IntervalDescriptorV2

/-- Compiler-side selected plan and exact stable package maps. -/
structure Descriptor {sig : Sig} (base : Ctx sig)
    (lower upper : ValuePlan sig) : Type where
  selected : ValuePlan sig
  lowerAdapter : StableIdentity.Adapter base lower selected
  upperAdapter : StableIdentity.Adapter base selected upper

namespace Descriptor

/-- Exact intervals retain the endpoint plan itself. -/
noncomputable def exact (base : Ctx sig) (endpoint : ValuePlan sig) :
    Descriptor base endpoint endpoint where
  selected := endpoint
  lowerAdapter := StableIdentity.Adapter.identity base endpoint
  upperAdapter := StableIdentity.Adapter.identity base endpoint

@[simp] theorem exact_selected (base : Ctx sig) (endpoint : ValuePlan sig) :
    (exact base endpoint).selected = endpoint := by
  rfl

/-- Substitute the complete descriptor, including both stable laws. -/
noncomputable def subst
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target}
    {lower upper : ValuePlan source}
    (descriptor : Descriptor sourceContext lower upper)
    (substitution : Subst source target)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    Descriptor targetContext (lower.subst substitution)
      (upper.subst substitution) where
  selected := descriptor.selected.subst substitution
  lowerAdapter := StableIdentity.Adapter.subst descriptor.lowerAdapter
    substitution typed
  upperAdapter := StableIdentity.Adapter.subst descriptor.upperAdapter
    substitution typed

/-- Bounds variance map.  It never chooses or replaces the selected plan. -/
structure Map (base : Ctx sig)
    (sourceLower sourceUpper targetLower targetUpper : ValuePlan sig) where
  lower : StableIdentity.Adapter base targetLower sourceLower
  upper : StableIdentity.Adapter base sourceUpper targetUpper

noncomputable def map
    (descriptor : Descriptor base sourceLower sourceUpper)
    (mapping : Map base sourceLower sourceUpper targetLower targetUpper) :
    Descriptor base targetLower targetUpper where
  selected := descriptor.selected
  lowerAdapter := mapping.lower.compose descriptor.lowerAdapter
  upperAdapter := descriptor.upperAdapter.compose mapping.upper

@[simp] theorem map_selected
    (descriptor : Descriptor base sourceLower sourceUpper)
    (mapping : Map base sourceLower sourceUpper targetLower targetUpper) :
    (map descriptor mapping).selected = descriptor.selected := by
  rfl

noncomputable def Map.identity (base : Ctx sig)
    (lower upper : ValuePlan sig) : Map base lower upper lower upper where
  lower := StableIdentity.Adapter.identity base lower
  upper := StableIdentity.Adapter.identity base upper

noncomputable def Map.compose
    (first : Map base sourceLower sourceUpper middleLower middleUpper)
    (second : Map base middleLower middleUpper targetLower targetUpper) :
    Map base sourceLower sourceUpper targetLower targetUpper where
  lower := second.lower.compose first.lower
  upper := first.upper.compose second.upper

end Descriptor

/-- Sealed exact `[T,T]` introduction.  Callers supply only the actual first
arguments; the selected plan and both adapters are forced. -/
structure ExactResult {sig : Sig} (base : Ctx sig)
    (first : ValuePlan sig) (endpoint : ValuePlan first.scope) : Type where
  private mk ::
  firstArguments : Telescope.Args base first.telescope

namespace ExactResult

noncomputable def make (base : Ctx sig) (first : ValuePlan sig)
    (endpoint : ValuePlan first.scope)
    (firstArguments : Telescope.Args base first.telescope) :
    ExactResult base first endpoint :=
  .mk firstArguments

noncomputable def descriptor
    (_result : ExactResult base first endpoint) :
    Descriptor (first.context base) endpoint endpoint :=
  Descriptor.exact (first.context base) endpoint

noncomputable def openedDescriptor
    (result : ExactResult base first endpoint) :
    Descriptor base (endpoint.subst result.firstArguments.substitution)
      (endpoint.subst result.firstArguments.substitution) :=
  result.descriptor.subst result.firstArguments.substitution
    result.firstArguments.substitution_typed

/-- Exact package tied definitionally to the opened descriptor. -/
noncomputable def package
    (result : ExactResult base first endpoint) :
    PathPackageZipper.CompiledPackage base
      (Pair.IntervalV2.plan first endpoint.inputTy endpoint.inputTy) := by
  let opened := result.openedDescriptor
  have lowerTyping : Co.HasType base opened.lowerAdapter.coercion
      (endpoint.inputTy.subst result.firstArguments.substitution)
      opened.selected.inputTy := by
    simpa only [ValuePlan.inputTy_subst] using
      opened.lowerAdapter.coercion_hasType
  have upperTyping : Co.HasType base opened.upperAdapter.coercion
      opened.selected.inputTy
      (endpoint.inputTy.subst result.firstArguments.substitution) := by
    simpa only [ValuePlan.inputTy_subst] using
      opened.upperAdapter.coercion_hasType
  exact
    { expression := Pair.IntervalV2.exactWithAdapters first endpoint.inputTy
        endpoint.inputTy result.firstArguments opened.selected.inputTy
        opened.lowerAdapter.coercion lowerTyping opened.upperAdapter.coercion
        upperTyping
      typing := Pair.IntervalV2.exactWithAdapters_hasType first
        endpoint.inputTy endpoint.inputTy result.firstArguments
        opened.selected.inputTy opened.lowerAdapter.coercion lowerTyping
        opened.upperAdapter.coercion upperTyping }

end ExactResult

end IntervalDescriptorV2

end LambdaPToFCo.Full
