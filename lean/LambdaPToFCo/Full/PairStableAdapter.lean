import LambdaPToFCo.Full.PairInterface
import LambdaPToFCo.Full.StableIdentity

/-!
# Stable adapters for pair representations

A one-way coercion between Church representations is enough to map an outer
pair plan. The adapter retains the source package's exact hidden identity and
payload and changes only its `I => representation` observation.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

namespace PairStableAdapter

/-- Compose an opened pair's retained representation observation with a
base-level one-way representation coercion. -/
noncomputable def representationEvidenceAtSource
    {sig : Sig}
    (sourceRepresentation : Telescope sig)
    (evidence : Co sig) :
    Co (StableIdentity.sourceAtBinder
      (Pair.plan sourceRepresentation)).scope :=
  .trans (.cvar .here)
    ((evidence.weaken .var).rename
      (StableIdentity.sourceAtBinder
        (Pair.plan sourceRepresentation)).telescope.weaken)

noncomputable def representationEvidenceAtSource_hasType
    {sig : Sig} {base : Ctx sig}
    (sourceRepresentation targetRepresentation : Telescope sig)
    (evidence : Co sig)
    (typing : Co.HasType base evidence sourceRepresentation.existsTy
      targetRepresentation.existsTy) :
    Co.HasType
      (StableIdentity.openedContext base (Pair.plan sourceRepresentation))
      (representationEvidenceAtSource sourceRepresentation evidence)
      (StableIdentity.sourceAtBinder
        (Pair.plan sourceRepresentation)).identityTy
      ((targetRepresentation.existsTy.weaken .var).rename
        (StableIdentity.sourceAtBinder
          (Pair.plan sourceRepresentation)).telescope.weaken) := by
  apply Co.HasType.trans (middle :=
    (sourceRepresentation.existsTy.weaken .var).rename
      (StableIdentity.sourceAtBinder
        (Pair.plan sourceRepresentation)).telescope.weaken)
  · have renamed :=
      (Pair.toRepresentation_hasType base sourceRepresentation).rename
        ((Pair.plan sourceRepresentation).telescope.liftRename_typed
          (Rename.Typed.weaken base
            (.var (Pair.plan sourceRepresentation).inputTy)))
    have middleEq :=
      (Pair.plan sourceRepresentation).telescope.weakenType_liftRename
        sourceRepresentation.existsTy (Rename.weaken .var)
    have adjusted := middleEq ▸ renamed
    simpa only [StableIdentity.openedContext,
      StableIdentity.sourceAtBinder, Pair.toRepresentation_rename,
      ValuePlan.identityTy_rename, Pair.finalRepresentationTy_rename,
      Pair.plan_rename, Pair.finalRepresentationTy,
      ValuePlan.telescope_rename, Ty.weaken] using adjusted
  · simpa only [StableIdentity.openedContext] using
      (weakenCo_hasType
        (StableIdentity.sourceAtBinder
          (Pair.plan sourceRepresentation)).telescope
        (typing.weaken
          (.var (Pair.plan sourceRepresentation).inputTy)))

/-- The exact-I/i repack justified by a representation coercion. -/
noncomputable def repack
    {sig : Sig} (base : Ctx sig)
    (sourceRepresentation targetRepresentation : Telescope sig)
    (evidence : Co sig)
    (typing : Co.HasType base evidence sourceRepresentation.existsTy
      targetRepresentation.existsTy) :
    StableIdentity.Repack base (Pair.plan sourceRepresentation)
      (Pair.plan targetRepresentation) where
  observations := by
    unfold StableIdentity.observationTelescope
    rw [StableIdentity.targetAtSource,
      Pair.plan_rename, Pair.plan_rename]
    simp only [Pair.plan, Telescope.subst,
      Single.identityAtPayload_open,
      Pair.representationAtPayload_open]
    exact .cvar
      (representationEvidenceAtSource sourceRepresentation evidence)
      (by
        have targetEq :
            ((targetRepresentation.existsTy.weaken .var).rename
                (StableIdentity.sourceAtBinder
                  (Pair.plan sourceRepresentation)).telescope.weaken) =
              ((targetRepresentation.rename (Rename.weaken .var)).rename
                (StableIdentity.sourceAtBinder
                  (Pair.plan sourceRepresentation)).telescope.weaken).existsTy := by
          simp only [Ty.weaken, existsTy_rename]
        exact targetEq ▸
          representationEvidenceAtSource_hasType sourceRepresentation
            targetRepresentation evidence typing) .nil

/-- Lift one-way representation covariance to complete pair packages. -/
noncomputable def adapter
    {sig : Sig} (base : Ctx sig)
    (sourceRepresentation targetRepresentation : Telescope sig)
    (evidence : Co sig)
    (typing : Co.HasType base evidence sourceRepresentation.existsTy
      targetRepresentation.existsTy) :
    StableIdentity.Adapter base (Pair.plan sourceRepresentation)
      (Pair.plan targetRepresentation) :=
  .ofRepack (repack base sourceRepresentation targetRepresentation
    evidence typing)

/-! A focused exact dependent-pair regression. -/

namespace Regression

def representation : Telescope ([] : Sig) :=
  Pair.Proper.representation PairRegression.first
    PairRegression.dependentMember

noncomputable def exactAdapter :
    StableIdentity.Adapter Ctx.empty (Pair.plan representation)
      (Pair.plan representation) :=
  adapter Ctx.empty representation representation
    (.refl representation.existsTy) Co.HasType.refl

noncomputable def exactAdapter_hasType :
    Co.HasType Ctx.empty exactAdapter.coercion
      (Pair.plan representation).inputTy
      (Pair.plan representation).inputTy :=
  exactAdapter.coercion_hasType

end Regression

end PairStableAdapter

end LambdaPToFCo.Full
