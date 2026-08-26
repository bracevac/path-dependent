import LambdaPToFCo.Full.StableIdentity

/-!
# Stable adapters for dependent-function code

A one-way coercion between dependent code types is enough to map an outer
function plan. The adapter retains the source package's exact hidden identity
and payload and changes only its `I => code` observation.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

namespace FunctionStableAdapter

/-- Compose an opened function's retained code observation with a base-level
one-way code coercion. -/
noncomputable def codeEvidenceAtSource
    {sig : Sig}
    (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (evidence : Co sig) :
    Co (StableIdentity.sourceAtBinder
      (Function.plan sourceDomain sourceCodomain)).scope :=
  .trans (.cvar .here)
    ((evidence.weaken .var).rename
      (StableIdentity.sourceAtBinder
        (Function.plan sourceDomain sourceCodomain)).telescope.weaken)

noncomputable def codeEvidenceAtSource_hasType
    {sig : Sig} {base : Ctx sig}
    (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig)
    (targetCodomain : ValuePlan targetDomain.scope)
    (evidence : Co sig)
    (typing : Co.HasType base evidence
      (Function.codeTy sourceDomain sourceCodomain)
      (Function.codeTy targetDomain targetCodomain)) :
    Co.HasType
      (StableIdentity.openedContext base
        (Function.plan sourceDomain sourceCodomain))
      (codeEvidenceAtSource sourceDomain sourceCodomain evidence)
      (StableIdentity.sourceAtBinder
        (Function.plan sourceDomain sourceCodomain)).identityTy
      (((Function.codeTy targetDomain targetCodomain).weaken .var).rename
        (StableIdentity.sourceAtBinder
          (Function.plan sourceDomain sourceCodomain)).telescope.weaken) := by
  apply Co.HasType.trans (middle :=
    ((Function.codeTy sourceDomain sourceCodomain).weaken .var).rename
      (StableIdentity.sourceAtBinder
        (Function.plan sourceDomain sourceCodomain)).telescope.weaken)
  · have renamed :=
      (Function.toCode_hasType base sourceDomain sourceCodomain).rename
        ((Function.plan sourceDomain sourceCodomain).telescope.liftRename_typed
          (Rename.Typed.weaken base
            (.var (Function.plan sourceDomain sourceCodomain).inputTy)))
    have middleEq :=
      (Function.plan sourceDomain sourceCodomain).telescope.weakenType_liftRename
        (Function.codeTy sourceDomain sourceCodomain) (Rename.weaken .var)
    have adjusted := middleEq ▸ renamed
    simpa only [StableIdentity.openedContext,
      StableIdentity.sourceAtBinder, Function.toCode_rename,
      ValuePlan.identityTy_rename, Function.finalCodeTy_rename,
      Function.plan_rename, Function.finalCodeTy,
      ValuePlan.telescope_rename, Ty.weaken] using adjusted
  · simpa only [StableIdentity.openedContext] using
      (weakenCo_hasType
        (StableIdentity.sourceAtBinder
          (Function.plan sourceDomain sourceCodomain)).telescope
        (typing.weaken
          (.var (Function.plan sourceDomain sourceCodomain).inputTy)))

/-- The exact-I/i repack justified by a one-way code coercion. -/
noncomputable def repack
    {sig : Sig} (base : Ctx sig)
    (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig)
    (targetCodomain : ValuePlan targetDomain.scope)
    (evidence : Co sig)
    (typing : Co.HasType base evidence
      (Function.codeTy sourceDomain sourceCodomain)
      (Function.codeTy targetDomain targetCodomain)) :
    StableIdentity.Repack base
      (Function.plan sourceDomain sourceCodomain)
      (Function.plan targetDomain targetCodomain) where
  observations := by
    unfold StableIdentity.observationTelescope
    rw [StableIdentity.targetAtSource,
      Function.plan_rename, Function.plan_rename]
    simp only [Function.plan, Telescope.subst,
      Single.identityAtPayload_open,
      Function.codeAtPayload_open]
    exact .cvar
      (codeEvidenceAtSource sourceDomain sourceCodomain evidence)
      (by
        have targetEq :
            (((Function.codeTy targetDomain targetCodomain).weaken .var).rename
                (StableIdentity.sourceAtBinder
                  (Function.plan sourceDomain sourceCodomain)).telescope.weaken) =
              Function.codeTy
                ((targetDomain.rename (Rename.weaken .var)).rename
                  (StableIdentity.sourceAtBinder
                    (Function.plan sourceDomain sourceCodomain)).telescope.weaken)
                (Function.renameCodomain
                  (targetDomain.rename (Rename.weaken .var))
                  (Function.renameCodomain targetDomain targetCodomain
                    (Rename.weaken .var))
                  (StableIdentity.sourceAtBinder
                    (Function.plan sourceDomain sourceCodomain)).telescope.weaken) := by
          simp only [Ty.weaken, Function.codeTy_rename]
        exact targetEq ▸
          codeEvidenceAtSource_hasType sourceDomain sourceCodomain
            targetDomain targetCodomain evidence typing) .nil

/-- Lift one-way code covariance to complete function packages. -/
noncomputable def adapter
    {sig : Sig} (base : Ctx sig)
    (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig)
    (targetCodomain : ValuePlan targetDomain.scope)
    (evidence : Co sig)
    (typing : Co.HasType base evidence
      (Function.codeTy sourceDomain sourceCodomain)
      (Function.codeTy targetDomain targetCodomain)) :
    StableIdentity.Adapter base
      (Function.plan sourceDomain sourceCodomain)
      (Function.plan targetDomain targetCodomain) :=
  .ofRepack (repack base sourceDomain sourceCodomain targetDomain
    targetCodomain evidence typing)

/-! A focused dependent-function regression. -/

namespace Regression

noncomputable def exactAdapter :
    StableIdentity.Adapter Ctx.empty
      (Function.plan FunctionRegression.domain FunctionRegression.codomain)
      (Function.plan FunctionRegression.domain FunctionRegression.codomain) :=
  adapter Ctx.empty FunctionRegression.domain FunctionRegression.codomain
    FunctionRegression.domain FunctionRegression.codomain
    (.refl (Function.codeTy FunctionRegression.domain
      FunctionRegression.codomain)) Co.HasType.refl

noncomputable def exactAdapter_hasType :
    Co.HasType Ctx.empty exactAdapter.coercion
      (Function.plan FunctionRegression.domain
        FunctionRegression.codomain).inputTy
      (Function.plan FunctionRegression.domain
        FunctionRegression.codomain).inputTy :=
  exactAdapter.coercion_hasType

end Regression

end FunctionStableAdapter

end LambdaPToFCo.Full
