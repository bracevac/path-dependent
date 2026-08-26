import LambdaPToFCo.Full.ValueModel

/-!
# Faithful atomic value models

Singleton and selected types retain an exact hidden identity. Neither model
uses an advertised upper bound as the runtime identity.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

/-- Weaken typed coercion evidence through every field of a target
telescope. -/
noncomputable def weakenCo_hasType
    (tele : Telescope sig) {base : Ctx sig} {coercion : Co sig}
    {source target : Ty sig}
    (typing : Co.HasType base coercion source target) :
    Co.HasType (tele.context base) (coercion.rename tele.weaken)
      (source.rename tele.weaken) (target.rename tele.weaken) := by
  induction tele with
  | nil =>
      change Co.HasType base (coercion.rename Rename.id)
        (source.rename Rename.id) (target.rename Rename.id)
      rw [Co.rename_id, Ty.rename_id, Ty.rename_id]
      exact typing
  | var parameter tail ih =>
      have first := typing.weaken (.var parameter)
      have rest := ih first
      simpa only [Telescope.context, Telescope.weaken,
        Co.weaken, Ty.weaken, Co.rename_comp, Ty.rename_comp] using rest
  | tvar tail ih =>
      have first := typing.weaken .tvar
      have rest := ih first
      simpa only [Telescope.context, Telescope.weaken,
        Co.weaken, Ty.weaken, Co.rename_comp, Ty.rename_comp] using rest
  | cvar evidenceSource evidenceTarget tail ih =>
      have first := typing.weaken (.cvar evidenceSource evidenceTarget)
      have rest := ih first
      simpa only [Telescope.context, Telescope.weaken,
        Co.weaken, Ty.weaken, Co.rename_comp, Ty.rename_comp] using rest

namespace Single

/-- Referent identity in the observation base scope, after hidden `I, i`. -/
def referentAtPayload (referentIdentity : Ty sig) :
    Ty ((sig ,, .tvar) ,, .var) :=
  (referentIdentity.weaken .tvar).weaken .var

/-- Faithful singleton plan. Its two observations are explicit evidence
`I => referent` and `referent => I`. -/
def plan (referentIdentity : Ty sig) : ValuePlan sig where
  observations :=
    .cvar (ValuePlan.identityAtPayload sig)
      (referentAtPayload referentIdentity)
      (.cvar
        ((referentAtPayload referentIdentity).weaken .cvar)
        ((ValuePlan.identityAtPayload sig).weaken .cvar)
        .nil)

theorem identityAtPayload_rename (mapping : Rename source target) :
    (ValuePlan.identityAtPayload source).rename
        ((mapping.lift .tvar).lift .var) =
      ValuePlan.identityAtPayload target := by
  rfl

theorem identityAtPayload_subst (substitution : Subst source target) :
    (ValuePlan.identityAtPayload source).subst
        ((substitution.lift .tvar).lift .var) =
      ValuePlan.identityAtPayload target := by
  rfl

theorem referentAtPayload_rename (referentIdentity : Ty source)
    (mapping : Rename source target) :
    (referentAtPayload referentIdentity).rename
        ((mapping.lift .tvar).lift .var) =
      referentAtPayload (referentIdentity.rename mapping) := by
  unfold referentAtPayload
  rw [Ty.weaken_rename_comm, Ty.weaken_rename_comm]

theorem referentAtPayload_subst (referentIdentity : Ty source)
    (substitution : Subst source target) :
    (referentAtPayload referentIdentity).subst
        ((substitution.lift .tvar).lift .var) =
      referentAtPayload (referentIdentity.subst substitution) := by
  unfold referentAtPayload
  rw [← Ty.weaken_subst_comm_base, ← Ty.weaken_subst_comm_base]

theorem referentEvidence_rename (referentIdentity : Ty source)
    (mapping : Rename source target) :
    ((referentAtPayload referentIdentity).weaken .cvar).rename
        (((mapping.lift .tvar).lift .var).lift .cvar) =
      (referentAtPayload (referentIdentity.rename mapping)).weaken
        .cvar := by
  rw [Ty.weaken_rename_comm, referentAtPayload_rename]

theorem identityEvidence_rename (mapping : Rename source target) :
    ((ValuePlan.identityAtPayload source).weaken .cvar).rename
        (((mapping.lift .tvar).lift .var).lift .cvar) =
      (ValuePlan.identityAtPayload target).weaken .cvar := by
  rw [Ty.weaken_rename_comm, identityAtPayload_rename]

theorem referentEvidence_subst (referentIdentity : Ty source)
    (substitution : Subst source target) :
    ((referentAtPayload referentIdentity).weaken .cvar).subst
        (((substitution.lift .tvar).lift .var).lift .cvar) =
      (referentAtPayload (referentIdentity.subst substitution)).weaken
        .cvar := by
  rw [← Ty.weaken_subst_comm_base, referentAtPayload_subst]

theorem identityEvidence_subst (substitution : Subst source target) :
    ((ValuePlan.identityAtPayload source).weaken .cvar).subst
        (((substitution.lift .tvar).lift .var).lift .cvar) =
      (ValuePlan.identityAtPayload target).weaken .cvar := by
  rw [← Ty.weaken_subst_comm_base, identityAtPayload_subst]

theorem plan_rename (referentIdentity : Ty source)
    (mapping : Rename source target) :
    (plan referentIdentity).rename mapping =
      plan (referentIdentity.rename mapping) := by
  unfold ValuePlan.rename plan
  simp only [Telescope.rename]
  simp only [referentAtPayload_rename, identityAtPayload_rename,
    referentEvidence_rename, identityEvidence_rename]

theorem plan_subst (referentIdentity : Ty source)
    (substitution : Subst source target) :
    (plan referentIdentity).subst substitution =
      plan (referentIdentity.subst substitution) := by
  unfold ValuePlan.subst plan
  simp only [Telescope.subst]
  simp only [referentAtPayload_subst, identityAtPayload_subst,
    referentEvidence_subst, identityEvidence_subst]

@[simp] theorem identityAtPayload_open (identity : Ty sig)
    (payload : Exp sig) :
    ((ValuePlan.identityAtPayload sig).subst
      ((Subst.openTVar identity).lift .var)).subst
        (Subst.openVar payload) = identity := by
  unfold ValuePlan.identityAtPayload
  change (identity.weaken .var).subst (Subst.openVar payload) = identity
  exact identity.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openVar payload)

@[simp] theorem referentAtPayload_open (referentIdentity identity : Ty sig)
    (payload : Exp sig) :
    ((referentAtPayload referentIdentity).subst
      ((Subst.openTVar identity).lift .var)).subst
        (Subst.openVar payload) = referentIdentity := by
  unfold referentAtPayload
  rw [← Ty.weaken_subst_comm_base]
  rw [referentIdentity.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openTVar identity)]
  exact referentIdentity.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openVar payload)

@[simp] theorem identityEvidence_open (identity : Ty sig)
    (payload : Exp sig) (evidence : Co sig) :
    ((((ValuePlan.identityAtPayload sig).weaken .cvar).subst
      (((Subst.openTVar identity).lift .var).lift .cvar)).subst
        ((Subst.openVar payload).lift .cvar)).subst
          (Subst.openCVar evidence) = identity := by
  rw [← Ty.weaken_subst_comm_base, ← Ty.weaken_subst_comm_base,
    identityAtPayload_open]
  exact identity.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openCVar evidence)

@[simp] theorem referentEvidence_open (referentIdentity identity : Ty sig)
    (payload : Exp sig) (evidence : Co sig) :
    ((((referentAtPayload referentIdentity).weaken .cvar).subst
      (((Subst.openTVar identity).lift .var).lift .cvar)).subst
        ((Subst.openVar payload).lift .cvar)).subst
          (Subst.openCVar evidence) = referentIdentity := by
  rw [← Ty.weaken_subst_comm_base, ← Ty.weaken_subst_comm_base,
    referentAtPayload_open]
  exact referentIdentity.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openCVar evidence)

/-- Referent identity in the complete final plan scope. -/
def referentTy (referentIdentity : Ty sig) :
    Ty (plan referentIdentity).scope :=
  referentIdentity.rename (plan referentIdentity).telescope.weaken

theorem referentTy_rename (referentIdentity : Ty source)
    (mapping : Rename source target) :
    (referentTy referentIdentity).rename
        ((plan referentIdentity).telescope.liftRename mapping) =
      referentTy (referentIdentity.rename mapping) := by
  simpa only [referentTy, ValuePlan.telescope_rename, plan_rename] using
    (plan referentIdentity).telescope.weakenType_liftRename
      referentIdentity mapping

theorem referentTy_subst (referentIdentity : Ty source)
    (substitution : Subst source target) :
    (referentTy referentIdentity).subst
        ((plan referentIdentity).telescope.liftSubst substitution) =
      referentTy (referentIdentity.subst substitution) := by
  simpa only [referentTy, ValuePlan.telescope_subst, plan_subst] using
    (plan referentIdentity).telescope.weakenType_liftSubst
      referentIdentity substitution

/-- Evidence from the hidden identity to the referent identity. -/
def toReferent (referentIdentity : Ty sig) :
    Co (plan referentIdentity).scope :=
  .cvar (.there .here)

/-- Evidence from the referent identity back to the hidden identity. -/
def fromReferent (referentIdentity : Ty sig) :
    Co (plan referentIdentity).scope :=
  .cvar .here

theorem toReferent_rename (referentIdentity : Ty source)
    (mapping : Rename source target) :
    (toReferent referentIdentity).rename
        ((plan referentIdentity).telescope.liftRename mapping) =
      toReferent (referentIdentity.rename mapping) := by
  rfl

theorem fromReferent_rename (referentIdentity : Ty source)
    (mapping : Rename source target) :
    (fromReferent referentIdentity).rename
        ((plan referentIdentity).telescope.liftRename mapping) =
      fromReferent (referentIdentity.rename mapping) := by
  rfl

theorem toReferent_subst (referentIdentity : Ty source)
    (substitution : Subst source target) :
    (toReferent referentIdentity).subst
        ((plan referentIdentity).telescope.liftSubst substitution) =
      toReferent (referentIdentity.subst substitution) := by
  rfl

theorem fromReferent_subst (referentIdentity : Ty source)
    (substitution : Subst source target) :
    (fromReferent referentIdentity).subst
        ((plan referentIdentity).telescope.liftSubst substitution) =
      fromReferent (referentIdentity.subst substitution) := by
  rfl

noncomputable def toReferent_hasType (base : Ctx sig)
    (referentIdentity : Ty sig) :
    Co.HasType ((plan referentIdentity).context base)
      (toReferent referentIdentity)
      (plan referentIdentity).identityTy
      (referentTy referentIdentity) := by
  have evidence :
      Co.HasType ((plan referentIdentity).context base)
        (.cvar (.there .here))
        (((ValuePlan.identityAtPayload sig).weaken .cvar).weaken .cvar)
        (((referentAtPayload referentIdentity).weaken .cvar).weaken
          .cvar) :=
    .cvar (Ctx.Lookup.there Ctx.Lookup.here)
  simpa only [ValuePlan.context, ValuePlan.telescope, plan,
    ValuePlan.identityTy, referentTy, referentAtPayload,
    Telescope.context, Telescope.weaken, Ty.weaken, Ty.rename_comp,
    Rename.comp_id] using evidence

noncomputable def fromReferent_hasType (base : Ctx sig)
    (referentIdentity : Ty sig) :
    Co.HasType ((plan referentIdentity).context base)
      (fromReferent referentIdentity)
      (referentTy referentIdentity)
      (plan referentIdentity).identityTy := by
  have evidence :
      Co.HasType ((plan referentIdentity).context base)
        (.cvar .here)
        (((referentAtPayload referentIdentity).weaken .cvar).weaken
          .cvar)
        (((ValuePlan.identityAtPayload sig).weaken .cvar).weaken .cvar) :=
    .cvar Ctx.Lookup.here
  simpa only [ValuePlan.context, ValuePlan.telescope, plan,
    ValuePlan.identityTy, referentTy, referentAtPayload,
    Telescope.context, Telescope.weaken, Ty.weaken, Ty.rename_comp,
    Rename.comp_id] using evidence

/-- Payload viewed at the referent identity. -/
def payloadAsReferent (referentIdentity : Ty sig) :
    Exp (plan referentIdentity).scope :=
  .cast (plan referentIdentity).payload (toReferent referentIdentity)

noncomputable def payloadAsReferent_hasType (base : Ctx sig)
    (referentIdentity : Ty sig) :
    Exp.HasType ((plan referentIdentity).context base)
      (payloadAsReferent referentIdentity) (referentTy referentIdentity) :=
  .cast ((plan referentIdentity).payload_hasType base)
    (toReferent_hasType base referentIdentity)

theorem payloadAsReferent_rename (referentIdentity : Ty source)
    (mapping : Rename source target) :
    (payloadAsReferent referentIdentity).rename
        ((plan referentIdentity).telescope.liftRename mapping) =
      payloadAsReferent (referentIdentity.rename mapping) := by
  unfold payloadAsReferent
  simp only [Exp.rename]
  rw [ValuePlan.payload_rename, toReferent_rename]
  rfl

theorem payloadAsReferent_subst (referentIdentity : Ty source)
    (substitution : Subst source target) :
    (payloadAsReferent referentIdentity).subst
        ((plan referentIdentity).telescope.liftSubst substitution) =
      payloadAsReferent (referentIdentity.subst substitution) := by
  unfold payloadAsReferent
  simp only [Exp.subst]
  rw [ValuePlan.payload_subst, toReferent_subst]
  rfl

theorem inputTy_rename (referentIdentity : Ty source)
    (mapping : Rename source target) :
    (plan referentIdentity).inputTy.rename mapping =
      (plan (referentIdentity.rename mapping)).inputTy := by
  calc
    (plan referentIdentity).inputTy.rename mapping =
        ((plan referentIdentity).rename mapping).inputTy :=
      ValuePlan.inputTy_rename (plan referentIdentity) mapping
    _ = (plan (referentIdentity.rename mapping)).inputTy := by
      rw [plan_rename]

theorem inputTy_subst (referentIdentity : Ty source)
    (substitution : Subst source target) :
    (plan referentIdentity).inputTy.subst substitution =
      (plan (referentIdentity.subst substitution)).inputTy := by
  calc
    (plan referentIdentity).inputTy.subst substitution =
        ((plan referentIdentity).subst substitution).inputTy :=
      ValuePlan.inputTy_subst (plan referentIdentity) substitution
    _ = (plan (referentIdentity.subst substitution)).inputTy := by
      rw [plan_subst]

/-- Supply a hidden identity, payload, and the two directions of exact
identity evidence. -/
def arguments {sig : Sig} {base : Ctx sig}
    (referentIdentity identity : Ty sig)
    (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (toReferentEvidence : Co sig)
    (toReferentTyping : Co.HasType base toReferentEvidence
      identity referentIdentity)
    (fromReferentEvidence : Co sig)
    (fromReferentTyping : Co.HasType base fromReferentEvidence
      referentIdentity identity) :
    Telescope.Args base (plan referentIdentity).telescope :=
  .tvar identity
    (.var payload payloadTyping
      (.cvar toReferentEvidence (by
        rw [identityAtPayload_open, referentAtPayload_open]
        exact toReferentTyping)
        (.cvar fromReferentEvidence (by
          rw [referentEvidence_open, identityEvidence_open]
          exact fromReferentTyping) .nil)))

noncomputable def package {sig : Sig} {base : Ctx sig}
    (referentIdentity identity : Ty sig)
    (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (toReferentEvidence : Co sig)
    (toReferentTyping : Co.HasType base toReferentEvidence
      identity referentIdentity)
    (fromReferentEvidence : Co sig)
    (fromReferentTyping : Co.HasType base fromReferentEvidence
      referentIdentity identity) : Exp sig :=
  (plan referentIdentity).pack
    (arguments referentIdentity identity payload payloadTyping
      toReferentEvidence toReferentTyping
      fromReferentEvidence fromReferentTyping)

noncomputable def package_hasType {sig : Sig} {base : Ctx sig}
    (referentIdentity identity : Ty sig)
    (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (toReferentEvidence : Co sig)
    (toReferentTyping : Co.HasType base toReferentEvidence
      identity referentIdentity)
    (fromReferentEvidence : Co sig)
    (fromReferentTyping : Co.HasType base fromReferentEvidence
      referentIdentity identity) :
    Exp.HasType base
      (package referentIdentity identity payload payloadTyping
        toReferentEvidence toReferentTyping
        fromReferentEvidence fromReferentTyping)
      (plan referentIdentity).inputTy :=
  (plan referentIdentity).pack_hasType
    (arguments referentIdentity identity payload payloadTyping
      toReferentEvidence toReferentTyping
      fromReferentEvidence fromReferentTyping)

/-- Exact singleton arguments reuse the referent itself as hidden identity and
both directions are reflexivity evidence. -/
def exactArguments {sig : Sig} {base : Ctx sig}
    (referentIdentity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload referentIdentity) :
    Telescope.Args base (plan referentIdentity).telescope :=
  arguments referentIdentity referentIdentity payload payloadTyping
    (.refl referentIdentity) Co.HasType.refl
    (.refl referentIdentity) Co.HasType.refl

noncomputable def exactPackage {sig : Sig} {base : Ctx sig}
    (referentIdentity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload referentIdentity) : Exp sig :=
  (plan referentIdentity).pack
    (exactArguments referentIdentity payload payloadTyping)

noncomputable def exactPackage_hasType {sig : Sig} {base : Ctx sig}
    (referentIdentity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload referentIdentity) :
    Exp.HasType base
      (exactPackage referentIdentity payload payloadTyping)
      (plan referentIdentity).inputTy :=
  (plan referentIdentity).pack_hasType
    (exactArguments referentIdentity payload payloadTyping)

end Single

namespace Selection

/-- A selection exposes only an opaque exact witness identity bridge. It does
not expose, inspect, or erase to the witness's concrete observations. -/
def plan (witnessIdentity : Ty sig) : ValuePlan sig :=
  Single.plan witnessIdentity

def witnessTy (witnessIdentity : Ty sig) :
    Ty (plan witnessIdentity).scope :=
  Single.referentTy witnessIdentity

def toWitness (witnessIdentity : Ty sig) :
    Co (plan witnessIdentity).scope :=
  Single.toReferent witnessIdentity

def fromWitness (witnessIdentity : Ty sig) :
    Co (plan witnessIdentity).scope :=
  Single.fromReferent witnessIdentity

noncomputable def toWitness_hasType (base : Ctx sig)
    (witnessIdentity : Ty sig) :
    Co.HasType ((plan witnessIdentity).context base)
      (toWitness witnessIdentity)
      (plan witnessIdentity).identityTy
      (witnessTy witnessIdentity) :=
  Single.toReferent_hasType base witnessIdentity

noncomputable def fromWitness_hasType (base : Ctx sig)
    (witnessIdentity : Ty sig) :
    Co.HasType ((plan witnessIdentity).context base)
      (fromWitness witnessIdentity)
      (witnessTy witnessIdentity)
      (plan witnessIdentity).identityTy :=
  Single.fromReferent_hasType base witnessIdentity

/-- Typing witness for the representation value bound by `Co.adapter`. -/
noncomputable def wrapPayloadTyping (base : Ctx sig)
    (witnessIdentity : Ty sig) :
    Exp.HasType (base.bindVar witnessIdentity) (.var .here)
      (witnessIdentity.weaken .var) :=
  .var Ctx.Lookup.here

/-- Exact introduction body for the computational representation wrapper. -/
noncomputable def wrapBody (base : Ctx sig) (witnessIdentity : Ty sig) :
    Exp (sig ,, .var) :=
  let witness := witnessIdentity.weaken .var
  Single.exactPackage witness (.var .here)
    (wrapPayloadTyping base witnessIdentity)

/-- Computationally wrap a representation value as an opaque selection
package, using `I = X`, the payload itself, and reflexivity both ways. -/
noncomputable def wrap (base : Ctx sig) (witnessIdentity : Ty sig) : Co sig :=
  .adapter witnessIdentity (wrapBody base witnessIdentity)

noncomputable def wrap_hasType (base : Ctx sig)
    (witnessIdentity : Ty sig) :
    Co.HasType base (wrap base witnessIdentity) witnessIdentity
      (plan witnessIdentity).inputTy := by
  apply Co.HasType.adapter
  have bodyTyping := Single.exactPackage_hasType
    (witnessIdentity.weaken .var) (.var .here)
    (wrapPayloadTyping base witnessIdentity)
  change Exp.HasType (base.bindVar witnessIdentity)
    (Single.exactPackage (witnessIdentity.weaken .var) (.var .here)
      (wrapPayloadTyping base witnessIdentity))
    ((Single.plan witnessIdentity).inputTy.weaken .var)
  unfold Ty.weaken
  rw [Single.inputTy_rename]
  exact bodyTyping

/-- Elimination body for the computational representation unwrapper. -/
def unwrapBody (witnessIdentity : Ty sig) : Exp (sig ,, .var) :=
  let witness := witnessIdentity.weaken .var
  (plan witness).unpack (.var .here) witness
    (Single.payloadAsReferent witness)

/-- Computationally eliminate an opaque selection package back to its exact
witness representation type. -/
def unwrap (witnessIdentity : Ty sig) : Co sig :=
  .adapter (plan witnessIdentity).inputTy (unwrapBody witnessIdentity)

noncomputable def unwrap_hasType (base : Ctx sig)
    (witnessIdentity : Ty sig) :
    Co.HasType base (unwrap witnessIdentity)
      (plan witnessIdentity).inputTy witnessIdentity := by
  apply Co.HasType.adapter
  let witness := witnessIdentity.weaken .var
  have packageTyping :
      Exp.HasType (base.bindVar (plan witnessIdentity).inputTy)
        (.var .here) ((plan witnessIdentity).inputTy.weaken .var) :=
    .var Ctx.Lookup.here
  have packageTyping' :
      Exp.HasType (base.bindVar (plan witnessIdentity).inputTy)
        (.var .here) (plan witness).inputTy := by
    change Exp.HasType (base.bindVar (Single.plan witnessIdentity).inputTy)
      (.var .here)
      (Single.plan
        (witnessIdentity.rename (Rename.weaken .var))).inputTy
    rw [← Single.inputTy_rename]
    exact packageTyping
  exact (plan witness).unpack_hasType packageTyping'
    (Single.payloadAsReferent_hasType
      (base.bindVar (plan witnessIdentity).inputTy) witness)

/-- Package-level lower adapter, composed around the exact representation
wrapper. -/
noncomputable def lowerToPackage (base : Ctx sig)
    (witnessIdentity : Ty sig) (lowerEvidence : Co sig) : Co sig :=
  .trans lowerEvidence (wrap base witnessIdentity)

noncomputable def lowerToPackage_hasType
    (base : Ctx sig) (witnessIdentity lower : Ty sig)
    (lowerEvidence : Co sig)
    (lowerTyping : Co.HasType base lowerEvidence lower witnessIdentity) :
    Co.HasType base (lowerToPackage base witnessIdentity lowerEvidence)
      lower (plan witnessIdentity).inputTy :=
  .trans lowerTyping (wrap_hasType base witnessIdentity)

/-- Package-level upper adapter, composed after exact representation
unwrapping. -/
def packageToUpper (witnessIdentity : Ty sig)
    (upperEvidence : Co sig) : Co sig :=
  .trans (unwrap witnessIdentity) upperEvidence

noncomputable def packageToUpper_hasType
    (base : Ctx sig) (witnessIdentity upper : Ty sig)
    (upperEvidence : Co sig)
    (upperTyping : Co.HasType base upperEvidence witnessIdentity upper) :
    Co.HasType base (packageToUpper witnessIdentity upperEvidence)
      (plan witnessIdentity).inputTy upper :=
  .trans (unwrap_hasType base witnessIdentity) upperTyping

/-- Lower bound as seen in the final opaque selection scope. -/
def lowerTy (witnessIdentity lower : Ty sig) :
    Ty (plan witnessIdentity).scope :=
  lower.rename (plan witnessIdentity).telescope.weaken

/-- Upper bound as seen in the final opaque selection scope. -/
def upperTy (witnessIdentity upper : Ty sig) :
    Ty (plan witnessIdentity).scope :=
  upper.rename (plan witnessIdentity).telescope.weaken

/-- Compose `lower => witness` with the retained `witness => I`. -/
def lowerToIdentity (witnessIdentity : Ty sig)
    (lowerEvidence : Co sig) : Co (plan witnessIdentity).scope :=
  .trans
    (lowerEvidence.rename (plan witnessIdentity).telescope.weaken)
    (fromWitness witnessIdentity)

noncomputable def lowerToIdentity_hasType
    (base : Ctx sig) (witnessIdentity lower : Ty sig)
    (lowerEvidence : Co sig)
    (lowerTyping : Co.HasType base lowerEvidence lower witnessIdentity) :
    Co.HasType ((plan witnessIdentity).context base)
      (lowerToIdentity witnessIdentity lowerEvidence)
      (lowerTy witnessIdentity lower)
      (plan witnessIdentity).identityTy :=
  .trans
    (weakenCo_hasType (plan witnessIdentity).telescope lowerTyping)
    (fromWitness_hasType base witnessIdentity)

/-- Compose the retained `I => witness` with `witness => upper`. -/
def identityToUpper (witnessIdentity : Ty sig)
    (upperEvidence : Co sig) : Co (plan witnessIdentity).scope :=
  .trans (toWitness witnessIdentity)
    (upperEvidence.rename (plan witnessIdentity).telescope.weaken)

noncomputable def identityToUpper_hasType
    (base : Ctx sig) (witnessIdentity upper : Ty sig)
    (upperEvidence : Co sig)
    (upperTyping : Co.HasType base upperEvidence witnessIdentity upper) :
    Co.HasType ((plan witnessIdentity).context base)
      (identityToUpper witnessIdentity upperEvidence)
      (plan witnessIdentity).identityTy
      (upperTy witnessIdentity upper) :=
  .trans (toWitness_hasType base witnessIdentity)
    (weakenCo_hasType (plan witnessIdentity).telescope upperTyping)

/-- General opaque-selection arguments. -/
def arguments {sig : Sig} {base : Ctx sig}
    (witnessIdentity identity : Ty sig)
    (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (toWitnessEvidence : Co sig)
    (toWitnessTyping : Co.HasType base toWitnessEvidence
      identity witnessIdentity)
    (fromWitnessEvidence : Co sig)
    (fromWitnessTyping : Co.HasType base fromWitnessEvidence
      witnessIdentity identity) :
    Telescope.Args base (plan witnessIdentity).telescope :=
  Single.arguments witnessIdentity identity payload payloadTyping
    toWitnessEvidence toWitnessTyping fromWitnessEvidence fromWitnessTyping

noncomputable def package {sig : Sig} {base : Ctx sig}
    (witnessIdentity identity : Ty sig)
    (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (toWitnessEvidence : Co sig)
    (toWitnessTyping : Co.HasType base toWitnessEvidence
      identity witnessIdentity)
    (fromWitnessEvidence : Co sig)
    (fromWitnessTyping : Co.HasType base fromWitnessEvidence
      witnessIdentity identity) : Exp sig :=
  (plan witnessIdentity).pack
    (arguments witnessIdentity identity payload payloadTyping
      toWitnessEvidence toWitnessTyping
      fromWitnessEvidence fromWitnessTyping)

noncomputable def package_hasType {sig : Sig} {base : Ctx sig}
    (witnessIdentity identity : Ty sig)
    (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (toWitnessEvidence : Co sig)
    (toWitnessTyping : Co.HasType base toWitnessEvidence
      identity witnessIdentity)
    (fromWitnessEvidence : Co sig)
    (fromWitnessTyping : Co.HasType base fromWitnessEvidence
      witnessIdentity identity) :
    Exp.HasType base
      (package witnessIdentity identity payload payloadTyping
        toWitnessEvidence toWitnessTyping
        fromWitnessEvidence fromWitnessTyping)
      (plan witnessIdentity).inputTy :=
  (plan witnessIdentity).pack_hasType
    (arguments witnessIdentity identity payload payloadTyping
      toWitnessEvidence toWitnessTyping
      fromWitnessEvidence fromWitnessTyping)

def exactArguments {sig : Sig} {base : Ctx sig}
    (witnessIdentity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload witnessIdentity) :
    Telescope.Args base (plan witnessIdentity).telescope :=
  Single.exactArguments witnessIdentity payload payloadTyping

noncomputable def exactPackage {sig : Sig} {base : Ctx sig}
    (witnessIdentity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload witnessIdentity) : Exp sig :=
  (plan witnessIdentity).pack
    (exactArguments witnessIdentity payload payloadTyping)

noncomputable def exactPackage_hasType {sig : Sig} {base : Ctx sig}
    (witnessIdentity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload witnessIdentity) :
    Exp.HasType base
      (exactPackage witnessIdentity payload payloadTyping)
      (plan witnessIdentity).inputTy :=
  (plan witnessIdentity).pack_hasType
    (exactArguments witnessIdentity payload payloadTyping)

theorem plan_rename (witnessIdentity : Ty source)
    (mapping : Rename source target) :
    (plan witnessIdentity).rename mapping =
      plan (witnessIdentity.rename mapping) :=
  Single.plan_rename witnessIdentity mapping

theorem plan_subst (witnessIdentity : Ty source)
    (substitution : Subst source target) :
    (plan witnessIdentity).subst substitution =
      plan (witnessIdentity.subst substitution) :=
  Single.plan_subst witnessIdentity substitution

theorem inputTy_rename (witnessIdentity : Ty source)
    (mapping : Rename source target) :
    (plan witnessIdentity).inputTy.rename mapping =
      (plan (witnessIdentity.rename mapping)).inputTy :=
  Single.inputTy_rename witnessIdentity mapping

theorem inputTy_subst (witnessIdentity : Ty source)
    (substitution : Subst source target) :
    (plan witnessIdentity).inputTy.subst substitution =
      (plan (witnessIdentity.subst substitution)).inputTy :=
  Single.inputTy_subst witnessIdentity substitution

end Selection

namespace AtomicRegression

def identityFunction : Exp ([] : Sig) :=
  .abs .top (.var .here)

noncomputable def identityFunction_hasType :
    Exp.HasType Ctx.empty identityFunction (.arrow .top .top) :=
  .abs (.var Ctx.Lookup.here)

def topPayload : Exp ([] : Sig) :=
  .cast identityFunction (.top (.arrow .top .top))

noncomputable def topPayload_hasType :
    Exp.HasType Ctx.empty topPayload .top :=
  .cast identityFunction_hasType Co.HasType.top

/-- Closed regression for exact singleton introduction. -/
noncomputable def exactSingle : Exp ([] : Sig) :=
  Single.exactPackage .top topPayload topPayload_hasType

noncomputable def exactSingle_hasType :
    Exp.HasType Ctx.empty exactSingle (Single.plan (.top : Ty [])).inputTy :=
  Single.exactPackage_hasType .top topPayload topPayload_hasType

/-- Closed regression for opaque exact-selection introduction. -/
noncomputable def exactSelection : Exp ([] : Sig) :=
  Selection.exactPackage .top topPayload topPayload_hasType

noncomputable def exactSelection_hasType :
    Exp.HasType Ctx.empty exactSelection
      (Selection.plan (.top : Ty [])).inputTy :=
  Selection.exactPackage_hasType .top topPayload topPayload_hasType

/-- The exact selection representation has computational adapters in both
directions; neither adapter mentions an upper-bound erasure. -/
noncomputable def wrapTop_hasType :
    Co.HasType Ctx.empty (Selection.wrap Ctx.empty (.top : Ty []))
      .top (Selection.plan (.top : Ty [])).inputTy :=
  Selection.wrap_hasType Ctx.empty .top

noncomputable def unwrapTop_hasType :
    Co.HasType Ctx.empty (Selection.unwrap (.top : Ty []))
      (Selection.plan (.top : Ty [])).inputTy .top :=
  Selection.unwrap_hasType Ctx.empty .top

noncomputable def boundedWrapTop_hasType :
    Co.HasType Ctx.empty
      (Selection.lowerToPackage Ctx.empty (.top : Ty []) (.refl .top))
      .top (Selection.plan (.top : Ty [])).inputTy :=
  Selection.lowerToPackage_hasType Ctx.empty .top .top (.refl .top)
    Co.HasType.refl

noncomputable def boundedUnwrapTop_hasType :
    Co.HasType Ctx.empty
      (Selection.packageToUpper (.top : Ty []) (.refl .top))
      (Selection.plan (.top : Ty [])).inputTy .top :=
  Selection.packageToUpper_hasType Ctx.empty .top .top (.refl .top)
    Co.HasType.refl

end AtomicRegression

end LambdaPToFCo.Full
