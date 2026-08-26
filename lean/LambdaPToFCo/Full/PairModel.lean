import LambdaPToFCo.Full.FunctionModel
import SystemFCoExt.TelescopeInstances

/-!
# Faithful dependent pair value models

Both pair forms retain their first value interface. Proper members append a
dependent value interface. Interval members hide a concrete representation
type and store computational adapters to and from its opaque selection plan.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

namespace Pair

/-- Transport syntax from a dependent suffix scope to the literal scope of
the concatenated telescope. -/
def fromSuffixExp (first : Telescope sig)
    (suffix : Telescope first.scope) (expression : Exp suffix.scope) :
    Exp (first.append suffix).scope :=
  cast (congrArg Exp (first.appendScopeEq suffix).symm) expression

def fromSuffixTy (first : Telescope sig)
    (suffix : Telescope first.scope) (type : Ty suffix.scope) :
    Ty (first.append suffix).scope :=
  cast (congrArg Ty (first.appendScopeEq suffix).symm) type

def fromSuffixCo (first : Telescope sig)
    (suffix : Telescope first.scope) (coercion : Co suffix.scope) :
    Co (first.append suffix).scope :=
  cast (congrArg Co (first.appendScopeEq suffix).symm) coercion

/-- Pair representation type in the observation base scope. -/
def representationAtPayload (representation : Telescope sig) :
    Ty ((sig ,, .tvar) ,, .var) :=
  (representation.existsTy.weaken .tvar).weaken .var

theorem representationAtPayload_rename
    (representation : Telescope source) (mapping : Rename source target) :
    (representationAtPayload representation).rename
        ((mapping.lift .tvar).lift .var) =
      representationAtPayload (representation.rename mapping) := by
  unfold representationAtPayload
  rw [Ty.weaken_rename_comm, Ty.weaken_rename_comm, existsTy_rename]

theorem representationAtPayload_subst
    (representation : Telescope source) (substitution : Subst source target) :
    (representationAtPayload representation).subst
        ((substitution.lift .tvar).lift .var) =
      representationAtPayload (representation.subst substitution) := by
  unfold representationAtPayload
  rw [← Ty.weaken_subst_comm_base, ← Ty.weaken_subst_comm_base,
    existsTy_subst]

/-- A pair's outer stable identity retains only the direction needed to
observe its Church-encoded representation. -/
def plan (representation : Telescope sig) : ValuePlan sig where
  observations :=
    .cvar (ValuePlan.identityAtPayload sig)
      (representationAtPayload representation) .nil

theorem plan_rename (representation : Telescope source)
    (mapping : Rename source target) :
    (plan representation).rename mapping =
      plan (representation.rename mapping) := by
  unfold ValuePlan.rename plan
  simp only [Telescope.rename]
  rw [Single.identityAtPayload_rename,
    representationAtPayload_rename]

theorem plan_subst (representation : Telescope source)
    (substitution : Subst source target) :
    (plan representation).subst substitution =
      plan (representation.subst substitution) := by
  unfold ValuePlan.subst plan
  simp only [Telescope.subst]
  rw [Single.identityAtPayload_subst,
    representationAtPayload_subst]

@[simp] theorem representationAtPayload_open
    (representation : Telescope sig) (identity : Ty sig)
    (payload : Exp sig) :
    ((representationAtPayload representation).subst
      ((Subst.openTVar identity).lift .var)).subst
        (Subst.openVar payload) = representation.existsTy := by
  unfold representationAtPayload
  rw [← Ty.weaken_subst_comm_base]
  rw [representation.existsTy.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openTVar identity)]
  exact representation.existsTy.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openVar payload)

/-- Representation type in the complete outer-pair interface. -/
def finalRepresentationTy (representation : Telescope sig) :
    Ty (plan representation).scope :=
  representation.existsTy.rename (plan representation).telescope.weaken

theorem finalRepresentationTy_rename
    (representation : Telescope source) (mapping : Rename source target) :
    (finalRepresentationTy representation).rename
        ((plan representation).telescope.liftRename mapping) =
      finalRepresentationTy (representation.rename mapping) := by
  simpa only [finalRepresentationTy, ValuePlan.telescope_rename,
    plan_rename, existsTy_rename] using
      (plan representation).telescope.weakenType_liftRename
        representation.existsTy mapping

theorem finalRepresentationTy_subst
    (representation : Telescope source) (substitution : Subst source target) :
    (finalRepresentationTy representation).subst
        ((plan representation).telescope.liftSubst substitution) =
      finalRepresentationTy (representation.subst substitution) := by
  simpa only [finalRepresentationTy, ValuePlan.telescope_subst,
    plan_subst, existsTy_subst] using
      (plan representation).telescope.weakenType_liftSubst
        representation.existsTy substitution

def toRepresentation (representation : Telescope sig) :
    Co (plan representation).scope :=
  .cvar .here

theorem toRepresentation_rename
    (representation : Telescope source) (mapping : Rename source target) :
    (toRepresentation representation).rename
        ((plan representation).telescope.liftRename mapping) =
      toRepresentation (representation.rename mapping) := by
  rfl

theorem toRepresentation_subst
    (representation : Telescope source) (substitution : Subst source target) :
    (toRepresentation representation).subst
        ((plan representation).telescope.liftSubst substitution) =
      toRepresentation (representation.subst substitution) := by
  rfl

noncomputable def toRepresentation_hasType (base : Ctx sig)
    (representation : Telescope sig) :
    Co.HasType ((plan representation).context base)
      (toRepresentation representation) (plan representation).identityTy
      (finalRepresentationTy representation) := by
  have evidence :
      Co.HasType ((plan representation).context base) (.cvar .here)
        ((ValuePlan.identityAtPayload sig).weaken .cvar)
        ((representationAtPayload representation).weaken .cvar) :=
    .cvar Ctx.Lookup.here
  simpa only [ValuePlan.context, ValuePlan.telescope, plan,
    ValuePlan.identityTy, finalRepresentationTy,
    representationAtPayload, Telescope.context, Telescope.weaken,
    Ty.weaken, Ty.rename_comp, Rename.comp_id] using evidence

/-- Cast the retained outer payload to the pair representation. -/
def asRepresentation (representation : Telescope sig) :
    Exp (plan representation).scope :=
  .cast (plan representation).payload (toRepresentation representation)

noncomputable def asRepresentation_hasType (base : Ctx sig)
    (representation : Telescope sig) :
    Exp.HasType ((plan representation).context base)
      (asRepresentation representation)
      (finalRepresentationTy representation) :=
  .cast ((plan representation).payload_hasType base)
    (toRepresentation_hasType base representation)

/-- A target representation as seen in the opened source-pair plan. -/
def representationTyAtPlan (sourceRepresentation targetRepresentation :
    Telescope sig) : Ty (plan sourceRepresentation).scope :=
  targetRepresentation.existsTy.rename
    (plan sourceRepresentation).telescope.weaken

/-- One-way covariance witness. A representation coercion extends the
retained `I => sourceRep` observation to `I => targetRep`; no reverse
`targetRep => I` evidence is required. -/
def mapToRepresentation (sourceRepresentation : Telescope sig)
    (representationEvidence : Co sig) :
    Co (plan sourceRepresentation).scope :=
  .trans (toRepresentation sourceRepresentation)
    (representationEvidence.rename
      (plan sourceRepresentation).telescope.weaken)

noncomputable def mapToRepresentation_hasType (base : Ctx sig)
    (sourceRepresentation targetRepresentation : Telescope sig)
    (representationEvidence : Co sig)
    (representationTyping : Co.HasType base representationEvidence
      sourceRepresentation.existsTy targetRepresentation.existsTy) :
    Co.HasType ((plan sourceRepresentation).context base)
      (mapToRepresentation sourceRepresentation representationEvidence)
      (plan sourceRepresentation).identityTy
      (representationTyAtPlan sourceRepresentation targetRepresentation) :=
  .trans (toRepresentation_hasType base sourceRepresentation)
    (weakenCo_hasType (plan sourceRepresentation).telescope
      representationTyping)

theorem asRepresentation_rename
    (representation : Telescope source) (mapping : Rename source target) :
    (asRepresentation representation).rename
        ((plan representation).telescope.liftRename mapping) =
      asRepresentation (representation.rename mapping) := by
  unfold asRepresentation
  simp only [Exp.rename]
  rw [ValuePlan.payload_rename, toRepresentation_rename]
  rfl

theorem asRepresentation_subst
    (representation : Telescope source) (substitution : Subst source target) :
    (asRepresentation representation).subst
        ((plan representation).telescope.liftSubst substitution) =
      asRepresentation (representation.subst substitution) := by
  unfold asRepresentation
  simp only [Exp.subst]
  rw [ValuePlan.payload_subst, toRepresentation_subst]
  rfl

theorem inputTy_rename (representation : Telescope source)
    (mapping : Rename source target) :
    (plan representation).inputTy.rename mapping =
      (plan (representation.rename mapping)).inputTy := by
  calc
    (plan representation).inputTy.rename mapping =
        ((plan representation).rename mapping).inputTy :=
      ValuePlan.inputTy_rename (plan representation) mapping
    _ = _ := by rw [plan_rename]

theorem inputTy_subst (representation : Telescope source)
    (substitution : Subst source target) :
    (plan representation).inputTy.subst substitution =
      (plan (representation.subst substitution)).inputTy := by
  calc
    (plan representation).inputTy.subst substitution =
        ((plan representation).subst substitution).inputTy :=
      ValuePlan.inputTy_subst (plan representation) substitution
    _ = _ := by rw [plan_subst]

/-- Build exact outer-pair arguments from a fully supplied representation. -/
noncomputable def exactArguments {sig : Sig} {base : Ctx sig}
    (representation : Telescope sig)
    (arguments : Telescope.Args base representation) :
    Telescope.Args base (plan representation).telescope :=
  .tvar representation.existsTy
    (.var (Telescope.pack arguments) (Telescope.pack_hasType arguments)
      (.cvar (.refl representation.existsTy) (by
        rw [Single.identityAtPayload_open,
          representationAtPayload_open]
        exact Co.HasType.refl) .nil))

noncomputable def exactPackage {sig : Sig} {base : Ctx sig}
    (representation : Telescope sig)
    (arguments : Telescope.Args base representation) : Exp sig :=
  (plan representation).pack (exactArguments representation arguments)

noncomputable def exactPackage_hasType {sig : Sig} {base : Ctx sig}
    (representation : Telescope sig)
    (arguments : Telescope.Args base representation) :
    Exp.HasType base (exactPackage representation arguments)
      (plan representation).inputTy :=
  (plan representation).pack_hasType
    (exactArguments representation arguments)

/-- The retained first payload, weakened through a dependent suffix and then
transported to the literal append scope. -/
def firstPayload (first : ValuePlan sig)
    (suffix : Telescope first.scope) :
    Exp (first.telescope.append suffix).scope :=
  fromSuffixExp first.telescope suffix
    (first.payload.rename suffix.weaken)

def firstIdentityTy (first : ValuePlan sig)
    (suffix : Telescope first.scope) :
    Ty (first.telescope.append suffix).scope :=
  fromSuffixTy first.telescope suffix
    (first.identityTy.rename suffix.weaken)

/-- Untransported accessor used directly in the nested suffix context. -/
def firstPayloadAtSuffix (first : ValuePlan sig)
    (suffix : Telescope first.scope) : Exp suffix.scope :=
  first.payload.rename suffix.weaken

def firstIdentityAtSuffix (first : ValuePlan sig)
    (suffix : Telescope first.scope) : Ty suffix.scope :=
  first.identityTy.rename suffix.weaken

noncomputable def firstPayloadAtSuffix_hasType (first : ValuePlan sig)
    (suffix : Telescope first.scope) (base : Ctx sig) :
    Exp.HasType (suffix.context (first.context base))
      (firstPayloadAtSuffix first suffix)
      (firstIdentityAtSuffix first suffix) :=
  weakenExp_hasType suffix (first.payload_hasType base)

end Pair

namespace Pair.Proper

/-- The proper-member plan after reindexing the first interface. -/
def renameMember (first : ValuePlan source)
    (member : ValuePlan first.scope) (mapping : Rename source target) :
    ValuePlan (first.rename mapping).scope :=
  member.rename (first.telescope.liftRename mapping)

def substMember (first : ValuePlan source)
    (member : ValuePlan first.scope) (substitution : Subst source target) :
    ValuePlan (first.subst substitution).scope :=
  member.subst (first.telescope.liftSubst substitution)

/-- Proper pair representation: the retained first interface followed by the
dependent member interface. -/
def representation (first : ValuePlan sig)
    (member : ValuePlan first.scope) : Telescope sig :=
  first.telescope.append member.telescope

def plan (first : ValuePlan sig) (member : ValuePlan first.scope) :
    ValuePlan sig :=
  Pair.plan (representation first member)

theorem representation_rename (first : ValuePlan source)
    (member : ValuePlan first.scope) (mapping : Rename source target) :
    (representation first member).rename mapping =
      representation (first.rename mapping)
        (renameMember first member mapping) := by
  unfold representation renameMember
  rw [Telescope.append_rename]
  rfl

theorem representation_subst (first : ValuePlan source)
    (member : ValuePlan first.scope) (substitution : Subst source target) :
    (representation first member).subst substitution =
      representation (first.subst substitution)
        (substMember first member substitution) := by
  unfold representation substMember
  rw [Telescope.append_subst]
  rfl

  theorem plan_rename (first : ValuePlan source)
    (member : ValuePlan first.scope) (mapping : Rename source target) :
    (plan first member).rename mapping =
      plan (first.rename mapping) (renameMember first member mapping) := by
  unfold plan
  rw [Pair.plan_rename, representation_rename]

theorem plan_subst (first : ValuePlan source)
    (member : ValuePlan first.scope) (substitution : Subst source target) :
    (plan first member).subst substitution =
      plan (first.subst substitution)
        (substMember first member substitution) := by
  unfold plan
  rw [Pair.plan_subst, representation_subst]

/-- First and member payload projections in the nested representation
context. The first projection is explicitly weakened through the member
interface; the second is the member plan's stable payload. -/
def firstValue (first : ValuePlan sig) (member : ValuePlan first.scope) :
    Exp member.scope :=
  Pair.firstPayloadAtSuffix first member.telescope

def firstValueTy (first : ValuePlan sig) (member : ValuePlan first.scope) :
    Ty member.scope :=
  Pair.firstIdentityAtSuffix first member.telescope

noncomputable def firstValue_hasType (base : Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :
    Exp.HasType (member.context (first.context base))
      (firstValue first member) (firstValueTy first member) :=
  Pair.firstPayloadAtSuffix_hasType first member.telescope base

def memberValue (first : ValuePlan sig) (member : ValuePlan first.scope) :
    Exp member.scope :=
  member.payload

def memberValueTy (first : ValuePlan sig) (member : ValuePlan first.scope) :
    Ty member.scope :=
  member.identityTy

noncomputable def memberValue_hasType (base : Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) :
    Exp.HasType (member.context (first.context base))
      (memberValue first member) (memberValueTy first member) :=
  member.payload_hasType (first.context base)

/-- Literal-scope transports of the proper projections. -/
def firstValueAtRepresentation (first : ValuePlan sig)
    (member : ValuePlan first.scope) : Exp (representation first member).scope :=
  Pair.firstPayload first member.telescope

def memberValueAtRepresentation (first : ValuePlan sig)
    (member : ValuePlan first.scope) : Exp (representation first member).scope :=
  Pair.fromSuffixExp first.telescope member.telescope member.payload

theorem memberValue_rename (first : ValuePlan source)
    (member : ValuePlan first.scope) (mapping : Rename source target) :
    (memberValue first member).rename
        (member.telescope.liftRename
          (first.telescope.liftRename mapping)) =
      memberValue (first.rename mapping)
        (renameMember first member mapping) :=
  member.payload_rename (first.telescope.liftRename mapping)

theorem inputTy_rename (first : ValuePlan source)
    (member : ValuePlan first.scope) (mapping : Rename source target) :
    (plan first member).inputTy.rename mapping =
      (plan (first.rename mapping)
        (renameMember first member mapping)).inputTy := by
  unfold plan
  rw [Pair.inputTy_rename, representation_rename]

theorem inputTy_subst (first : ValuePlan source)
    (member : ValuePlan first.scope) (substitution : Subst source target) :
    (plan first member).inputTy.subst substitution =
      (plan (first.subst substitution)
        (substMember first member substitution)).inputTy := by
  unfold plan
  rw [Pair.inputTy_subst, representation_subst]

/-- Exact dependent representation fields. -/
noncomputable def representationArguments
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (member : ValuePlan first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (memberArguments : Telescope.Args base
      (member.telescope.subst firstArguments.substitution)) :
    Telescope.Args base (representation first member) :=
  firstArguments.append member.telescope memberArguments

noncomputable def exactArguments
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (member : ValuePlan first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (memberArguments : Telescope.Args base
      (member.telescope.subst firstArguments.substitution)) :
    Telescope.Args base (plan first member).telescope :=
  Pair.exactArguments (representation first member)
    (representationArguments first member firstArguments memberArguments)

noncomputable def exactPackage
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (member : ValuePlan first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (memberArguments : Telescope.Args base
      (member.telescope.subst firstArguments.substitution)) : Exp sig :=
  Pair.exactPackage (representation first member)
    (representationArguments first member firstArguments memberArguments)

noncomputable def exactPackage_hasType
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (member : ValuePlan first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (memberArguments : Telescope.Args base
      (member.telescope.subst firstArguments.substitution)) :
    Exp.HasType base
      (exactPackage first member firstArguments memberArguments)
      (plan first member).inputTy :=
  Pair.exactPackage_hasType (representation first member)
    (representationArguments first member firstArguments memberArguments)

/-- Exact proper/value-pair introduction. The member arguments are indexed by
the precise substitution chosen by the first interface. -/
noncomputable def exactValuePair
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (member : ValuePlan first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (memberArguments : Telescope.Args base
      (member.telescope.subst firstArguments.substitution)) : Exp sig :=
  exactPackage first member firstArguments memberArguments

noncomputable def exactValuePair_hasType
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (member : ValuePlan first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (memberArguments : Telescope.Args base
      (member.telescope.subst firstArguments.substitution)) :
    Exp.HasType base
      (exactValuePair first member firstArguments memberArguments)
      (plan first member).inputTy :=
  exactPackage_hasType first member firstArguments memberArguments

end Pair.Proper

namespace Pair.Interval

/-- The interval member hidden after the retained first interface. The middle
type is not the raw witness representation `X`, but its opaque selection
package, so the stored bound evidence is computational. -/
def memberTail (lower upper : Ty sig) : Telescope (sig ,, .tvar) :=
  .cvar (lower.weaken .tvar)
    (Selection.plan (.tvar .here)).inputTy
    (.cvar
      ((Selection.plan (.tvar .here)).inputTy.weaken .cvar)
      ((upper.weaken .tvar).weaken .cvar) .nil)

def memberTelescope (lower upper : Ty sig) : Telescope sig :=
  .tvar (memberTail lower upper)

def openedMember (lower upper witnessRepresentation : Ty sig) :
    Telescope sig :=
  .cvar lower (Selection.plan witnessRepresentation).inputTy
    (.cvar ((Selection.plan witnessRepresentation).inputTy.weaken .cvar)
      (upper.weaken .cvar) .nil)

theorem memberTail_open (lower upper witnessRepresentation : Ty sig) :
    (memberTail lower upper).subst
        (Subst.openTVar witnessRepresentation) =
      openedMember lower upper witnessRepresentation := by
  unfold memberTail openedMember
  simp only [Telescope.subst]
  rw [lower.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openTVar witnessRepresentation)]
  rw [Selection.inputTy_subst]
  change Telescope.cvar lower (Selection.plan witnessRepresentation).inputTy
    (Telescope.cvar
      (((Selection.plan (.tvar .here)).inputTy.weaken .cvar).subst
        ((Subst.openTVar witnessRepresentation).lift .cvar))
      (((upper.weaken .tvar).weaken .cvar).subst
        ((Subst.openTVar witnessRepresentation).lift .cvar)) .nil) = _
  rw [← Ty.weaken_subst_comm_base, Selection.inputTy_subst]
  rw [← Ty.weaken_subst_comm_base]
  rw [upper.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openTVar witnessRepresentation)]
  rfl

theorem openedTail_open (upper witnessRepresentation : Ty sig)
    (evidence : Co sig) :
    (Telescope.cvar
      ((Selection.plan witnessRepresentation).inputTy.weaken .cvar)
      (upper.weaken .cvar) .nil).subst (Subst.openCVar evidence) =
      Telescope.cvar (Selection.plan witnessRepresentation).inputTy
        upper .nil := by
  simp only [Telescope.subst]
  rw [(Selection.plan witnessRepresentation).inputTy.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openCVar evidence)]
  rw [upper.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openCVar evidence)]

theorem memberTelescope_rename (lower upper : Ty source)
    (mapping : Rename source target) :
    (memberTelescope lower upper).rename mapping =
      memberTelescope (lower.rename mapping) (upper.rename mapping) := by
  unfold memberTelescope memberTail
  simp only [Telescope.rename]
  rw [Ty.weaken_rename_comm, Selection.inputTy_rename,
    Ty.weaken_rename_comm, Selection.inputTy_rename,
    Ty.weaken_rename_comm, Ty.weaken_rename_comm]
  rfl

theorem memberTelescope_subst (lower upper : Ty source)
    (substitution : Subst source target) :
    (memberTelescope lower upper).subst substitution =
      memberTelescope (lower.subst substitution)
        (upper.subst substitution) := by
  unfold memberTelescope memberTail
  simp only [Telescope.subst]
  rw [← Ty.weaken_subst_comm_base, Selection.inputTy_subst,
    ← Ty.weaken_subst_comm_base, Selection.inputTy_subst,
    ← Ty.weaken_subst_comm_base, ← Ty.weaken_subst_comm_base]
  rfl

/-- Interval pair representation: retained first interface followed by the
hidden witness representation and its two bound adapters. -/
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

/-- Projections in the final interval-member scope. -/
def witnessRepresentation (lower upper : Ty sig) :
    Ty (memberTelescope lower upper).scope :=
  .tvar (.there (.there .here))

def lowerTy (lower upper : Ty sig) :
    Ty (memberTelescope lower upper).scope :=
  ((lower.weaken .tvar).weaken .cvar).weaken .cvar

def selectedTy (lower upper : Ty sig) :
    Ty (memberTelescope lower upper).scope :=
  (((Selection.plan (.tvar .here)).inputTy.weaken .cvar).weaken .cvar)

def upperTy (lower upper : Ty sig) :
    Ty (memberTelescope lower upper).scope :=
  ((upper.weaken .tvar).weaken .cvar).weaken .cvar

def lowerAdapter (lower upper : Ty sig) :
    Co (memberTelescope lower upper).scope :=
  .cvar (.there .here)

def upperAdapter (lower upper : Ty sig) :
    Co (memberTelescope lower upper).scope :=
  .cvar .here

noncomputable def lowerAdapter_hasType (base : Ctx sig)
    (lower upper : Ty sig) :
    Co.HasType ((memberTelescope lower upper).context base)
      (lowerAdapter lower upper) (lowerTy lower upper)
      (selectedTy lower upper) :=
  .cvar (Ctx.Lookup.there Ctx.Lookup.here)

noncomputable def upperAdapter_hasType (base : Ctx sig)
    (lower upper : Ty sig) :
    Co.HasType ((memberTelescope lower upper).context base)
      (upperAdapter lower upper) (selectedTy lower upper)
      (upperTy lower upper) :=
  .cvar Ctx.Lookup.here

theorem witnessRepresentation_rename (lower upper : Ty source)
    (mapping : Rename source target) :
    (witnessRepresentation lower upper).rename
        ((memberTelescope lower upper).liftRename mapping) =
      witnessRepresentation (lower.rename mapping) (upper.rename mapping) := by
  rfl

theorem witnessRepresentation_subst (lower upper : Ty source)
    (substitution : Subst source target) :
    (witnessRepresentation lower upper).subst
        ((memberTelescope lower upper).liftSubst substitution) =
      witnessRepresentation (lower.subst substitution)
        (upper.subst substitution) := by
  rfl

theorem lowerTy_rename (lower upper : Ty source)
    (mapping : Rename source target) :
    (lowerTy lower upper).rename
        ((memberTelescope lower upper).liftRename mapping) =
      lowerTy (lower.rename mapping) (upper.rename mapping) := by
  unfold lowerTy memberTelescope memberTail
  simp only [Telescope.liftRename]
  calc
    (((lower.weaken .tvar).weaken .cvar).weaken .cvar).rename
        (((mapping.lift .tvar).lift .cvar).lift .cvar) =
      (((lower.weaken .tvar).weaken .cvar).rename
        ((mapping.lift .tvar).lift .cvar)).weaken .cvar :=
      Ty.weaken_rename_comm _ _
    _ = (((lower.weaken .tvar).rename (mapping.lift .tvar)).weaken
        .cvar).weaken .cvar :=
      congrArg (fun type : Ty ((target ,, .tvar) ,, .cvar) =>
        type.weaken .cvar)
        (Ty.weaken_rename_comm _ _)
    _ = (((lower.rename mapping).weaken .tvar).weaken .cvar).weaken
        .cvar :=
      congrArg (fun type : Ty (target ,, .tvar) =>
        (type.weaken .cvar).weaken .cvar)
        (Ty.weaken_rename_comm _ _)

theorem lowerTy_subst (lower upper : Ty source)
    (substitution : Subst source target) :
    (lowerTy lower upper).subst
        ((memberTelescope lower upper).liftSubst substitution) =
      lowerTy (lower.subst substitution) (upper.subst substitution) := by
  unfold lowerTy memberTelescope memberTail
  simp only [Telescope.liftSubst]
  calc
    (((lower.weaken .tvar).weaken .cvar).weaken .cvar).subst
        (((substitution.lift .tvar).lift .cvar).lift .cvar) =
      (((lower.weaken .tvar).weaken .cvar).subst
        ((substitution.lift .tvar).lift .cvar)).weaken .cvar :=
      (Ty.weaken_subst_comm_base _ _).symm
    _ = (((lower.weaken .tvar).subst
        (substitution.lift .tvar)).weaken .cvar).weaken .cvar :=
      congrArg (fun type : Ty ((target ,, .tvar) ,, .cvar) =>
        type.weaken .cvar)
        (Ty.weaken_subst_comm_base _ _).symm
    _ = (((lower.subst substitution).weaken .tvar).weaken .cvar).weaken
        .cvar :=
      congrArg (fun type : Ty (target ,, .tvar) =>
        (type.weaken .cvar).weaken .cvar)
        (Ty.weaken_subst_comm_base _ _).symm

theorem selectedTy_rename (lower upper : Ty source)
    (mapping : Rename source target) :
    (selectedTy lower upper).rename
        ((memberTelescope lower upper).liftRename mapping) =
      selectedTy (lower.rename mapping) (upper.rename mapping) := by
  rfl

theorem selectedTy_subst (lower upper : Ty source)
    (substitution : Subst source target) :
    (selectedTy lower upper).subst
        ((memberTelescope lower upper).liftSubst substitution) =
      selectedTy (lower.subst substitution) (upper.subst substitution) := by
  rfl

theorem upperTy_rename (lower upper : Ty source)
    (mapping : Rename source target) :
    (upperTy lower upper).rename
        ((memberTelescope lower upper).liftRename mapping) =
      upperTy (lower.rename mapping) (upper.rename mapping) := by
  unfold upperTy memberTelescope memberTail
  simp only [Telescope.liftRename]
  calc
    (((upper.weaken .tvar).weaken .cvar).weaken .cvar).rename
        (((mapping.lift .tvar).lift .cvar).lift .cvar) =
      (((upper.weaken .tvar).weaken .cvar).rename
        ((mapping.lift .tvar).lift .cvar)).weaken .cvar :=
      Ty.weaken_rename_comm _ _
    _ = (((upper.weaken .tvar).rename (mapping.lift .tvar)).weaken
        .cvar).weaken .cvar :=
      congrArg (fun type : Ty ((target ,, .tvar) ,, .cvar) =>
        type.weaken .cvar)
        (Ty.weaken_rename_comm _ _)
    _ = (((upper.rename mapping).weaken .tvar).weaken .cvar).weaken
        .cvar :=
      congrArg (fun type : Ty (target ,, .tvar) =>
        (type.weaken .cvar).weaken .cvar)
        (Ty.weaken_rename_comm _ _)

theorem upperTy_subst (lower upper : Ty source)
    (substitution : Subst source target) :
    (upperTy lower upper).subst
        ((memberTelescope lower upper).liftSubst substitution) =
      upperTy (lower.subst substitution) (upper.subst substitution) := by
  unfold upperTy memberTelescope memberTail
  simp only [Telescope.liftSubst]
  calc
    (((upper.weaken .tvar).weaken .cvar).weaken .cvar).subst
        (((substitution.lift .tvar).lift .cvar).lift .cvar) =
      (((upper.weaken .tvar).weaken .cvar).subst
        ((substitution.lift .tvar).lift .cvar)).weaken .cvar :=
      (Ty.weaken_subst_comm_base _ _).symm
    _ = (((upper.weaken .tvar).subst
        (substitution.lift .tvar)).weaken .cvar).weaken .cvar :=
      congrArg (fun type : Ty ((target ,, .tvar) ,, .cvar) =>
        type.weaken .cvar)
        (Ty.weaken_subst_comm_base _ _).symm
    _ = (((upper.subst substitution).weaken .tvar).weaken .cvar).weaken
        .cvar :=
      congrArg (fun type : Ty (target ,, .tvar) =>
        (type.weaken .cvar).weaken .cvar)
        (Ty.weaken_subst_comm_base _ _).symm

theorem lowerAdapter_rename (lower upper : Ty source)
    (mapping : Rename source target) :
    (lowerAdapter lower upper).rename
        ((memberTelescope lower upper).liftRename mapping) =
      lowerAdapter (lower.rename mapping) (upper.rename mapping) := by
  rfl

theorem lowerAdapter_subst (lower upper : Ty source)
    (substitution : Subst source target) :
    (lowerAdapter lower upper).subst
        ((memberTelescope lower upper).liftSubst substitution) =
      lowerAdapter (lower.subst substitution) (upper.subst substitution) := by
  rfl

theorem upperAdapter_rename (lower upper : Ty source)
    (mapping : Rename source target) :
    (upperAdapter lower upper).rename
        ((memberTelescope lower upper).liftRename mapping) =
      upperAdapter (lower.rename mapping) (upper.rename mapping) := by
  rfl

theorem upperAdapter_subst (lower upper : Ty source)
    (substitution : Subst source target) :
    (upperAdapter lower upper).subst
        ((memberTelescope lower upper).liftSubst substitution) =
      upperAdapter (lower.subst substitution) (upper.subst substitution) := by
  rfl

/-- The middle selected type is exactly the opaque selection plan at the
hidden final-scope witness representation. -/
  theorem selectedTy_eq (lower upper : Ty sig) :
    selectedTy lower upper =
      (Selection.plan (witnessRepresentation lower upper)).inputTy := by
  unfold selectedTy witnessRepresentation memberTelescope memberTail
  unfold Ty.weaken
  rw [Selection.inputTy_rename, Selection.inputTy_rename]
  rfl

/-- The complete stable selection interface available after applying the
stored lower adapter. Higher path compilation can unpack this plan, retain its
hidden identity and payload, and repack it after contextual reindexing. -/
def selectedPlan (lower upper : Ty sig) :
    ValuePlan (memberTelescope lower upper).scope :=
  Selection.plan (witnessRepresentation lower upper)

theorem selectedPlan_inputTy (lower upper : Ty sig) :
    (selectedPlan lower upper).inputTy = selectedTy lower upper :=
  (selectedTy_eq lower upper).symm

theorem selectedPlan_rename (lower upper : Ty source)
    (mapping : Rename source target) :
    (selectedPlan lower upper).rename
        ((memberTelescope lower upper).liftRename mapping) =
      selectedPlan (lower.rename mapping) (upper.rename mapping) := by
  unfold selectedPlan
  rw [Selection.plan_rename, witnessRepresentation_rename]
  rfl

theorem selectedPlan_subst (lower upper : Ty source)
    (substitution : Subst source target) :
    (selectedPlan lower upper).subst
        ((memberTelescope lower upper).liftSubst substitution) =
      selectedPlan (lower.subst substitution) (upper.subst substitution) := by
  unfold selectedPlan
  rw [Selection.plan_subst, witnessRepresentation_subst]
  rfl

def selectedIdentityTy (lower upper : Ty sig) :
    Ty (selectedPlan lower upper).scope :=
  (selectedPlan lower upper).identityTy

def selectedPayload (lower upper : Ty sig) :
    Exp (selectedPlan lower upper).scope :=
  (selectedPlan lower upper).payload

def selectedToWitness (lower upper : Ty sig) :
    Co (selectedPlan lower upper).scope :=
  Selection.toWitness (witnessRepresentation lower upper)

def selectedFromWitness (lower upper : Ty sig) :
    Co (selectedPlan lower upper).scope :=
  Selection.fromWitness (witnessRepresentation lower upper)

noncomputable def selectedPayload_hasType (base : Ctx sig)
    (lower upper : Ty sig) :
    Exp.HasType
      ((selectedPlan lower upper).context
        ((memberTelescope lower upper).context base))
      (selectedPayload lower upper) (selectedIdentityTy lower upper) :=
  (selectedPlan lower upper).payload_hasType
    ((memberTelescope lower upper).context base)

noncomputable def selectedToWitness_hasType (base : Ctx sig)
    (lower upper : Ty sig) :
    Co.HasType
      ((selectedPlan lower upper).context
        ((memberTelescope lower upper).context base))
      (selectedToWitness lower upper) (selectedIdentityTy lower upper)
      (Selection.witnessTy (witnessRepresentation lower upper)) :=
  Selection.toWitness_hasType
    ((memberTelescope lower upper).context base)
    (witnessRepresentation lower upper)

noncomputable def selectedFromWitness_hasType (base : Ctx sig)
    (lower upper : Ty sig) :
    Co.HasType
      ((selectedPlan lower upper).context
        ((memberTelescope lower upper).context base))
      (selectedFromWitness lower upper)
      (Selection.witnessTy (witnessRepresentation lower upper))
      (selectedIdentityTy lower upper) :=
  Selection.fromWitness_hasType
    ((memberTelescope lower upper).context base)
    (witnessRepresentation lower upper)

noncomputable def repackSelected {sig : Sig} {base : Ctx sig}
    (lower upper : Ty sig)
    (arguments : Telescope.Args ((memberTelescope lower upper).context base)
      (selectedPlan lower upper).telescope) :
    Exp (memberTelescope lower upper).scope :=
  (selectedPlan lower upper).pack arguments

noncomputable def repackSelected_hasType {sig : Sig} {base : Ctx sig}
    (lower upper : Ty sig)
    (arguments : Telescope.Args ((memberTelescope lower upper).context base)
      (selectedPlan lower upper).telescope) :
    Exp.HasType ((memberTelescope lower upper).context base)
      (repackSelected lower upper arguments) (selectedTy lower upper) := by
  rw [← selectedPlan_inputTy]
  exact (selectedPlan lower upper).pack_hasType arguments

/-- Literal representation-scope versions of the first value and interval
member projections. -/
def firstValueAtRepresentation (first : ValuePlan sig)
    (lower upper : Ty first.scope) :
    Exp (representation first lower upper).scope :=
  Pair.firstPayload first (memberTelescope lower upper)

def witnessAtRepresentation (first : ValuePlan sig)
    (lower upper : Ty first.scope) :
    Ty (representation first lower upper).scope :=
  Pair.fromSuffixTy first.telescope (memberTelescope lower upper)
    (witnessRepresentation lower upper)

def lowerAdapterAtRepresentation (first : ValuePlan sig)
    (lower upper : Ty first.scope) :
    Co (representation first lower upper).scope :=
  Pair.fromSuffixCo first.telescope (memberTelescope lower upper)
    (lowerAdapter lower upper)

def upperAdapterAtRepresentation (first : ValuePlan sig)
    (lower upper : Ty first.scope) :
    Co (representation first lower upper).scope :=
  Pair.fromSuffixCo first.telescope (memberTelescope lower upper)
    (upperAdapter lower upper)

theorem inputTy_rename (first : ValuePlan source)
    (lower upper : Ty first.scope) (mapping : Rename source target) :
    (plan first lower upper).inputTy.rename mapping =
      (plan (first.rename mapping)
        (lower.rename (first.telescope.liftRename mapping))
        (upper.rename (first.telescope.liftRename mapping))).inputTy := by
  unfold plan
  rw [Pair.inputTy_rename, representation_rename]

theorem inputTy_subst (first : ValuePlan source)
    (lower upper : Ty first.scope) (substitution : Subst source target) :
    (plan first lower upper).inputTy.subst substitution =
      (plan (first.subst substitution)
        (lower.subst (first.telescope.liftSubst substitution))
        (upper.subst (first.telescope.liftSubst substitution))).inputTy := by
  unfold plan
  rw [Pair.inputTy_subst, representation_subst]

/-- Core interval fields. The caller supplies package-level computational
adapters, so a higher compiler can preserve the lower package's hidden stable
identity and payload while reindexing it to the selected representation. -/
noncomputable def openedArgumentsWithAdapters
    {sig : Sig} (base : Ctx sig)
    (lower upper witnessRepresentation : Ty sig)
    (lowerPackageEvidence : Co sig)
    (lowerPackageTyping : Co.HasType base lowerPackageEvidence lower
      (Selection.plan witnessRepresentation).inputTy)
    (upperPackageEvidence : Co sig)
    (upperPackageTyping : Co.HasType base upperPackageEvidence
      (Selection.plan witnessRepresentation).inputTy upper) :
    Telescope.Args base (openedMember lower upper witnessRepresentation) := by
  refine .cvar lowerPackageEvidence lowerPackageTyping ?_
  exact (openedTail_open upper witnessRepresentation
      lowerPackageEvidence).symm ▸
    (.cvar upperPackageEvidence upperPackageTyping .nil)

noncomputable def memberArgumentsWithAdapters
    {sig : Sig} (base : Ctx sig)
    (lower upper witnessRepresentation : Ty sig)
    (lowerPackageEvidence : Co sig)
    (lowerPackageTyping : Co.HasType base lowerPackageEvidence lower
      (Selection.plan witnessRepresentation).inputTy)
    (upperPackageEvidence : Co sig)
    (upperPackageTyping : Co.HasType base upperPackageEvidence
      (Selection.plan witnessRepresentation).inputTy upper) :
    Telescope.Args base (memberTelescope lower upper) :=
  .tvar witnessRepresentation
    ((memberTail_open lower upper witnessRepresentation).symm ▸
      openedArgumentsWithAdapters base lower upper witnessRepresentation
        lowerPackageEvidence lowerPackageTyping upperPackageEvidence
        upperPackageTyping)

/-- Exact interval representation fields, indexed by the precise first
interface substitution. No well-formedness evidence for either endpoint is
needed. -/
noncomputable def representationArgumentsWithAdapters
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (lower upper : Ty first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (witnessRepresentation : Ty sig)
    (lowerPackageEvidence : Co sig)
    (lowerPackageTyping : Co.HasType base lowerPackageEvidence
      (lower.subst firstArguments.substitution)
      (Selection.plan witnessRepresentation).inputTy)
    (upperPackageEvidence : Co sig)
    (upperPackageTyping : Co.HasType base upperPackageEvidence
      (Selection.plan witnessRepresentation).inputTy
      (upper.subst firstArguments.substitution)) :
    Telescope.Args base (representation first lower upper) := by
  let supplied := memberArgumentsWithAdapters base
    (lower.subst firstArguments.substitution)
    (upper.subst firstArguments.substitution) witnessRepresentation
    lowerPackageEvidence lowerPackageTyping upperPackageEvidence
    upperPackageTyping
  have reindexed := memberTelescope_subst lower upper
    firstArguments.substitution
  exact firstArguments.append (memberTelescope lower upper)
    (reindexed.symm ▸ supplied)

noncomputable def exactArgumentsWithAdapters
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (lower upper : Ty first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (witnessRepresentation : Ty sig)
    (lowerPackageEvidence : Co sig)
    (lowerPackageTyping : Co.HasType base lowerPackageEvidence
      (lower.subst firstArguments.substitution)
      (Selection.plan witnessRepresentation).inputTy)
    (upperPackageEvidence : Co sig)
    (upperPackageTyping : Co.HasType base upperPackageEvidence
      (Selection.plan witnessRepresentation).inputTy
      (upper.subst firstArguments.substitution)) :
    Telescope.Args base (plan first lower upper).telescope :=
  Pair.exactArguments (representation first lower upper)
    (representationArgumentsWithAdapters first lower upper firstArguments
      witnessRepresentation lowerPackageEvidence lowerPackageTyping
      upperPackageEvidence upperPackageTyping)

/-- High-level exact interval introduction. Both adapters operate on complete
stable packages; no fixed low-level choice of hidden identity is imposed. -/
noncomputable def exactWithAdapters
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (lower upper : Ty first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (witnessRepresentation : Ty sig)
    (lowerPackageEvidence : Co sig)
    (lowerPackageTyping : Co.HasType base lowerPackageEvidence
      (lower.subst firstArguments.substitution)
      (Selection.plan witnessRepresentation).inputTy)
    (upperPackageEvidence : Co sig)
    (upperPackageTyping : Co.HasType base upperPackageEvidence
      (Selection.plan witnessRepresentation).inputTy
      (upper.subst firstArguments.substitution)) : Exp sig :=
  Pair.exactPackage (representation first lower upper)
    (representationArgumentsWithAdapters first lower upper firstArguments
      witnessRepresentation lowerPackageEvidence lowerPackageTyping
      upperPackageEvidence upperPackageTyping)

noncomputable def exactWithAdapters_hasType
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (lower upper : Ty first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (witnessRepresentation : Ty sig)
    (lowerPackageEvidence : Co sig)
    (lowerPackageTyping : Co.HasType base lowerPackageEvidence
      (lower.subst firstArguments.substitution)
      (Selection.plan witnessRepresentation).inputTy)
    (upperPackageEvidence : Co sig)
    (upperPackageTyping : Co.HasType base upperPackageEvidence
      (Selection.plan witnessRepresentation).inputTy
      (upper.subst firstArguments.substitution)) :
    Exp.HasType base
      (exactWithAdapters first lower upper firstArguments
        witnessRepresentation lowerPackageEvidence lowerPackageTyping
        upperPackageEvidence upperPackageTyping)
      (plan first lower upper).inputTy :=
  Pair.exactPackage_hasType (representation first lower upper)
    (representationArgumentsWithAdapters first lower upper firstArguments
      witnessRepresentation lowerPackageEvidence lowerPackageTyping
      upperPackageEvidence upperPackageTyping)

/-- Explicitly low-level convenience: raw lower-to-representation and
representation-to-upper evidence is wrapped through `Selection.wrap/unwrap`.
This does not promise contextual stable-identity alignment. -/
noncomputable def representationArgumentsFromWitnessEvidence
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (lower upper : Ty first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (witnessRepresentation : Ty sig)
    (lowerEvidence : Co sig)
    (lowerTyping : Co.HasType base lowerEvidence
      (lower.subst firstArguments.substitution) witnessRepresentation)
    (upperEvidence : Co sig)
    (upperTyping : Co.HasType base upperEvidence witnessRepresentation
      (upper.subst firstArguments.substitution)) :
    Telescope.Args base (representation first lower upper) :=
  representationArgumentsWithAdapters first lower upper firstArguments
    witnessRepresentation
    (Selection.lowerToPackage base witnessRepresentation lowerEvidence)
    (Selection.lowerToPackage_hasType base witnessRepresentation
      (lower.subst firstArguments.substitution) lowerEvidence lowerTyping)
    (Selection.packageToUpper witnessRepresentation upperEvidence)
    (Selection.packageToUpper_hasType base witnessRepresentation
      (upper.subst firstArguments.substitution) upperEvidence upperTyping)

noncomputable def packageFromWitnessEvidence
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (lower upper : Ty first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (witnessRepresentation : Ty sig)
    (lowerEvidence : Co sig)
    (lowerTyping : Co.HasType base lowerEvidence
      (lower.subst firstArguments.substitution) witnessRepresentation)
    (upperEvidence : Co sig)
    (upperTyping : Co.HasType base upperEvidence witnessRepresentation
      (upper.subst firstArguments.substitution)) : Exp sig :=
  Pair.exactPackage (representation first lower upper)
    (representationArgumentsFromWitnessEvidence first lower upper
      firstArguments witnessRepresentation lowerEvidence lowerTyping
      upperEvidence upperTyping)

noncomputable def packageFromWitnessEvidence_hasType
    {sig : Sig} {base : Ctx sig}
    (first : ValuePlan sig) (lower upper : Ty first.scope)
    (firstArguments : Telescope.Args base first.telescope)
    (witnessRepresentation : Ty sig)
    (lowerEvidence : Co sig)
    (lowerTyping : Co.HasType base lowerEvidence
      (lower.subst firstArguments.substitution) witnessRepresentation)
    (upperEvidence : Co sig)
    (upperTyping : Co.HasType base upperEvidence witnessRepresentation
      (upper.subst firstArguments.substitution)) :
    Exp.HasType base
      (packageFromWitnessEvidence first lower upper firstArguments
        witnessRepresentation lowerEvidence lowerTyping upperEvidence
        upperTyping)
      (plan first lower upper).inputTy :=
  Pair.exactPackage_hasType (representation first lower upper)
    (representationArgumentsFromWitnessEvidence first lower upper
      firstArguments witnessRepresentation lowerEvidence lowerTyping
      upperEvidence upperTyping)

/-- Exact interval/type-pair introduction through caller-supplied stable
package adapters. -/
noncomputable def exactTypePair := @exactWithAdapters

noncomputable def exactTypePair_hasType := @exactWithAdapters_hasType

end Pair.Interval

/-! A closed dependent regression. The proper member and both interval bounds
refer to the first plan's hidden identity. Supplying `I = Top` must reindex all
of them through the exact first-argument substitution. -/

namespace PairRegression

def first : ValuePlan ([] : Sig) := Top.plan []

def dependentMember : ValuePlan first.scope :=
  Single.plan first.identityTy

noncomputable def firstArguments :
    Telescope.Args Ctx.empty first.telescope :=
  Top.arguments .top AtomicRegression.topPayload
    AtomicRegression.topPayload_hasType

theorem dependentMember_opens :
    dependentMember.telescope.subst firstArguments.substitution =
      (Single.plan (.top : Ty ([] : Sig))).telescope := by
  rfl

noncomputable def memberArguments :
    Telescope.Args Ctx.empty
      (dependentMember.telescope.subst firstArguments.substitution) :=
  dependentMember_opens.symm ▸
    Single.exactArguments .top AtomicRegression.topPayload
      AtomicRegression.topPayload_hasType

noncomputable def exactValuePair : Exp ([] : Sig) :=
  Pair.Proper.exactValuePair first dependentMember firstArguments
    memberArguments

noncomputable def exactValuePair_hasType :
    Exp.HasType Ctx.empty exactValuePair
      (Pair.Proper.plan first dependentMember).inputTy :=
  Pair.Proper.exactValuePair_hasType first dependentMember firstArguments
    memberArguments

def lower : Ty first.scope := first.identityTy

def upper : Ty first.scope := first.identityTy

theorem lower_opens :
    lower.subst firstArguments.substitution = (.top : Ty ([] : Sig)) := by
  rfl

theorem upper_opens :
    upper.subst firstArguments.substitution = (.top : Ty ([] : Sig)) := by
  rfl

noncomputable def lowerTyping :
    Co.HasType Ctx.empty (.refl .top)
      (lower.subst firstArguments.substitution) .top :=
  lower_opens.symm ▸ Co.HasType.refl

noncomputable def upperTyping :
    Co.HasType Ctx.empty (.refl .top) .top
      (upper.subst firstArguments.substitution) :=
  upper_opens.symm ▸ Co.HasType.refl

noncomputable def lowerPackageEvidence : Co ([] : Sig) :=
  Selection.lowerToPackage Ctx.empty (.top : Ty ([] : Sig)) (.refl .top)

noncomputable def lowerPackageTyping :
    Co.HasType Ctx.empty lowerPackageEvidence
      (lower.subst firstArguments.substitution)
      (Selection.plan (.top : Ty ([] : Sig))).inputTy := by
  rw [lower_opens]
  exact Selection.lowerToPackage_hasType Ctx.empty .top .top (.refl .top)
    Co.HasType.refl

def upperPackageEvidence : Co ([] : Sig) :=
  Selection.packageToUpper (.top : Ty ([] : Sig)) (.refl .top)

noncomputable def upperPackageTyping :
    Co.HasType Ctx.empty upperPackageEvidence
      (Selection.plan (.top : Ty ([] : Sig))).inputTy
      (upper.subst firstArguments.substitution) := by
  rw [upper_opens]
  exact Selection.packageToUpper_hasType Ctx.empty .top .top (.refl .top)
    Co.HasType.refl

noncomputable def exactTypePair : Exp ([] : Sig) :=
  Pair.Interval.exactTypePair first lower upper firstArguments .top
    lowerPackageEvidence lowerPackageTyping upperPackageEvidence
    upperPackageTyping

noncomputable def exactTypePair_hasType :
    Exp.HasType Ctx.empty exactTypePair
      (Pair.Interval.plan first lower upper).inputTy :=
  Pair.Interval.exactTypePair_hasType first lower upper firstArguments .top
    lowerPackageEvidence lowerPackageTyping upperPackageEvidence
    upperPackageTyping

end PairRegression

end LambdaPToFCo.Full
