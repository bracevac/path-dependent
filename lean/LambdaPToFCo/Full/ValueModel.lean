import SystemFCoExt.Telescope

/-!
# Stable-identity target value plans

This file is target-only. A plan always hides an identity type `I`, then a
payload `i : I`, before introducing any type-specific observations.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

/-- Weaken a typed expression through every field of a target telescope. -/
noncomputable def weakenExp_hasType
    (tele : Telescope sig) {base : Ctx sig} {expression : Exp sig}
    {type : Ty sig} (typing : Exp.HasType base expression type) :
    Exp.HasType (tele.context base) (expression.rename tele.weaken)
      (type.rename tele.weaken) := by
  induction tele with
  | nil =>
      change Exp.HasType base (expression.rename Rename.id)
        (type.rename Rename.id)
      rw [Exp.rename_id, Ty.rename_id]
      exact typing
  | var parameter tail ih =>
      have first := typing.weaken (.var parameter)
      have rest := ih first
      simpa only [Telescope.context, Telescope.weaken,
        Exp.weaken, Ty.weaken, Exp.rename_comp, Ty.rename_comp] using rest
  | tvar tail ih =>
      have first := typing.weaken .tvar
      have rest := ih first
      simpa only [Telescope.context, Telescope.weaken,
        Exp.weaken, Ty.weaken, Exp.rename_comp, Ty.rename_comp] using rest
  | cvar source target tail ih =>
      have first := typing.weaken (.cvar source target)
      have rest := ih first
      simpa only [Telescope.context, Telescope.weaken,
        Exp.weaken, Ty.weaken, Exp.rename_comp, Ty.rename_comp] using rest

/-! Church-existential naturality needed by value plans. -/

theorem existsHandler_rename (tele : Telescope source)
    (mapping : Rename source target) :
    tele.existsHandler.rename (mapping.lift .tvar) =
      (tele.rename mapping).existsHandler := by
  unfold Telescope.existsHandler
  rw [Telescope.handler_rename, tele.rename_comp,
    Rename.weaken_lift_comm, ← tele.rename_comp]
  rfl

theorem existsBody_rename (tele : Telescope source)
    (mapping : Rename source target) :
    tele.existsBody.rename (mapping.lift .tvar) =
      (tele.rename mapping).existsBody := by
  unfold Telescope.existsBody
  simp only [Ty.rename]
  rw [existsHandler_rename]
  rfl

theorem existsTy_rename (tele : Telescope source)
    (mapping : Rename source target) :
    tele.existsTy.rename mapping = (tele.rename mapping).existsTy := by
  unfold Telescope.existsTy
  simp only [Ty.rename]
  rw [existsBody_rename]

theorem existsHandler_subst (tele : Telescope source)
    (substitution : Subst source target) :
    tele.existsHandler.subst (substitution.lift .tvar) =
      (tele.subst substitution).existsHandler := by
  unfold Telescope.existsHandler
  rw [Telescope.handler_subst]
  rw [← tele.rename_subst_comm (substitution.weakenComm .tvar)]
  rfl

theorem existsBody_subst (tele : Telescope source)
    (substitution : Subst source target) :
    tele.existsBody.subst (substitution.lift .tvar) =
      (tele.subst substitution).existsBody := by
  unfold Telescope.existsBody
  simp only [Ty.subst]
  rw [existsHandler_subst]
  rfl

theorem existsTy_subst (tele : Telescope source)
    (substitution : Subst source target) :
    tele.existsTy.subst substitution = (tele.subst substitution).existsTy := by
  unfold Telescope.existsTy
  simp only [Ty.subst]
  rw [existsBody_subst]

/-- A target value interface. Observations are scoped after the mandatory
hidden identity type and its payload. -/
structure ValuePlan (sig : Sig) where
  observations : Telescope ((sig ,, .tvar) ,, .var)

namespace ValuePlan

/-- Hidden identity type as seen immediately after the payload binder. -/
def identityAtPayload (sig : Sig) : Ty ((sig ,, .tvar) ,, .var) :=
  (.tvar .here : Ty (sig ,, .tvar)).weaken .var

/-- Complete interface telescope: `I`, `i : I`, then observations. -/
def telescope (plan : ValuePlan sig) : Telescope sig :=
  .tvar (.var (.tvar .here) plan.observations)

def scope (plan : ValuePlan sig) : Sig :=
  plan.telescope.scope

def context (plan : ValuePlan sig) (base : Ctx sig) : Ctx plan.scope :=
  plan.telescope.context base

/-- Stable hidden identity in the final interface scope. -/
def identityTy (plan : ValuePlan sig) : Ty plan.scope :=
  (identityAtPayload sig).rename plan.observations.weaken

/-- Stable payload accessor in the final interface scope. -/
def payload (plan : ValuePlan sig) : Exp plan.scope :=
  (.var .here : Exp ((sig ,, .tvar) ,, .var)).rename
    plan.observations.weaken

noncomputable def payload_hasType (plan : ValuePlan sig)
    (base : Ctx sig) :
    Exp.HasType (plan.context base) plan.payload plan.identityTy := by
  apply weakenExp_hasType plan.observations
  exact .var Ctx.Lookup.here

/-- Reindex every observation while preserving the hidden `I, i : I`
prefix. -/
def rename (plan : ValuePlan source) (mapping : Rename source target) :
    ValuePlan target where
  observations := plan.observations.rename
    ((mapping.lift .tvar).lift .var)

/-- Substitute every observation while preserving the hidden `I, i : I`
prefix. -/
def subst (plan : ValuePlan source) (substitution : Subst source target) :
    ValuePlan target where
  observations := plan.observations.subst
    ((substitution.lift .tvar).lift .var)

@[simp] theorem rename_id (plan : ValuePlan sig) :
    plan.rename Rename.id = plan := by
  cases plan with
  | mk observations =>
      simp only [rename, Rename.lift_id, Telescope.rename_id]

theorem rename_comp (plan : ValuePlan source)
    (first : Rename source middle) (second : Rename middle target) :
    (plan.rename first).rename second = plan.rename (first.comp second) := by
  cases plan with
  | mk observations =>
      simp only [rename, Telescope.rename_comp, Rename.lift_comp]

@[simp] theorem subst_id (plan : ValuePlan sig) :
    plan.subst Subst.id = plan := by
  cases plan with
  | mk observations =>
      simp only [subst, Subst.lift_id, Telescope.subst_id]

theorem subst_comp (plan : ValuePlan source)
    (first : Subst source middle) (second : Subst middle target) :
    (plan.subst first).subst second = plan.subst (first.comp second) := by
  cases plan with
  | mk observations =>
      simp only [subst, Telescope.subst_comp, Subst.comp_lift]

@[simp] theorem telescope_rename (plan : ValuePlan source)
    (mapping : Rename source target) :
    plan.telescope.rename mapping = (plan.rename mapping).telescope := by
  rfl

@[simp] theorem telescope_subst (plan : ValuePlan source)
    (substitution : Subst source target) :
    plan.telescope.subst substitution = (plan.subst substitution).telescope := by
  rfl

theorem identityTy_rename (plan : ValuePlan source)
    (mapping : Rename source target) :
    plan.identityTy.rename (plan.telescope.liftRename mapping) =
      (plan.rename mapping).identityTy := by
  apply plan.observations.weakenType_liftRename

theorem identityTy_subst (plan : ValuePlan source)
    (substitution : Subst source target) :
    plan.identityTy.subst (plan.telescope.liftSubst substitution) =
      (plan.subst substitution).identityTy := by
  apply plan.observations.weakenType_liftSubst

theorem payload_rename (plan : ValuePlan source)
    (mapping : Rename source target) :
    plan.payload.rename (plan.telescope.liftRename mapping) =
      (plan.rename mapping).payload := by
  change
    ((.var .here : Exp ((source ,, .tvar) ,, .var)).rename
        plan.observations.weaken).rename
      (plan.observations.liftRename
        ((mapping.lift .tvar).lift .var)) =
    (.var .here : Exp ((target ,, .tvar) ,, .var)).rename
      (plan.observations.rename
        ((mapping.lift .tvar).lift .var)).weaken
  rw [Exp.rename_comp, plan.observations.weaken_liftRename,
    ← Exp.rename_comp]
  rfl

theorem payload_subst (plan : ValuePlan source)
    (substitution : Subst source target) :
    plan.payload.subst (plan.telescope.liftSubst substitution) =
      (plan.subst substitution).payload := by
  change
    ((.var .here : Exp ((source ,, .tvar) ,, .var)).rename
        plan.observations.weaken).subst
      (plan.observations.liftSubst
        ((substitution.lift .tvar).lift .var)) =
    (.var .here : Exp ((target ,, .tvar) ,, .var)).rename
      (plan.observations.subst
        ((substitution.lift .tvar).lift .var)).weaken
  rw [Exp.rename_asSubst, Exp.subst_comp,
    plan.observations.weaken_liftSubst, ← Exp.subst_comp,
    Exp.subst_asSubst]
  rfl

/-- Runtime input type: a Church existential hiding the complete stable
identity interface. -/
def inputTy (plan : ValuePlan sig) : Ty sig :=
  plan.telescope.existsTy

theorem inputTy_rename (plan : ValuePlan source)
    (mapping : Rename source target) :
    plan.inputTy.rename mapping = (plan.rename mapping).inputTy := by
  unfold inputTy
  rw [existsTy_rename, telescope_rename]

theorem inputTy_subst (plan : ValuePlan source)
    (substitution : Subst source target) :
    plan.inputTy.subst substitution = (plan.subst substitution).inputTy := by
  unfold inputTy
  rw [existsTy_subst, telescope_subst]

/-- Package a fully typed stable-identity interface. -/
noncomputable def pack
    (plan : ValuePlan sig) {base : Ctx sig}
    (arguments : Telescope.Args base plan.telescope) : Exp sig :=
  Telescope.pack arguments

noncomputable def pack_hasType
    (plan : ValuePlan sig) {base : Ctx sig}
    (arguments : Telescope.Args base plan.telescope) :
    Exp.HasType base (plan.pack arguments) plan.inputTy :=
  Telescope.pack_hasType arguments

/-- Eliminate a stable-identity package into a result type. -/
def unpack (plan : ValuePlan sig) (package : Exp sig) (result : Ty sig)
    (body : Exp plan.scope) : Exp sig :=
  plan.telescope.unpack package result body

noncomputable def unpack_hasType
    (plan : ValuePlan sig) {base : Ctx sig} {package : Exp sig}
    {result : Ty sig} {body : Exp plan.scope}
    (packageTyping : Exp.HasType base package plan.inputTy)
    (bodyTyping : Exp.HasType (plan.context base) body
      (result.rename plan.telescope.weaken)) :
    Exp.HasType base (plan.unpack package result body) result :=
  plan.telescope.unpack_hasType packageTyping bodyTyping

end ValuePlan

/-! ## Atomic full-language value plans -/

namespace Top

/-- Top observes nothing beyond stable identity and payload. -/
def plan (sig : Sig) : ValuePlan sig where
  observations := .nil

/-- Any identity type and any well-typed payload form a Top package. -/
def arguments {sig : Sig} {base : Ctx sig}
    (identity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity) :
    Telescope.Args base (plan sig).telescope :=
  .tvar identity (.var payload payloadTyping .nil)

noncomputable def package {sig : Sig} {base : Ctx sig}
    (identity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity) : Exp sig :=
  (plan sig).pack (arguments identity payload payloadTyping)

noncomputable def package_hasType {sig : Sig} {base : Ctx sig}
    (identity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity) :
    Exp.HasType base (package identity payload payloadTyping)
      (plan sig).inputTy :=
  (plan sig).pack_hasType (arguments identity payload payloadTyping)

end Top

namespace Bot

/-- Bottom observation immediately after `I, i : I`. -/
def eliminatorAtPayload (sig : Sig) :
    Ty ((sig ,, .tvar) ,, .var) :=
  .arrow (ValuePlan.identityAtPayload sig) Ty.bottom

/-- Bottom retains a computational eliminator from the exact hidden identity
to impredicative target bottom. -/
def plan (sig : Sig) : ValuePlan sig where
  observations := .var (eliminatorAtPayload sig) .nil

@[simp] theorem eliminatorAtPayload_open (identity : Ty sig)
    (payload : Exp sig) :
    ((eliminatorAtPayload sig).subst
      ((Subst.openTVar identity).lift .var)).subst
        (Subst.openVar payload) =
      .arrow identity Ty.bottom := by
  unfold eliminatorAtPayload ValuePlan.identityAtPayload
  simp only [Ty.subst, Ty.bottom_subst]
  change Ty.arrow ((identity.weaken .var).subst (Subst.openVar payload))
    Ty.bottom = Ty.arrow identity Ty.bottom
  rw [identity.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openVar payload)]

/-- Final-scope accessor for the retained bottom eliminator. -/
def eliminator (sig : Sig) : Exp (plan sig).scope :=
  .var .here

noncomputable def eliminator_hasType (base : Ctx sig) :
    Exp.HasType ((plan sig).context base) (eliminator sig)
      (.arrow (plan sig).identityTy Ty.bottom) := by
  exact .var Ctx.Lookup.here

/-- Applying the retained eliminator to the retained payload produces target
bottom in the final plan context. -/
def eliminatePayload (sig : Sig) : Exp (plan sig).scope :=
  .app (eliminator sig) (plan sig).payload

noncomputable def eliminatePayload_hasType (base : Ctx sig) :
    Exp.HasType ((plan sig).context base) (eliminatePayload sig) Ty.bottom :=
  .app (eliminator_hasType base) ((plan sig).payload_hasType base)

/-- Bottom arguments must supply identity, payload, and an eliminator for that
same identity. -/
def arguments {sig : Sig} {base : Ctx sig}
    (identity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (abort : Exp sig)
    (abortTyping : Exp.HasType base abort (.arrow identity Ty.bottom)) :
    Telescope.Args base (plan sig).telescope :=
  .tvar identity (.var payload payloadTyping (.var abort (by
    rw [eliminatorAtPayload_open]
    exact abortTyping) .nil))

noncomputable def package {sig : Sig} {base : Ctx sig}
    (identity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (abort : Exp sig)
    (abortTyping : Exp.HasType base abort (.arrow identity Ty.bottom)) :
    Exp sig :=
  (plan sig).pack
    (arguments identity payload payloadTyping abort abortTyping)

noncomputable def package_hasType {sig : Sig} {base : Ctx sig}
    (identity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (abort : Exp sig)
    (abortTyping : Exp.HasType base abort (.arrow identity Ty.bottom)) :
    Exp.HasType base
      (package identity payload payloadTyping abort abortTyping)
      (plan sig).inputTy :=
  (plan sig).pack_hasType
    (arguments identity payload payloadTyping abort abortTyping)

end Bot

end LambdaPToFCo.Full
