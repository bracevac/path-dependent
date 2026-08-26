import LambdaPToFCo.Direct.Telescope
import LambdaPToFCo.Direct.Adapter

/-!
# Direct Church packages with ordinary function dictionaries

This target-only leaf builds packages entirely from unchanged `SystemFCo`
syntax.  A plan hides an identity type `I`, then a payload `i : I`, before
introducing its observations.  The interval plan stores lower and upper
evidence as the ordinary term fields `lower -> I` and `I -> upper`.

There is no use of qualified target types or coercion variables for this
evidence, and no analogue of a computational coercion constructor.  Exact
construction, elimination, typing, and the closed beta regression all use
ordinary polymorphism, lambdas, and applications.
-/

namespace LambdaPToFCo.Direct.Package

open SystemFCo

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
structure Plan (sig : Sig) where
  observations : Telescope ((sig ,, .tvar) ,, .var)

namespace Plan

/-- Hidden identity type as seen immediately after the payload binder. -/
def identityAtPayload (sig : Sig) : Ty ((sig ,, .tvar) ,, .var) :=
  (.tvar .here : Ty (sig ,, .tvar)).weaken .var

/-- Complete interface telescope: `I`, `i : I`, then observations. -/
def telescope (plan : Plan sig) : Telescope sig :=
  .tvar (.var (.tvar .here) plan.observations)

def scope (plan : Plan sig) : Sig :=
  plan.telescope.scope

def context (plan : Plan sig) (base : Ctx sig) : Ctx plan.scope :=
  plan.telescope.context base

/-- Stable hidden identity in the final interface scope. -/
def identityTy (plan : Plan sig) : Ty plan.scope :=
  (identityAtPayload sig).rename plan.observations.weaken

/-- Stable payload accessor in the final interface scope. -/
def payload (plan : Plan sig) : Exp plan.scope :=
  (.var .here : Exp ((sig ,, .tvar) ,, .var)).rename
    plan.observations.weaken

noncomputable def payload_hasType (plan : Plan sig)
    (base : Ctx sig) :
    Exp.HasType (plan.context base) plan.payload plan.identityTy := by
  apply weakenExp_hasType plan.observations
  exact .var Ctx.Lookup.here

/-- Reindex every observation while preserving the hidden `I, i : I`
prefix. -/
def rename (plan : Plan source) (mapping : Rename source target) :
    Plan target where
  observations := plan.observations.rename
    ((mapping.lift .tvar).lift .var)

/-- Substitute every observation while preserving the hidden `I, i : I`
prefix. -/
def subst (plan : Plan source) (substitution : Subst source target) :
    Plan target where
  observations := plan.observations.subst
    ((substitution.lift .tvar).lift .var)

@[simp] theorem rename_id (plan : Plan sig) :
    plan.rename Rename.id = plan := by
  cases plan with
  | mk observations =>
      simp only [rename, Rename.lift_id, Telescope.rename_id]

theorem rename_comp (plan : Plan source)
    (first : Rename source middle) (second : Rename middle target) :
    (plan.rename first).rename second = plan.rename (first.comp second) := by
  cases plan with
  | mk observations =>
      simp only [rename, Telescope.rename_comp, Rename.lift_comp]

@[simp] theorem subst_id (plan : Plan sig) :
    plan.subst Subst.id = plan := by
  cases plan with
  | mk observations =>
      simp only [subst, Subst.lift_id, Telescope.subst_id]

theorem subst_comp (plan : Plan source)
    (first : Subst source middle) (second : Subst middle target) :
    (plan.subst first).subst second = plan.subst (first.comp second) := by
  cases plan with
  | mk observations =>
      simp only [subst, Telescope.subst_comp, Subst.comp_lift]

@[simp] theorem telescope_rename (plan : Plan source)
    (mapping : Rename source target) :
    plan.telescope.rename mapping = (plan.rename mapping).telescope := by
  rfl

@[simp] theorem telescope_subst (plan : Plan source)
    (substitution : Subst source target) :
    plan.telescope.subst substitution = (plan.subst substitution).telescope := by
  rfl

theorem identityTy_rename (plan : Plan source)
    (mapping : Rename source target) :
    plan.identityTy.rename (plan.telescope.liftRename mapping) =
      (plan.rename mapping).identityTy := by
  apply plan.observations.weakenType_liftRename

theorem identityTy_subst (plan : Plan source)
    (substitution : Subst source target) :
    plan.identityTy.subst (plan.telescope.liftSubst substitution) =
      (plan.subst substitution).identityTy := by
  apply plan.observations.weakenType_liftSubst

theorem payload_rename (plan : Plan source)
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

theorem payload_subst (plan : Plan source)
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
def inputTy (plan : Plan sig) : Ty sig :=
  plan.telescope.existsTy

theorem inputTy_rename (plan : Plan source)
    (mapping : Rename source target) :
    plan.inputTy.rename mapping = (plan.rename mapping).inputTy := by
  unfold inputTy
  rw [existsTy_rename, telescope_rename]

theorem inputTy_subst (plan : Plan source)
    (substitution : Subst source target) :
    plan.inputTy.subst substitution = (plan.subst substitution).inputTy := by
  unfold inputTy
  rw [existsTy_subst, telescope_subst]

/-- Package a fully typed stable-identity interface. -/
noncomputable def pack
    (plan : Plan sig) {base : Ctx sig}
    (arguments : Telescope.Args base plan.telescope) : Exp sig :=
  Telescope.pack arguments

noncomputable def pack_hasType
    (plan : Plan sig) {base : Ctx sig}
    (arguments : Telescope.Args base plan.telescope) :
    Exp.HasType base (plan.pack arguments) plan.inputTy :=
  Telescope.pack_hasType arguments

/-- Eliminate a stable-identity package into a result type. -/
def unpack (plan : Plan sig) (package : Exp sig) (result : Ty sig)
    (body : Exp plan.scope) : Exp sig :=
  plan.telescope.unpack package result body

noncomputable def unpack_hasType
    (plan : Plan sig) {base : Ctx sig} {package : Exp sig}
    {result : Ty sig} {body : Exp plan.scope}
    (packageTyping : Exp.HasType base package plan.inputTy)
    (bodyTyping : Exp.HasType (plan.context base) body
      (result.rename plan.telescope.weaken)) :
    Exp.HasType base (plan.unpack package result body) result :=
  plan.telescope.unpack_hasType packageTyping bodyTyping

end Plan

/-! ## Function-dictionary interval packages -/

namespace Interval

@[simp] private theorem weaken_openTVar (type argument : Ty sig) :
    (type.weaken .tvar).subst (Subst.openTVar argument) = type :=
  type.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openTVar argument)

@[simp] private theorem weaken_openVar (type : Ty sig)
    (argument : Exp sig) :
    (type.weaken .var).subst (Subst.openVar argument) = type :=
  type.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openVar argument)

/-- Lower evidence, scoped after the hidden identity type and payload. -/
def lowerField (lower : Ty sig) : Ty ((sig ,, .tvar) ,, .var) :=
  .arrow ((lower.weaken .tvar).weaken .var) (Plan.identityAtPayload sig)

/-- Upper evidence, scoped after the lower function field. -/
def upperField (upper : Ty sig) :
    Ty ((((sig ,, .tvar) ,, .var) ,, .var)) :=
  .arrow ((Plan.identityAtPayload sig).weaken .var)
    (((upper.weaken .tvar).weaken .var).weaken .var)

/-- A hidden identity and payload with ordinary function dictionaries
`lower -> identity` and `identity -> upper`. -/
def plan (lower upper : Ty sig) : Plan sig where
  observations := .var (lowerField lower) (.var (upperField upper) .nil)

/-- The opened lower dictionary. -/
def lowerFunction (lower upper : Ty sig) : Exp (plan lower upper).scope :=
  .var (.there .here)

/-- The opened upper dictionary. -/
def upperFunction (lower upper : Ty sig) : Exp (plan lower upper).scope :=
  .var .here

noncomputable def lowerFunction_hasType (base : Ctx sig)
    (lower upper : Ty sig) :
    Exp.HasType ((plan lower upper).context base)
      (lowerFunction lower upper)
      (.arrow (lower.rename (plan lower upper).telescope.weaken)
        (plan lower upper).identityTy) := by
  simpa [plan, lowerFunction, lowerField, upperField, Plan.context,
    Plan.telescope, Plan.identityTy, Plan.identityAtPayload,
    Telescope.context, Telescope.weaken, Ty.weaken, Ty.rename,
    Ty.rename_comp,
    Rename.comp_assoc, Rename.comp_id] using
    (Exp.HasType.var
      (Ctx.Lookup.there Ctx.Lookup.here :
        Ctx.VarLookup ((plan lower upper).context base) (.there .here) _))

noncomputable def upperFunction_hasType (base : Ctx sig)
    (lower upper : Ty sig) :
    Exp.HasType ((plan lower upper).context base)
      (upperFunction lower upper)
      (.arrow (plan lower upper).identityTy
        (upper.rename (plan lower upper).telescope.weaken)) := by
  simpa [plan, upperFunction, lowerField, upperField, Plan.context,
    Plan.telescope, Plan.identityTy, Plan.identityAtPayload,
    Telescope.context, Telescope.weaken, Ty.weaken, Ty.rename,
    Ty.rename_comp,
    Rename.comp_assoc, Rename.comp_id] using
    (Exp.HasType.var
      (Ctx.Lookup.here :
        Ctx.VarLookup ((plan lower upper).context base) .here _))

/-- Apply the opened upper dictionary to the stable payload. -/
def observeUpper (lower upper : Ty sig) : Exp (plan lower upper).scope :=
  Adapter.apply (upperFunction lower upper) (plan lower upper).payload

noncomputable def observeUpper_hasType (base : Ctx sig)
    (lower upper : Ty sig) :
    Exp.HasType ((plan lower upper).context base)
      (observeUpper lower upper)
      (upper.rename (plan lower upper).telescope.weaken) :=
  Adapter.apply_hasType (upperFunction_hasType base lower upper)
    ((plan lower upper).payload_hasType base)

/-- Exact introduction arguments.  Both bounds are witnessed by ordinary
target functions; no qualified type or coercion variable is introduced. -/
def exactArguments {base : Ctx sig} (lower upper witness : Ty sig)
    (payload lowerFunction upperFunction : Exp sig)
    (payloadTyping : Exp.HasType base payload witness)
    (lowerTyping : Exp.HasType base lowerFunction (.arrow lower witness))
    (upperTyping : Exp.HasType base upperFunction (.arrow witness upper)) :
    Telescope.Args base (plan lower upper).telescope := by
  refine .tvar witness (.var payload payloadTyping
    (.var lowerFunction ?_ (.var upperFunction ?_ .nil)))
  · rw [TyOps.closeVar_open]
    have opened :
          (lowerField lower).subst
            ((Subst.openTVar witness).lift .var) =
          (Ty.arrow lower witness).weaken .var := by
      unfold lowerField Plan.identityAtPayload
      simp only [Ty.subst]
      rw [← Ty.weaken_subst_comm_base
        (lower.weaken .tvar) (Subst.openTVar witness)]
      rw [weaken_openTVar]
      rw [← Ty.weaken_subst_comm_base
        ((.tvar .here : Ty (sig ,, .tvar)))
        (Subst.openTVar witness)]
      rfl
    rw [opened, TyOps.closeVar_of_weaken]
    exact lowerTyping
  · have afterWitness :
        (upperField upper).subst
            (((Subst.openTVar witness).lift .var).lift .var) =
          ((Ty.arrow witness upper).weaken .var).weaken .var := by
      unfold upperField Plan.identityAtPayload
      simp only [Ty.subst]
      congr 1
      rw [← Ty.weaken_subst_comm_base
        ((upper.weaken .tvar).weaken .var)
        ((Subst.openTVar witness).lift .var)]
      rw [← Ty.weaken_subst_comm_base
        (upper.weaken .tvar) (Subst.openTVar witness)]
      rw [weaken_openTVar]
      rfl
    rw [afterWitness]
    rw [← Ty.weaken_subst_comm_base
      ((Ty.arrow witness upper).weaken .var)
      (Subst.openVar payload)]
    rw [weaken_openVar, weaken_openVar]
    exact upperTyping

/-- Exact Church package construction. -/
noncomputable def exact {base : Ctx sig} (lower upper witness : Ty sig)
    (payload lowerFunction upperFunction : Exp sig)
    (payloadTyping : Exp.HasType base payload witness)
    (lowerTyping : Exp.HasType base lowerFunction (.arrow lower witness))
    (upperTyping : Exp.HasType base upperFunction (.arrow witness upper)) :
    Exp sig :=
  (plan lower upper).pack
    (exactArguments lower upper witness payload lowerFunction upperFunction
      payloadTyping lowerTyping upperTyping)

noncomputable def exact_hasType {base : Ctx sig}
    (lower upper witness : Ty sig)
    (payload lowerFunction upperFunction : Exp sig)
    (payloadTyping : Exp.HasType base payload witness)
    (lowerTyping : Exp.HasType base lowerFunction (.arrow lower witness))
    (upperTyping : Exp.HasType base upperFunction (.arrow witness upper)) :
    Exp.HasType base
      (exact lower upper witness payload lowerFunction upperFunction
        payloadTyping lowerTyping upperTyping)
      (plan lower upper).inputTy :=
  (plan lower upper).pack_hasType
    (exactArguments lower upper witness payload lowerFunction upperFunction
      payloadTyping lowerTyping upperTyping)

noncomputable def exactArguments_allValues {base : Ctx sig}
    (lower upper witness : Ty sig)
    (payload lowerFunction upperFunction : Exp sig)
    (payloadTyping : Exp.HasType base payload witness)
    (lowerTyping : Exp.HasType base lowerFunction (.arrow lower witness))
    (upperTyping : Exp.HasType base upperFunction (.arrow witness upper))
    (payloadValue : Exp.IsValue payload)
    (lowerValue : Exp.IsValue lowerFunction)
    (upperValue : Exp.IsValue upperFunction) :
    Telescope.Args.AllValues
      (exactArguments lower upper witness payload lowerFunction upperFunction
        payloadTyping lowerTyping upperTyping) := by
  exact ⟨payloadValue, lowerValue, upperValue, True.intro⟩

/-- Eliminate an interval package with a body in its exact opened scope. -/
def unpack (lower upper : Ty sig) (package : Exp sig) (answer : Ty sig)
    (body : Exp (plan lower upper).scope) : Exp sig :=
  (plan lower upper).unpack package answer body

noncomputable def unpack_hasType {base : Ctx sig}
    {lower upper answer : Ty sig} {package : Exp sig}
    {body : Exp (plan lower upper).scope}
    (packageTyping : Exp.HasType base package (plan lower upper).inputTy)
    (bodyTyping : Exp.HasType ((plan lower upper).context base) body
      (answer.rename (plan lower upper).telescope.weaken)) :
    Exp.HasType base (unpack lower upper package answer body) answer :=
  (plan lower upper).unpack_hasType packageTyping bodyTyping

/-- Exact construction followed by elimination performs the ordinary Church
beta sequence.  Readiness is required only for the three term fields. -/
theorem unpack_exact_steps {base : Ctx sig}
    (lower upper witness answer : Ty sig)
    (payload lowerFunction upperFunction : Exp sig)
    (payloadTyping : Exp.HasType base payload witness)
    (lowerTyping : Exp.HasType base lowerFunction (.arrow lower witness))
    (upperTyping : Exp.HasType base upperFunction (.arrow witness upper))
    (payloadValue : Exp.IsValue payload)
    (lowerValue : Exp.IsValue lowerFunction)
    (upperValue : Exp.IsValue upperFunction)
    (body : Exp (plan lower upper).scope) :
    Exp.Steps
      (unpack lower upper
        (exact lower upper witness payload lowerFunction upperFunction
          payloadTyping lowerTyping upperTyping)
        answer body)
      (body.subst
        (exactArguments lower upper witness payload lowerFunction upperFunction
          payloadTyping lowerTyping upperTyping).substitution) := by
  apply (plan lower upper).telescope.unpack_pack_steps_of_ne_nil
  · exact exactArguments_allValues lower upper witness payload
      lowerFunction upperFunction payloadTyping lowerTyping upperTyping
      payloadValue lowerValue upperValue
  · intro empty
    cases empty

end Interval

/-- The observation-free package plan used for source Top. -/
def topPlan (sig : Sig) : Plan sig where
  observations := .nil

/-- The exact interval plan for one concrete target type. -/
def identityPlan (type : Ty sig) : Plan sig :=
  Interval.plan type type

/-! ## Closed ordinary-function package regression -/

namespace Regression

def endpoint : Ty [] :=
  .arrow .top .top

def payload : Exp [] :=
  Adapter.identity .top

def dictionary : Exp [] :=
  Adapter.identity endpoint

noncomputable def payloadTyping :
    Exp.HasType Ctx.empty payload endpoint :=
  Adapter.identity_hasType Ctx.empty .top

noncomputable def dictionaryTyping :
    Exp.HasType Ctx.empty dictionary (.arrow endpoint endpoint) :=
  Adapter.identity_hasType Ctx.empty endpoint

noncomputable def arguments :=
  Interval.exactArguments endpoint endpoint endpoint payload dictionary
    dictionary payloadTyping dictionaryTyping dictionaryTyping

noncomputable def exactPackage : Exp [] :=
  Interval.exact endpoint endpoint endpoint payload dictionary dictionary
    payloadTyping dictionaryTyping dictionaryTyping

noncomputable def exactPackageTyping :
    Exp.HasType Ctx.empty exactPackage (identityPlan endpoint).inputTy :=
  Interval.exact_hasType endpoint endpoint endpoint payload dictionary
    dictionary payloadTyping dictionaryTyping dictionaryTyping

def body : Exp (identityPlan endpoint).scope :=
  Interval.observeUpper endpoint endpoint

noncomputable def bodyTyping :
    Exp.HasType ((identityPlan endpoint).context Ctx.empty) body
      (endpoint.rename (identityPlan endpoint).telescope.weaken) :=
  Interval.observeUpper_hasType Ctx.empty endpoint endpoint

noncomputable def program : Exp [] :=
  Interval.unpack endpoint endpoint exactPackage endpoint body

noncomputable def programTyping :
    Exp.HasType Ctx.empty program endpoint :=
  Interval.unpack_hasType exactPackageTyping bodyTyping

noncomputable def result : Exp [] :=
  body.subst arguments.substitution

theorem result_eq : result = Adapter.apply dictionary payload :=
  rfl

theorem churchBeta : Exp.Steps program result :=
  Interval.unpack_exact_steps endpoint endpoint endpoint endpoint payload
    dictionary dictionary payloadTyping dictionaryTyping dictionaryTyping
    .abs .abs .abs body

/-- The closed package exposes its ordinary upper dictionary and payload.
This regression crosses the Church type/handler betas and all four telescope
fields without any qualified type or coercion-variable application. -/
theorem churchBeta_dictionary_application :
    Exp.Steps program (Adapter.apply dictionary payload) := by
  rw [← result_eq]
  exact churchBeta

theorem dictionaryBeta :
    Exp.Step (Adapter.apply dictionary payload) payload :=
  Adapter.identity_apply_step .abs

theorem churchBeta_payload : Exp.Steps program payload :=
  Exp.Steps.trans churchBeta_dictionary_application
    (Exp.Steps.single dictionaryBeta)

end Regression

end LambdaPToFCo.Direct.Package
