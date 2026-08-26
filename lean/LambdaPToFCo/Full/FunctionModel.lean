import LambdaPToFCo.Full.AtomicModels

/-!
# Faithful dependent-function value model

A function package hides its stable identity and retains explicit evidence
from that identity to its dependent telescope code.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

namespace Function

/-- Reindex a dependent codomain along a base renaming. -/
def renameCodomain (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (mapping : Rename source target) :
    ValuePlan (domain.rename mapping).scope :=
  codomain.rename (domain.telescope.liftRename mapping)

/-- Reindex a dependent codomain along a base substitution. -/
def substCodomain (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (substitution : Subst source target) :
    ValuePlan (domain.subst substitution).scope :=
  codomain.subst (domain.telescope.liftSubst substitution)

/-- Dependent target code: abstract the codomain package type over the
complete domain interface. -/
def codeTy (domain : ValuePlan sig) (codomain : ValuePlan domain.scope) :
    Ty sig :=
  domain.telescope.forallTy codomain.inputTy

theorem codeTy_rename (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (mapping : Rename source target) :
    (codeTy domain codomain).rename mapping =
      codeTy (domain.rename mapping)
        (renameCodomain domain codomain mapping) := by
  unfold codeTy renameCodomain
  rw [Telescope.forallTy_rename]
  congr 1
  exact ValuePlan.inputTy_rename codomain
    (domain.telescope.liftRename mapping)

theorem codeTy_subst (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (substitution : Subst source target) :
    (codeTy domain codomain).subst substitution =
      codeTy (domain.subst substitution)
        (substCodomain domain codomain substitution) := by
  unfold codeTy substCodomain
  rw [Telescope.forallTy_subst]
  congr 1
  exact ValuePlan.inputTy_subst codomain
    (domain.telescope.liftSubst substitution)

/-- Function code in the observation base scope, after hidden `I, i`. -/
def codeAtPayload (domain : ValuePlan sig)
    (codomain : ValuePlan domain.scope) :
    Ty ((sig ,, .tvar) ,, .var) :=
  ((codeTy domain codomain).weaken .tvar).weaken .var

theorem codeAtPayload_rename (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (mapping : Rename source target) :
    (codeAtPayload domain codomain).rename
        ((mapping.lift .tvar).lift .var) =
      codeAtPayload (domain.rename mapping)
        (renameCodomain domain codomain mapping) := by
  unfold codeAtPayload
  rw [Ty.weaken_rename_comm, Ty.weaken_rename_comm, codeTy_rename]

theorem codeAtPayload_subst (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (substitution : Subst source target) :
    (codeAtPayload domain codomain).subst
        ((substitution.lift .tvar).lift .var) =
      codeAtPayload (domain.subst substitution)
        (substCodomain domain codomain substitution) := by
  unfold codeAtPayload
  rw [← Ty.weaken_subst_comm_base, ← Ty.weaken_subst_comm_base,
    codeTy_subst]

/-- A faithful function plan retains explicit evidence from its hidden
identity to its dependent code. -/
def plan (domain : ValuePlan sig) (codomain : ValuePlan domain.scope) :
    ValuePlan sig where
  observations :=
    .cvar (ValuePlan.identityAtPayload sig)
      (codeAtPayload domain codomain) .nil

theorem plan_rename (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (mapping : Rename source target) :
    (plan domain codomain).rename mapping =
      plan (domain.rename mapping)
        (renameCodomain domain codomain mapping) := by
  cases domain
  unfold ValuePlan.rename plan
  simp only [Telescope.rename]
  rw [Single.identityAtPayload_rename, codeAtPayload_rename]
  rfl

theorem plan_subst (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (substitution : Subst source target) :
    (plan domain codomain).subst substitution =
      plan (domain.subst substitution)
        (substCodomain domain codomain substitution) := by
  cases domain
  unfold ValuePlan.subst plan
  simp only [Telescope.subst]
  rw [Single.identityAtPayload_subst, codeAtPayload_subst]
  rfl

@[simp] theorem codeAtPayload_open (domain : ValuePlan sig)
    (codomain : ValuePlan domain.scope) (identity : Ty sig)
    (payload : Exp sig) :
    ((codeAtPayload domain codomain).subst
      ((Subst.openTVar identity).lift .var)).subst
        (Subst.openVar payload) = codeTy domain codomain := by
  unfold codeAtPayload
  rw [← Ty.weaken_subst_comm_base]
  rw [(codeTy domain codomain).weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openTVar identity)]
  exact (codeTy domain codomain).weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openVar payload)

/-- Dependent code as seen in the final function-plan scope. -/
def finalCodeTy (domain : ValuePlan sig)
    (codomain : ValuePlan domain.scope) : Ty (plan domain codomain).scope :=
  (codeTy domain codomain).rename (plan domain codomain).telescope.weaken

theorem finalCodeTy_rename (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (mapping : Rename source target) :
    (finalCodeTy domain codomain).rename
        ((plan domain codomain).telescope.liftRename mapping) =
      finalCodeTy (domain.rename mapping)
        (renameCodomain domain codomain mapping) := by
  simpa only [finalCodeTy, ValuePlan.telescope_rename, plan_rename,
    codeTy_rename] using
      (plan domain codomain).telescope.weakenType_liftRename
        (codeTy domain codomain) mapping

theorem finalCodeTy_subst (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (substitution : Subst source target) :
    (finalCodeTy domain codomain).subst
        ((plan domain codomain).telescope.liftSubst substitution) =
      finalCodeTy (domain.subst substitution)
        (substCodomain domain codomain substitution) := by
  simpa only [finalCodeTy, ValuePlan.telescope_subst, plan_subst,
    codeTy_subst] using
      (plan domain codomain).telescope.weakenType_liftSubst
        (codeTy domain codomain) substitution

/-- Retained evidence from the hidden function identity to its code. -/
def toCode (domain : ValuePlan sig) (codomain : ValuePlan domain.scope) :
    Co (plan domain codomain).scope :=
  .cvar .here

theorem toCode_rename (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (mapping : Rename source target) :
    (toCode domain codomain).rename
        ((plan domain codomain).telescope.liftRename mapping) =
      toCode (domain.rename mapping)
        (renameCodomain domain codomain mapping) := by
  rfl

theorem toCode_subst (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (substitution : Subst source target) :
    (toCode domain codomain).subst
        ((plan domain codomain).telescope.liftSubst substitution) =
      toCode (domain.subst substitution)
        (substCodomain domain codomain substitution) := by
  rfl

noncomputable def toCode_hasType (base : Ctx sig)
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope) :
    Co.HasType ((plan domain codomain).context base)
      (toCode domain codomain) (plan domain codomain).identityTy
      (finalCodeTy domain codomain) := by
  have evidence :
      Co.HasType ((plan domain codomain).context base) (.cvar .here)
        ((ValuePlan.identityAtPayload sig).weaken .cvar)
        ((codeAtPayload domain codomain).weaken .cvar) :=
    .cvar Ctx.Lookup.here
  simpa only [ValuePlan.context, ValuePlan.telescope, plan,
    ValuePlan.identityTy, finalCodeTy, codeAtPayload,
    Telescope.context, Telescope.weaken, Ty.weaken, Ty.rename_comp,
    Rename.comp_id] using evidence

/-- The retained payload cast to executable dependent code. -/
def asCode (domain : ValuePlan sig) (codomain : ValuePlan domain.scope) :
    Exp (plan domain codomain).scope :=
  .cast (plan domain codomain).payload (toCode domain codomain)

noncomputable def asCode_hasType (base : Ctx sig)
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope) :
    Exp.HasType ((plan domain codomain).context base)
      (asCode domain codomain) (finalCodeTy domain codomain) :=
  .cast ((plan domain codomain).payload_hasType base)
    (toCode_hasType base domain codomain)

theorem asCode_rename (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (mapping : Rename source target) :
    (asCode domain codomain).rename
        ((plan domain codomain).telescope.liftRename mapping) =
      asCode (domain.rename mapping)
        (renameCodomain domain codomain mapping) := by
  unfold asCode
  simp only [Exp.rename]
  rw [ValuePlan.payload_rename, toCode_rename]
  rfl

theorem asCode_subst (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (substitution : Subst source target) :
    (asCode domain codomain).subst
        ((plan domain codomain).telescope.liftSubst substitution) =
      asCode (domain.subst substitution)
        (substCodomain domain codomain substitution) := by
  unfold asCode
  simp only [Exp.subst]
  rw [ValuePlan.payload_subst, toCode_subst]
  rfl

theorem inputTy_rename (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (mapping : Rename source target) :
    (plan domain codomain).inputTy.rename mapping =
      (plan (domain.rename mapping)
        (renameCodomain domain codomain mapping)).inputTy := by
  calc
    (plan domain codomain).inputTy.rename mapping =
        ((plan domain codomain).rename mapping).inputTy :=
      ValuePlan.inputTy_rename (plan domain codomain) mapping
    _ = _ := by rw [plan_rename]

theorem inputTy_subst (domain : ValuePlan source)
    (codomain : ValuePlan domain.scope)
    (substitution : Subst source target) :
    (plan domain codomain).inputTy.subst substitution =
      (plan (domain.subst substitution)
        (substCodomain domain codomain substitution)).inputTy := by
  calc
    (plan domain codomain).inputTy.subst substitution =
        ((plan domain codomain).subst substitution).inputTy :=
      ValuePlan.inputTy_subst (plan domain codomain) substitution
    _ = _ := by rw [plan_subst]

/-- Supply a stable function identity, its payload, and evidence that the
payload identity implements the dependent code. -/
def arguments {sig : Sig} {base : Ctx sig}
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope)
    (identity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (toCodeEvidence : Co sig)
    (toCodeTyping : Co.HasType base toCodeEvidence identity
      (codeTy domain codomain)) :
    Telescope.Args base (plan domain codomain).telescope :=
  .tvar identity
    (.var payload payloadTyping
      (.cvar toCodeEvidence (by
        rw [Single.identityAtPayload_open, codeAtPayload_open]
        exact toCodeTyping) .nil))

noncomputable def package {sig : Sig} {base : Ctx sig}
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope)
    (identity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (toCodeEvidence : Co sig)
    (toCodeTyping : Co.HasType base toCodeEvidence identity
      (codeTy domain codomain)) : Exp sig :=
  (plan domain codomain).pack
    (arguments domain codomain identity payload payloadTyping
      toCodeEvidence toCodeTyping)

noncomputable def package_hasType {sig : Sig} {base : Ctx sig}
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope)
    (identity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (toCodeEvidence : Co sig)
    (toCodeTyping : Co.HasType base toCodeEvidence identity
      (codeTy domain codomain)) :
    Exp.HasType base
      (package domain codomain identity payload payloadTyping
        toCodeEvidence toCodeTyping)
      (plan domain codomain).inputTy :=
  (plan domain codomain).pack_hasType
    (arguments domain codomain identity payload payloadTyping
      toCodeEvidence toCodeTyping)

/-- Exact function arguments use the dependent code itself as the hidden
identity and reflexivity as implementation evidence. -/
def exactArguments {sig : Sig} {base : Ctx sig}
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope)
    (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload (codeTy domain codomain)) :
    Telescope.Args base (plan domain codomain).telescope :=
  arguments domain codomain (codeTy domain codomain) payload payloadTyping
    (.refl (codeTy domain codomain)) Co.HasType.refl

noncomputable def exactPackage {sig : Sig} {base : Ctx sig}
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope)
    (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload (codeTy domain codomain)) :
    Exp sig :=
  (plan domain codomain).pack
    (exactArguments domain codomain payload payloadTyping)

noncomputable def exactPackage_hasType {sig : Sig} {base : Ctx sig}
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope)
    (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload (codeTy domain codomain)) :
    Exp.HasType base
      (exactPackage domain codomain payload payloadTyping)
      (plan domain codomain).inputTy :=
  (plan domain codomain).pack_hasType
    (exactArguments domain codomain payload payloadTyping)

/-- Abstract a compiled codomain package over the complete domain
interface. -/
def abstraction (domain : ValuePlan sig) (body : Exp domain.scope) : Exp sig :=
  domain.telescope.lambda body

theorem abstraction_rename (domain : ValuePlan source)
    (body : Exp domain.scope)
    (mapping : Rename source target) :
    (abstraction domain body).rename mapping =
      abstraction (domain.rename mapping)
        (body.rename (domain.telescope.liftRename mapping)) := by
  exact domain.telescope.lambda_rename body mapping

theorem abstraction_subst (domain : ValuePlan source)
    (body : Exp domain.scope)
    (substitution : Subst source target) :
    (abstraction domain body).subst substitution =
      abstraction (domain.subst substitution)
        (body.subst (domain.telescope.liftSubst substitution)) := by
  exact domain.telescope.lambda_subst body substitution

noncomputable def abstraction_hasType {sig : Sig} {base : Ctx sig}
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope)
    (body : Exp domain.scope)
    (bodyTyping : Exp.HasType (domain.context base) body
      codomain.inputTy) :
    Exp.HasType base (abstraction domain body)
      (codeTy domain codomain) :=
  domain.telescope.lambda_hasType bodyTyping

/-- Exact function introduction from a compiled codomain package under the
domain interface context. -/
noncomputable def exactAbstractionArguments {sig : Sig} {base : Ctx sig}
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope)
    (body : Exp domain.scope)
    (bodyTyping : Exp.HasType (domain.context base) body
      codomain.inputTy) :
    Telescope.Args base (plan domain codomain).telescope :=
  exactArguments domain codomain (abstraction domain body)
    (abstraction_hasType domain codomain body bodyTyping)

noncomputable def exactAbstractionPackage {sig : Sig} {base : Ctx sig}
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope)
    (body : Exp domain.scope)
    (bodyTyping : Exp.HasType (domain.context base) body
      codomain.inputTy) : Exp sig :=
  (plan domain codomain).pack
    (exactAbstractionArguments domain codomain body bodyTyping)

noncomputable def exactAbstractionPackage_hasType
    {sig : Sig} {base : Ctx sig}
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope)
    (body : Exp domain.scope)
    (bodyTyping : Exp.HasType (domain.context base) body
      codomain.inputTy) :
    Exp.HasType base
      (exactAbstractionPackage domain codomain body bodyTyping)
      (plan domain codomain).inputTy :=
  (plan domain codomain).pack_hasType
    (exactAbstractionArguments domain codomain body bodyTyping)

/-- Apply dependent telescope code to a complete domain argument spine. -/
def apply {sig : Sig} {base : Ctx sig}
    (domain : ValuePlan sig)
    (arguments : Telescope.Args base domain.telescope)
    (function : Exp sig) : Exp sig :=
  arguments.apply function

/-- Application returns the codomain package opened by the exact
heterogeneous domain substitution. -/
noncomputable def apply_hasType {sig : Sig} {base : Ctx sig}
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope)
    (arguments : Telescope.Args base domain.telescope)
    (function : Exp sig)
    (functionTyping : Exp.HasType base function (codeTy domain codomain)) :
    Exp.HasType base (apply domain arguments function)
      (codomain.inputTy.subst arguments.substitution) := by
  have applied := arguments.apply_hasType
    (result := codomain.inputTy) functionTyping
  rw [arguments.instantiate_eq_subst] at applied
  exact applied

end Function

/-! A closed regression whose codomain identity is the hidden identity chosen
by the domain package. Applying the code at `I = Top` must open that dependent
codomain to the singleton plan at `Top`. -/

namespace FunctionRegression

def domain : ValuePlan ([] : Sig) := Top.plan []

def codomain : ValuePlan domain.scope :=
  Single.plan domain.identityTy

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

noncomputable def body : Exp domain.scope :=
  Single.exactPackage domain.identityTy domain.payload
    (domain.payload_hasType Ctx.empty)

noncomputable def body_hasType :
    Exp.HasType (domain.context Ctx.empty) body codomain.inputTy :=
  Single.exactPackage_hasType domain.identityTy domain.payload
    (domain.payload_hasType Ctx.empty)

noncomputable def packagedFunction : Exp ([] : Sig) :=
  Function.exactAbstractionPackage domain codomain body body_hasType

noncomputable def packagedFunction_hasType :
    Exp.HasType Ctx.empty packagedFunction
      (Function.plan domain codomain).inputTy :=
  Function.exactAbstractionPackage_hasType
    domain codomain body body_hasType

noncomputable def domainArguments :
    Telescope.Args Ctx.empty domain.telescope :=
  Top.arguments .top topPayload topPayload_hasType

noncomputable def applied : Exp ([] : Sig) :=
  Function.apply domain domainArguments
    (Function.abstraction domain body)

noncomputable def applied_hasType :
    Exp.HasType Ctx.empty applied
      (codomain.inputTy.subst domainArguments.substitution) :=
  Function.apply_hasType domain codomain domainArguments
    (Function.abstraction domain body)
    (Function.abstraction_hasType domain codomain body body_hasType)

theorem dependentResult_opens :
    codomain.inputTy.subst domainArguments.substitution =
      (Single.plan (.top : Ty ([] : Sig))).inputTy := by
  rfl

noncomputable def applied_open_hasType :
    Exp.HasType Ctx.empty applied
      (Single.plan (.top : Ty ([] : Sig))).inputTy := by
  rw [← dependentResult_opens]
  exact applied_hasType

end FunctionRegression

end LambdaPToFCo.Full
