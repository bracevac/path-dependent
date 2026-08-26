import LambdaPToFCo.Direct.Shape

/-!
# Canonical structural plans for the direct compiler

This target-only leaf gives functions and dependent pairs their canonical
`SystemFCo` package shapes.  Every computational observation is an ordinary
term field of arrow type.  In particular, this file introduces no qualified
type, coercion variable, or extension-target syntax.

A function retains one `I -> code` observation.  A pair retains one
`I -> representation` observation, where its representation telescope is the
complete first interface followed by the proper or interval member interface.
An interval member hides one raw selected input type and stores ordinary
functions from the lower input to that type and from that type to the upper
input.  Opening it therefore exposes an opaque `Shape`, never a fabricated
stable plan.

This leaf deliberately supplies no generic dependent pair-covariance mapper.
Raw endpoint functions do not induce the scope substitution needed to transport
a dependent member; a compiler rule that performs that transport must provide
its additional alignment evidence separately.
-/

namespace LambdaPToFCo.Direct

open SystemFCo

@[simp] private theorem identityAtPayload_open (identity : Ty sig)
    (payload : Exp sig) :
    ((Package.Plan.identityAtPayload sig).subst
      ((Subst.openTVar identity).lift .var)).subst
        (Subst.openVar payload) = identity := by
  unfold Package.Plan.identityAtPayload
  change (identity.weaken .var).subst (Subst.openVar payload) = identity
  exact identity.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openVar payload)

namespace Function

/-- Reindex a dependent codomain along a base renaming. -/
def renameCodomain (domain : Shape source)
    (codomain : Shape domain.scope)
    (mapping : Rename source target) :
    Shape (domain.rename mapping).scope :=
  codomain.rename (domain.liftRename mapping)

/-- Substitute a dependent codomain along a base substitution. -/
def substCodomain (domain : Shape source)
    (codomain : Shape domain.scope)
    (substitution : Subst source target) :
    Shape (domain.subst substitution).scope :=
  codomain.subst (domain.liftSubst substitution)

/-- Dependent target code, abstracted over the complete domain interface. -/
def codeTy (domain : Shape sig)
    (codomain : Shape domain.scope) : Ty sig :=
  domain.binders.forallTy codomain.inputTy

theorem codeTy_rename (domain : Shape source)
    (codomain : Shape domain.scope)
    (mapping : Rename source target) :
    (codeTy domain codomain).rename mapping =
      codeTy (domain.rename mapping)
        (renameCodomain domain codomain mapping) := by
  cases domain with
  | stable plan =>
      unfold codeTy renameCodomain Shape.scope Shape.binders
        Shape.liftRename
      rw [Telescope.forallTy_rename]
      change (plan.telescope.rename mapping).forallTy
        (codomain.inputTy.rename (plan.telescope.liftRename mapping)) =
        (plan.telescope.rename mapping).forallTy
          (codomain.rename (plan.telescope.liftRename mapping)).inputTy
      congr 1
      exact Shape.inputTy_rename codomain _
  | «opaque» type =>
      unfold codeTy renameCodomain Shape.scope Shape.binders
        Shape.liftRename
      rw [Telescope.forallTy_rename]
      change ((Telescope.var type Telescope.nil).rename mapping).forallTy
        (codomain.inputTy.rename
          ((Telescope.var type Telescope.nil).liftRename mapping)) =
        ((Telescope.var type Telescope.nil).rename mapping).forallTy
          (codomain.rename
            ((Telescope.var type Telescope.nil).liftRename mapping)).inputTy
      congr 1
      exact Shape.inputTy_rename codomain _

theorem codeTy_subst (domain : Shape source)
    (codomain : Shape domain.scope)
    (substitution : Subst source target) :
    (codeTy domain codomain).subst substitution =
      codeTy (domain.subst substitution)
        (substCodomain domain codomain substitution) := by
  cases domain with
  | stable plan =>
      unfold codeTy substCodomain Shape.scope Shape.binders Shape.liftSubst
      rw [Telescope.forallTy_subst]
      change (plan.telescope.subst substitution).forallTy
        (codomain.inputTy.subst (plan.telescope.liftSubst substitution)) =
        (plan.telescope.subst substitution).forallTy
          (codomain.subst (plan.telescope.liftSubst substitution)).inputTy
      congr 1
      exact Shape.inputTy_subst codomain _
  | «opaque» type =>
      unfold codeTy substCodomain Shape.scope Shape.binders Shape.liftSubst
      rw [Telescope.forallTy_subst]
      change ((Telescope.var type Telescope.nil).subst
          substitution).forallTy
        (codomain.inputTy.subst
          ((Telescope.var type Telescope.nil).liftSubst substitution)) =
        ((Telescope.var type Telescope.nil).subst substitution).forallTy
          (codomain.subst
            ((Telescope.var type Telescope.nil).liftSubst
              substitution)).inputTy
      congr 1
      exact Shape.inputTy_subst codomain _

/-- Function code in the observation base, after hidden `I, i`. -/
def codeAtPayload (domain : Shape sig)
    (codomain : Shape domain.scope) :
    Ty ((sig ,, .tvar) ,, .var) :=
  ((codeTy domain codomain).weaken .tvar).weaken .var

theorem codeAtPayload_rename (domain : Shape source)
    (codomain : Shape domain.scope)
    (mapping : Rename source target) :
    (codeAtPayload domain codomain).rename
        ((mapping.lift .tvar).lift .var) =
      codeAtPayload (domain.rename mapping)
        (renameCodomain domain codomain mapping) := by
  unfold codeAtPayload
  rw [Ty.weaken_rename_comm, Ty.weaken_rename_comm, codeTy_rename]

theorem codeAtPayload_subst (domain : Shape source)
    (codomain : Shape domain.scope)
    (substitution : Subst source target) :
    (codeAtPayload domain codomain).subst
        ((substitution.lift .tvar).lift .var) =
      codeAtPayload (domain.subst substitution)
        (substCodomain domain codomain substitution) := by
  unfold codeAtPayload
  rw [← Ty.weaken_subst_comm_base, ← Ty.weaken_subst_comm_base,
    codeTy_subst]

/-- Ordinary `I -> code` observation retained by a function package. -/
def toCodeField (domain : Shape sig)
    (codomain : Shape domain.scope) :
    Ty ((sig ,, .tvar) ,, .var) :=
  .arrow (Package.Plan.identityAtPayload sig)
    (codeAtPayload domain codomain)

theorem toCodeField_rename (domain : Shape source)
    (codomain : Shape domain.scope)
    (mapping : Rename source target) :
    (toCodeField domain codomain).rename
        ((mapping.lift .tvar).lift .var) =
      toCodeField (domain.rename mapping)
        (renameCodomain domain codomain mapping) := by
  simp only [toCodeField, Ty.rename, codeAtPayload_rename]
  rfl

theorem toCodeField_subst (domain : Shape source)
    (codomain : Shape domain.scope)
    (substitution : Subst source target) :
    (toCodeField domain codomain).subst
        ((substitution.lift .tvar).lift .var) =
      toCodeField (domain.subst substitution)
        (substCodomain domain codomain substitution) := by
  simp only [toCodeField, Ty.subst, codeAtPayload_subst]
  rfl

/-- Canonical faithful function plan. -/
def plan (domain : Shape sig)
    (codomain : Shape domain.scope) : Package.Plan sig where
  observations := .var (toCodeField domain codomain) .nil

theorem plan_rename (domain : Shape source)
    (codomain : Shape domain.scope)
    (mapping : Rename source target) :
    (plan domain codomain).rename mapping =
      plan (domain.rename mapping)
        (renameCodomain domain codomain mapping) := by
  unfold Package.Plan.rename plan
  simp only [Telescope.rename, toCodeField_rename]

theorem plan_subst (domain : Shape source)
    (codomain : Shape domain.scope)
    (substitution : Subst source target) :
    (plan domain codomain).subst substitution =
      plan (domain.subst substitution)
        (substCodomain domain codomain substitution) := by
  unfold Package.Plan.subst plan
  simp only [Telescope.subst, toCodeField_subst]

@[simp] theorem codeAtPayload_open (domain : Shape sig)
    (codomain : Shape domain.scope) (identity : Ty sig)
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

@[simp] theorem toCodeField_open (domain : Shape sig)
    (codomain : Shape domain.scope) (identity : Ty sig)
    (payload : Exp sig) :
    ((toCodeField domain codomain).subst
      ((Subst.openTVar identity).lift .var)).subst
        (Subst.openVar payload) =
      .arrow identity (codeTy domain codomain) := by
  simp only [toCodeField, Ty.subst, identityAtPayload_open,
    codeAtPayload_open]

/-- Dependent code in the complete opened function-plan scope. -/
def finalCodeTy (domain : Shape sig)
    (codomain : Shape domain.scope) : Ty (plan domain codomain).scope :=
  (codeTy domain codomain).rename (plan domain codomain).telescope.weaken

theorem finalCodeTy_rename (domain : Shape source)
    (codomain : Shape domain.scope)
    (mapping : Rename source target) :
    (finalCodeTy domain codomain).rename
        ((plan domain codomain).telescope.liftRename mapping) =
      finalCodeTy (domain.rename mapping)
        (renameCodomain domain codomain mapping) := by
  simpa only [finalCodeTy, Package.Plan.telescope_rename, plan_rename,
    codeTy_rename] using
      (plan domain codomain).telescope.weakenType_liftRename
        (codeTy domain codomain) mapping

theorem finalCodeTy_subst (domain : Shape source)
    (codomain : Shape domain.scope)
    (substitution : Subst source target) :
    (finalCodeTy domain codomain).subst
        ((plan domain codomain).telescope.liftSubst substitution) =
      finalCodeTy (domain.subst substitution)
        (substCodomain domain codomain substitution) := by
  simpa only [finalCodeTy, Package.Plan.telescope_subst, plan_subst,
    codeTy_subst] using
      (plan domain codomain).telescope.weakenType_liftSubst
        (codeTy domain codomain) substitution

/-- Opened ordinary function from the hidden identity to executable code. -/
def toCode (domain : Shape sig)
    (codomain : Shape domain.scope) : Exp (plan domain codomain).scope :=
  .var .here

theorem toCode_rename (domain : Shape source)
    (codomain : Shape domain.scope)
    (mapping : Rename source target) :
    (toCode domain codomain).rename
        ((plan domain codomain).telescope.liftRename mapping) =
      toCode (domain.rename mapping)
        (renameCodomain domain codomain mapping) := by
  rfl

theorem toCode_subst (domain : Shape source)
    (codomain : Shape domain.scope)
    (substitution : Subst source target) :
    (toCode domain codomain).subst
        ((plan domain codomain).telescope.liftSubst substitution) =
      toCode (domain.subst substitution)
        (substCodomain domain codomain substitution) := by
  rfl

noncomputable def toCode_hasType (base : Ctx sig)
    (domain : Shape sig) (codomain : Shape domain.scope) :
    Exp.HasType ((plan domain codomain).context base)
      (toCode domain codomain)
      (.arrow (plan domain codomain).identityTy
        (finalCodeTy domain codomain)) := by
  have identityEq :
      (plan domain codomain).identityTy =
        (Package.Plan.identityAtPayload sig).weaken .var := by
    unfold Package.Plan.identityTy plan Ty.weaken
    simp only [Telescope.weaken]
    congr 1
  have codeEq :
      finalCodeTy domain codomain =
        (codeAtPayload domain codomain).weaken .var := by
    unfold finalCodeTy codeAtPayload Package.Plan.telescope plan
    simp only [Telescope.weaken, Ty.weaken, Ty.rename_comp]
    congr 1
  rw [identityEq, codeEq]
  exact Exp.HasType.var Ctx.Lookup.here

/-- Apply the retained ordinary observation to the stable payload. -/
def asCode (domain : Shape sig)
    (codomain : Shape domain.scope) : Exp (plan domain codomain).scope :=
  Adapter.apply (toCode domain codomain) (plan domain codomain).payload

noncomputable def asCode_hasType (base : Ctx sig)
    (domain : Shape sig) (codomain : Shape domain.scope) :
    Exp.HasType ((plan domain codomain).context base)
      (asCode domain codomain) (finalCodeTy domain codomain) :=
  Adapter.apply_hasType (toCode_hasType base domain codomain)
    ((plan domain codomain).payload_hasType base)

theorem asCode_rename (domain : Shape source)
    (codomain : Shape domain.scope)
    (mapping : Rename source target) :
    (asCode domain codomain).rename
        ((plan domain codomain).telescope.liftRename mapping) =
      asCode (domain.rename mapping)
        (renameCodomain domain codomain mapping) := by
  unfold asCode Adapter.apply
  simp only [Exp.rename]
  rw [Package.Plan.payload_rename, toCode_rename]
  rfl

theorem asCode_subst (domain : Shape source)
    (codomain : Shape domain.scope)
    (substitution : Subst source target) :
    (asCode domain codomain).subst
        ((plan domain codomain).telescope.liftSubst substitution) =
      asCode (domain.subst substitution)
        (substCodomain domain codomain substitution) := by
  unfold asCode Adapter.apply
  simp only [Exp.subst]
  rw [Package.Plan.payload_subst, toCode_subst]
  rfl

theorem inputTy_rename (domain : Shape source)
    (codomain : Shape domain.scope)
    (mapping : Rename source target) :
    (plan domain codomain).inputTy.rename mapping =
      (plan (domain.rename mapping)
        (renameCodomain domain codomain mapping)).inputTy := by
  calc
    (plan domain codomain).inputTy.rename mapping =
        ((plan domain codomain).rename mapping).inputTy :=
      Package.Plan.inputTy_rename (plan domain codomain) mapping
    _ = _ := by rw [plan_rename]

theorem inputTy_subst (domain : Shape source)
    (codomain : Shape domain.scope)
    (substitution : Subst source target) :
    (plan domain codomain).inputTy.subst substitution =
      (plan (domain.subst substitution)
        (substCodomain domain codomain substitution)).inputTy := by
  calc
    (plan domain codomain).inputTy.subst substitution =
        ((plan domain codomain).subst substitution).inputTy :=
      Package.Plan.inputTy_subst (plan domain codomain) substitution
    _ = _ := by rw [plan_subst]

/-- Supply a hidden function identity, its payload, and its ordinary
`identity -> code` implementation function. -/
def arguments {sig : Sig} {base : Ctx sig}
    (domain : Shape sig) (codomain : Shape domain.scope)
    (identity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (toCodeFunction : Exp sig)
    (toCodeTyping : Exp.HasType base toCodeFunction
      (.arrow identity (codeTy domain codomain))) :
    Telescope.Args base (plan domain codomain).telescope :=
  .tvar identity (.var payload payloadTyping (.var toCodeFunction (by
    rw [toCodeField_open]
    exact toCodeTyping) .nil))

/-- Exact function arguments use the code type as identity. -/
noncomputable def exactArguments {sig : Sig} {base : Ctx sig}
    (domain : Shape sig) (codomain : Shape domain.scope)
    (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload (codeTy domain codomain)) :
    Telescope.Args base (plan domain codomain).telescope :=
  arguments domain codomain (codeTy domain codomain) payload payloadTyping
    (Adapter.identity (codeTy domain codomain))
    (Adapter.identity_hasType base (codeTy domain codomain))

noncomputable def exactPackage {sig : Sig} {base : Ctx sig}
    (domain : Shape sig) (codomain : Shape domain.scope)
    (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload (codeTy domain codomain)) :
    Exp sig :=
  (plan domain codomain).pack
    (exactArguments domain codomain payload payloadTyping)

noncomputable def exactPackage_hasType {sig : Sig} {base : Ctx sig}
    (domain : Shape sig) (codomain : Shape domain.scope)
    (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload (codeTy domain codomain)) :
    Exp.HasType base
      (exactPackage domain codomain payload payloadTyping)
      (plan domain codomain).inputTy :=
  (plan domain codomain).pack_hasType
    (exactArguments domain codomain payload payloadTyping)

end Function

namespace Pair

/-- Transport an expression from a suffix scope to the literal append scope. -/
def fromSuffixExp (first : Telescope sig)
    (suffix : Telescope first.scope) (expression : Exp suffix.scope) :
    Exp (first.append suffix).scope :=
  cast (congrArg Exp (first.appendScopeEq suffix).symm) expression

/-- Transport a type from a suffix scope to the literal append scope. -/
def fromSuffixTy (first : Telescope sig)
    (suffix : Telescope first.scope) (type : Ty suffix.scope) :
    Ty (first.append suffix).scope :=
  cast (congrArg Ty (first.appendScopeEq suffix).symm) type

/-- Church representation type after the outer hidden identity and payload. -/
def representationAtPayload (representation : Telescope sig) :
    Ty ((sig ,, .tvar) ,, .var) :=
  (representation.existsTy.weaken .tvar).weaken .var

theorem representationAtPayload_rename
    (representation : Telescope source) (mapping : Rename source target) :
    (representationAtPayload representation).rename
        ((mapping.lift .tvar).lift .var) =
      representationAtPayload (representation.rename mapping) := by
  unfold representationAtPayload
  rw [Ty.weaken_rename_comm, Ty.weaken_rename_comm,
    Package.existsTy_rename]

theorem representationAtPayload_subst
    (representation : Telescope source)
    (substitution : Subst source target) :
    (representationAtPayload representation).subst
        ((substitution.lift .tvar).lift .var) =
      representationAtPayload (representation.subst substitution) := by
  unfold representationAtPayload
  rw [← Ty.weaken_subst_comm_base, ← Ty.weaken_subst_comm_base,
    Package.existsTy_subst]

/-- Ordinary `I -> representation` observation retained by a pair package. -/
def toRepresentationField (representation : Telescope sig) :
    Ty ((sig ,, .tvar) ,, .var) :=
  .arrow (Package.Plan.identityAtPayload sig)
    (representationAtPayload representation)

theorem toRepresentationField_rename
    (representation : Telescope source) (mapping : Rename source target) :
    (toRepresentationField representation).rename
        ((mapping.lift .tvar).lift .var) =
      toRepresentationField (representation.rename mapping) := by
  simp only [toRepresentationField, Ty.rename,
    representationAtPayload_rename]
  rfl

theorem toRepresentationField_subst
    (representation : Telescope source)
    (substitution : Subst source target) :
    (toRepresentationField representation).subst
        ((substitution.lift .tvar).lift .var) =
      toRepresentationField (representation.subst substitution) := by
  simp only [toRepresentationField, Ty.subst,
    representationAtPayload_subst]
  rfl

/-- Canonical outer pair shell. -/
def plan (representation : Telescope sig) : Package.Plan sig where
  observations := .var (toRepresentationField representation) .nil

theorem plan_rename (representation : Telescope source)
    (mapping : Rename source target) :
    (plan representation).rename mapping =
      plan (representation.rename mapping) := by
  unfold Package.Plan.rename plan
  simp only [Telescope.rename, toRepresentationField_rename]

theorem plan_subst (representation : Telescope source)
    (substitution : Subst source target) :
    (plan representation).subst substitution =
      plan (representation.subst substitution) := by
  unfold Package.Plan.subst plan
  simp only [Telescope.subst, toRepresentationField_subst]

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

@[simp] theorem toRepresentationField_open
    (representation : Telescope sig) (identity : Ty sig)
    (payload : Exp sig) :
    ((toRepresentationField representation).subst
      ((Subst.openTVar identity).lift .var)).subst
        (Subst.openVar payload) =
      .arrow identity representation.existsTy := by
  simp only [toRepresentationField, Ty.subst,
    identityAtPayload_open, representationAtPayload_open]

/-- Representation type in the complete outer-pair interface. -/
def finalRepresentationTy (representation : Telescope sig) :
    Ty (plan representation).scope :=
  representation.existsTy.rename (plan representation).telescope.weaken

theorem finalRepresentationTy_rename
    (representation : Telescope source) (mapping : Rename source target) :
    (finalRepresentationTy representation).rename
        ((plan representation).telescope.liftRename mapping) =
      finalRepresentationTy (representation.rename mapping) := by
  simpa only [finalRepresentationTy, Package.Plan.telescope_rename,
    plan_rename, Package.existsTy_rename] using
      (plan representation).telescope.weakenType_liftRename
        representation.existsTy mapping

theorem finalRepresentationTy_subst
    (representation : Telescope source)
    (substitution : Subst source target) :
    (finalRepresentationTy representation).subst
        ((plan representation).telescope.liftSubst substitution) =
      finalRepresentationTy (representation.subst substitution) := by
  simpa only [finalRepresentationTy, Package.Plan.telescope_subst,
    plan_subst, Package.existsTy_subst] using
      (plan representation).telescope.weakenType_liftSubst
        representation.existsTy substitution

/-- Opened ordinary function from the pair identity to its representation. -/
def toRepresentation (representation : Telescope sig) :
    Exp (plan representation).scope :=
  .var .here

theorem toRepresentation_rename
    (representation : Telescope source) (mapping : Rename source target) :
    (toRepresentation representation).rename
        ((plan representation).telescope.liftRename mapping) =
      toRepresentation (representation.rename mapping) := by
  rfl

theorem toRepresentation_subst
    (representation : Telescope source)
    (substitution : Subst source target) :
    (toRepresentation representation).subst
        ((plan representation).telescope.liftSubst substitution) =
      toRepresentation (representation.subst substitution) := by
  rfl

noncomputable def toRepresentation_hasType (base : Ctx sig)
    (representation : Telescope sig) :
    Exp.HasType ((plan representation).context base)
      (toRepresentation representation)
      (.arrow (plan representation).identityTy
        (finalRepresentationTy representation)) := by
  have identityEq :
      (plan representation).identityTy =
        (Package.Plan.identityAtPayload sig).weaken .var := by
    unfold Package.Plan.identityTy plan Ty.weaken
    simp only [Telescope.weaken]
    congr 1
  have representationEq :
      finalRepresentationTy representation =
        (representationAtPayload representation).weaken .var := by
    unfold finalRepresentationTy representationAtPayload
      Package.Plan.telescope plan
    simp only [Telescope.weaken, Ty.weaken, Ty.rename_comp]
    congr 1
  rw [identityEq, representationEq]
  exact Exp.HasType.var Ctx.Lookup.here

/-- Observe the Church representation with ordinary application. -/
def asRepresentation (representation : Telescope sig) :
    Exp (plan representation).scope :=
  Adapter.apply (toRepresentation representation) (plan representation).payload

noncomputable def asRepresentation_hasType (base : Ctx sig)
    (representation : Telescope sig) :
    Exp.HasType ((plan representation).context base)
      (asRepresentation representation)
      (finalRepresentationTy representation) :=
  Adapter.apply_hasType (toRepresentation_hasType base representation)
    ((plan representation).payload_hasType base)

theorem asRepresentation_rename
    (representation : Telescope source) (mapping : Rename source target) :
    (asRepresentation representation).rename
        ((plan representation).telescope.liftRename mapping) =
      asRepresentation (representation.rename mapping) := by
  unfold asRepresentation Adapter.apply
  simp only [Exp.rename]
  rw [Package.Plan.payload_rename, toRepresentation_rename]
  rfl

theorem asRepresentation_subst
    (representation : Telescope source)
    (substitution : Subst source target) :
    (asRepresentation representation).subst
        ((plan representation).telescope.liftSubst substitution) =
      asRepresentation (representation.subst substitution) := by
  unfold asRepresentation Adapter.apply
  simp only [Exp.subst]
  rw [Package.Plan.payload_subst, toRepresentation_subst]
  rfl

theorem inputTy_rename (representation : Telescope source)
    (mapping : Rename source target) :
    (plan representation).inputTy.rename mapping =
      (plan (representation.rename mapping)).inputTy := by
  calc
    (plan representation).inputTy.rename mapping =
        ((plan representation).rename mapping).inputTy :=
      Package.Plan.inputTy_rename (plan representation) mapping
    _ = _ := by rw [plan_rename]

theorem inputTy_subst (representation : Telescope source)
    (substitution : Subst source target) :
    (plan representation).inputTy.subst substitution =
      (plan (representation.subst substitution)).inputTy := by
  calc
    (plan representation).inputTy.subst substitution =
        ((plan representation).subst substitution).inputTy :=
      Package.Plan.inputTy_subst (plan representation) substitution
    _ = _ := by rw [plan_subst]

/-- Exact outer-pair arguments package the supplied representation and use
ordinary identity as the sole outer observation. -/
noncomputable def exactArguments {sig : Sig} {base : Ctx sig}
    (representation : Telescope sig)
    (arguments : Telescope.Args base representation) :
    Telescope.Args base (plan representation).telescope :=
  .tvar representation.existsTy
    (.var (Telescope.pack arguments) (Telescope.pack_hasType arguments)
      (.var (Adapter.identity representation.existsTy) (by
        rw [toRepresentationField_open]
        exact Adapter.identity_hasType base representation.existsTy) .nil))

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

/-- First payload, viewed in a dependent suffix context. -/
def firstPayloadAtSuffix (first : Shape sig)
    (suffix : Telescope first.scope) : Exp suffix.scope :=
  first.value.rename suffix.weaken

/-- First identity, viewed in a dependent suffix context. -/
def firstIdentityAtSuffix (first : Shape sig)
    (suffix : Telescope first.scope) : Ty suffix.scope :=
  first.valueTy.rename suffix.weaken

noncomputable def firstPayloadAtSuffix_hasType (first : Shape sig)
    (suffix : Telescope first.scope) (base : Ctx sig) :
    Exp.HasType (suffix.context (first.context base))
      (firstPayloadAtSuffix first suffix)
      (firstIdentityAtSuffix first suffix) :=
  Package.weakenExp_hasType suffix (first.value_hasType base)

/-- Literal append-scope form of the retained first payload. -/
def firstPayload (first : Shape sig)
    (suffix : Telescope first.scope) :
    Exp (first.binders.append suffix).scope :=
  fromSuffixExp first.binders suffix (firstPayloadAtSuffix first suffix)

/-- Literal append-scope form of the retained first identity. -/
def firstIdentityTy (first : Shape sig)
    (suffix : Telescope first.scope) :
    Ty (first.binders.append suffix).scope :=
  fromSuffixTy first.binders suffix (firstIdentityAtSuffix first suffix)

end Pair

namespace Pair.Proper

/-- Reindex the dependent member with the complete first interface. -/
def renameMember (first : Shape source)
    (member : Shape first.scope) (mapping : Rename source target) :
    Shape (first.rename mapping).scope :=
  member.rename (first.liftRename mapping)

/-- Substitute the dependent member with the complete first interface. -/
def substMember (first : Shape source)
    (member : Shape first.scope)
    (substitution : Subst source target) :
    Shape (first.subst substitution).scope :=
  member.subst (first.liftSubst substitution)

/-- Proper representation: first interface followed by member interface. -/
def representation (first : Shape sig)
    (member : Shape first.scope) : Telescope sig :=
  first.binders.append member.binders

/-- Canonical proper-pair plan. -/
def plan (first : Shape sig)
    (member : Shape first.scope) : Package.Plan sig :=
  Pair.plan (representation first member)

theorem representation_rename (first : Shape source)
    (member : Shape first.scope) (mapping : Rename source target) :
    (representation first member).rename mapping =
      representation (first.rename mapping)
        (renameMember first member mapping) := by
  cases first with
  | stable plan =>
      unfold representation renameMember Shape.scope Shape.binders
        Shape.liftRename
      rw [Telescope.append_rename]
      change (plan.telescope.rename mapping).append
        (member.binders.rename (plan.telescope.liftRename mapping)) =
        (plan.telescope.rename mapping).append
          (member.rename (plan.telescope.liftRename mapping)).binders
      congr 1
      exact Shape.binders_rename member _
  | «opaque» type =>
      unfold representation renameMember Shape.scope Shape.binders
        Shape.liftRename
      rw [Telescope.append_rename]
      change ((Telescope.var type Telescope.nil).rename mapping).append
        (member.binders.rename
          ((Telescope.var type Telescope.nil).liftRename mapping)) =
        ((Telescope.var type Telescope.nil).rename mapping).append
          (member.rename
            ((Telescope.var type Telescope.nil).liftRename mapping)).binders
      congr 1
      exact Shape.binders_rename member _

theorem representation_subst (first : Shape source)
    (member : Shape first.scope)
    (substitution : Subst source target) :
    (representation first member).subst substitution =
      representation (first.subst substitution)
        (substMember first member substitution) := by
  cases first with
  | stable plan =>
      unfold representation substMember Shape.scope Shape.binders
        Shape.liftSubst
      rw [Telescope.append_subst]
      change (plan.telescope.subst substitution).append
        (member.binders.subst (plan.telescope.liftSubst substitution)) =
        (plan.telescope.subst substitution).append
          (member.subst (plan.telescope.liftSubst substitution)).binders
      congr 1
      exact Shape.binders_subst member _
  | «opaque» type =>
      unfold representation substMember Shape.scope Shape.binders
        Shape.liftSubst
      rw [Telescope.append_subst]
      change ((Telescope.var type Telescope.nil).subst substitution).append
        (member.binders.subst
          ((Telescope.var type Telescope.nil).liftSubst substitution)) =
        ((Telescope.var type Telescope.nil).subst substitution).append
          (member.subst
            ((Telescope.var type Telescope.nil).liftSubst
              substitution)).binders
      congr 1
      exact Shape.binders_subst member _

theorem plan_rename (first : Shape source)
    (member : Shape first.scope) (mapping : Rename source target) :
    (plan first member).rename mapping =
      plan (first.rename mapping) (renameMember first member mapping) := by
  unfold plan
  rw [Pair.plan_rename, representation_rename]

theorem plan_subst (first : Shape source)
    (member : Shape first.scope)
    (substitution : Subst source target) :
    (plan first member).subst substitution =
      plan (first.subst substitution)
        (substMember first member substitution) := by
  unfold plan
  rw [Pair.plan_subst, representation_subst]

/-- Proper first-value accessor in the nested member context. -/
def firstValue (first : Shape sig)
    (member : Shape first.scope) : Exp member.scope :=
  Pair.firstPayloadAtSuffix first member.binders

def firstValueTy (first : Shape sig)
    (member : Shape first.scope) : Ty member.scope :=
  Pair.firstIdentityAtSuffix first member.binders

noncomputable def firstValue_hasType (base : Ctx sig)
    (first : Shape sig) (member : Shape first.scope) :
    Exp.HasType (member.context (first.context base))
      (firstValue first member) (firstValueTy first member) :=
  Pair.firstPayloadAtSuffix_hasType first member.binders base

/-- Proper member-value accessor in the nested member context. -/
def memberValue (first : Shape sig)
    (member : Shape first.scope) : Exp member.scope :=
  member.value

def memberValueTy (first : Shape sig)
    (member : Shape first.scope) : Ty member.scope :=
  member.valueTy

noncomputable def memberValue_hasType (base : Ctx sig)
    (first : Shape sig) (member : Shape first.scope) :
    Exp.HasType (member.context (first.context base))
      (memberValue first member) (memberValueTy first member) :=
  member.value_hasType (first.context base)

theorem memberValue_rename (first : Shape source)
    (member : Shape first.scope) (mapping : Rename source target) :
    (memberValue first member).rename
        (member.liftRename (first.liftRename mapping)) =
      memberValue (first.rename mapping)
        (renameMember first member mapping) :=
  member.value_rename (first.liftRename mapping)

theorem memberValue_subst (first : Shape source)
    (member : Shape first.scope)
    (substitution : Subst source target) :
    (memberValue first member).subst
        (member.liftSubst (first.liftSubst substitution)) =
      memberValue (first.subst substitution)
        (substMember first member substitution) :=
  member.value_subst (first.liftSubst substitution)

theorem inputTy_rename (first : Shape source)
    (member : Shape first.scope) (mapping : Rename source target) :
    (plan first member).inputTy.rename mapping =
      (plan (first.rename mapping)
        (renameMember first member mapping)).inputTy := by
  unfold plan
  rw [Pair.inputTy_rename, representation_rename]

theorem inputTy_subst (first : Shape source)
    (member : Shape first.scope)
    (substitution : Subst source target) :
    (plan first member).inputTy.subst substitution =
      (plan (first.subst substitution)
        (substMember first member substitution)).inputTy := by
  unfold plan
  rw [Pair.inputTy_subst, representation_subst]

/-- Exact dependent representation arguments. -/
noncomputable def representationArguments
    {sig : Sig} {base : Ctx sig}
    (first : Shape sig) (member : Shape first.scope)
    (firstArguments : Telescope.Args base first.binders)
    (memberArguments : Telescope.Args base
      (member.binders.subst firstArguments.substitution)) :
    Telescope.Args base (representation first member) :=
  firstArguments.append member.binders memberArguments

noncomputable def exactArguments
    {sig : Sig} {base : Ctx sig}
    (first : Shape sig) (member : Shape first.scope)
    (firstArguments : Telescope.Args base first.binders)
    (memberArguments : Telescope.Args base
      (member.binders.subst firstArguments.substitution)) :
    Telescope.Args base (plan first member).telescope :=
  Pair.exactArguments (representation first member)
    (representationArguments first member firstArguments memberArguments)

noncomputable def exactPackage
    {sig : Sig} {base : Ctx sig}
    (first : Shape sig) (member : Shape first.scope)
    (firstArguments : Telescope.Args base first.binders)
    (memberArguments : Telescope.Args base
      (member.binders.subst firstArguments.substitution)) : Exp sig :=
  Pair.exactPackage (representation first member)
    (representationArguments first member firstArguments memberArguments)

noncomputable def exactPackage_hasType
    {sig : Sig} {base : Ctx sig}
    (first : Shape sig) (member : Shape first.scope)
    (firstArguments : Telescope.Args base first.binders)
    (memberArguments : Telescope.Args base
      (member.binders.subst firstArguments.substitution)) :
    Exp.HasType base
      (exactPackage first member firstArguments memberArguments)
      (plan first member).inputTy :=
  Pair.exactPackage_hasType (representation first member)
    (representationArguments first member firstArguments memberArguments)

end Pair.Proper

namespace Pair.Interval

/-- Lower ordinary function field under the hidden selected input type. -/
def lowerField (lower : Shape sig) : Ty (sig ,, .tvar) :=
  .arrow (lower.inputTy.weaken .tvar) (.tvar .here)

/-- Upper ordinary function field, weakened through the lower term field. -/
def upperField (upper : Shape sig) : Ty ((sig ,, .tvar) ,, .var) :=
  .arrow ((.tvar .here : Ty (sig ,, .tvar)).weaken .var)
    ((upper.inputTy.weaken .tvar).weaken .var)

/-- Tail under the hidden selected input type. -/
def memberTail (lower upper : Shape sig) : Telescope (sig ,, .tvar) :=
  .var (lowerField lower) (.var (upperField upper) .nil)

/-- Interval member: selected input type, lower function, upper function. -/
def memberTelescope (lower upper : Shape sig) : Telescope sig :=
  .tvar (memberTail lower upper)

/-- Opened interval member for one chosen witness shape. -/
def openedMember (lower upper witness : Shape sig) : Telescope sig :=
  .var (.arrow lower.inputTy witness.inputTy)
    (.var ((Ty.arrow witness.inputTy upper.inputTy).weaken .var) .nil)

theorem memberTail_open (lower upper witness : Shape sig) :
    (memberTail lower upper).subst (Subst.openTVar witness.inputTy) =
      openedMember lower upper witness := by
  unfold memberTail openedMember lowerField upperField
  simp only [Telescope.subst, Ty.subst]
  rw [lower.inputTy.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openTVar witness.inputTy)]
  change Telescope.var (.arrow lower.inputTy witness.inputTy)
    (Telescope.var
      (Ty.arrow
        (((.tvar .here : Ty (_ ,, .tvar)).weaken .var).subst
          ((Subst.openTVar witness.inputTy).lift .var))
        (((upper.inputTy.weaken .tvar).weaken .var).subst
          ((Subst.openTVar witness.inputTy).lift .var))) .nil) = _
  rw [← Ty.weaken_subst_comm_base, ← Ty.weaken_subst_comm_base]
  rw [upper.inputTy.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openTVar witness.inputTy)]
  rfl

theorem memberTelescope_rename (lower upper : Shape source)
    (mapping : Rename source target) :
    (memberTelescope lower upper).rename mapping =
      memberTelescope (lower.rename mapping) (upper.rename mapping) := by
  unfold memberTelescope memberTail lowerField upperField
  simp only [Telescope.rename, Ty.rename, Ty.weaken_rename_comm,
    Shape.inputTy_rename, Rename.lift_here]

theorem memberTelescope_subst (lower upper : Shape source)
    (substitution : Subst source target) :
    (memberTelescope lower upper).subst substitution =
      memberTelescope (lower.subst substitution)
        (upper.subst substitution) := by
  unfold memberTelescope memberTail lowerField upperField
  simp only [Telescope.subst, Ty.subst,
    ← Ty.weaken_subst_comm_base, Shape.inputTy_subst,
    Subst.lift_tvar_here]

/-- Interval representation: first interface followed by interval member. -/
def representation (first : Shape sig)
    (lower upper : Shape first.scope) : Telescope sig :=
  first.binders.append (memberTelescope lower upper)

/-- Canonical interval-pair plan. -/
def plan (first : Shape sig)
    (lower upper : Shape first.scope) : Package.Plan sig :=
  Pair.plan (representation first lower upper)

theorem representation_rename (first : Shape source)
    (lower upper : Shape first.scope)
    (mapping : Rename source target) :
    (representation first lower upper).rename mapping =
      representation (first.rename mapping)
        (lower.rename (first.liftRename mapping))
        (upper.rename (first.liftRename mapping)) := by
  cases first with
  | stable plan =>
      unfold representation Shape.scope Shape.binders Shape.liftRename
      rw [Telescope.append_rename, memberTelescope_rename]
      change (plan.telescope.rename mapping).append
        (memberTelescope
          (lower.rename (plan.telescope.liftRename mapping))
          (upper.rename (plan.telescope.liftRename mapping))) = _
      rfl
  | «opaque» type =>
      unfold representation Shape.scope Shape.binders Shape.liftRename
      rw [Telescope.append_rename, memberTelescope_rename]
      change ((Telescope.var type Telescope.nil).rename mapping).append
        (memberTelescope
          (lower.rename
            ((Telescope.var type Telescope.nil).liftRename mapping))
          (upper.rename
            ((Telescope.var type Telescope.nil).liftRename mapping))) = _
      rfl

theorem representation_subst (first : Shape source)
    (lower upper : Shape first.scope)
    (substitution : Subst source target) :
    (representation first lower upper).subst substitution =
      representation (first.subst substitution)
        (lower.subst (first.liftSubst substitution))
        (upper.subst (first.liftSubst substitution)) := by
  cases first with
  | stable plan =>
      unfold representation Shape.scope Shape.binders Shape.liftSubst
      rw [Telescope.append_subst, memberTelescope_subst]
      change (plan.telescope.subst substitution).append
        (memberTelescope
          (lower.subst (plan.telescope.liftSubst substitution))
          (upper.subst (plan.telescope.liftSubst substitution))) = _
      rfl
  | «opaque» type =>
      unfold representation Shape.scope Shape.binders Shape.liftSubst
      rw [Telescope.append_subst, memberTelescope_subst]
      change ((Telescope.var type Telescope.nil).subst substitution).append
        (memberTelescope
          (lower.subst
            ((Telescope.var type Telescope.nil).liftSubst substitution))
          (upper.subst
            ((Telescope.var type Telescope.nil).liftSubst substitution))) = _
      rfl

theorem plan_rename (first : Shape source)
    (lower upper : Shape first.scope)
    (mapping : Rename source target) :
    (plan first lower upper).rename mapping =
      plan (first.rename mapping)
        (lower.rename (first.liftRename mapping))
        (upper.rename (first.liftRename mapping)) := by
  unfold plan
  rw [Pair.plan_rename, representation_rename]

theorem plan_subst (first : Shape source)
    (lower upper : Shape first.scope)
    (substitution : Subst source target) :
    (plan first lower upper).subst substitution =
      plan (first.subst substitution)
        (lower.subst (first.liftSubst substitution))
        (upper.subst (first.liftSubst substitution)) := by
  unfold plan
  rw [Pair.plan_subst, representation_subst]

/-- Hidden selected package-input type in the final member scope. -/
def selectedTy (lower upper : Shape sig) :
    Ty (memberTelescope lower upper).scope :=
  .tvar (.there (.there .here))

def lowerTy (lower upper : Shape sig) :
    Ty (memberTelescope lower upper).scope :=
  lower.inputTy.rename (memberTelescope lower upper).weaken

def upperTy (lower upper : Shape sig) :
    Ty (memberTelescope lower upper).scope :=
  upper.inputTy.rename (memberTelescope lower upper).weaken

/-- Opened lower-to-selected ordinary function. -/
def lowerFunction (lower upper : Shape sig) :
    Exp (memberTelescope lower upper).scope :=
  .var (.there .here)

/-- Opened selected-to-upper ordinary function. -/
def upperFunction (lower upper : Shape sig) :
    Exp (memberTelescope lower upper).scope :=
  .var .here

noncomputable def lowerFunction_hasType (base : Ctx sig)
    (lower upper : Shape sig) :
    Exp.HasType ((memberTelescope lower upper).context base)
      (lowerFunction lower upper)
      (.arrow (lowerTy lower upper) (selectedTy lower upper)) := by
  simpa [memberTelescope, memberTail, lowerField, upperField,
    lowerFunction, lowerTy, selectedTy, Telescope.context,
    Telescope.weaken, Ty.weaken, Ty.rename, Ty.rename_comp,
    Shape.rename_comp, Rename.comp_assoc, Rename.comp_id] using
    (Exp.HasType.var
      (Ctx.Lookup.there Ctx.Lookup.here : Ctx.VarLookup
        ((memberTelescope lower upper).context base) (.there .here) _))

noncomputable def upperFunction_hasType (base : Ctx sig)
    (lower upper : Shape sig) :
    Exp.HasType ((memberTelescope lower upper).context base)
      (upperFunction lower upper)
      (.arrow (selectedTy lower upper) (upperTy lower upper)) := by
  simpa [memberTelescope, memberTail, lowerField, upperField,
    upperFunction, upperTy, selectedTy, Telescope.context,
    Telescope.weaken, Ty.weaken, Ty.rename, Ty.rename_comp,
    Shape.rename_comp, Rename.comp_assoc, Rename.comp_id] using
    (Exp.HasType.var
      (Ctx.Lookup.here : Ctx.VarLookup
        ((memberTelescope lower upper).context base) .here _))

theorem selectedTy_rename (lower upper : Shape source)
    (mapping : Rename source target) :
    (selectedTy lower upper).rename
        ((memberTelescope lower upper).liftRename mapping) =
      selectedTy (lower.rename mapping) (upper.rename mapping) := by
  rfl

theorem selectedTy_subst (lower upper : Shape source)
    (substitution : Subst source target) :
    (selectedTy lower upper).subst
        ((memberTelescope lower upper).liftSubst substitution) =
      selectedTy (lower.subst substitution)
        (upper.subst substitution) := by
  rfl

theorem lowerTy_rename (lower upper : Shape source)
    (mapping : Rename source target) :
    (lowerTy lower upper).rename
        ((memberTelescope lower upper).liftRename mapping) =
      lowerTy (lower.rename mapping) (upper.rename mapping) := by
  simpa only [lowerTy, memberTelescope_rename,
    Shape.inputTy_rename] using
    (memberTelescope lower upper).weakenType_liftRename
      lower.inputTy mapping

theorem lowerTy_subst (lower upper : Shape source)
    (substitution : Subst source target) :
    (lowerTy lower upper).subst
        ((memberTelescope lower upper).liftSubst substitution) =
      lowerTy (lower.subst substitution)
        (upper.subst substitution) := by
  simpa only [lowerTy, memberTelescope_subst,
    Shape.inputTy_subst] using
    (memberTelescope lower upper).weakenType_liftSubst
      lower.inputTy substitution

theorem upperTy_rename (lower upper : Shape source)
    (mapping : Rename source target) :
    (upperTy lower upper).rename
        ((memberTelescope lower upper).liftRename mapping) =
      upperTy (lower.rename mapping) (upper.rename mapping) := by
  simpa only [upperTy, memberTelescope_rename,
    Shape.inputTy_rename] using
    (memberTelescope lower upper).weakenType_liftRename
      upper.inputTy mapping

theorem upperTy_subst (lower upper : Shape source)
    (substitution : Subst source target) :
    (upperTy lower upper).subst
        ((memberTelescope lower upper).liftSubst substitution) =
      upperTy (lower.subst substitution)
        (upper.subst substitution) := by
  simpa only [upperTy, memberTelescope_subst,
    Shape.inputTy_subst] using
    (memberTelescope lower upper).weakenType_liftSubst
      upper.inputTy substitution

theorem lowerFunction_rename (lower upper : Shape source)
    (mapping : Rename source target) :
    (lowerFunction lower upper).rename
        ((memberTelescope lower upper).liftRename mapping) =
      lowerFunction (lower.rename mapping) (upper.rename mapping) := by
  rfl

theorem lowerFunction_subst (lower upper : Shape source)
    (substitution : Subst source target) :
    (lowerFunction lower upper).subst
        ((memberTelescope lower upper).liftSubst substitution) =
      lowerFunction (lower.subst substitution)
        (upper.subst substitution) := by
  rfl

theorem upperFunction_rename (lower upper : Shape source)
    (mapping : Rename source target) :
    (upperFunction lower upper).rename
        ((memberTelescope lower upper).liftRename mapping) =
      upperFunction (lower.rename mapping) (upper.rename mapping) := by
  rfl

theorem upperFunction_subst (lower upper : Shape source)
    (substitution : Subst source target) :
    (upperFunction lower upper).subst
        ((memberTelescope lower upper).liftSubst substitution) =
      upperFunction (lower.subst substitution)
        (upper.subst substitution) := by
  rfl

theorem inputTy_rename (first : Shape source)
    (lower upper : Shape first.scope)
    (mapping : Rename source target) :
    (plan first lower upper).inputTy.rename mapping =
      (plan (first.rename mapping)
        (lower.rename (first.liftRename mapping))
        (upper.rename (first.liftRename mapping))).inputTy := by
  unfold plan
  rw [Pair.inputTy_rename, representation_rename]

theorem inputTy_subst (first : Shape source)
    (lower upper : Shape first.scope)
    (substitution : Subst source target) :
    (plan first lower upper).inputTy.subst substitution =
      (plan (first.subst substitution)
        (lower.subst (first.liftSubst substitution))
        (upper.subst (first.liftSubst substitution))).inputTy := by
  unfold plan
  rw [Pair.inputTy_subst, representation_subst]

/-- First value in the nested interval-member context. -/
def firstValue (first : Shape sig)
    (lower upper : Shape first.scope) :
    Exp (memberTelescope lower upper).scope :=
  Pair.firstPayloadAtSuffix first (memberTelescope lower upper)

def firstValueTy (first : Shape sig)
    (lower upper : Shape first.scope) :
    Ty (memberTelescope lower upper).scope :=
  Pair.firstIdentityAtSuffix first (memberTelescope lower upper)

noncomputable def firstValue_hasType (base : Ctx sig)
    (first : Shape sig)
    (lower upper : Shape first.scope) :
    Exp.HasType
      ((memberTelescope lower upper).context (first.context base))
      (firstValue first lower upper) (firstValueTy first lower upper) :=
  Pair.firstPayloadAtSuffix_hasType first (memberTelescope lower upper) base

/-- The abstract shape exposed after opening an interval member. No stable
plan is fabricated for the hidden selected type. -/
def selectedShape (lower upper : Shape sig) :
    Shape (memberTelescope lower upper).scope :=
  .opaque (selectedTy lower upper)

theorem selectedShape_rename (lower upper : Shape source)
    (mapping : Rename source target) :
    (selectedShape lower upper).rename
        ((memberTelescope lower upper).liftRename mapping) =
      selectedShape (lower.rename mapping) (upper.rename mapping) := by
  change Shape.opaque ((selectedTy lower upper).rename
    ((memberTelescope lower upper).liftRename mapping)) = _
  rw [selectedTy_rename]
  rfl

theorem selectedShape_subst (lower upper : Shape source)
    (substitution : Subst source target) :
    (selectedShape lower upper).subst
        ((memberTelescope lower upper).liftSubst substitution) =
      selectedShape (lower.subst substitution)
        (upper.subst substitution) := by
  change Shape.opaque ((selectedTy lower upper).subst
    ((memberTelescope lower upper).liftSubst substitution)) = _
  rw [selectedTy_subst]
  rfl

/-- Opened arguments for one chosen witness shape. -/
noncomputable def openedArguments
    {sig : Sig} (base : Ctx sig)
    (lower upper witness : Shape sig)
    (lowerFunction : Exp sig)
    (lowerTyping : Exp.HasType base lowerFunction
      (.arrow lower.inputTy witness.inputTy))
    (upperFunction : Exp sig)
    (upperTyping : Exp.HasType base upperFunction
      (.arrow witness.inputTy upper.inputTy)) :
    Telescope.Args base (openedMember lower upper witness) := by
  refine .var lowerFunction lowerTyping ?_
  refine .var upperFunction ?_ .nil
  rw [(Ty.arrow witness.inputTy upper.inputTy).weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openVar lowerFunction)]
  exact upperTyping

/-- Interval-member arguments hide `witness.inputTy` at runtime. -/
noncomputable def memberArguments
    {sig : Sig} (base : Ctx sig)
    (lower upper witness : Shape sig)
    (lowerFunction : Exp sig)
    (lowerTyping : Exp.HasType base lowerFunction
      (.arrow lower.inputTy witness.inputTy))
    (upperFunction : Exp sig)
    (upperTyping : Exp.HasType base upperFunction
      (.arrow witness.inputTy upper.inputTy)) :
    Telescope.Args base (memberTelescope lower upper) :=
  .tvar witness.inputTy
    ((memberTail_open lower upper witness).symm ▸
      openedArguments base lower upper witness lowerFunction lowerTyping
        upperFunction upperTyping)

/-- Exact interval representation arguments after the precise first
interface substitution. -/
noncomputable def representationArguments
    {sig : Sig} {base : Ctx sig}
    (first : Shape sig)
    (lower upper : Shape first.scope)
    (firstInterface : Shape.Interface base first)
    (witness : Shape sig)
    (lowerFunction : Exp sig)
    (lowerTyping : Exp.HasType base lowerFunction
      (.arrow (lower.subst firstInterface.substitution).inputTy
        witness.inputTy))
    (upperFunction : Exp sig)
    (upperTyping : Exp.HasType base upperFunction
      (.arrow witness.inputTy
        (upper.subst firstInterface.substitution).inputTy)) :
    Telescope.Args base (representation first lower upper) := by
  rw [firstInterface.arguments_substitution.symm] at lowerTyping
  rw [firstInterface.arguments_substitution.symm] at upperTyping
  let supplied := memberArguments base
    (lower.subst firstInterface.arguments.substitution)
    (upper.subst firstInterface.arguments.substitution) witness lowerFunction
    lowerTyping upperFunction upperTyping
  have reindexed := memberTelescope_subst lower upper
    firstInterface.arguments.substitution
  exact firstInterface.arguments.append (memberTelescope lower upper)
    (reindexed.symm ▸ supplied)

/-- Outer arguments for an exact interval-pair package. -/
noncomputable def exactArguments
    {sig : Sig} {base : Ctx sig}
    (first : Shape sig)
    (lower upper : Shape first.scope)
    (firstInterface : Shape.Interface base first)
    (witness : Shape sig)
    (lowerFunction : Exp sig)
    (lowerTyping : Exp.HasType base lowerFunction
      (.arrow (lower.subst firstInterface.substitution).inputTy
        witness.inputTy))
    (upperFunction : Exp sig)
    (upperTyping : Exp.HasType base upperFunction
      (.arrow witness.inputTy
        (upper.subst firstInterface.substitution).inputTy)) :
    Telescope.Args base (plan first lower upper).telescope :=
  Pair.exactArguments (representation first lower upper)
    (representationArguments first lower upper firstInterface witness
      lowerFunction lowerTyping upperFunction upperTyping)

/-- Exact interval-pair construction with a chosen witness shape. -/
noncomputable def exactPackage
    {sig : Sig} {base : Ctx sig}
    (first : Shape sig)
    (lower upper : Shape first.scope)
    (firstInterface : Shape.Interface base first)
    (witness : Shape sig)
    (lowerFunction : Exp sig)
    (lowerTyping : Exp.HasType base lowerFunction
      (.arrow (lower.subst firstInterface.substitution).inputTy
        witness.inputTy))
    (upperFunction : Exp sig)
    (upperTyping : Exp.HasType base upperFunction
      (.arrow witness.inputTy
        (upper.subst firstInterface.substitution).inputTy)) : Exp sig :=
  Pair.exactPackage (representation first lower upper)
    (representationArguments first lower upper firstInterface witness
      lowerFunction lowerTyping upperFunction upperTyping)

noncomputable def exactPackage_hasType
    {sig : Sig} {base : Ctx sig}
    (first : Shape sig)
    (lower upper : Shape first.scope)
    (firstInterface : Shape.Interface base first)
    (witness : Shape sig)
    (lowerFunction : Exp sig)
    (lowerTyping : Exp.HasType base lowerFunction
      (.arrow (lower.subst firstInterface.substitution).inputTy
        witness.inputTy))
    (upperFunction : Exp sig)
    (upperTyping : Exp.HasType base upperFunction
      (.arrow witness.inputTy
        (upper.subst firstInterface.substitution).inputTy)) :
    Exp.HasType base
      (exactPackage first lower upper firstInterface witness lowerFunction
        lowerTyping upperFunction upperTyping)
      (plan first lower upper).inputTy :=
  Pair.exactPackage_hasType (representation first lower upper)
    (representationArguments first lower upper firstInterface witness
      lowerFunction lowerTyping upperFunction upperTyping)

/-- Exact source `tpair`: the opened endpoint shape itself is selected and both
package maps are ordinary identity functions. -/
noncomputable def exactTypePair
    {sig : Sig} {base : Ctx sig}
    (first : Shape sig) (endpoint : Shape first.scope)
    (firstInterface : Shape.Interface base first) : Exp sig :=
  let opened := endpoint.subst firstInterface.substitution
  exactPackage first endpoint endpoint firstInterface opened
    (Adapter.identity opened.inputTy)
    (Adapter.identity_hasType base opened.inputTy)
    (Adapter.identity opened.inputTy)
    (Adapter.identity_hasType base opened.inputTy)

noncomputable def exactTypePair_hasType
    {sig : Sig} {base : Ctx sig}
    (first : Shape sig) (endpoint : Shape first.scope)
    (firstInterface : Shape.Interface base first) :
    Exp.HasType base (exactTypePair first endpoint firstInterface)
      (plan first endpoint endpoint).inputTy := by
  exact exactPackage_hasType first endpoint endpoint firstInterface
    (endpoint.subst firstInterface.substitution)
    (Adapter.identity
      (endpoint.subst firstInterface.substitution).inputTy)
    (Adapter.identity_hasType base
      (endpoint.subst firstInterface.substitution).inputTy)
    (Adapter.identity
      (endpoint.subst firstInterface.substitution).inputTy)
    (Adapter.identity_hasType base
      (endpoint.subst firstInterface.substitution).inputTy)

end Pair.Interval

end LambdaPToFCo.Direct
