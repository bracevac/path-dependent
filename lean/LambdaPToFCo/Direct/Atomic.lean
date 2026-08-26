import LambdaPToFCo.Direct.Package

/-!
# Canonical atomic plans for the direct compiler

This target-only leaf supplies the canonical plans for source Top, Bottom,
and singleton.  A selected interval endpoint retains its already selected
plan directly rather than receiving another wrapper plan.  Every
computational observation is an ordinary `SystemFCo.Exp` function field. In
particular, singleton bridges are the two term fields `R -> I` and `I -> R`;
they are not coercion binders.

The final section builds stable package-to-package functions.  Repacking
reuses the exact hidden identity type and payload obtained by opening the
source package.  Bottom synthesis is deliberately restricted to telescopes
whose fields are term or type fields, so it cannot manufacture arbitrary
target coercions.
-/

namespace LambdaPToFCo.Direct

open SystemFCo

/-! ## Observation-free Top -/

namespace Top

def plan (sig : Sig) : Package.Plan sig :=
  Package.topPlan sig

@[simp] theorem plan_rename (mapping : Rename source target) :
    (plan source).rename mapping = plan target := by
  rfl

@[simp] theorem plan_subst (substitution : Subst source target) :
    (plan source).subst substitution = plan target := by
  rfl

theorem inputTy_rename (mapping : Rename source target) :
    (plan source).inputTy.rename mapping = (plan target).inputTy := by
  rw [Package.Plan.inputTy_rename, plan_rename]

theorem inputTy_subst (substitution : Subst source target) :
    (plan source).inputTy.subst substitution = (plan target).inputTy := by
  rw [Package.Plan.inputTy_subst, plan_subst]

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

/-! ## Bottom with an ordinary eliminator field -/

namespace Bot

def eliminatorAtPayload (sig : Sig) :
    Ty ((sig ,, .tvar) ,, .var) :=
  .arrow (Package.Plan.identityAtPayload sig)
    (Adapter.bottomTy : Ty ((sig ,, .tvar) ,, .var))

def plan (sig : Sig) : Package.Plan sig where
  observations := .var (eliminatorAtPayload sig) .nil

@[simp] theorem bottomTy_rename (mapping : Rename source target) :
    (Adapter.bottomTy : Ty source).rename mapping =
      (Adapter.bottomTy : Ty target) := by
  rfl

@[simp] theorem bottomTy_subst (substitution : Subst source target) :
    (Adapter.bottomTy : Ty source).subst substitution =
      (Adapter.bottomTy : Ty target) := by
  rfl

@[simp] theorem identityAtPayload_rename
    (mapping : Rename source target) :
    (Package.Plan.identityAtPayload source).rename
        ((mapping.lift .tvar).lift .var) =
      Package.Plan.identityAtPayload target := by
  rfl

@[simp] theorem identityAtPayload_subst
    (substitution : Subst source target) :
    (Package.Plan.identityAtPayload source).subst
        ((substitution.lift .tvar).lift .var) =
      Package.Plan.identityAtPayload target := by
  rfl

@[simp] theorem eliminatorAtPayload_rename
    (mapping : Rename source target) :
    (eliminatorAtPayload source).rename
        ((mapping.lift .tvar).lift .var) =
      eliminatorAtPayload target := by
  simp only [eliminatorAtPayload, Ty.rename, identityAtPayload_rename,
    bottomTy_rename]

@[simp] theorem eliminatorAtPayload_subst
    (substitution : Subst source target) :
    (eliminatorAtPayload source).subst
        ((substitution.lift .tvar).lift .var) =
      eliminatorAtPayload target := by
  simp only [eliminatorAtPayload, Ty.subst, identityAtPayload_subst,
    bottomTy_subst]

@[simp] theorem plan_rename (mapping : Rename source target) :
    (plan source).rename mapping = plan target := by
  unfold Package.Plan.rename plan
  simp only [Telescope.rename, eliminatorAtPayload_rename]

@[simp] theorem plan_subst (substitution : Subst source target) :
    (plan source).subst substitution = plan target := by
  unfold Package.Plan.subst plan
  simp only [Telescope.subst, eliminatorAtPayload_subst]

theorem inputTy_rename (mapping : Rename source target) :
    (plan source).inputTy.rename mapping = (plan target).inputTy := by
  rw [Package.Plan.inputTy_rename, plan_rename]

theorem inputTy_subst (substitution : Subst source target) :
    (plan source).inputTy.subst substitution = (plan target).inputTy := by
  rw [Package.Plan.inputTy_subst, plan_subst]

@[simp] theorem identityAtPayload_open (identity : Ty sig)
    (payload : Exp sig) :
    ((Package.Plan.identityAtPayload sig).subst
      ((Subst.openTVar identity).lift .var)).subst
        (Subst.openVar payload) = identity := by
  unfold Package.Plan.identityAtPayload
  change (identity.weaken .var).subst (Subst.openVar payload) = identity
  exact identity.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openVar payload)

@[simp] theorem eliminatorAtPayload_open (identity : Ty sig)
    (payload : Exp sig) :
    ((eliminatorAtPayload sig).subst
      ((Subst.openTVar identity).lift .var)).subst
        (Subst.openVar payload) =
      .arrow identity Adapter.bottomTy := by
  simp only [eliminatorAtPayload, Ty.subst, identityAtPayload_open,
    bottomTy_subst]

def eliminator (sig : Sig) : Exp (plan sig).scope :=
  .var .here

theorem eliminator_rename (mapping : Rename source target) :
    (eliminator source).rename
        ((plan source).telescope.liftRename mapping) =
      eliminator target := by
  rfl

theorem eliminator_subst (substitution : Subst source target) :
    (eliminator source).subst
        ((plan source).telescope.liftSubst substitution) =
      eliminator target := by
  rfl

noncomputable def eliminator_hasType (base : Ctx sig) :
    Exp.HasType ((plan sig).context base) (eliminator sig)
      (.arrow (plan sig).identityTy Adapter.bottomTy) := by
  exact .var Ctx.Lookup.here

def eliminatePayload (sig : Sig) : Exp (plan sig).scope :=
  Adapter.apply (eliminator sig) (plan sig).payload

theorem eliminatePayload_rename (mapping : Rename source target) :
    (eliminatePayload source).rename
        ((plan source).telescope.liftRename mapping) =
      eliminatePayload target := by
  rfl

theorem eliminatePayload_subst (substitution : Subst source target) :
    (eliminatePayload source).subst
        ((plan source).telescope.liftSubst substitution) =
      eliminatePayload target := by
  rfl

noncomputable def eliminatePayload_hasType (base : Ctx sig) :
    Exp.HasType ((plan sig).context base) (eliminatePayload sig)
      Adapter.bottomTy :=
  Adapter.apply_hasType (eliminator_hasType base)
    ((plan sig).payload_hasType base)

def arguments {sig : Sig} {base : Ctx sig}
    (identity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (eliminator : Exp sig)
    (eliminatorTyping : Exp.HasType base eliminator
      (.arrow identity Adapter.bottomTy)) :
    Telescope.Args base (plan sig).telescope :=
  .tvar identity (.var payload payloadTyping (.var eliminator (by
    rw [eliminatorAtPayload_open]
    exact eliminatorTyping) .nil))

noncomputable def package {sig : Sig} {base : Ctx sig}
    (identity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (eliminator : Exp sig)
    (eliminatorTyping : Exp.HasType base eliminator
      (.arrow identity Adapter.bottomTy)) : Exp sig :=
  (plan sig).pack
    (arguments identity payload payloadTyping eliminator eliminatorTyping)

noncomputable def package_hasType {sig : Sig} {base : Ctx sig}
    (identity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (eliminator : Exp sig)
    (eliminatorTyping : Exp.HasType base eliminator
      (.arrow identity Adapter.bottomTy)) :
    Exp.HasType base
      (package identity payload payloadTyping eliminator eliminatorTyping)
      (plan sig).inputTy :=
  (plan sig).pack_hasType
    (arguments identity payload payloadTyping eliminator eliminatorTyping)

end Bot

/-! ## Singleton identity bridges -/

namespace Single

/-- The singleton plan is the exact interval plan at its referent identity.
The older field is `referent -> I`; the newer field is `I -> referent`. -/
def plan (referentIdentity : Ty sig) : Package.Plan sig :=
  Package.identityPlan referentIdentity

@[simp] theorem plan_rename (referentIdentity : Ty source)
    (mapping : Rename source target) :
    (plan referentIdentity).rename mapping =
      plan (referentIdentity.rename mapping) := by
  unfold plan Package.identityPlan Package.Plan.rename
    Package.Interval.plan Package.Interval.lowerField
    Package.Interval.upperField
  simp only [Telescope.rename, Ty.rename, Ty.weaken_rename_comm]
  rfl

@[simp] theorem plan_subst (referentIdentity : Ty source)
    (substitution : Subst source target) :
    (plan referentIdentity).subst substitution =
      plan (referentIdentity.subst substitution) := by
  unfold plan Package.identityPlan Package.Plan.subst
    Package.Interval.plan Package.Interval.lowerField
    Package.Interval.upperField
  simp only [Telescope.subst, Ty.subst, ← Ty.weaken_subst_comm_base]
  rfl

def referentTy (referentIdentity : Ty sig) :
    Ty (plan referentIdentity).scope :=
  referentIdentity.rename (plan referentIdentity).telescope.weaken

theorem referentTy_rename (referentIdentity : Ty source)
    (mapping : Rename source target) :
    (referentTy referentIdentity).rename
        ((plan referentIdentity).telescope.liftRename mapping) =
      referentTy (referentIdentity.rename mapping) := by
  simpa only [referentTy, Package.Plan.telescope_rename, plan_rename] using
    (plan referentIdentity).telescope.weakenType_liftRename
      referentIdentity mapping

theorem referentTy_subst (referentIdentity : Ty source)
    (substitution : Subst source target) :
    (referentTy referentIdentity).subst
        ((plan referentIdentity).telescope.liftSubst substitution) =
      referentTy (referentIdentity.subst substitution) := by
  simpa only [referentTy, Package.Plan.telescope_subst, plan_subst] using
    (plan referentIdentity).telescope.weakenType_liftSubst
      referentIdentity substitution

/-- Opened bridge from the referent identity to the hidden identity. -/
def fromReferent (referentIdentity : Ty sig) :
    Exp (plan referentIdentity).scope :=
  Package.Interval.lowerFunction referentIdentity referentIdentity

/-- Opened bridge from the hidden identity to the referent identity. -/
def toReferent (referentIdentity : Ty sig) :
    Exp (plan referentIdentity).scope :=
  Package.Interval.upperFunction referentIdentity referentIdentity

noncomputable def fromReferent_hasType (base : Ctx sig)
    (referentIdentity : Ty sig) :
    Exp.HasType ((plan referentIdentity).context base)
      (fromReferent referentIdentity)
      (.arrow (referentTy referentIdentity)
        (plan referentIdentity).identityTy) :=
  Package.Interval.lowerFunction_hasType base referentIdentity
    referentIdentity

noncomputable def toReferent_hasType (base : Ctx sig)
    (referentIdentity : Ty sig) :
    Exp.HasType ((plan referentIdentity).context base)
      (toReferent referentIdentity)
      (.arrow (plan referentIdentity).identityTy
        (referentTy referentIdentity)) :=
  Package.Interval.upperFunction_hasType base referentIdentity
    referentIdentity

theorem fromReferent_rename (referentIdentity : Ty source)
    (mapping : Rename source target) :
    (fromReferent referentIdentity).rename
        ((plan referentIdentity).telescope.liftRename mapping) =
      fromReferent (referentIdentity.rename mapping) := by
  rfl

theorem toReferent_rename (referentIdentity : Ty source)
    (mapping : Rename source target) :
    (toReferent referentIdentity).rename
        ((plan referentIdentity).telescope.liftRename mapping) =
      toReferent (referentIdentity.rename mapping) := by
  rfl

theorem fromReferent_subst (referentIdentity : Ty source)
    (substitution : Subst source target) :
    (fromReferent referentIdentity).subst
        ((plan referentIdentity).telescope.liftSubst substitution) =
      fromReferent (referentIdentity.subst substitution) := by
  rfl

theorem toReferent_subst (referentIdentity : Ty source)
    (substitution : Subst source target) :
    (toReferent referentIdentity).subst
        ((plan referentIdentity).telescope.liftSubst substitution) =
      toReferent (referentIdentity.subst substitution) := by
  rfl

def payloadAsReferent (referentIdentity : Ty sig) :
    Exp (plan referentIdentity).scope :=
  Adapter.apply (toReferent referentIdentity)
    (plan referentIdentity).payload

noncomputable def payloadAsReferent_hasType (base : Ctx sig)
    (referentIdentity : Ty sig) :
    Exp.HasType ((plan referentIdentity).context base)
      (payloadAsReferent referentIdentity)
      (referentTy referentIdentity) :=
  Adapter.apply_hasType (toReferent_hasType base referentIdentity)
    ((plan referentIdentity).payload_hasType base)

theorem payloadAsReferent_rename (referentIdentity : Ty source)
    (mapping : Rename source target) :
    (payloadAsReferent referentIdentity).rename
        ((plan referentIdentity).telescope.liftRename mapping) =
      payloadAsReferent (referentIdentity.rename mapping) := by
  rfl

theorem payloadAsReferent_subst (referentIdentity : Ty source)
    (substitution : Subst source target) :
    (payloadAsReferent referentIdentity).subst
        ((plan referentIdentity).telescope.liftSubst substitution) =
      payloadAsReferent (referentIdentity.subst substitution) := by
  rfl

theorem inputTy_rename (referentIdentity : Ty source)
    (mapping : Rename source target) :
    (plan referentIdentity).inputTy.rename mapping =
      (plan (referentIdentity.rename mapping)).inputTy := by
  rw [Package.Plan.inputTy_rename, plan_rename]

theorem inputTy_subst (referentIdentity : Ty source)
    (substitution : Subst source target) :
    (plan referentIdentity).inputTy.subst substitution =
      (plan (referentIdentity.subst substitution)).inputTy := by
  rw [Package.Plan.inputTy_subst, plan_subst]

def arguments {sig : Sig} {base : Ctx sig}
    (referentIdentity identity : Ty sig)
    (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (toReferentFunction : Exp sig)
    (toReferentTyping : Exp.HasType base toReferentFunction
      (.arrow identity referentIdentity))
    (fromReferentFunction : Exp sig)
    (fromReferentTyping : Exp.HasType base fromReferentFunction
      (.arrow referentIdentity identity)) :
    Telescope.Args base (plan referentIdentity).telescope :=
  Package.Interval.exactArguments referentIdentity referentIdentity identity
    payload fromReferentFunction toReferentFunction payloadTyping
    fromReferentTyping toReferentTyping

noncomputable def package {sig : Sig} {base : Ctx sig}
    (referentIdentity identity : Ty sig)
    (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (toReferentFunction : Exp sig)
    (toReferentTyping : Exp.HasType base toReferentFunction
      (.arrow identity referentIdentity))
    (fromReferentFunction : Exp sig)
    (fromReferentTyping : Exp.HasType base fromReferentFunction
      (.arrow referentIdentity identity)) : Exp sig :=
  (plan referentIdentity).pack
    (arguments referentIdentity identity payload payloadTyping
      toReferentFunction toReferentTyping
      fromReferentFunction fromReferentTyping)

noncomputable def package_hasType {sig : Sig} {base : Ctx sig}
    (referentIdentity identity : Ty sig)
    (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload identity)
    (toReferentFunction : Exp sig)
    (toReferentTyping : Exp.HasType base toReferentFunction
      (.arrow identity referentIdentity))
    (fromReferentFunction : Exp sig)
    (fromReferentTyping : Exp.HasType base fromReferentFunction
      (.arrow referentIdentity identity)) :
    Exp.HasType base
      (package referentIdentity identity payload payloadTyping
        toReferentFunction toReferentTyping
        fromReferentFunction fromReferentTyping)
      (plan referentIdentity).inputTy :=
  (plan referentIdentity).pack_hasType
    (arguments referentIdentity identity payload payloadTyping
      toReferentFunction toReferentTyping
      fromReferentFunction fromReferentTyping)

noncomputable def exactArguments {sig : Sig} {base : Ctx sig}
    (referentIdentity : Ty sig) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload referentIdentity) :
    Telescope.Args base (plan referentIdentity).telescope :=
  arguments referentIdentity referentIdentity payload payloadTyping
    (Adapter.identity referentIdentity)
    (Adapter.identity_hasType base referentIdentity)
    (Adapter.identity referentIdentity)
    (Adapter.identity_hasType base referentIdentity)

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

/-!
Selected interval endpoints do not receive another wrapper plan here.  A
compiler-side interval descriptor retains the selected `Package.Plan`
itself, and selection returns that exact plan.  `Single.plan` is the only
atomic exact-identity alias supplied by this leaf.
-/

/-! ## Term-only observations -/

namespace Telescope

/-- Evidence that a telescope contains only ordinary term fields and hidden
type fields.  There is intentionally no constructor for a coercion field. -/
inductive TermOnly : {sig : Sig} -> Telescope sig -> Type where
  | nil : TermOnly (.nil : Telescope sig)
  | var {type : Ty sig} {tail : Telescope (sig ,, .var)} :
      TermOnly tail -> TermOnly (.var type tail)
  | tvar {tail : Telescope (sig ,, .tvar)} :
      TermOnly tail -> TermOnly (.tvar tail)

namespace TermOnly

noncomputable def rename {tele : Telescope source} (ordinary : TermOnly tele)
    (mapping : Rename source target) :
    TermOnly (tele.rename mapping) := by
  induction ordinary generalizing target with
  | nil => exact .nil
  | var tail ih => exact .var (ih (mapping.lift .var))
  | tvar tail ih => exact .tvar (ih (mapping.lift .tvar))

noncomputable def subst {tele : Telescope source} (ordinary : TermOnly tele)
    (substitution : Subst source target) :
    TermOnly (tele.subst substitution) := by
  induction ordinary generalizing target with
  | nil => exact .nil
  | var tail ih => exact .var (ih (substitution.lift .var))
  | tvar tail ih => exact .tvar (ih (substitution.lift .tvar))

end TermOnly

def TermOnly.fieldCount : {tele : Telescope sig} -> TermOnly tele -> Nat
  | _, .nil => 0
  | _, .var tail | _, .tvar tail => tail.fieldCount + 1

@[simp] theorem TermOnly.fieldCount_subst
    {tele : Telescope source} (ordinary : TermOnly tele)
    (substitution : Subst source target) :
    (ordinary.subst substitution).fieldCount = ordinary.fieldCount := by
  induction ordinary generalizing target with
  | nil => rfl
  | var tail ih =>
      change
        (tail.subst (substitution.lift .var)).fieldCount + 1 =
          tail.fieldCount + 1
      rw [ih (substitution.lift .var)]
  | tvar tail ih =>
      change
        (tail.subst (substitution.lift .tvar)).fieldCount + 1 =
          tail.fieldCount + 1
      rw [ih (substitution.lift .tvar)]

end Telescope

namespace Package.Plan

def TermOnly (plan : Package.Plan sig) : Type :=
  Telescope.TermOnly plan.observations

namespace TermOnly

noncomputable def rename {plan : Package.Plan source}
    (ordinary : plan.TermOnly)
    (mapping : Rename source target) :
    (plan.rename mapping).TermOnly :=
  Telescope.TermOnly.rename ordinary ((mapping.lift .tvar).lift .var)

noncomputable def subst {plan : Package.Plan source}
    (ordinary : plan.TermOnly)
    (substitution : Subst source target) :
    (plan.subst substitution).TermOnly :=
  Telescope.TermOnly.subst ordinary
    ((substitution.lift .tvar).lift .var)

end TermOnly

end Package.Plan

def Top.termOnly (sig : Sig) : (Top.plan sig).TermOnly :=
  .nil

def Bot.termOnly (sig : Sig) : (Bot.plan sig).TermOnly :=
  .var .nil

def Single.termOnly (referentIdentity : Ty sig) :
    (Single.plan referentIdentity).TermOnly :=
  .var (.var .nil)

/-! ## Bottom synthesis for term-only telescopes -/

namespace BottomSynthesis

/-- Populate every ordinary observation from impredicative Bottom.  A type
field is instantiated with Bottom itself; a term field is obtained by type
application of the retained Bottom value. -/
noncomputable def arguments {sig : Sig} {base : Ctx sig}
    (bottom : Exp sig)
    (bottomTyping : Exp.HasType base bottom Adapter.bottomTy) :
    (tele : Telescope sig) -> tele.TermOnly -> Telescope.Args base tele
  | .nil, .nil => .nil
  | .var type tail, .var ordinary =>
      let argument := Adapter.eliminateBottom bottom type
      let argumentTyping := Adapter.eliminateBottom_hasType bottomTyping
      .var argument argumentTyping
        (arguments bottom bottomTyping
          (tail.subst (Subst.openVar argument))
          (ordinary.subst (Subst.openVar argument)))
  | .tvar tail, .tvar ordinary =>
      .tvar Adapter.bottomTy
        (arguments bottom bottomTyping
          (tail.subst (Subst.openTVar Adapter.bottomTy))
          (ordinary.subst (Subst.openTVar Adapter.bottomTy)))
termination_by _ ordinary => ordinary.fieldCount
decreasing_by
  all_goals
    rw [Telescope.TermOnly.fieldCount_subst]
    simp only [Telescope.TermOnly.fieldCount, Nat.lt_add_one_iff]
    exact Nat.le_refl _

end BottomSynthesis

/-! ## Stable ordinary-function package adapters

This namespace is compiler-internal target construction.  It deliberately
contains no source-language evidence, resolution policy, or runtime
metadata. -/

namespace Stable

/-- Source plan under the ordinary adapter's input-package binder. -/
def sourceAtBinder (source : Package.Plan sig) :
    Package.Plan (sig ,, .var) :=
  source.rename (Rename.weaken .var)

/-- Target plan reindexed into the final scope of the opened source. -/
def targetAtSource (source target : Package.Plan sig) :
    Package.Plan (sourceAtBinder source).scope :=
  (target.rename (Rename.weaken .var)).rename
    (sourceAtBinder source).telescope.weaken

def openedContext (base : Ctx sig) (source : Package.Plan sig) :
    Ctx (sourceAtBinder source).scope :=
  (sourceAtBinder source).context (base.bindVar source.inputTy)

/-- Target observations after fixing their hidden identity and payload to the
exact projections opened from the source package. -/
def observationTelescope (source target : Package.Plan sig) :
    Telescope (sourceAtBinder source).scope :=
  (((targetAtSource source target).observations.subst
    ((Subst.openTVar (sourceAtBinder source).identityTy).lift .var)).subst
      (Subst.openVar (sourceAtBinder source).payload))

structure Repack (base : Ctx sig)
    (source target : Package.Plan sig) : Type where
  observations : Telescope.Args (openedContext base source)
    (observationTelescope source target)

namespace Repack

/-- Complete target arguments with the source's exact hidden identity and
payload in front of the target-specific observations. -/
noncomputable def arguments
    {sig : Sig} {base : Ctx sig}
    {source target : Package.Plan sig}
    (repack : Repack base source target) :
    Telescope.Args (openedContext base source)
      (targetAtSource source target).telescope :=
  .tvar (sourceAtBinder source).identityTy
    (.var (sourceAtBinder source).payload
      ((sourceAtBinder source).payload_hasType
        (base.bindVar source.inputTy))
      repack.observations)

noncomputable def result
    {sig : Sig} {base : Ctx sig}
    {source target : Package.Plan sig}
    (repack : Repack base source target) :
    Exp (sourceAtBinder source).scope :=
  (targetAtSource source target).pack repack.arguments

noncomputable def result_hasType
    {sig : Sig} {base : Ctx sig}
    {source target : Package.Plan sig}
    (repack : Repack base source target) :
    Exp.HasType (openedContext base source) repack.result
      ((target.inputTy.weaken .var).rename
        (sourceAtBinder source).telescope.weaken) := by
  have packed := (targetAtSource source target).pack_hasType repack.arguments
  change Exp.HasType (openedContext base source) repack.result
    (((target.rename (Rename.weaken .var)).rename
      (sourceAtBinder source).telescope.weaken).inputTy) at packed
  change Exp.HasType (openedContext base source) repack.result
    ((target.inputTy.rename (Rename.weaken .var)).rename
      (sourceAtBinder source).telescope.weaken)
  simpa only [Package.Plan.inputTy_rename] using packed

noncomputable def packageTyping (base : Ctx sig)
    (source : Package.Plan sig) :
    Exp.HasType (base.bindVar source.inputTy) (.var .here)
      (sourceAtBinder source).inputTy := by
  have variableTyping :
      Exp.HasType (base.bindVar source.inputTy) (.var .here)
        (source.inputTy.weaken .var) :=
    .var Ctx.Lookup.here
  simpa only [sourceAtBinder, Package.Plan.inputTy_rename, Ty.weaken] using
    variableTyping

/-- Unpack the source and immediately repack the exact same hidden identity
and payload with the target observations. -/
noncomputable def body
    {sig : Sig} {base : Ctx sig}
    {source target : Package.Plan sig}
    (repack : Repack base source target) :
    Exp (sig ,, .var) :=
  (sourceAtBinder source).unpack (.var .here)
    (target.inputTy.weaken .var) repack.result

noncomputable def body_hasType
    {sig : Sig} {base : Ctx sig}
    {source target : Package.Plan sig}
    (repack : Repack base source target) :
    Exp.HasType (base.bindVar source.inputTy) repack.body
      (target.inputTy.weaken .var) :=
  (sourceAtBinder source).unpack_hasType
    (packageTyping base source) repack.result_hasType

end Repack

/-- A stable package transformation is determined solely by its exact
repacking witness.  Its target term and typing are computed below, so an
unrelated function cannot be paired with a `Repack`. -/
structure Adapter (base : Ctx sig)
    (source target : Package.Plan sig) : Type where
  private mk ::
  repack : Repack base source target

namespace Adapter

noncomputable def ofRepack
    {sig : Sig} {base : Ctx sig}
    {source target : Package.Plan sig}
    (repack : Repack base source target) :
    Adapter base source target where
  repack := repack

noncomputable def function
    {sig : Sig} {base : Ctx sig}
    {source target : Package.Plan sig}
    (adapter : Adapter base source target) : Exp sig :=
  Direct.Adapter.ofBody source.inputTy adapter.repack.body

noncomputable def functionTyping
    {sig : Sig} {base : Ctx sig}
    {source target : Package.Plan sig}
    (adapter : Adapter base source target) :
    Exp.HasType base adapter.function
      (.arrow source.inputTy target.inputTy) :=
  Direct.Adapter.ofBody_hasType adapter.repack.body_hasType

noncomputable def apply {sig : Sig} {base : Ctx sig}
    {source target : Package.Plan sig}
    (adapter : Adapter base source target)
    (package : Exp sig) : Exp sig :=
  Direct.Adapter.apply adapter.function package

noncomputable def apply_hasType
    {sig : Sig} {base : Ctx sig}
    {source target : Package.Plan sig}
    (adapter : Adapter base source target)
    {package : Exp sig}
    (packageTyping : Exp.HasType base package source.inputTy) :
    Exp.HasType base (adapter.apply package) target.inputTy :=
  Direct.Adapter.apply_hasType adapter.functionTyping packageTyping

/-- Forget every observation while retaining the exact hidden identity and
payload. -/
noncomputable def toTop (base : Ctx sig) (source : Package.Plan sig) :
    Adapter base source (Top.plan sig) :=
  .ofRepack { observations := .nil }

private noncomputable def openedTargetTermOnly
    {source target : Package.Plan sig}
    (ordinary : target.TermOnly) :
    (observationTelescope source target).TermOnly := by
  let atSource : (targetAtSource source target).TermOnly :=
    (ordinary.rename (Rename.weaken .var)).rename
      (sourceAtBinder source).telescope.weaken
  exact Telescope.TermOnly.subst
    (Telescope.TermOnly.subst atSource
      ((Subst.openTVar (sourceAtBinder source).identityTy).lift .var))
    (Subst.openVar (sourceAtBinder source).payload)

/-- Bottom can synthesize every term-only target observation while still
reusing its exact hidden identity and payload. -/
noncomputable def fromBottom (base : Ctx sig)
    (target : Package.Plan sig) (ordinary : target.TermOnly) :
    Adapter base (Bot.plan sig) target := by
  apply ofRepack
  let bottom := Bot.eliminatePayload (sig ,, .var)
  have bottomTyping :
      Exp.HasType (openedContext base (Bot.plan sig)) bottom
        Adapter.bottomTy := by
    simpa only [openedContext, sourceAtBinder, Bot.plan_rename] using
      Bot.eliminatePayload_hasType
        (base.bindVar (Bot.plan sig).inputTy)
  exact
    { observations := BottomSynthesis.arguments bottom bottomTyping _
        (openedTargetTermOnly ordinary) }

end Adapter

end Stable

/-! ## Focused closed regressions -/

namespace AtomicRegression

def endpoint : Ty [] :=
  .arrow .top .top

def payload : Exp [] :=
  Direct.Adapter.identity .top

noncomputable def payload_hasType :
    Exp.HasType Ctx.empty payload endpoint :=
  Direct.Adapter.identity_hasType Ctx.empty .top

noncomputable def exactSingle : Exp [] :=
  Single.exactPackage endpoint payload payload_hasType

noncomputable def exactSingle_hasType :
    Exp.HasType Ctx.empty exactSingle (Single.plan endpoint).inputTy :=
  Single.exactPackage_hasType endpoint payload payload_hasType

noncomputable def toTop :
    Stable.Adapter Ctx.empty (Single.plan endpoint) (Top.plan []) :=
  Stable.Adapter.toTop Ctx.empty (Single.plan endpoint)

/-- GeneralPair's upper endpoint erasure is a package-to-package ordinary
function, not a target coercion. -/
noncomputable def toTop_hasType :
    Exp.HasType Ctx.empty toTop.function
      (.arrow (Single.plan endpoint).inputTy (Top.plan []).inputTy) :=
  toTop.functionTyping

noncomputable def fromBottom :
    Stable.Adapter Ctx.empty (Bot.plan []) (Single.plan endpoint) :=
  Stable.Adapter.fromBottom Ctx.empty (Single.plan endpoint)
    (Single.termOnly endpoint)

/-- GeneralPair's lower endpoint introduction is likewise an ordinary
package function synthesized solely from the retained Bottom eliminator. -/
noncomputable def fromBottom_hasType :
    Exp.HasType Ctx.empty fromBottom.function
      (.arrow (Bot.plan []).inputTy (Single.plan endpoint).inputTy) :=
  fromBottom.functionTyping

noncomputable def erasedExactSingle : Exp [] :=
  toTop.apply exactSingle

noncomputable def erasedExactSingle_hasType :
    Exp.HasType Ctx.empty erasedExactSingle (Top.plan []).inputTy :=
  toTop.apply_hasType exactSingle_hasType

end AtomicRegression

end LambdaPToFCo.Direct
