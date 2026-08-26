import LambdaPToFCo.Full.StableIdentity
import SystemFCoExt.TelescopeReduction

/-!
# Operational evidence for ready stable-identity adapters

This module adds an honest operational layer above the static
`StableIdentity.Adapter` law. A ready interface explicitly requires every
term field in its mixed argument spine to be a target value. Its Church
package is consequently exposed with both typing and value evidence.

Ordinary adapter execution mirrors identity, primitive repack, and
composition. Primitive repacks must provide the exact equations needed by
mixed Church beta; there is no generic constructor for
`StableIdentity.Adapter.fromBottom`. The source-level ordinary/absurd split
remains the responsibility of translation provenance above this module.
-/

namespace LambdaPToFCo.Full.StableIdentityReduction

open SystemFCoExt
open LambdaPToFCo.Full.StableIdentity

/-- An opened value interface whose complete mixed argument spine is ready.
Only term fields contribute premises to `Telescope.Args.AllValues`; type and
coercion fields are administrative. -/
structure ReadyInterface (sig : Sig) (base : Ctx sig) where
  interface : ValueInterface base
  ready : interface.arguments.AllValues

namespace ReadyInterface

def identity (ready : ReadyInterface sig base) : Ty sig :=
  ready.interface.identity

def payload (ready : ReadyInterface sig base) : Exp sig :=
  ready.interface.payload

@[simp] theorem interface_identity (ready : ReadyInterface sig base) :
    ready.interface.identity = ready.identity := by
  rfl

@[simp] theorem interface_payload (ready : ReadyInterface sig base) :
    ready.interface.payload = ready.payload := by
  rfl

/-- The canonical Church package for the ready opened interface. -/
noncomputable def package (ready : ReadyInterface sig base) : Exp sig :=
  ready.interface.package

noncomputable def package_hasType (ready : ReadyInterface sig base) :
    Exp.HasType base ready.package ready.interface.plan.inputTy :=
  ready.interface.package_hasType

/-- Church packaging always introduces an outer type abstraction. -/
theorem package_isValue (ready : ReadyInterface sig base) :
    Exp.IsValue ready.package := by
  exact .tabs

end ReadyInterface

private theorem valuePlan_telescope_ne_nil (plan : ValuePlan sig) :
    plan.telescope ≠ .nil := by
  intro equal
  cases plan with
  | mk observations => cases equal

private theorem steps_castExpression
    {sig : Sig} {source target : Exp sig}
    (steps : Exp.Steps source target)
    (coercion : Co sig) :
    Exp.Steps (.cast source coercion) (.cast target coercion) := by
  induction steps with
  | refl => exact .refl
  | tail step steps ih => exact .tail (.castExpression step) ih

/-- Operational data for one ordinary primitive repack. The equations expose
the source Church unpack and identify its instantiated body with the ready
target package. `bodySteps` derives the actual reduction sequence; it is not
stored as an unchecked abstract execution law. -/
structure ReadyRepack {sig : Sig} {base : Ctx sig}
    (sourceInterface targetInterface : ReadyInterface sig base)
    (repack : Repack base sourceInterface.interface.plan
      targetInterface.interface.plan) : Type where
  identity_eq : targetInterface.identity = sourceInterface.identity
  payload_eq : targetInterface.payload = sourceInterface.payload
  body : Exp sourceInterface.interface.plan.scope
  body_eq : repack.body.subst
      (Subst.openVar sourceInterface.package) =
    sourceInterface.interface.plan.unpack sourceInterface.package
      targetInterface.interface.plan.inputTy body
  result_eq : body.subst sourceInterface.interface.arguments.substitution =
    targetInterface.package

namespace ReadyRepack

/-- Exact mixed Church beta for a ready primitive repack. -/
noncomputable def bodySteps
    {sig : Sig} {base : Ctx sig}
    (sourceInterface targetInterface : ReadyInterface sig base)
    (repack : Repack base sourceInterface.interface.plan
      targetInterface.interface.plan)
    (execution : ReadyRepack sourceInterface targetInterface repack) :
    Exp.Steps
      (repack.body.subst (Subst.openVar sourceInterface.package))
      targetInterface.package := by
  rw [execution.body_eq]
  apply Exp.Steps.trans
    (Telescope.unpack_pack_steps_of_ne_nil
      sourceInterface.interface.arguments sourceInterface.ready
      targetInterface.interface.plan.inputTy execution.body
      (valuePlan_telescope_ne_nil sourceInterface.interface.plan))
  exact execution.result_eq ▸ Exp.Steps.refl

end ReadyRepack

/-! ## Ordinary adapter execution -/

/-- Ordinary execution mirrors only statically justified adapter nodes.
There is intentionally no constructor which turns `Adapter.fromBottom` into
ordinary evidence. A primitive repack must instead supply the exact
`ReadyRepack` witness above. -/
inductive Ordinary {sig : Sig} {base : Ctx sig} :
    (source target : ReadyInterface sig base) ->
    StableIdentity.Adapter base source.interface.plan target.interface.plan ->
    Type where
  | identity (source : ReadyInterface sig base) :
      Ordinary source source
        (StableIdentity.Adapter.identity base source.interface.plan)
  | repack
      (execution : ReadyRepack source target repack) :
      Ordinary source target (StableIdentity.Adapter.ofRepack repack)
  | compose
      (first : Ordinary source middle firstAdapter)
      (second : Ordinary middle target secondAdapter) :
      Ordinary source target (firstAdapter.compose secondAdapter)

namespace Ordinary

private def sourceInterface
    {sig : Sig} {base : Ctx sig}
    {source target : ReadyInterface sig base}
    {valueAdapter : StableIdentity.Adapter base source.interface.plan
      target.interface.plan}
    (_execution : Ordinary source target valueAdapter) :
    ReadyInterface sig base :=
  source

private def targetInterface
    {sig : Sig} {base : Ctx sig}
    {source target : ReadyInterface sig base}
    {valueAdapter : StableIdentity.Adapter base source.interface.plan
      target.interface.plan}
    (_execution : Ordinary source target valueAdapter) :
    ReadyInterface sig base :=
  target

private def staticAdapter
    {sig : Sig} {base : Ctx sig}
    {source target : ReadyInterface sig base}
    {valueAdapter : StableIdentity.Adapter base source.interface.plan
      target.interface.plan}
    (_execution : Ordinary source target valueAdapter) :
    StableIdentity.Adapter base source.interface.plan target.interface.plan :=
  valueAdapter

/-- Ordinary adapters retain the exact hidden identity type. -/
def identity_eq
    (execution : Ordinary source target adapter) :
    target.identity = source.identity := by
  induction execution with
  | identity => rfl
  | repack execution => exact execution.identity_eq
  | compose _ _ firstIH secondIH => exact secondIH.trans firstIH

/-- Ordinary adapters retain the exact hidden payload term. -/
def payload_eq
    (execution : Ordinary source target adapter) :
    target.payload = source.payload := by
  induction execution with
  | identity => rfl
  | repack execution => exact execution.payload_eq
  | compose _ _ firstIH secondIH => exact secondIH.trans firstIH

/-- Reduction after the outer adapter cast has fired. Composition lifts the
first body execution under the second adapter cast and then fires/runs the
second adapter. -/
noncomputable def bodySteps
    (execution : Ordinary source target adapter) :
    Exp.Steps
      (adapter.body.subst (Subst.openVar source.package))
      target.package := by
  induction execution with
  | identity source =>
      exact .refl
  | repack execution =>
      exact execution.bodySteps _ _ _
  | compose first second firstIH secondIH =>
      change Exp.Steps
        ((StableIdentity.Adapter.composeBody first.staticAdapter
          second.staticAdapter).subst
          (Subst.openVar first.sourceInterface.package))
        second.targetInterface.package
      simp only [StableIdentity.Adapter.composeBody, Exp.subst]
      rw [second.staticAdapter.coercion.weaken_subst_cancel
        (Subst.openVar first.sourceInterface.package)
        (Subst.weakenAsSubst_comp_openVar first.sourceInterface.package)]
      apply Exp.Steps.trans
        (steps_castExpression firstIH second.staticAdapter.coercion)
      exact .tail (.castAdapter first.targetInterface.package_isValue) secondIH

/-- Exact public execution of the complete adapter application. -/
noncomputable def steps
    (execution : Ordinary source target adapter) :
    Exp.Steps (adapter.apply source.package) target.package :=
  .tail (.castAdapter source.package_isValue) execution.bodySteps

end Ordinary

/-! Focused construction checks. -/

noncomputable example (source : ReadyInterface sig base) :
    Ordinary source source
      (StableIdentity.Adapter.identity base source.interface.plan) :=
  .identity source

noncomputable example
    (first : Ordinary source middle firstAdapter)
    (second : Ordinary middle target secondAdapter) :
    Ordinary source target (firstAdapter.compose secondAdapter) :=
  .compose first second

noncomputable example
    (execution : Ordinary source target adapter) :
    Exp.Steps (adapter.apply source.package) target.package :=
  execution.steps

end LambdaPToFCo.Full.StableIdentityReduction
