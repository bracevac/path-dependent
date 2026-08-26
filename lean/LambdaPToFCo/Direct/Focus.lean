import LambdaPToFCo.Direct.Core

/-!
# Focused package opening for the direct compiler

Church elimination exposes a plan's mixed telescope only inside its consumer
body.  This module records that one target-scoping fact directly: all opened
fields can be repackaged at the renamed plan, and a source environment can be
reindexed into the opened target scope with that package as its newest slot.

No source type representation is inferred here.  The later path compiler
decides when to enter a package and what its source typing derivation permits
it to observe.
-/

namespace LambdaPToFCo.Direct

open LambdaPFC
open SystemFCo

namespace Internal

namespace Focus

/-- Canonical arguments for the exact plan visible inside its own unpack
body. -/
noncomputable def arguments (targetContext : SystemFCo.Ctx sig)
    (plan : Package.Plan sig) :
    Telescope.Args (plan.context targetContext)
      (plan.rename plan.telescope.weaken).telescope := by
  simpa only [Package.Plan.telescope_rename] using
    (Telescope.Args.identity plan.telescope targetContext)

/-- Repackage all fields exposed by a plan elimination. -/
noncomputable def package (targetContext : SystemFCo.Ctx sig)
    (plan : Package.Plan sig) : Exp plan.scope :=
  (plan.rename plan.telescope.weaken).pack (arguments targetContext plan)

/-- The canonical repackaging has exactly the renamed plan's public input
type. -/
noncomputable def package_hasType (targetContext : SystemFCo.Ctx sig)
    (plan : Package.Plan sig) :
    Exp.HasType (plan.context targetContext) (package targetContext plan)
      (plan.rename plan.telescope.weaken).inputTy :=
  (plan.rename plan.telescope.weaken).pack_hasType
    (arguments targetContext plan)

/-- Close a body authored at the package focus. -/
def eliminate (plan : Package.Plan sig) (package : Exp sig)
    (answer : Ty sig) (body : Exp plan.scope) : Compiled sig where
  targetType := answer
  expression := plan.unpack package answer body

/-- Extrinsic typing for focused elimination. -/
noncomputable def eliminate_wellTyped
    (plan : Package.Plan sig) {targetContext : SystemFCo.Ctx sig}
    {package : Exp sig} {answer : Ty sig} {body : Exp plan.scope}
    (packageTyping : Exp.HasType targetContext package plan.inputTy)
    (bodyTyping : Exp.HasType (plan.context targetContext) body
      (answer.rename plan.telescope.weaken)) :
    (eliminate plan package answer body).WellTyped targetContext :=
  plan.unpack_hasType packageTyping bodyTyping

end Focus

namespace Env

/-- Open one plan and install its canonical repackaging as the newest source
slot. Older packages are weakened through the complete target telescope. -/
noncomputable def enter
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    (targetContext : SystemFCo.Ctx sig)
    (environment : Env sourceContext sig)
    (sourceType : LambdaPFC.Ty n) (plan : Package.Plan sig) :
    Env (sourceContext.snoc sourceType) plan.scope where
  lookup := Fin.cases
    { plan := plan.rename plan.telescope.weaken
      expression := Focus.package targetContext plan }
    (fun older =>
      (environment.lookup older).rename plan.telescope.weaken)

@[simp] theorem enter_here
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    (targetContext : SystemFCo.Ctx sig)
    (environment : Env sourceContext sig)
    (sourceType : LambdaPFC.Ty n) (plan : Package.Plan sig) :
    (environment.enter targetContext sourceType plan).lookup 0 =
      { plan := plan.rename plan.telescope.weaken
        expression := Focus.package targetContext plan } := by
  rfl

@[simp] theorem enter_there
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    (targetContext : SystemFCo.Ctx sig)
    (environment : Env sourceContext sig)
    (sourceType : LambdaPFC.Ty n) (plan : Package.Plan sig)
    (index : Fin n) :
    (environment.enter targetContext sourceType plan).lookup index.succ =
      (environment.lookup index).rename plan.telescope.weaken := by
  rfl

end Env

namespace Env.WellTyped

/-- Opening a plan preserves every old slot and types the canonical new
slot. -/
noncomputable def enter
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    {environment : Env sourceContext sig}
    (typedEnvironment : Env.WellTyped targetContext environment)
    (sourceType : LambdaPFC.Ty n) (plan : Package.Plan sig) :
    Env.WellTyped (plan.context targetContext)
      (environment.enter targetContext sourceType plan) where
  lookup index := by
    refine Fin.cases ?_ (fun older => ?_) index
    · exact Focus.package_hasType targetContext plan
    · exact (typedEnvironment.lookup older).rename plan.telescope.weaken
        (plan.telescope.weaken_typed targetContext)

end Env.WellTyped

end Internal

end LambdaPToFCo.Direct
