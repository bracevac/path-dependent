import LambdaPToFCo.Direct.ContextRelation
import LambdaPToFCo.Direct.AtomicSubtyping

/-!
Regression for raw contextual alignment across a genuinely changed binder.
The source endpoint extends with Bottom and the target endpoint with Top, so
the newest pointwise relation cannot be obtained by raw reflexivity.
-/

namespace LambdaPToFCo.Direct.ContextRelationRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.ContextRelation

private noncomputable def changedHead
    {base : Ctx sig} :
    Relation base (.Bot : LambdaPFC.Ty n) .Top
      (.stable (Bot.plan sig)) (.stable (Top.plan sig)) :=
  (AtomicSubtyping.top {
    shape := .stable (Bot.plan sig)
    rep := .bottom base }).relation

/-- Extend with the two actual endpoint interfaces and the literal
Bottom-to-Top head relation. -/
noncomputable def changedBinderScope
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (prior : Scope sourceContext targetContext .source base)
    (sourceInterface : Shape.Interface base (.stable (Bot.plan sig)))
    (targetInterface : Shape.Interface base (.stable (Top.plan sig))) :
    Scope (sourceContext.snoc .Bot) (targetContext.snoc .Top)
      .source base :=
  prior.extendPair sourceInterface (.bottom base)
    targetInterface (.top base) changedHead

/-- Looking up the newest aligned slot yields the changed head relation,
not an identity relation between independently chosen Shapes. -/
noncomputable def changedBinderAlignment
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (prior : Scope sourceContext targetContext .source base)
    (sourceInterface : Shape.Interface base (.stable (Bot.plan sig)))
    (targetInterface : Shape.Interface base (.stable (Top.plan sig))) :
    Relation base
      ((.Bot : LambdaPFC.Ty n).rename LambdaPFC.FinFun.weaken)
      ((.Top : LambdaPFC.Ty n).rename LambdaPFC.FinFun.weaken)
      (.stable (Bot.plan sig)) (.stable (Top.plan sig)) := by
  let extended := changedBinderScope prior sourceInterface targetInterface
  simpa only [extended, changedBinderScope, LambdaPFC.Ctx.lookup,
    extendAtInterface_here, Fin.cases_zero] using
    extended.aligned (0 : Fin (n + 1))

/-- The changed alignment remains exact after an arbitrary typed target
renaming, exercising both the scope zipper and relation naturality. -/
noncomputable def renamedChangedBinderAlignment
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    (prior : Scope sourceContext targetContext .source sourceBase)
    (sourceInterface : Shape.Interface sourceBase
      (.stable (Bot.plan sourceSig)))
    (targetInterface : Shape.Interface sourceBase
      (.stable (Top.plan sourceSig)))
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceBase targetBase mapping) :
    Relation targetBase
      ((.Bot : LambdaPFC.Ty n).rename LambdaPFC.FinFun.weaken)
      ((.Top : LambdaPFC.Ty n).rename LambdaPFC.FinFun.weaken)
      ((Shape.stable (Bot.plan sourceSig)).rename mapping)
      ((Shape.stable (Top.plan sourceSig)).rename mapping) := by
  let extended := changedBinderScope prior sourceInterface targetInterface
  let renamed := extended.targetRename mapping typed
  simpa only [renamed, LambdaPFC.Ctx.lookup, Env.targetRename,
    extendAtInterface_here, Slot.targetRename, Fin.cases_zero] using
    renamed.aligned (0 : Fin (n + 1))

end LambdaPToFCo.Direct.ContextRelationRegression
