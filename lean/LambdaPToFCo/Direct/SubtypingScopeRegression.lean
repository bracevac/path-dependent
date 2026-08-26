import LambdaPToFCo.Direct.SubtypingScope
import LambdaPToFCo.Direct.AtomicSubtyping

/-!
Regression for contextual reflexivity across a genuinely changed dependent
pair binder.  The source binding has type Bottom and the target binding has
type Top.  The member singleton relation must therefore use the sealed slot
alignment; target identity cannot typecheck at its two distinct plans.
-/

namespace LambdaPToFCo.Direct.SubtypingScopeRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.Formation
open LambdaPToFCo.Direct.Internal.SubtypingScope

private noncomputable def changedHead
    {base : Ctx sig} :
    Relation base (.Bot : LambdaPFC.Ty n) .Top
      (.stable (Bot.plan sig)) (.stable (Top.plan sig)) :=
  (AtomicSubtyping.top {
    shape := .stable (Bot.plan sig)
    rep := .bottom base }).relation

/-- The changed binder is extended only with its two exact continuation
interfaces and the literal Bottom-to-Top head relation. -/
noncomputable def changedBinderScope
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (prior : Scope sourceContext targetContext .source base)
    (sourceInterface : Shape.Interface base (.stable (Bot.plan sig)))
    (targetInterface : Shape.Interface base (.stable (Top.plan sig))) :
    Scope (sourceContext.snoc .Bot) (targetContext.snoc .Top)
      .source base :=
  prior.extendPair sourceInterface
    (Formation.bottom (sourceContext := sourceContext)
      (targetContext := base))
    targetInterface
    (Formation.top (sourceContext := targetContext)
      (targetContext := base))
    changedHead

/-- Contextual reflexivity retargets the newest singleton from the Bottom
plan to the distinct Top plan. -/
noncomputable def changedBinderSingletonRelation
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (prior : Scope sourceContext targetContext .source base)
    (sourceInterface : Shape.Interface base (.stable (Bot.plan sig)))
    (targetInterface : Shape.Interface base (.stable (Top.plan sig))) :
    Relation base
      (.Single (.var (0 : Fin (n + 1))))
      (.Single (.var (0 : Fin (n + 1))))
      (.stable (Single.plan (Bot.plan sig).inputTy))
      (.stable (Single.plan (Top.plan sig).inputTy)) := by
  let extended := changedBinderScope prior sourceInterface targetInterface
  simpa only [extended, changedBinderScope, Fin.cases_zero] using
    extended.reflSingletonVariable (0 : Fin (n + 1))

/-- The same regression packaged as the literal contextual `Tau.Sub.refl`
cut, retaining endpoint-specific formations in `Γ,Bot` and `Γ,Top`. -/
noncomputable def changedBinderSingletonCut
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (prior : Scope sourceContext targetContext .source base)
    (sourceInterface : Shape.Interface base (.stable (Bot.plan sig)))
    (targetInterface : Shape.Interface base (.stable (Top.plan sig))) :
    let extended := changedBinderScope prior sourceInterface targetInterface
    CutView extended
      (LambdaPFC.Tau.Sub.refl
        (Γ := sourceContext.snoc (.Bot : LambdaPFC.Ty n))
        (τ := .ty (.Single (.var (0 : Fin (n + 1))))))
      (.stable (Single.plan (Bot.plan sig).inputTy))
      (.stable (Single.plan (Top.plan sig).inputTy)) := by
  dsimp only
  let extended := changedBinderScope prior sourceInterface targetInterface
  let sourceSlot := extended.source.lookup (0 : Fin (n + 1))
  let targetSlot := extended.target.lookup (0 : Fin (n + 1))
  exact CutView.ofRelation
    (.singleton .var sourceSlot.interface sourceSlot.formation)
    (.singleton .var targetSlot.interface targetSlot.formation)
    (changedBinderSingletonRelation prior sourceInterface targetInterface)

end LambdaPToFCo.Direct.SubtypingScopeRegression
