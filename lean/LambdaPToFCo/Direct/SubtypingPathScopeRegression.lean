import LambdaPToFCo.Direct.SubtypingPathScope

/-!
Regression for the bounded contextual path layer.  In the target-oriented
scope, the newest target binder is Bottom and the corresponding source binder
is Top.  Thus the proof-side alignment is genuinely Bottom-to-Top, and
neither contextual singleton reflexivity nor target-oriented widening can
collapse to homogeneous Shape identity.
-/

namespace LambdaPToFCo.Direct.SubtypingPathScopeRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Formation
open LambdaPToFCo.Direct.Internal.SubtypingScope
open LambdaPToFCo.Direct.Internal.SubtypingPathScope

noncomputable def changedScope
    {base : Ctx sig}
    (sourceInterface : Shape.Interface base (.stable (Top.plan sig)))
    (targetInterface : Shape.Interface base (.stable (Bot.plan sig))) :
    Scope (LambdaPFC.Ctx.nil.snoc .Top)
      (LambdaPFC.Ctx.nil.snoc .Bot) .target base :=
  let root := Scope.root (Env.empty base) .target
  root.extendFunction sourceInterface
    (Formation.top (sourceContext := LambdaPFC.Ctx.nil)
      (targetContext := base))
    targetInterface
    (Formation.bottom (sourceContext := LambdaPFC.Ctx.nil)
      (targetContext := base))
    (AtomicSubtyping.top {
      shape := .stable (Bot.plan sig)
      rep := .bottom base
    }).relation

private def newest : Fin 1 := 0

private def targetVariableTyping :
    LambdaPFC.Path.Ty (LambdaPFC.Ctx.nil.snoc .Bot)
      (.var newest) (.ty .Bot) := by
  simpa only [newest, LambdaPFC.Ctx.lookup, LambdaPFC.Ty.weaken,
    LambdaPFC.Ty.rename] using
    (LambdaPFC.Path.Ty.var :
      LambdaPFC.Path.Ty (LambdaPFC.Ctx.nil.snoc .Bot)
        (.var newest)
        (.ty ((LambdaPFC.Ctx.nil.snoc .Bot).lookup newest)))

/-- The exact endpoint formations used by target-oriented variable
widening. -/
noncomputable def changedWiden
    {base : Ctx sig}
    (sourceInterface : Shape.Interface base (.stable (Top.plan sig)))
    (targetInterface : Shape.Interface base (.stable (Bot.plan sig))) :
    let scope := changedScope sourceInterface targetInterface
    WidenResult scope targetVariableTyping
      (.stable (Single.plan (Top.plan sig).inputTy))
      (.stable (Bot.plan sig)) := by
  dsimp only
  let scope := changedScope sourceInterface targetInterface
  let sourceFormation : Formation (LambdaPFC.Ctx.nil.snoc .Top) base
      (.Single (.var newest))
      (.stable (Single.plan (Top.plan sig).inputTy)) :=
    .singleton .var sourceInterface
      (Formation.top (sourceContext := LambdaPFC.Ctx.nil.snoc .Top)
        (targetContext := base))
  let targetFormation : Formation (LambdaPFC.Ctx.nil.snoc .Bot) base
      .Bot (.stable (Bot.plan sig)) := .bottom
  simpa only [scope, changedScope, Fin.cases_zero] using
    widenTargetVariable scope newest targetVariableTyping sourceFormation
      targetFormation

/-- The resulting ordinary conversion crosses the distinct singleton-of-Top
and Bottom carriers. -/
noncomputable example
    {base : Ctx sig}
    (sourceInterface : Shape.Interface base (.stable (Top.plan sig)))
    (targetInterface : Shape.Interface base (.stable (Bot.plan sig))) :
    Exp.HasType base
      ((changedWiden sourceInterface targetInterface).relation.conversion
        |>.function)
      (.arrow (Single.plan (Top.plan sig).inputTy).inputTy
        (Bot.plan sig).inputTy) :=
  ((changedWiden sourceInterface targetInterface).relation.conversion
    |>.functionTyping)

end LambdaPToFCo.Direct.SubtypingPathScopeRegression
