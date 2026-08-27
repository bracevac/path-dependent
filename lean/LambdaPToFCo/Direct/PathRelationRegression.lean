import LambdaPToFCo.Direct.PathRelation
import LambdaPToFCo.Direct.ContextRelationRegression

/-!
Regression for contextual variable identity across a changed raw binder.
The two endpoint slots have Bottom and Top Shapes, so this relation must use
the sealed Bottom-to-Top alignment rather than homogeneous reflexivity.
-/

namespace LambdaPToFCo.Direct.PathRelationRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.ContextRelation
open LambdaPToFCo.Direct.Internal.PathRelation

/-- Resolve the newest contextual variable singleton across Bottom and Top
endpoint binders. -/
noncomputable def changedBinderSingleton
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
  let scope :=
    ContextRelationRegression.changedBinderScope prior sourceInterface
      targetInterface
  simpa only [scope, ContextRelationRegression.changedBinderScope,
    extendAtInterface_here, Fin.cases_zero] using
    singletonVariable scope (0 : Fin (n + 1))

/-- The generated target term is an ordinary conversion between the two
distinct singleton package types. -/
noncomputable def changedBinderSingletonTyping
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (prior : Scope sourceContext targetContext .source base)
    (sourceInterface : Shape.Interface base (.stable (Bot.plan sig)))
    (targetInterface : Shape.Interface base (.stable (Top.plan sig))) :
    Exp.HasType base
      (changedBinderSingleton prior sourceInterface targetInterface
        |>.conversion.function)
      (.arrow
        (Single.plan (Bot.plan sig).inputTy).inputTy
        (Single.plan (Top.plan sig).inputTy).inputTy) :=
  (changedBinderSingleton prior sourceInterface targetInterface
    |>.conversion.functionTyping)

end LambdaPToFCo.Direct.PathRelationRegression
