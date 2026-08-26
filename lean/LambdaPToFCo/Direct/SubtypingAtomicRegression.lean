import LambdaPToFCo.Direct.SubtypingAtomic
import LambdaPToFCo.Direct.SubtypingScopeRegression

/-!
Focused checks for the partial polarity kernel.  The transitivity examples
force the exact middle formation through Push and Pull in opposite orders;
the singleton example crosses the existing Bottom-to-Top changed binder.
-/

namespace LambdaPToFCo.Direct.SubtypingAtomicRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Formation
open LambdaPToFCo.Direct.Internal.SubtypingScope
open LambdaPToFCo.Direct.Internal.SubtypingAtomic

private def topValue {sig : Sig} : Exp sig :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

private noncomputable def topValue_hasType (base : Ctx sig) :
    Exp.HasType base (topValue : Exp sig) .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

private noncomputable def rootScope (base : Ctx sig) :
    Scope LambdaPFC.Ctx.nil LambdaPFC.Ctx.nil .source base :=
  Scope.root (Env.empty base) .source

/-- Push computes the exact intermediate Bottom formation through refl, then
feeds it to Top without rebuilding the middle shape. -/
noncomputable def pushReflTop (base : Ctx sig) :
    Path.Body base .top :=
  let first : Push
      (LambdaPFC.Tau.Sub.refl
        (Γ := LambdaPFC.Ctx.nil) (τ := .ty .Bot)) := pushRefl
  let second : Push
      (LambdaPFC.Tau.Sub.top
        (Γ := LambdaPFC.Ctx.nil) (T := .Bot)) := pushTop
  let compiler := pushTrans first second
  compiler.run (rootScope base) (.bottom (targetContext := base)) .top
    (fun _mapping _typed _target _cut => {
      expression := topValue
      typing := topValue_hasType _
    })

/-- Pull computes the exact intermediate Top formation through refl, then
feeds it backward to Bottom without rebuilding the middle shape. -/
noncomputable def pullBottomRefl (base : Ctx sig) :
    Path.Body base .top :=
  let first : Pull
      (LambdaPFC.Tau.Sub.bot
        (Γ := LambdaPFC.Ctx.nil) (T := .Top)) := pullBottom
  let second : Pull
      (LambdaPFC.Tau.Sub.refl
        (Γ := LambdaPFC.Ctx.nil) (τ := .ty .Top)) := pullRefl
  let compiler := pullTrans first second
  compiler.run (rootScope base) (.top (targetContext := base)) .top
    (fun _mapping _typed _source _cut => {
      expression := topValue
      typing := topValue_hasType _
    })

/-- The dispatcher atom consumes the sealed alignment across genuinely
different newest binder types, rather than choosing either endpoint by
identity. -/
noncomputable def changedBinderSingleton
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (prior : Scope sourceContext targetContext .source base)
    (sourceInterface : Shape.Interface base (.stable (Bot.plan sig)))
    (targetInterface : Shape.Interface base (.stable (Top.plan sig))) :=
  reflSingletonVariable
    (LambdaPToFCo.Direct.SubtypingScopeRegression.changedBinderScope
      prior sourceInterface targetInterface)
    (0 : Fin (n + 1))

end LambdaPToFCo.Direct.SubtypingAtomicRegression
