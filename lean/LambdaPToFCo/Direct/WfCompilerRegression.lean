import LambdaPToFCo.Direct.WfCompiler

/-!
# Total Wf compiler regression

One opened environment contains an outer proper pair whose first component is
itself an interval-member pair.  The two Wf derivations below therefore force
the compiler through a nested `fst.fst` proper path and through a selection
whose receiver is the non-variable path `fst`.
-/

namespace LambdaPToFCo.Direct.WfCompilerRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal.Formation
open LambdaPToFCo.Direct.Internal.FormedPath
open LambdaPToFCo.Direct.Internal.WfCompiler

private abbrev InnerLabel : LambdaPFC.Name := 3
private abbrev OuterLabel : LambdaPFC.Name := 7

private abbrev InnerSource (n : Nat) : LambdaPFC.Ty n :=
  .Pair .Top InnerLabel (.intv .Bot .Top)

private abbrev OuterSource : LambdaPFC.Ty 0 :=
  .Pair (InnerSource 0) OuterLabel (.ty .Top)

private abbrev SourceContext : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc OuterSource

private def innerFirst : Shape [] := .stable (Top.plan [])

private def innerLower : Shape innerFirst.scope :=
  .stable (Bot.plan innerFirst.scope)

private def innerUpper : Shape innerFirst.scope :=
  .stable (Top.plan innerFirst.scope)

private def innerShape : Shape [] :=
  .stable
    (Pair.Interval.plan innerFirst innerLower innerUpper)

private def outerMember : Shape innerShape.scope :=
  .stable (Top.plan innerShape.scope)

private def outerShape : Shape [] :=
  .stable (Pair.Proper.plan innerShape outerMember)

private noncomputable def innerFormation :
    Formation SourceContext Ctx.empty (InnerSource 1) innerShape := by
  exact .intervalPair .top .bottom .top

private noncomputable def outerFormation :
    Formation SourceContext Ctx.empty (SourceContext.lookup 0) outerShape := by
  change Formation SourceContext Ctx.empty
    (.Pair (InnerSource 1) OuterLabel (.ty .Top)) outerShape
  exact .properPair innerFormation .top

private abbrev TargetContext : Ctx outerShape.scope :=
  outerShape.context Ctx.empty

private noncomputable def receiver :
    Slot SourceContext TargetContext (SourceContext.lookup 0) where
  shape := outerShape.rename outerShape.binders.weaken
  interface := Shape.Interface.canonical Ctx.empty outerShape
  formation := outerFormation.targetRename outerShape.binders.weaken
    (outerShape.binders.weaken_typed Ctx.empty)

private noncomputable def environment :
    Env SourceContext TargetContext where
  lookup index := Fin.cases receiver (fun older => Fin.elim0 older) index

private def receiverTyping :
    LambdaPFC.Path.Ty SourceContext (.var 0)
      (.ty (SourceContext.lookup 0)) :=
  .var

private def innerTyping :
    LambdaPFC.Path.Ty SourceContext (.fst (.var 0))
      (.ty (InnerSource 1)) := by
  exact receiverTyping.fst

private def nestedFirstTyping :
    LambdaPFC.Path.Ty SourceContext (.fst (.fst (.var 0))) (.ty .Top) :=
  innerTyping.fst

private def nestedSelectionTyping :
    LambdaPFC.Path.Ty SourceContext
      (.sel (.fst (.var 0)) InnerLabel) (.intv .Bot .Top) := by
  simpa only [LambdaPFC.Tau.open] using innerTyping.sel_r

private def nestedPathWf :
    LambdaPFC.Tau.Wf SourceContext
      (.ty (.Single (.fst (.fst (.var 0))))) :=
  .path nestedFirstTyping

private def nestedSelectionWf :
    LambdaPFC.Tau.Wf SourceContext
      (.ty (.TSel (.fst (.var 0)) InnerLabel)) :=
  .sel nestedSelectionTyping .bot

/-- Total recursion through the non-variable proper path. -/
noncomputable def nestedPath :
    Proper SourceContext TargetContext
      (.Single (.fst (.fst (.var 0)))) := by
  cases compile nestedPathWf environment with
  | proper result => exact result

/-- The Wf result and term-introduction materializer use exactly the same
closed singleton Shape, with no caller-provided equality. -/
theorem nestedPath_shape_coherent :
    nestedPath.shape =
      (materializeSingleton nestedFirstTyping environment).shape :=
  path_shape_coherent nestedFirstTyping environment

/-- Total recursion through a selection whose receiver is itself a `fst`. -/
noncomputable def nestedSelection :
    Proper SourceContext TargetContext
      (.TSel (.fst (.var 0)) InnerLabel) := by
  cases compile nestedSelectionWf environment with
  | proper result => exact result

/-- No auxiliary evidence wrapper is needed: the exact source selection remains
in the Formation index, and `.rep` preserves its selected endpoints/functions
for the ordinary sel-hi/sel-lo consumers. -/
noncomputable def nestedSelectionRep :
    LambdaPToFCo.Direct.Internal.Representation.Rep TargetContext
      ((.TSel (.fst (.var 0)) InnerLabel) : LambdaPFC.Ty 1)
      nestedSelection.shape :=
  nestedSelection.formation.rep

theorem nestedSelection_isClosed :
    match nestedSelection.shape with
    | .opaque _ => True
    | .stable _ => False := by
  trivial

end LambdaPToFCo.Direct.WfCompilerRegression
