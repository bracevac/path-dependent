import LambdaPToFCo.Direct.WfFocus

/-!
# Focused selection closure regression

The selected type below is reached through the first component of an outer
pair and then through an interval member of an inner pair.  Wf compilation
does not invent a value of that selected type.  Instead it retains the exact
nested focus; once a symbolic interface is supplied at that focus, the same
runner repacks it into the root carrier selected by `FocusedProper.proper`.
-/

namespace LambdaPToFCo.Direct.WfFocusRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal.Formation
open LambdaPToFCo.Direct.Internal.WfFocus

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
  .stable (Pair.Interval.plan innerFirst innerLower innerUpper)

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

private def nestedSelectionTyping :
    LambdaPFC.Path.Ty SourceContext
      (.sel (.fst (.var 0)) InnerLabel) (.intv .Bot .Top) := by
  simpa only [LambdaPFC.Tau.open] using innerTyping.sel_r

private def nestedSelectionWf :
    LambdaPFC.Tau.Wf SourceContext
      (.ty (.TSel (.fst (.var 0)) InnerLabel)) :=
  .sel nestedSelectionTyping .bot

/-- The result retains Formation and its exact nested focus, but deliberately
contains no selected value or interface. -/
noncomputable def nestedSelection :
    FocusedProper SourceContext TargetContext
      (.TSel (.fst (.var 0)) InnerLabel) := by
  cases compile nestedSelectionWf environment with
  | proper result => exact result

/-- Supply an arbitrary symbolic selected interface only after Wf formation;
the retained focus closes it to exactly the material root Shape. -/
noncomputable def closedInterface
    (symbolic : Shape.Interface nestedSelection.currentContext
      nestedSelection.shape) :
    Shape.Interface TargetContext nestedSelection.proper.shape :=
  nestedSelection.closeInterface symbolic

/-- The same operation as a full exact formed Slot. -/
noncomputable def closedSlot
    (symbolic : Shape.Interface nestedSelection.currentContext
      nestedSelection.shape) :
    Slot SourceContext TargetContext
      (.TSel (.fst (.var 0)) InnerLabel) :=
  nestedSelection.closeSlot symbolic

theorem closedSlot_has_exact_shape
    (symbolic : Shape.Interface nestedSelection.currentContext
      nestedSelection.shape) :
    (closedSlot symbolic).shape = nestedSelection.proper.shape := by
  rfl

/-- The reclosed symbolic package has ordinary unchanged-System-FCo target
typing at precisely the input type of the material Wf result. -/
noncomputable def closedPackage_hasType
    (symbolic : Shape.Interface nestedSelection.currentContext
      nestedSelection.shape) :
    Exp.HasType TargetContext (closedInterface symbolic).package
      nestedSelection.proper.shape.inputTy :=
  (closedInterface symbolic).package_hasType

end LambdaPToFCo.Direct.WfFocusRegression
