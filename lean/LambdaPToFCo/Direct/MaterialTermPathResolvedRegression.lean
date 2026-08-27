import LambdaPToFCo.Direct.MaterialTermPath

/-!
# Direct dependent material-path result regression

The nested `fst ; sel_r` path below resolves to an interval by returning the
ordinary dependent `MaterialTermPath.Resolved` existential.  Its hidden
selected target type is consumed by direct pattern matching, without a CPS
runner or a second path traversal.
-/

namespace LambdaPToFCo.Direct.MaterialTermPathResolvedRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.MaterialTermPath

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

private def innerRep :
    Rep Ctx.empty (InnerSource 1) innerShape :=
  .intervalPair (.top _) (.bottom _) (.top _)

private def outerRep :
    Rep Ctx.empty (SourceContext.lookup 0) outerShape := by
  change Rep Ctx.empty
    (.Pair (InnerSource 1) OuterLabel (.ty .Top)) outerShape
  exact .properPair innerRep (.top _)

private abbrev TargetContext : Ctx outerShape.scope :=
  outerShape.context Ctx.empty

private noncomputable def receiver :
    Slot TargetContext (SourceContext.lookup 0) where
  shape := outerShape.rename outerShape.binders.weaken
  interface := Shape.Interface.canonical Ctx.empty outerShape
  rep := outerRep.targetRename outerShape.binders.weaken
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
      (.ty (InnerSource 1)) :=
  receiverTyping.fst

private def selectionTyping :
    LambdaPFC.Path.Ty SourceContext
      (.sel (.fst (.var 0)) InnerLabel) (.intv .Bot .Top) := by
  simpa only [LambdaPFC.Tau.open] using innerTyping.sel_r

/-- The direct API returns the hidden interval as an ordinary existential. -/
noncomputable def nestedResolved :
    Resolved (sourceContext := SourceContext) TargetContext
      (.intv (.Bot : LambdaPFC.Ty 1) .Top) :=
  resolve selectionTyping environment

/-- Pattern matching opens the selected target type in exactly its material
scope and can immediately form the corresponding selection representation. -/
noncomputable def consumeNestedResolved : PUnit := by
  cases nestedResolved with
  | focused _focus _currentEnvironment view =>
      cases view with
      | interval interval =>
          let _selected := interval.selection
            (.fst (.var 0)) InnerLabel
          exact PUnit.unit

/-- The direct result is definitionally the interval branch for this nested
receiver; no proper fallback or replay is involved. -/
theorem nestedResolved_isInterval :
    match nestedResolved with
    | .focused _ _ (.interval _) => True := by
  trivial

end LambdaPToFCo.Direct.MaterialTermPathResolvedRegression
