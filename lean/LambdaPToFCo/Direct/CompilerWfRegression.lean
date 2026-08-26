import LambdaPToFCo.Direct.CompilerWf

/-!
# Raw total-Wf compiler regressions

The first example follows nested non-variable proper and interval paths.  The
second compiles `Wf.path (.var)` where the referenced context entry was added
without, and provably has no, source Wf derivation.
-/

namespace LambdaPToFCo.Direct.CompilerWfRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.Wf
open LambdaPToFCo.Direct.Internal.CompilerWf

/-! ## Literal constructor coverage -/

private abbrev EmptySourceContext : LambdaPFC.Ctx 0 := .nil
private abbrev EmptyTargetContext : Ctx [] := Ctx.empty

private def emptyEnvironment : Env EmptySourceContext EmptyTargetContext :=
  Env.empty EmptyTargetContext

private def bottomWf :
    LambdaPFC.Tau.Wf EmptySourceContext
      (.ty (.Bot : LambdaPFC.Ty 0)) := .bot

private def topWf :
    LambdaPFC.Tau.Wf EmptySourceContext
      (.ty (.Top : LambdaPFC.Ty 0)) := .top

private def functionWf :
    LambdaPFC.Tau.Wf EmptySourceContext
      (.ty (.Fun .Top (.Top : LambdaPFC.Ty 1))) :=
  .fun .top .top

private def pairWf :
    LambdaPFC.Tau.Wf EmptySourceContext
      (.ty (.Pair .Top 19 (.ty (.Top : LambdaPFC.Ty 1)))) :=
  .pair .top .top

private def boundsWf :
    LambdaPFC.Tau.Wf EmptySourceContext
      (.intv (.Bot : LambdaPFC.Ty 0) .Top) :=
  .bounds_wf .bot .top .bot

noncomputable def bottomResult :
    Proper EmptyTargetContext (.Bot : LambdaPFC.Ty 0) := by
  cases compile bottomWf emptyEnvironment with
  | proper result => exact result

noncomputable def topResult :
    Proper EmptyTargetContext (.Top : LambdaPFC.Ty 0) := by
  cases compile topWf emptyEnvironment with
  | proper result => exact result

noncomputable def functionResult :
    Proper EmptyTargetContext
      (.Fun .Top (.Top : LambdaPFC.Ty 1)) := by
  cases compile functionWf emptyEnvironment with
  | proper result => exact result

noncomputable def pairResult :
    Proper EmptyTargetContext
      (.Pair .Top 19 (.ty (.Top : LambdaPFC.Ty 1))) := by
  cases compile pairWf emptyEnvironment with
  | proper result => exact result

noncomputable def boundsResult :
    Interval EmptyTargetContext (.Bot : LambdaPFC.Ty 0) .Top := by
  cases compile boundsWf emptyEnvironment with
  | interval result => exact result

/-! ## Nested raw projection and selection -/

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

private def nestedFirstTyping :
    LambdaPFC.Path.Ty SourceContext (.fst (.fst (.var 0))) (.ty .Top) :=
  innerTyping.fst

private def nestedSelectionTyping :
    LambdaPFC.Path.Ty SourceContext
      (.sel (.fst (.var 0)) InnerLabel) (.intv .Bot .Top) := by
  simpa only [LambdaPFC.Tau.open] using innerTyping.sel_r

private abbrev NestedProperPath : LambdaPFC.Path 1 :=
  .fst (.fst (.var 0))

private abbrev NestedSelectionReceiver : LambdaPFC.Path 1 :=
  .fst (.var 0)

private def nestedPathWf :
    LambdaPFC.Tau.Wf SourceContext
      (.ty (.Single NestedProperPath)) :=
  .path nestedFirstTyping

private def nestedSelectionWf :
    LambdaPFC.Tau.Wf SourceContext
      (.ty (.TSel NestedSelectionReceiver InnerLabel)) :=
  .sel nestedSelectionTyping .bot

noncomputable def nestedPath : Proper TargetContext
    (.Single NestedProperPath) := by
  cases compile nestedPathWf environment with
  | proper result => exact result

noncomputable def nestedSelection : Proper TargetContext
    (.TSel NestedSelectionReceiver InnerLabel) := by
  cases compile nestedSelectionWf environment with
  | proper result => exact result

theorem nestedPath_isClosed :
    match nestedPath.shape with
    | .opaque _ => True
    | .stable _ => False := by
  trivial

theorem nestedSelection_isClosed :
    match nestedSelection.shape with
    | .opaque _ => True
    | .stable _ => False := by
  trivial

/-! ## A path referent with no source Wf derivation -/

private def Bad : LambdaPFC.Ty 0 :=
  .Fun .Top (.Single (.fst (.var 0)))

/-- The codomain singleton asks for `fst` of a precise Top variable, so this
closed source type has no Wf derivation. -/
def bad_not_wf :
    LambdaPFC.Tau.Wf LambdaPFC.Ctx.nil (.ty Bad) -> Empty := by
  intro wf
  cases wf with
  | «fun» _ codomainWf =>
      cases codomainWf with
      | path typing =>
          cases typing with
          | fst receiver => cases receiver

private def badDomain : Shape [] := .stable (Top.plan [])
private def badCodomain : Shape badDomain.scope :=
  .stable (Single.plan (.top : Ty badDomain.scope))
private def badShape : Shape [] :=
  .stable (Function.plan badDomain badCodomain)

private def badRep : Rep Ctx.empty Bad badShape :=
  .function (.top _)
    (.singleton _ (.fst (.var 0)) (.top : Ty badDomain.scope))

private abbrev BadContext : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc Bad
private abbrev BadVariable : LambdaPFC.Path 1 := .var 0
private abbrev BadTargetContext : Ctx badShape.scope :=
  badShape.context Ctx.empty

private noncomputable def badSlot :
    Slot BadTargetContext (BadContext.lookup 0) where
  shape := badShape.rename badShape.binders.weaken
  interface := Shape.Interface.canonical Ctx.empty badShape
  rep := (badRep.sourceRename LambdaPFC.FinFun.weaken).targetRename
    badShape.binders.weaken (badShape.binders.weaken_typed Ctx.empty)

private noncomputable def badEnvironment :
    Env BadContext BadTargetContext where
  lookup index := Fin.cases badSlot (fun older => Fin.elim0 older) index

private def badPathWf :
    LambdaPFC.Tau.Wf BadContext (.ty (.Single BadVariable)) :=
  .path (LambdaPFC.Path.Ty.var :
    LambdaPFC.Path.Ty BadContext BadVariable
      (.ty (BadContext.lookup 0)))

/-- Compilation succeeds although no referent Wf premise exists or can be
supplied for the context entry from which the path was formed. -/
noncomputable def badPath : Proper BadTargetContext
    (.Single BadVariable) := by
  cases compile badPathWf badEnvironment with
  | proper result => exact result

end LambdaPToFCo.Direct.CompilerWfRegression
