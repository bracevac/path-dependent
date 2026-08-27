import LambdaPToFCo.Direct.Action

/-!
# Lexically reindexed Action regressions

A concrete Bot-to-Top action is retained at an older source slot across both
source-oriented pair extension and target-oriented function extension. The
result is indexed by the literal extended scope alignment, with no equality
transport or arbitrary rebase.
-/

namespace LambdaPToFCo.Direct.Internal.ActionLexicalRegression

open SystemFCo
open Representation

private abbrev TargetSig : Sig := ([] : Sig) ,, .var

private abbrev TargetContext : Ctx TargetSig :=
  Ctx.empty.bindVar Adapter.bottomTy

private def bottomValue : Exp TargetSig := .var .here

private noncomputable def bottomValue_hasType :
    Exp.HasType TargetContext bottomValue Adapter.bottomTy :=
  .var Ctx.Lookup.here

private def topPayload {sig : Sig} : Exp sig :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

private noncomputable def topPayload_hasType (base : Ctx sig) :
    Exp.HasType base (topPayload : Exp sig) .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

private noncomputable def topInterface (base : Ctx sig) :
    Shape.Interface base (.stable (Top.plan sig)) where
  arguments := Top.arguments .top topPayload (topPayload_hasType base)

private noncomputable def bottomSlot :
    Slot TargetContext (.Bot : LambdaPFC.Ty 0) :=
  Slot.absurd bottomValue bottomValue_hasType

private noncomputable def topSlot {n : Nat} :
    Slot TargetContext (.Top : LambdaPFC.Ty n) where
  shape := .stable (Top.plan TargetSig)
  interface := topInterface TargetContext
  rep := .top TargetContext

private noncomputable def bottomWf :
    Wf.Proper TargetContext (.Bot : LambdaPFC.Ty 0) := {
  shape := bottomSlot.shape
  rep := bottomSlot.rep
}

private noncomputable def bottomToTop :
    Relation TargetContext (.Bot : LambdaPFC.Ty 0) .Top
      bottomSlot.shape (topSlot (n := 0)).shape := by
  simpa only [topSlot] using (AtomicSubtyping.top bottomWf).relation

private abbrev SourceOne : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc (.Bot : LambdaPFC.Ty 0)

private abbrev TargetOne : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc (.Top : LambdaPFC.Ty 0)

private noncomputable def emptySourceScope :
    ContextRelation.Scope (LambdaPFC.Ctx.nil : LambdaPFC.Ctx 0)
      .nil .source TargetContext :=
  ContextRelation.Scope.root (Env.empty TargetContext) .source

private noncomputable def firstPairScope :
    ContextRelation.Scope SourceOne TargetOne .source TargetContext :=
  emptySourceScope.extendPair bottomSlot.interface bottomSlot.rep
    (topSlot (n := 0)).interface (topSlot (n := 0)).rep bottomToTop

private def botToTopSource : LambdaPFC.Tau.Sub SourceOne
    (.ty .Bot) (.ty .Top) :=
  .top

private noncomputable def firstPairAction :
    Action firstPairScope botToTopSource
      (.proper (firstPairScope.aligned 0)) := by
  let sourceAt : Wf.Proper TargetContext (.Bot : LambdaPFC.Ty 1) := {
    shape := bottomSlot.shape
    rep := bottomSlot.rep.sourceRename LambdaPFC.FinFun.weaken
  }
  simpa only [firstPairScope, emptySourceScope,
    ContextRelation.Scope.extendPair, ContextRelation.Scope.root,
    bottomToTop, AtomicSubtyping.top, sourceAt, LambdaPFC.Ctx.lookup,
    botToTopSource] using Action.top firstPairScope sourceAt

private abbrev SourceTwo : LambdaPFC.Ctx 2 := SourceOne.snoc .Top
private abbrev TargetTwo : LambdaPFC.Ctx 2 := TargetOne.snoc .Top

private noncomputable def secondPairScope :
    ContextRelation.Scope SourceTwo TargetTwo .source TargetContext :=
  firstPairScope.extendPair (topSlot (n := 1)).interface
    (topSlot (n := 1)).rep (topSlot (n := 1)).interface
    (topSlot (n := 1)).rep (Relation.refl (topSlot (n := 1)).rep)

/-- A real older Bot-to-Top action survives a source-oriented pair
extension, with both literal source endpoints weakened once. -/
noncomputable def pairOlderBotToTop :
    Action secondPairScope
      (botToTopSource.weaken (bound := (.Top : LambdaPFC.Ty 1)))
      (.proper (secondPairScope.aligned 1)) := by
  exact Action.extendPairOlder firstPairScope
    (topSlot (n := 1)).interface (topSlot (n := 1)).rep
    (topSlot (n := 1)).interface (topSlot (n := 1)).rep
    (Relation.refl (topSlot (n := 1)).rep) 0 firstPairAction

private abbrev FunctionSourceOne : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc (.Top : LambdaPFC.Ty 0)

private abbrev FunctionTargetOne : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc (.Bot : LambdaPFC.Ty 0)

private noncomputable def emptyTargetScope :
    ContextRelation.Scope (LambdaPFC.Ctx.nil : LambdaPFC.Ctx 0)
      .nil .target TargetContext :=
  ContextRelation.Scope.root (Env.empty TargetContext) .target

private noncomputable def firstFunctionScope :
    ContextRelation.Scope FunctionSourceOne FunctionTargetOne .target
      TargetContext :=
  emptyTargetScope.extendFunction (topSlot (n := 0)).interface
    (topSlot (n := 0)).rep bottomSlot.interface bottomSlot.rep bottomToTop

private def botToTopTarget : LambdaPFC.Tau.Sub FunctionTargetOne
    (.ty .Bot) (.ty .Top) :=
  .top

private noncomputable def firstFunctionAction :
    Action firstFunctionScope botToTopTarget
      (.proper (firstFunctionScope.aligned 0)) := by
  let sourceAt : Wf.Proper TargetContext (.Bot : LambdaPFC.Ty 1) := {
    shape := bottomSlot.shape
    rep := bottomSlot.rep.sourceRename LambdaPFC.FinFun.weaken
  }
  simpa only [firstFunctionScope, emptyTargetScope,
    ContextRelation.Scope.extendFunction, ContextRelation.Scope.root,
    bottomToTop, AtomicSubtyping.top, sourceAt, LambdaPFC.Ctx.lookup,
    botToTopTarget] using Action.top firstFunctionScope sourceAt

private abbrev FunctionSourceTwo : LambdaPFC.Ctx 2 :=
  FunctionSourceOne.snoc .Top

private abbrev FunctionTargetTwo : LambdaPFC.Ctx 2 :=
  FunctionTargetOne.snoc .Top

private noncomputable def secondFunctionScope :
    ContextRelation.Scope FunctionSourceTwo FunctionTargetTwo .target
      TargetContext :=
  firstFunctionScope.extendFunction (topSlot (n := 1)).interface
    (topSlot (n := 1)).rep (topSlot (n := 1)).interface
    (topSlot (n := 1)).rep (Relation.refl (topSlot (n := 1)).rep)

/-- The target-oriented function extension has the exact dual index. -/
noncomputable def functionOlderBotToTop :
    Action secondFunctionScope
      (botToTopTarget.weaken (bound := (.Top : LambdaPFC.Ty 1)))
      (.proper (secondFunctionScope.aligned 1)) := by
  exact Action.extendFunctionOlder firstFunctionScope
    (topSlot (n := 1)).interface (topSlot (n := 1)).rep
    (topSlot (n := 1)).interface (topSlot (n := 1)).rep
    (Relation.refl (topSlot (n := 1)).rep) 0 firstFunctionAction

theorem pairOlderBotToTop_treeSize :
    pairOlderBotToTop.treeSize = firstPairAction.treeSize + 1 := by
  rfl

theorem functionOlderBotToTop_treeSize :
    functionOlderBotToTop.treeSize = firstFunctionAction.treeSize + 1 := by
  rfl

end LambdaPToFCo.Direct.Internal.ActionLexicalRegression
