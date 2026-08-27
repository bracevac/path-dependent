import LambdaPToFCo.Direct.RealizedScope

/-!
# Realized-scope regressions

A concrete Bottom-to-Top action is retained through a later lexical pair
extension.  The newest Top slot is reflexive; the older changed slot keeps
both its frozen Action and its exact endpoint realizations.
-/

namespace LambdaPToFCo.Direct.Internal.RealizedScopeRegression

open SystemFCo
open Representation
open ContextRelation
open Realization

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

private noncomputable def emptyValid :
    ValidEnv (LambdaPFC.Ctx.nil : LambdaPFC.Ctx 0) TargetContext :=
  ValidEnv.empty TargetContext

private noncomputable def firstScope :
    Scope SourceOne TargetOne .source TargetContext :=
  (Scope.root emptyValid.raw .source).extendPair
    bottomSlot.interface bottomSlot.rep (topSlot (n := 0)).interface
    (topSlot (n := 0)).rep bottomToTop

/-- Exact raw head Action after the first Bottom-to-Top extension. -/
private noncomputable def firstHeadRawAction :
    RawAction firstScope 0 := by
  let sourceAt : Wf.Proper TargetContext (.Bot : LambdaPFC.Ty 1) := {
    shape := bottomSlot.shape
    rep := bottomSlot.rep.sourceRename LambdaPFC.FinFun.weaken
  }
  refine ⟨.top, ?_⟩
  simpa only [firstScope, Scope.extendPair, Scope.root, bottomToTop,
    AtomicSubtyping.top, sourceAt, LambdaPFC.Ctx.lookup] using
    Action.top firstScope sourceAt

/-- Positive value views at the exact Reps stored by the changed head
Relation. -/
private noncomputable def firstHeadAction :
    AlignedAction firstScope 0 := by
  refine ⟨firstHeadRawAction, ?_, ?_⟩
  · simpa only [firstScope, Scope.extendPair, LambdaPFC.Ctx.lookup,
      extendAtInterface_here, bottomToTop] using
      Realizes.sourceExtendAligned
        (Realizes.absurdValue emptyValid.raw (.Bot : LambdaPFC.Ty 0)
          bottomValue bottomValue_hasType)
        (.Bot : LambdaPFC.Ty 0) bottomSlot.interface bottomSlot.rep
  · simpa only [firstScope, Scope.extendPair, LambdaPFC.Ctx.lookup,
      extendAtInterface_here, bottomToTop, AtomicSubtyping.top] using
      Realizes.sourceExtendAligned
        (Realizes.topValue emptyValid.raw (topSlot (n := 0)).interface)
        (.Top : LambdaPFC.Ty 0) (topSlot (n := 0)).interface
        (topSlot (n := 0)).rep

private noncomputable def firstRealized : RealizedScope firstScope where
  sourceValid index := by
    refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index
    simpa only [firstScope, Scope.extendPair, Scope.root,
      LambdaPFC.Ctx.lookup, extendAtInterface_here] using
      Realizes.sourceExtendHead (.Bot : LambdaPFC.Ty 0)
        bottomSlot.interface bottomSlot.rep
        (Realizes.absurdValue emptyValid.raw (.Bot : LambdaPFC.Ty 0)
          bottomValue bottomValue_hasType)
  targetValid index := by
    refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index
    simpa only [firstScope, Scope.extendPair, Scope.root,
      LambdaPFC.Ctx.lookup, extendAtInterface_here] using
      Realizes.sourceExtendHead (.Top : LambdaPFC.Ty 0)
        (topSlot (n := 0)).interface (topSlot (n := 0)).rep
        (Realizes.topValue emptyValid.raw (topSlot (n := 0)).interface)
  alignedAction index := by
    refine Fin.cases firstHeadAction (fun impossible => Fin.elim0 impossible)
      index

private abbrev SourceTwo : LambdaPFC.Ctx 2 := SourceOne.snoc .Top
private abbrev TargetTwo : LambdaPFC.Ctx 2 := TargetOne.snoc .Top

private noncomputable def secondScope :
    Scope SourceTwo TargetTwo .source TargetContext :=
  firstScope.extendPair (topSlot (n := 1)).interface
    (topSlot (n := 1)).rep (topSlot (n := 1)).interface
    (topSlot (n := 1)).rep (Relation.refl (topSlot (n := 1)).rep)

/-- Exact newest-slot Action package for the later reflexive Top binder. -/
private noncomputable def secondHeadAction :
    AlignedAction secondScope 0 := by
  refine ⟨⟨.refl, ?_⟩, ?_, ?_⟩
  · simpa only [secondScope, Scope.extendPair, LambdaPFC.Ctx.lookup] using
      Action.reflProper secondScope
        ((topSlot (n := 1)).rep.sourceRename LambdaPFC.FinFun.weaken)
  · simpa only [secondScope, Scope.extendPair, LambdaPFC.Ctx.lookup,
      extendAtInterface_here] using
      Realizes.sourceExtendAligned
        (Realizes.topValue firstScope.source
          (topSlot (n := 1)).interface)
        (.Top : LambdaPFC.Ty 1) (topSlot (n := 1)).interface
        (topSlot (n := 1)).rep
  · simpa only [secondScope, Scope.extendPair, LambdaPFC.Ctx.lookup,
      extendAtInterface_here] using
      Realizes.sourceExtendAligned
        (Realizes.topValue firstScope.target
          (topSlot (n := 1)).interface)
        (.Top : LambdaPFC.Ty 1) (topSlot (n := 1)).interface
        (topSlot (n := 1)).rep

/-- The later extension preserves the older Bottom-to-Top Action and both
positive aligned endpoint views. -/
noncomputable def extendBotToTop : RealizedScope secondScope := by
  simpa only [secondScope] using
    RealizedScope.extendPair firstRealized
      (topSlot (n := 1)).interface (topSlot (n := 1)).rep
      (Realizes.topValue firstScope.source (topSlot (n := 1)).interface)
      (topSlot (n := 1)).interface (topSlot (n := 1)).rep
      (Realizes.topValue firstScope.target (topSlot (n := 1)).interface)
      (Relation.refl (topSlot (n := 1)).rep) secondHeadAction

end LambdaPToFCo.Direct.Internal.RealizedScopeRegression
