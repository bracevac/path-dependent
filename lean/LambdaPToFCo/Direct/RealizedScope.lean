import LambdaPToFCo.Direct.Realization
import LambdaPToFCo.Direct.Action

/-!
# Realized structural scopes

A `RealizedScope` is the pointwise environment shared by the direct
realization and structural-action kernels.  It is indexed by one exact raw
`ContextRelation.Scope`.  For each slot it retains validity of both raw
endpoint values, the literal `Action` for the scope alignment, and value
realizations at the exact Reps stored by that alignment.

The wrapper introduces no representation carrier and no equality transport.
Lexical extension uses the positive source-weakening constructors of
`Realizes` and `Action` at the literal extended scope.
-/

namespace LambdaPToFCo.Direct.Internal

open SystemFCo
open Representation
open ContextRelation
open Realization

/-- Exact source proof and Action at one raw scope lookup. -/
def RawAction
    {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {sig : Sig} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base)
    (index : Fin n) : Type :=
  match side with
  | .source =>
      Sigma fun subtyping : LambdaPFC.Tau.Sub sourceContext
          (.ty (sourceContext.lookup index))
          (.ty (targetContext.lookup index)) =>
        Action scope subtyping (.proper (scope.aligned index))
  | .target =>
      Sigma fun subtyping : LambdaPFC.Tau.Sub targetContext
          (.ty (targetContext.lookup index))
          (.ty (sourceContext.lookup index)) =>
        Action scope subtyping (.proper (scope.aligned index))

/-- An Action together with positive value realizations at the exact Reps
stored by its frozen Relation.  Raw `Scope.aligned` fixes only the endpoint
Shapes, so endpoint validity alone cannot provide these two views. -/
def AlignedAction
    {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {sig : Sig} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base)
    (index : Fin n) : Type :=
  match side with
  | .source =>
      RawAction scope index ×
        Realizes scope.source (scope.aligned index).sourceRep
          (.value (scope.source.lookup index).interface) ×
        Realizes scope.target (scope.aligned index).targetRep
          (.value (scope.target.lookup index).interface)
  | .target =>
      RawAction scope index ×
        Realizes scope.target (scope.aligned index).sourceRep
          (.value (scope.target.lookup index).interface) ×
        Realizes scope.source (scope.aligned index).targetRep
          (.value (scope.source.lookup index).interface)

/-- The pointwise environment shared by `Realizes` and `Action`. -/
structure RealizedScope
    {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {sig : Sig} {base : Ctx sig}
    (raw : Scope sourceContext targetContext side base) : Type where
  sourceValid : (index : Fin n) ->
    Realizes raw.source (raw.source.lookup index).rep
      (.value (raw.source.lookup index).interface)
  targetValid : (index : Fin n) ->
    Realizes raw.target (raw.target.lookup index).rep
      (.value (raw.target.lookup index).interface)
  alignedAction : (index : Fin n) -> AlignedAction raw index

namespace RealizedScope

/-- Recover the exact source endpoint as an ordinary valid environment. -/
def sourceEnvironment
    {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {sig : Sig} {base : Ctx sig}
    {raw : Scope sourceContext targetContext side base}
    (realized : RealizedScope raw) : ValidEnv sourceContext base where
  raw := raw.source
  valid := realized.sourceValid

/-- Recover the exact target endpoint as an ordinary valid environment. -/
def targetEnvironment
    {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {sig : Sig} {base : Ctx sig}
    {raw : Scope sourceContext targetContext side base}
    (realized : RealizedScope raw) : ValidEnv targetContext base where
  raw := raw.target
  valid := realized.targetValid

/-- Alias one exact valid environment at both endpoints.  Every alignment is
the literal reflexive Action over its retained representation. -/
noncomputable def root
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : ValidEnv sourceContext base) (side : ProofSide) :
    RealizedScope (Scope.root environment.raw side) := by
  cases side with
  | source =>
      exact {
        sourceValid := environment.valid
        targetValid := environment.valid
        alignedAction := fun index =>
          ⟨⟨.refl,
              Action.reflProper (Scope.root environment.raw .source)
                (environment.raw.lookup index).rep⟩,
            environment.valid index, environment.valid index⟩
      }
  | target =>
      exact {
        sourceValid := environment.valid
        targetValid := environment.valid
        alignedAction := fun index =>
          ⟨⟨.refl,
              Action.reflProper (Scope.root environment.raw .target)
                (environment.raw.lookup index).rep⟩,
            environment.valid index, environment.valid index⟩
      }

/-- Positively transport the whole pointwise kernel through one typed target
renaming. -/
noncomputable def targetRename
    {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide}
    {sourceSig targetSig : Sig}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    {raw : Scope sourceContext targetContext side sourceBase}
    (realized : RealizedScope raw)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceBase targetBase mapping) :
    RealizedScope (raw.targetRename mapping typed) := by
  cases side with
  | source =>
      exact {
        sourceValid := fun index => by
          simpa only [Scope.targetRename, Env.targetRename,
            Slot.targetRename] using
            Realizes.targetRename (realized.sourceValid index) mapping typed
        targetValid := fun index => by
          simpa only [Scope.targetRename, Env.targetRename,
            Slot.targetRename] using
            Realizes.targetRename (realized.targetValid index) mapping typed
        alignedAction := fun index =>
          let aligned := realized.alignedAction index
          ⟨⟨aligned.1.1,
              Action.targetRename aligned.1.2 mapping typed⟩,
            by
              simpa only [Scope.targetRename, Env.targetRename,
                Slot.targetRename] using
                Realizes.targetRename aligned.2.1 mapping typed,
            by
              simpa only [Scope.targetRename, Env.targetRename,
                Slot.targetRename] using
                Realizes.targetRename aligned.2.2 mapping typed⟩
      }
  | target =>
      exact {
        sourceValid := fun index => by
          simpa only [Scope.targetRename, Env.targetRename,
            Slot.targetRename] using
            Realizes.targetRename (realized.sourceValid index) mapping typed
        targetValid := fun index => by
          simpa only [Scope.targetRename, Env.targetRename,
            Slot.targetRename] using
            Realizes.targetRename (realized.targetValid index) mapping typed
        alignedAction := fun index =>
          let aligned := realized.alignedAction index
          ⟨⟨aligned.1.1,
              Action.targetRename aligned.1.2 mapping typed⟩,
            by
              simpa only [Scope.targetRename, Env.targetRename,
                Slot.targetRename] using
                Realizes.targetRename aligned.2.1 mapping typed,
            by
              simpa only [Scope.targetRename, Env.targetRename,
                Slot.targetRename] using
                Realizes.targetRename aligned.2.2 mapping typed⟩
      }

/-- Extend a source-oriented realized scope.  The head Action is indexed by
the literal extended scope and its literal newest raw alignment. -/
noncomputable def extendPair
    {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    {raw : Scope sourceContext targetContext .source base}
    (realized : RealizedScope raw)
    {sourceType targetType : LambdaPFC.Ty n}
    {sourceShape targetShape : Shape sig}
    (sourceInterface : Shape.Interface base sourceShape)
    (sourceRep : Rep base sourceType sourceShape)
    (sourceHead : Realizes raw.source sourceRep (.value sourceInterface))
    (targetInterface : Shape.Interface base targetShape)
    (targetRep : Rep base targetType targetShape)
    (targetHead : Realizes raw.target targetRep (.value targetInterface))
    (head : Relation base sourceType targetType sourceShape targetShape)
    (headAction : AlignedAction
      (raw.extendPair sourceInterface sourceRep targetInterface targetRep head)
      0) :
    RealizedScope
      (raw.extendPair sourceInterface sourceRep targetInterface targetRep
        head) where
  sourceValid index := by
    refine Fin.cases ?_ (fun older => ?_) index
    · simpa only [Scope.extendPair, LambdaPFC.Ctx.lookup,
        extendAtInterface_here] using
        Realizes.sourceExtendHead sourceType sourceInterface sourceRep
          sourceHead
    · have old := realized.sourceValid older
      simpa only [Scope.extendPair, LambdaPFC.Ctx.lookup,
        extendAtInterface_there, Slot.sourceRename] using
        Realizes.sourceExtendAligned old sourceType sourceInterface sourceRep
  targetValid index := by
    refine Fin.cases ?_ (fun older => ?_) index
    · simpa only [Scope.extendPair, LambdaPFC.Ctx.lookup,
        extendAtInterface_here] using
        Realizes.sourceExtendHead targetType targetInterface targetRep
          targetHead
    · have old := realized.targetValid older
      simpa only [Scope.extendPair, LambdaPFC.Ctx.lookup,
        extendAtInterface_there, Slot.sourceRename] using
        Realizes.sourceExtendAligned old targetType targetInterface targetRep
  alignedAction index := by
    refine Fin.cases headAction (fun older => ?_) index
    let old := realized.alignedAction older
    let extended := raw.extendPair sourceInterface sourceRep targetInterface
      targetRep head
    let actionAt : RawAction extended older.succ :=
      ⟨_, Action.extendPairOlder raw sourceInterface sourceRep
        targetInterface targetRep head older old.1.2⟩
    let sourceAt := Realizes.sourceExtendAligned old.2.1 sourceType
      sourceInterface sourceRep
    let targetAt := Realizes.sourceExtendAligned old.2.2 targetType
      targetInterface targetRep
    refine ⟨actionAt, ?_, ?_⟩
    · simpa only [extended, Scope.extendPair, LambdaPFC.Ctx.lookup,
        extendAtInterface_there, Slot.sourceRename] using sourceAt
    · simpa only [extended, Scope.extendPair, LambdaPFC.Ctx.lookup,
        extendAtInterface_there, Slot.sourceRename] using targetAt

/-- Exact target-oriented analogue for a function-domain continuation. -/
noncomputable def extendFunction
    {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    {raw : Scope sourceContext targetContext .target base}
    (realized : RealizedScope raw)
    {sourceType targetType : LambdaPFC.Ty n}
    {sourceShape targetShape : Shape sig}
    (sourceInterface : Shape.Interface base sourceShape)
    (sourceRep : Rep base sourceType sourceShape)
    (sourceHead : Realizes raw.source sourceRep (.value sourceInterface))
    (targetInterface : Shape.Interface base targetShape)
    (targetRep : Rep base targetType targetShape)
    (targetHead : Realizes raw.target targetRep (.value targetInterface))
    (head : Relation base targetType sourceType targetShape sourceShape)
    (headAction : AlignedAction
      (raw.extendFunction sourceInterface sourceRep targetInterface targetRep
        head) 0) :
    RealizedScope
      (raw.extendFunction sourceInterface sourceRep targetInterface targetRep
        head) where
  sourceValid index := by
    refine Fin.cases ?_ (fun older => ?_) index
    · simpa only [Scope.extendFunction, LambdaPFC.Ctx.lookup,
        extendAtInterface_here] using
        Realizes.sourceExtendHead sourceType sourceInterface sourceRep
          sourceHead
    · have old := realized.sourceValid older
      simpa only [Scope.extendFunction, LambdaPFC.Ctx.lookup,
        extendAtInterface_there, Slot.sourceRename] using
        Realizes.sourceExtendAligned old sourceType sourceInterface sourceRep
  targetValid index := by
    refine Fin.cases ?_ (fun older => ?_) index
    · simpa only [Scope.extendFunction, LambdaPFC.Ctx.lookup,
        extendAtInterface_here] using
        Realizes.sourceExtendHead targetType targetInterface targetRep
          targetHead
    · have old := realized.targetValid older
      simpa only [Scope.extendFunction, LambdaPFC.Ctx.lookup,
        extendAtInterface_there, Slot.sourceRename] using
        Realizes.sourceExtendAligned old targetType targetInterface targetRep
  alignedAction index := by
    refine Fin.cases headAction (fun older => ?_) index
    let old := realized.alignedAction older
    let extended := raw.extendFunction sourceInterface sourceRep
      targetInterface targetRep head
    let actionAt : RawAction extended older.succ :=
      ⟨_, Action.extendFunctionOlder raw sourceInterface sourceRep
        targetInterface targetRep head older old.1.2⟩
    let targetAt := Realizes.sourceExtendAligned old.2.1 targetType
      targetInterface targetRep
    let sourceAt := Realizes.sourceExtendAligned old.2.2 sourceType
      sourceInterface sourceRep
    refine ⟨actionAt, ?_, ?_⟩
    · simpa only [extended, Scope.extendFunction, LambdaPFC.Ctx.lookup,
        extendAtInterface_there, Slot.sourceRename] using targetAt
    · simpa only [extended, Scope.extendFunction, LambdaPFC.Ctx.lookup,
        extendAtInterface_there, Slot.sourceRename] using sourceAt

end RealizedScope

end LambdaPToFCo.Direct.Internal
