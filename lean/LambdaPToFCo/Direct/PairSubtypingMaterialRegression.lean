import LambdaPToFCo.Direct.Action

/-!
# Same-run material interval callback regression

An enriched interval action is consumed while the source representation is
open.  The recursive action, mapped witness, and selected identity bridge are
passed to one result-polymorphic continuation; none is replayed or stored for
a later opening.
-/

namespace LambdaPToFCo.Direct.Internal.PairSubtypingMaterialRegression

open SystemFCo
open Representation

/-- The exact action payload exposed by the material interval callback. -/
structure SelectedContinuation
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {scope : ContextRelation.Scope sourceContext targetContext .source base}
    {firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {memberSubtyping : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (memberRelation : Action.IntervalMemberRelations scope firstRelation
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep)
    (answer : Ty sig) : Type 1 where
  body : {final : Sig} -> {finalContext : Ctx final} ->
    (mapping : Rename
      (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst
        sourceLower sourceUpper) final) ->
    (typed : Rename.Typed
      (PairSubtyping.IntervalMemberCompiler.CallbackContext base sourceFirst
        sourceLower sourceUpper) finalContext mapping) ->
    (rootTyped : Rename.Typed base finalContext
      (PairSubtyping.MaterialRootAt sourceFirst sourceLower sourceUpper
        mapping)) ->
    (targetFirstInterface : Shape.Interface finalContext
      (PairSubtyping.IntervalMemberCompiler.TargetFirstAt sourceFirst
        sourceLower sourceUpper targetFirst mapping)) ->
    let sourceFirstInterface :=
      PairSubtyping.materialSourceFirstInterface sourceFirst sourceLower
        sourceUpper mapping typed
    let members := PairSubtyping.intervalMemberScopeAt scope.endpointEnvs
      firstRelation sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
      mapping typed sourceFirstInterface targetFirstInterface
    (sourceWitness : Conversion.Interval.Witness finalContext
      members.source.lower members.source.upper) ->
    (relation : AtomicSubtyping.IntervalRelation members.source
      members.target) ->
    Action
      (PairSubtyping.intervalActionScopeAt scope firstRelation mapping typed
        sourceFirstInterface targetFirstInterface)
      memberSubtyping (.interval relation) ->
    (targetWitness : Conversion.Interval.Witness finalContext
      members.target.lower members.target.upper) ->
    Conversion.Bridge finalContext sourceWitness.selected.inputTy
      targetWitness.selected.inputTy ->
    Path.Body finalContext
      (answer.rename
        (PairSubtyping.MaterialRootAt sourceFirst sourceLower sourceUpper
          mapping))

/-- `runMaterial` invokes `intervalEnriched` once and immediately exposes the
retained child action and the witness mapped by that same relation. -/
noncomputable def runSelected
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {scope : ContextRelation.Scope sourceContext targetContext .source base}
    {firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {memberSubtyping : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (memberRelation : Action.IntervalMemberRelations scope firstRelation
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep)
    (memberAction : {final : Sig} -> {finalContext : Ctx final} ->
      (mapping : Rename
        (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst
          sourceLower sourceUpper) final) ->
      (typed : Rename.Typed
        (PairSubtyping.IntervalMemberCompiler.CallbackContext base sourceFirst
          sourceLower sourceUpper) finalContext mapping) ->
      (sourceInterface : Shape.Interface finalContext
        (PairSubtyping.IntervalMemberCompiler.SourceFirstAt sourceFirst
          sourceLower sourceUpper mapping)) ->
      (targetInterface : Shape.Interface finalContext
        (PairSubtyping.IntervalMemberCompiler.TargetFirstAt sourceFirst
          sourceLower sourceUpper targetFirst mapping)) ->
      Action
        (PairSubtyping.intervalActionScopeAt scope firstRelation mapping typed
          sourceInterface targetInterface)
        memberSubtyping
        (.interval (memberRelation mapping typed sourceInterface
          targetInterface)))
    (sourceInterface : Shape.Interface base
      (.stable (Pair.Interval.plan sourceFirst sourceLower sourceUpper)))
    (answer : Ty sig)
    (continuation : SelectedContinuation (memberSubtyping := memberSubtyping)
      memberRelation answer) :
    Path.Body base answer := by
  let compiler := Action.intervalEnriched memberRelation memberAction
  apply PairSubtyping.runMaterial compiler sourceInterface answer
  exact {
    body := fun mapping typed rootTyped targetFirstInterface view => by
      exact continuation.body mapping typed rootTyped targetFirstInterface
        view.sourceWitness view.relation view.retained view.targetWitness
        view.selectedBridge
  }

end LambdaPToFCo.Direct.Internal.PairSubtypingMaterialRegression
