import LambdaPToFCo.Direct.Action

/-!
# Structural action regressions

The proper gate projects the exact retained first action. The interval gate
builds the reachable `widen ; interval-pair` action and separately invokes
the retained callback under one concrete delayed-member opening, obtaining
the interval child, mapped witness, and selected-identity bridge.
-/

namespace LambdaPToFCo.Direct.ActionRegression

noncomputable section

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.PairSubtyping

/-- A proper pair's first projection keeps the literal first premise and its
exact relation index. -/
private def properFstGate
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {firstSubtyping : LambdaPFC.Tau.Sub sourceContext
      (.ty sourceFirstType) (.ty targetFirstType)}
    {sourceFirst targetFirst : Shape sig}
    {scope : ContextRelation.Scope sourceContext targetContext .source base}
    {firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    (first : Action scope firstSubtyping (.proper firstRelation)) :
    Action scope firstSubtyping (.proper firstRelation) :=
  first.properFst

/-- The selected-child operation typechecks alongside the concrete reachable
action shape `widen q sourcePair ; intervalPair`. The widen premise runs under
the exact source endpoint root and is spliced into the outer pair Action. The
returned first component is that whole action; the second is produced
separately from the exact delayed-member callback retained by its pair child.
This deliberately does not claim an eliminator through the outer transitivity
node. -/
private noncomputable def intervalSelectedAlongsideWidenGate
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {path : LambdaPFC.Path n}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {scope : ContextRelation.Scope sourceContext targetContext .source base}
    {firstSubtyping : LambdaPFC.Tau.Sub sourceContext
      (.ty sourceFirstType) (.ty targetFirstType)}
    {memberSubtyping : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    {firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    (typing : LambdaPFC.Path.Ty sourceContext path
      (.ty (.Pair sourceFirstType label
        (.intv sourceLowerType sourceUpperType))))
    (first : Action scope firstSubtyping (.proper firstRelation))
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper)
    (sourcePairInterface : Shape.Interface base
      (.stable (Pair.Interval.plan sourceFirst sourceLower sourceUpper)))
    (memberRelation : Action.IntervalMemberRelations scope firstRelation
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep)
    (memberAction : {final : Sig} -> {finalContext : Ctx final} ->
      (mapping : Rename
        (IntervalMemberCompiler.CallbackSig sourceFirst sourceLower
          sourceUpper) final) ->
      (typed : Rename.Typed
        (IntervalMemberCompiler.CallbackContext base sourceFirst sourceLower
          sourceUpper) finalContext mapping) ->
      (sourceInterface : Shape.Interface finalContext
        (IntervalMemberCompiler.SourceFirstAt sourceFirst sourceLower
          sourceUpper mapping)) ->
      (targetInterface : Shape.Interface finalContext
        (IntervalMemberCompiler.TargetFirstAt sourceFirst sourceLower
          sourceUpper targetFirst mapping)) ->
      Action
        (intervalActionScopeAt scope firstRelation mapping typed
          sourceInterface targetInterface)
        memberSubtyping
        (.interval (memberRelation mapping typed sourceInterface
          targetInterface)))
    {final : Sig} {finalContext : Ctx final}
    (mapping : Rename
      (IntervalMemberCompiler.CallbackSig sourceFirst sourceLower sourceUpper)
      final)
    (typed : Rename.Typed
      (IntervalMemberCompiler.CallbackContext base sourceFirst sourceLower
        sourceUpper) finalContext mapping)
    (sourceInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.SourceFirstAt sourceFirst sourceLower sourceUpper
        mapping))
    (targetInterface : Shape.Interface finalContext
      (IntervalMemberCompiler.TargetFirstAt sourceFirst sourceLower sourceUpper
        targetFirst mapping))
    (sourceWitness :
      let members := intervalMemberScopeAt scope.endpointEnvs firstRelation
        sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep mapping
        typed sourceInterface targetInterface
      Conversion.Interval.Witness finalContext members.source.lower
        members.source.upper) := by
  let sourcePairRep : Rep base
      (.Pair sourceFirstType label
        (.intv sourceLowerType sourceUpperType))
      (.stable (Pair.Interval.plan sourceFirst sourceLower sourceUpper)) :=
    .intervalPair firstRelation.sourceRep sourceLowerRep sourceUpperRep
  let sourceSlot : Slot base
      (.Pair sourceFirstType label
        (.intv sourceLowerType sourceUpperType)) := {
    shape := .stable (Pair.Interval.plan sourceFirst sourceLower sourceUpper)
    interface := sourcePairInterface
    rep := sourcePairRep
  }
  let sourceRoot := ContextRelation.Scope.root scope.source .source
  let widenAction := Action.widenAt sourceRoot typing sourceSlot
  let pairAction := Action.intervalPair (label := label) scope first
    sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep memberRelation
    memberAction
  let wholeAction := Action.sourceProper scope widenAction pairAction
  let selected := Action.intervalSelected memberRelation memberAction mapping
    typed sourceInterface targetInterface sourceWitness
  exact (wholeAction, selected)

end

end LambdaPToFCo.Direct.ActionRegression
