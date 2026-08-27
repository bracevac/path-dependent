import LambdaPToFCo.Direct.Action

/-!
# Same-run material proper-pair callback regression

The enriched proper-pair action is consumed while its source representation
is open.  Its first and member interface maps each run once, and the retained
member Action is delivered with the exact two member interfaces produced by
that run.
-/

namespace LambdaPToFCo.Direct.Internal.PairSubtypingProperMaterialRegression

open SystemFCo
open Representation

structure SelectedContinuation
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    {scope : ContextRelation.Scope sourceContext targetContext .source base}
    {firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember}
    {targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember}
    {memberSubtyping : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (memberRelation : Action.ProperMemberRelations scope firstRelation
      sourceMemberRep targetMemberRep)
    (answer : Ty sig) : Type 1 where
  body : {firstFinal final : Sig} ->
    {firstContext : Ctx firstFinal} -> {finalContext : Ctx final} ->
    (firstMapping : Rename
      (PairSubtyping.ProperMemberCompiler.CallbackSig sourceFirst
        sourceMember) firstFinal) ->
    (firstTyped : Rename.Typed
      (PairSubtyping.ProperMemberCompiler.CallbackContext base sourceFirst
        sourceMember) firstContext firstMapping) ->
    (targetFirstInterface : Shape.Interface firstContext
      (PairSubtyping.ProperMemberCompiler.TargetFirstAt sourceFirst
        sourceMember targetFirst firstMapping)) ->
    let sourceFirstInterface :=
      PairSubtyping.properMaterialSourceFirstInterface firstMapping firstTyped
    let members := PairSubtyping.properMemberScopeAt scope.endpointEnvs
      firstRelation sourceMemberRep targetMemberRep firstMapping firstTyped
      sourceFirstInterface targetFirstInterface
    (relation : Relation firstContext sourceMemberType targetMemberType
      members.source.memberShape members.target.memberShape) ->
    (memberAction : Action
      (PairSubtyping.properActionScopeAt scope firstRelation firstMapping
        firstTyped sourceFirstInterface targetFirstInterface)
      memberSubtyping (.proper relation)) ->
    (memberMapping : Rename firstFinal final) ->
    (memberTyped : Rename.Typed firstContext finalContext memberMapping) ->
    Rename.Typed base finalContext
      (PairSubtyping.ProperMaterialRootAt firstMapping memberMapping) ->
    (sourceMemberInterface : Shape.Interface finalContext
      (members.source.memberShape.rename memberMapping)) ->
    (targetMemberInterface : Shape.Interface finalContext
      ((PairSubtyping.ProperMaterialTargetMemberAt
        (targetMember := targetMember) firstMapping memberMapping).subst
        (PairSubtyping.properMaterialTargetFirstInterface
          targetFirstInterface memberMapping memberTyped).substitution)) ->
    Path.Body finalContext
      (answer.rename
        (PairSubtyping.ProperMaterialRootAt firstMapping memberMapping))

/-- `runProperMaterial` consumes the callback produced by
`Action.properEnriched`; relation and retained member Action come from the
same invocation that maps the actual source-member interface. -/
noncomputable def runSelected
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    {scope : ContextRelation.Scope sourceContext targetContext .source base}
    {firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember}
    {targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember}
    {memberSubtyping : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (memberRelation : Action.ProperMemberRelations scope firstRelation
      sourceMemberRep targetMemberRep)
    (memberAction : {final : Sig} -> {finalContext : Ctx final} ->
      (mapping : Rename
        (PairSubtyping.ProperMemberCompiler.CallbackSig sourceFirst
          sourceMember) final) ->
      (typed : Rename.Typed
        (PairSubtyping.ProperMemberCompiler.CallbackContext base sourceFirst
          sourceMember) finalContext mapping) ->
      (sourceInterface : Shape.Interface finalContext
        (PairSubtyping.ProperMemberCompiler.SourceFirstAt sourceFirst
          sourceMember mapping)) ->
      (targetInterface : Shape.Interface finalContext
        (PairSubtyping.ProperMemberCompiler.TargetFirstAt sourceFirst
          sourceMember targetFirst mapping)) ->
      Action
        (PairSubtyping.properActionScopeAt scope firstRelation mapping typed
          sourceInterface targetInterface)
        memberSubtyping
        (.proper (memberRelation mapping typed sourceInterface
          targetInterface)))
    (sourceInterface : Shape.Interface base
      (.stable (Pair.Proper.plan sourceFirst sourceMember)))
    (answer : Ty sig)
    (continuation : SelectedContinuation (memberSubtyping := memberSubtyping)
      memberRelation answer) :
    Path.Body base answer := by
  let compiler := Action.properEnriched memberRelation memberAction
  apply PairSubtyping.runProperMaterial compiler sourceInterface answer
  exact {
    body := fun firstMapping firstTyped targetFirstInterface relation
        memberMapping memberTyped rootTyped view => by
      exact continuation.body firstMapping firstTyped targetFirstInterface
        relation view.retained memberMapping memberTyped rootTyped
        view.sourceMemberInterface view.targetMemberInterface
  }

end LambdaPToFCo.Direct.Internal.PairSubtypingProperMaterialRegression
