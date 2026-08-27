import LambdaPToFCo.Direct.PrincipalStructuralCuts
import LambdaPToFCo.Direct.AtomicSubtyping

/-!
# Principal structural-cut regressions

The proper-pair cut below has a real, non-reflexive middle:

```
{ Bot; Bot }  <:  { Top; Bot }  <:  { Top; Top }.
```

The first leg changes only the first component and the second leg changes
only the member.  Both frozen pair callbacks are therefore forced to share
the retained middle `Top/Bot` representation.  The surrounding raw
`ContextRelation.Scope` also contains a genuinely changed `Bot -> Top`
binder, represented from an in-scope impredicative Bottom value.
-/

namespace LambdaPToFCo.Direct.PrincipalStructuralCutsRegression

noncomputable section

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.ContextRelation
open LambdaPToFCo.Direct.Internal.PrincipalStructuralCuts

private abbrev Label : LambdaPFC.Name := 0

private abbrev SourceContext : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc (.Bot : LambdaPFC.Ty 0)

private abbrev TargetSourceContext : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc (.Top : LambdaPFC.Ty 0)

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

private noncomputable def topSlot
    (base : Ctx sig) : Slot base (.Top : LambdaPFC.Ty n) where
  shape := .stable (Top.plan sig)
  interface := {
    arguments := Top.arguments .top topPayload (topPayload_hasType base) }
  rep := .top base

private noncomputable def sourceBinding :
    Slot TargetContext (.Bot : LambdaPFC.Ty 0) :=
  Slot.absurd bottomValue bottomValue_hasType

private noncomputable def targetBinding :
    Slot TargetContext (.Top : LambdaPFC.Ty 0) :=
  topSlot TargetContext

private noncomputable def bindingRelation :
    Relation TargetContext (.Bot : LambdaPFC.Ty 0) .Top
      sourceBinding.shape targetBinding.shape := by
  let source : Wf.Proper TargetContext (.Bot : LambdaPFC.Ty 0) := {
    shape := sourceBinding.shape
    rep := sourceBinding.rep
  }
  simpa only [targetBinding, topSlot] using
    (AtomicSubtyping.top source).relation

/-- A non-root scope whose newest aligned source binding is Bottom and whose
opposite binding is Top. -/
private noncomputable def changedScope :
    Scope SourceContext TargetSourceContext .source TargetContext :=
  (Scope.root (Env.empty TargetContext) .source).extendPair
    sourceBinding.interface sourceBinding.rep
    targetBinding.interface targetBinding.rep bindingRelation

private def firstDerivation01 : LambdaPFC.Tau.Sub SourceContext
    (.ty .Bot) (.ty .Top) :=
  .top

private def firstDerivation12 : LambdaPFC.Tau.Sub SourceContext
    (.ty .Top) (.ty .Top) :=
  .refl

private def memberDerivation01 : LambdaPFC.Tau.Sub
    (SourceContext.snoc .Bot) (.ty .Bot) (.ty .Bot) :=
  .refl

private def memberDerivation12 : LambdaPFC.Tau.Sub
    (SourceContext.snoc .Top) (.ty .Bot) (.ty .Top) :=
  .top

private noncomputable def sourceFirst :
    Wf.Proper TargetContext (.Bot : LambdaPFC.Ty 1) :=
  .bottom TargetContext

private noncomputable def middleFirst :
    Wf.Proper TargetContext (.Top : LambdaPFC.Ty 1) :=
  .top TargetContext

private noncomputable def targetFirst :
    Wf.Proper TargetContext (.Top : LambdaPFC.Ty 1) :=
  middleFirst

private noncomputable def sourceMember :
    Wf.Proper (sourceFirst.shape.context TargetContext)
      (.Bot : LambdaPFC.Ty 2) :=
  .bottom _

private noncomputable def middleMember :
    Wf.Proper (middleFirst.shape.context TargetContext)
      (.Bot : LambdaPFC.Ty 2) :=
  .bottom _

private noncomputable def targetMember :
    Wf.Proper (targetFirst.shape.context TargetContext)
      (.Top : LambdaPFC.Ty 2) :=
  .top _

private noncomputable def first01 :
    PairSubtyping.FirstCompilation TargetContext firstDerivation01
      sourceFirst.shape middleFirst.shape := by
  exact { relation := (AtomicSubtyping.top sourceFirst).relation }

private noncomputable def first12 :
    PairSubtyping.FirstCompilation TargetContext firstDerivation12
      middleFirst.shape targetFirst.shape := by
  exact { relation := Relation.refl middleFirst.rep }

private noncomputable def member01 :
    PairSubtyping.ProperMemberCompiler changedScope.endpointEnvs
      first01.relation sourceMember.rep middleMember.rep
      memberDerivation01 := by
  refine { compile := ?_ }
  intro final finalContext mapping typed sourceInterface targetInterface
  let members := PairSubtyping.properMemberScopeAt
    changedScope.endpointEnvs first01.relation sourceMember.rep
      middleMember.rep mapping typed sourceInterface targetInterface
  let source : Wf.Proper finalContext (.Bot : LambdaPFC.Ty 2) := {
    shape := members.source.memberShape
    rep := members.source.memberRep
  }
  simpa only [members] using (AtomicSubtyping.refl source).relation

private noncomputable def member12 :
    PairSubtyping.ProperMemberCompiler changedScope.endpointEnvs
      first12.relation middleMember.rep targetMember.rep
      memberDerivation12 := by
  refine { compile := ?_ }
  intro final finalContext mapping typed sourceInterface targetInterface
  let members := PairSubtyping.properMemberScopeAt
    changedScope.endpointEnvs first12.relation middleMember.rep
      targetMember.rep mapping typed sourceInterface targetInterface
  let source : Wf.Proper finalContext (.Bot : LambdaPFC.Ty 2) := {
    shape := members.source.memberShape
    rep := members.source.memberRep
  }
  simpa only [members, PairSubtyping.properMemberScopeAt,
    Top.plan_subst] using (AtomicSubtyping.top source).relation

/-- The fused result skips any independently synthesized middle pair.  Both
legs are constructed around the exact `middleFirst` and `middleMember`. -/
noncomputable def changedMiddle :
    Relation TargetContext
      (.Pair (.Bot : LambdaPFC.Ty 1) Label (.ty .Bot))
      (.Pair (.Top : LambdaPFC.Ty 1) Label (.ty .Top))
      (.stable (Pair.Proper.plan sourceFirst.shape sourceMember.shape))
      (.stable (Pair.Proper.plan targetFirst.shape targetMember.shape)) :=
  properProper changedScope first01 first12 sourceMember.rep
    middleMember.rep targetMember.rep member01 member12

/-- The target conversion is an ordinary unchanged-SystemFCo function. -/
example : Exp.HasType TargetContext changedMiddle.conversion.function
    (.arrow
      (Pair.Proper.plan sourceFirst.shape sourceMember.shape).inputTy
      (Pair.Proper.plan targetFirst.shape targetMember.shape).inputTy) :=
  changedMiddle.conversion.functionTyping

end

end LambdaPToFCo.Direct.PrincipalStructuralCutsRegression
