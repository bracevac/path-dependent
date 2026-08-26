import LambdaPToFCo.Direct.SubtypingPair

/-!
# Formation-aware dependent-pair subtyping regressions

Both regressions change the first binder from Bottom to Top.  The proper
member is contextual singleton reflexivity, so its two target singleton
packages genuinely have different retained referent identities.  The
interval member maps `{x}..{x}` to `Bottom..Top` in the same extended scope.
-/

namespace LambdaPToFCo.Direct.SubtypingPairRegression

noncomputable section

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Formation
open LambdaPToFCo.Direct.Internal.SubtypingScope
open LambdaPToFCo.Direct.Internal.SubtypingPair

abbrev SourceContext : LambdaPFC.Ctx 0 := .nil
abbrev TargetContext : Ctx [] := Ctx.empty

noncomputable def environment : Formation.Env SourceContext TargetContext :=
  Formation.Env.empty TargetContext

noncomputable def scope : Scope SourceContext SourceContext .source
    TargetContext :=
  Scope.root environment .source

abbrev SourceFirstType : LambdaPFC.Ty 0 := .Bot
abbrev TargetFirstType : LambdaPFC.Ty 0 := .Top

abbrev SourceFirst : Shape [] := .stable (Bot.plan [])
abbrev TargetFirst : Shape [] := .stable (Top.plan [])

noncomputable def sourceFirstFormation : Formation SourceContext
    TargetContext SourceFirstType SourceFirst :=
  .bottom

noncomputable def targetFirstFormation : Formation SourceContext
    TargetContext TargetFirstType TargetFirst :=
  .top

def firstDerivation : LambdaPFC.Tau.Sub SourceContext
    (.ty SourceFirstType) (.ty TargetFirstType) :=
  .top

noncomputable def firstCut : CutView scope firstDerivation
    SourceFirst TargetFirst :=
  let source : Wf.Proper TargetContext SourceFirstType := {
    shape := SourceFirst
    rep := sourceFirstFormation.rep
  }
  CutView.ofRelation sourceFirstFormation targetFirstFormation
    (AtomicSubtyping.top source).relation

private noncomputable def singletonMemberFormation
    {firstType : LambdaPFC.Ty 0} {first : Shape []}
    (firstFormation : Formation SourceContext TargetContext firstType first) :
    Formation (SourceContext.snoc firstType) (first.context TargetContext)
      (.Single (.var 0))
      (.stable (Single.plan
        (first.rename first.binders.weaken).inputTy)) :=
  let opened := (firstFormation.sourceWeaken firstType).targetRename
    first.binders.weaken (first.binders.weaken_typed TargetContext)
  .singleton .var (Shape.Interface.canonical TargetContext first) opened

noncomputable def sourceSingletonFormation :=
  singletonMemberFormation sourceFirstFormation

noncomputable def targetSingletonFormation :=
  singletonMemberFormation targetFirstFormation

abbrev SourceSingleton : Shape SourceFirst.scope :=
  .stable (Single.plan
    (SourceFirst.rename SourceFirst.binders.weaken).inputTy)

abbrev TargetSingleton : Shape TargetFirst.scope :=
  .stable (Single.plan
    (TargetFirst.rename TargetFirst.binders.weaken).inputTy)

def properMemberDerivation : LambdaPFC.Tau.Sub
    (SourceContext.snoc SourceFirstType)
    (.ty (.Single (.var 0))) (.ty (.Single (.var 0))) :=
  .refl

noncomputable def properMemberCompiler : ProperCompiler firstCut
    sourceSingletonFormation targetSingletonFormation
    properMemberDerivation where
  compile mapping typed sourceInterface targetInterface := by
    let frame := properFrameAt firstCut sourceSingletonFormation
      targetSingletonFormation mapping typed sourceInterface targetInterface
    simpa only [frame] using
      SubtypingAtomic.reflSingletonVariable frame.scope 0

/-- Proper covariance across a genuinely changed first binder. -/
noncomputable def properCut : CutView scope
    (.pair (a := 0) firstDerivation properMemberDerivation)
    (.stable (Pair.Proper.plan SourceFirst SourceSingleton))
    (.stable (Pair.Proper.plan TargetFirst TargetSingleton)) :=
  SubtypingPair.proper firstCut sourceSingletonFormation
    targetSingletonFormation properMemberCompiler

example : Exp.HasType TargetContext properCut.relation.conversion.function
    (.arrow (Pair.Proper.plan SourceFirst SourceSingleton).inputTy
      (Pair.Proper.plan TargetFirst TargetSingleton).inputTy) :=
  properCut.relation.conversion.functionTyping

def intervalMemberDerivation : LambdaPFC.Tau.Sub
    (SourceContext.snoc SourceFirstType)
    (.intv (.Single (.var 0)) (.Single (.var 0)))
    (.intv .Bot .Top) :=
  .bounds .bot .top .refl

noncomputable def targetLowerFormation : Formation
    (SourceContext.snoc TargetFirstType)
    (TargetFirst.context TargetContext) (.Bot : LambdaPFC.Ty 1)
    (.stable (Bot.plan TargetFirst.scope)) :=
  .bottom

noncomputable def targetUpperFormation : Formation
    (SourceContext.snoc TargetFirstType)
    (TargetFirst.context TargetContext) (.Top : LambdaPFC.Ty 1)
    (.stable (Top.plan TargetFirst.scope)) :=
  .top

noncomputable def intervalMemberCompiler : IntervalCompiler firstCut
    sourceSingletonFormation sourceSingletonFormation targetLowerFormation
    targetUpperFormation intervalMemberDerivation where
  compile mapping typed sourceInterface targetInterface := by
    let frame := intervalFrameAt firstCut sourceSingletonFormation
      sourceSingletonFormation targetLowerFormation targetUpperFormation
      mapping typed sourceInterface targetInterface
    exact {
    lower := (AtomicSubtyping.bot {
      shape := frame.members.source.lower
      rep := frame.members.source.lowerRep
    }).relation
    upper := (AtomicSubtyping.top {
      shape := frame.members.source.upper
      rep := frame.members.source.upperRep
    }).relation
    }

/-- Interval covariance across the same changed first binder.  The source
selected witness remains the exact opaque witness opened from the package. -/
noncomputable def intervalCut : CutView scope
    (.pair (a := 0) firstDerivation intervalMemberDerivation)
    (.stable (Pair.Interval.plan SourceFirst
      SourceSingleton SourceSingleton))
    (.stable (Pair.Interval.plan TargetFirst
      (.stable (Bot.plan TargetFirst.scope))
      (.stable (Top.plan TargetFirst.scope)))) :=
  SubtypingPair.interval firstCut sourceSingletonFormation
    sourceSingletonFormation targetLowerFormation targetUpperFormation
    intervalMemberCompiler

example : Exp.HasType TargetContext intervalCut.relation.conversion.function
    (.arrow (Pair.Interval.plan SourceFirst SourceSingleton
      SourceSingleton).inputTy
      (Pair.Interval.plan TargetFirst
        (.stable (Bot.plan TargetFirst.scope))
        (.stable (Top.plan TargetFirst.scope))).inputTy) :=
  intervalCut.relation.conversion.functionTyping

end
end LambdaPToFCo.Direct.SubtypingPairRegression
