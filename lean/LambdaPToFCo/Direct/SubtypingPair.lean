import LambdaPToFCo.Direct.SubtypingAtomic
import LambdaPToFCo.Direct.PairSubtyping

/-!
# Formation-aware dependent-pair subtyping

This layer connects the literal source `Tau.Sub.pair` rule to the target-only
pair package transformer.  Recursive compilation is indexed by the two
literal premises.  The sealed contextual `Scope` is extended only inside the
first component's exact interface-map continuation, where both real first
interfaces are available.

No target shape equality or raw target function is accepted from callers.
The higher-order member boundaries below are compiler-internal and return a
sealed cut (or interval cut) for the exact formations constructed here.
-/

namespace LambdaPToFCo.Direct.Internal.SubtypingPair

open SystemFCo
open Representation
open Formation
open SubtypingScope

/-! ## Exact proper-pair continuation plumbing -/

private def sourceFirstAtBinder (first : Shape sig) : Shape (sig ,, .var) :=
  first.rename (Rename.weaken .var)

private def properMemberAtBinder (first : Shape sig)
    (member : Shape first.scope) : Shape (sourceFirstAtBinder first).scope :=
  Pair.Proper.renameMember first member (Rename.weaken .var)

private def properSourceOpening (first : Shape sig)
    (member : Shape first.scope) :
    Rename (sig ,, .var) (properMemberAtBinder first member).scope :=
  (sourceFirstAtBinder first).binders.weaken.comp
    (properMemberAtBinder first member).binders.weaken

private def properOpening (first : Shape sig) (member : Shape first.scope) :
    Rename sig (properMemberAtBinder first member).scope :=
  (Rename.weaken .var).comp (properSourceOpening first member)

private def properOpenedContext (base : Ctx sig) (first : Shape sig)
    (member : Shape first.scope) :
    Ctx (properMemberAtBinder first member).scope :=
  (properMemberAtBinder first member).context
    ((sourceFirstAtBinder first).context
      (base.bindVar (Pair.Proper.representation first member).existsTy))

private noncomputable def properOpening_typed (base : Ctx sig)
    (first : Shape sig) (member : Shape first.scope) :
    Rename.Typed base (properOpenedContext base first member)
      (properOpening first member) :=
  TypedRename.comp
    (Rename.Typed.weaken base
      (.var (Pair.Proper.representation first member).existsTy))
    (TypedRename.comp
      ((sourceFirstAtBinder first).binders.weaken_typed
        (base.bindVar
          (Pair.Proper.representation first member).existsTy))
      ((properMemberAtBinder first member).binders.weaken_typed
        ((sourceFirstAtBinder first).context
          (base.bindVar
            (Pair.Proper.representation first member).existsTy))))

private def properMemberOpening (first : Shape sig)
    (member : Shape first.scope) :
    Rename first.scope (properMemberAtBinder first member).scope :=
  (first.liftRename (Rename.weaken .var)).comp
    (properMemberAtBinder first member).binders.weaken

private noncomputable def properMemberOpening_typed (base : Ctx sig)
    (first : Shape sig) (member : Shape first.scope) :
    Rename.Typed (first.context base) (properOpenedContext base first member)
      (properMemberOpening first member) :=
  TypedRename.comp
    (first.liftRename_typed
      (Rename.Typed.weaken base
        (.var (Pair.Proper.representation first member).existsTy)))
    ((properMemberAtBinder first member).binders.weaken_typed
      ((sourceFirstAtBinder first).context
        (base.bindVar
          (Pair.Proper.representation first member).existsTy)))

private def properSourceMemberActual (first : Shape sig)
    (member : Shape first.scope) :
    Shape (properMemberAtBinder first member).scope :=
  (properMemberAtBinder first member).rename
    (properMemberAtBinder first member).binders.weaken

private noncomputable def properSourceMemberFormationAt
    {sourceContext : LambdaPFC.Ctx n}
    {sourceFirstType : LambdaPFC.Ty n}
    {sourceMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    (formation : Formation (sourceContext.snoc sourceFirstType)
      (sourceFirst.context base) sourceMemberType sourceMember)
    (mapping : Rename (properMemberAtBinder sourceFirst sourceMember).scope
      final)
    (typed : Rename.Typed (properOpenedContext base sourceFirst sourceMember)
      finalContext mapping) :
    Formation (sourceContext.snoc sourceFirstType) finalContext
      sourceMemberType
      ((properSourceMemberActual sourceFirst sourceMember).rename mapping) := by
  let opened := formation.targetRename
    (properMemberOpening sourceFirst sourceMember)
    (properMemberOpening_typed base sourceFirst sourceMember)
  let renamed := opened.targetRename mapping typed
  unfold properSourceMemberActual properMemberAtBinder
    Pair.Proper.renameMember
  change Formation _ _ _
    ((sourceMember.rename
      ((sourceFirst.liftRename (Rename.weaken .var)).comp
        (sourceMember.rename
          (sourceFirst.liftRename (Rename.weaken .var))).binders.weaken)).rename
      mapping) at renamed
  rw [← Shape.rename_comp] at renamed
  exact renamed

private noncomputable def properTargetMemberFormationAt
    {targetContext : LambdaPFC.Ctx n}
    {targetFirstType : LambdaPFC.Ty n}
    {targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceFirst : Shape sig} {sourceMember : Shape sourceFirst.scope}
    {targetFirst : Shape sig} {targetMember : Shape targetFirst.scope}
    (formation : Formation (targetContext.snoc targetFirstType)
      (targetFirst.context base) targetMemberType targetMember)
    (mapping : Rename (properMemberAtBinder sourceFirst sourceMember).scope
      final)
    (typed : Rename.Typed (properOpenedContext base sourceFirst sourceMember)
      finalContext mapping)
    (targetFirstInterface : Shape.Interface finalContext
      ((targetFirst.rename (properOpening sourceFirst sourceMember)).rename
        mapping)) :
    Formation (targetContext.snoc targetFirstType) finalContext
      targetMemberType
      ((Pair.Proper.renameMember
        (targetFirst.rename (properOpening sourceFirst sourceMember))
        (Pair.Proper.renameMember targetFirst targetMember
          (properOpening sourceFirst sourceMember)) mapping).subst
        targetFirstInterface.substitution) :=
  let opened := formation.targetRename
    (targetFirst.liftRename (properOpening sourceFirst sourceMember))
    (targetFirst.liftRename_typed
      (properOpening_typed base sourceFirst sourceMember))
  let renamed := opened.targetRename
    ((targetFirst.rename (properOpening sourceFirst sourceMember)).liftRename
      mapping)
    ((targetFirst.rename (properOpening sourceFirst sourceMember)).liftRename_typed
      typed)
  renamed.targetSubst targetFirstInterface.substitution
    targetFirstInterface.arguments.substitution_typed

/-- The exact proper-member frame computed inside the first interface-map
continuation. -/
structure ProperFrame
    (sourceContext targetContext : LambdaPFC.Ctx n)
    (sourceFirstType targetFirstType : LambdaPFC.Ty n)
    (sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1))
    (base : Ctx sig) : Type where
  members : MemberScope sourceContext targetContext sourceFirstType
    targetFirstType sourceMemberType targetMemberType base
  scope : Scope (sourceContext.snoc sourceFirstType)
    (targetContext.snoc targetFirstType) .source base
  sourceFormation : Formation (sourceContext.snoc sourceFirstType) base
    sourceMemberType members.source.memberShape
  targetFormation : Formation (targetContext.snoc targetFirstType) base
    targetMemberType members.target.memberShape

noncomputable def properFrameAt
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    {rootScope : Scope sourceContext targetContext .source base}
    {firstDerivation : LambdaPFC.Tau.Sub sourceContext
      (.ty sourceFirstType) (.ty targetFirstType)}
    (first : CutView rootScope firstDerivation sourceFirst targetFirst)
    (sourceMemberFormation : Formation
      (sourceContext.snoc sourceFirstType) (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberFormation : Formation
      (targetContext.snoc targetFirstType) (targetFirst.context base)
      targetMemberType targetMember)
    (mapping : Rename (properMemberAtBinder sourceFirst sourceMember).scope
      final)
    (typed : Rename.Typed (properOpenedContext base sourceFirst sourceMember)
      finalContext mapping)
    (sourceFirstInterface : Shape.Interface finalContext
      ((sourceFirst.rename (properOpening sourceFirst sourceMember)).rename
        mapping))
    (targetFirstInterface : Shape.Interface finalContext
      ((targetFirst.rename (properOpening sourceFirst sourceMember)).rename
        mapping)) :
    ProperFrame sourceContext targetContext sourceFirstType targetFirstType
      sourceMemberType targetMemberType finalContext := by
  let environments : EndpointEnvs sourceContext targetContext base := {
    source := rootScope.source.erase
    target := rootScope.target.erase
  }
  let members := PairSubtyping.properMemberScopeAt environments
    first.relation sourceMemberFormation.rep targetMemberFormation.rep
    mapping typed sourceFirstInterface targetFirstInterface
  let opening := properOpening sourceFirst sourceMember
  let openingTyped := properOpening_typed base sourceFirst sourceMember
  let scopeAt := (rootScope.targetRename opening openingTyped).targetRename
    mapping typed
  let firstAt := (first.targetRename opening openingTyped).targetRename
    mapping typed
  let sourceFirstFormationAt :=
    (first.sourceFormation.targetRename opening openingTyped).targetRename
      mapping typed
  let targetFirstFormationAt :=
    (first.targetFormation.targetRename opening openingTyped).targetRename
      mapping typed
  let sourceFormationAt : Formation
      (sourceContext.snoc sourceFirstType) finalContext sourceMemberType
      members.source.memberShape :=
    properSourceMemberFormationAt sourceMemberFormation mapping typed
  let targetFormationAt : Formation
      (targetContext.snoc targetFirstType) finalContext targetMemberType
      members.target.memberShape :=
    properTargetMemberFormationAt targetMemberFormation mapping typed
      targetFirstInterface
  exact {
    members := members
    scope := scopeAt.extendPair sourceFirstInterface sourceFirstFormationAt
      targetFirstInterface targetFirstFormationAt firstAt.relation
    sourceFormation := sourceFormationAt
    targetFormation := targetFormationAt
  }

/-- Literal proper-member recursion at the one exact frame constructed by
this pair rule. -/
structure ProperCompiler
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    {rootScope : Scope sourceContext targetContext .source base}
    {firstDerivation : LambdaPFC.Tau.Sub sourceContext
      (.ty sourceFirstType) (.ty targetFirstType)}
    (first : CutView rootScope firstDerivation sourceFirst targetFirst)
    (sourceMemberFormation : Formation
      (sourceContext.snoc sourceFirstType) (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberFormation : Formation
      (targetContext.snoc targetFirstType) (targetFirst.context base)
      targetMemberType targetMember)
    (_derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)) : Type where
  compile : {final : Sig} -> {finalContext : Ctx final} ->
    (mapping : Rename (properMemberAtBinder sourceFirst sourceMember).scope
      final) ->
    (typed : Rename.Typed (properOpenedContext base sourceFirst sourceMember)
      finalContext mapping) ->
    (sourceFirstInterface : Shape.Interface finalContext
      ((sourceFirst.rename (properOpening sourceFirst sourceMember)).rename
        mapping)) ->
    (targetFirstInterface : Shape.Interface finalContext
      ((targetFirst.rename (properOpening sourceFirst sourceMember)).rename
        mapping)) ->
    let frame := properFrameAt first sourceMemberFormation
      targetMemberFormation mapping typed sourceFirstInterface
      targetFirstInterface
    CutView frame.scope _derivation frame.members.source.memberShape
      frame.members.target.memberShape

private noncomputable def properMemberAdapter
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    {scope : Scope sourceContext targetContext .source base}
    {firstDerivation : LambdaPFC.Tau.Sub sourceContext
      (.ty sourceFirstType) (.ty targetFirstType)}
    (first : CutView scope firstDerivation sourceFirst targetFirst)
    (sourceMemberFormation : Formation
      (sourceContext.snoc sourceFirstType) (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberFormation : Formation
      (targetContext.snoc targetFirstType) (targetFirst.context base)
      targetMemberType targetMember)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (compiler : ProperCompiler first sourceMemberFormation
      targetMemberFormation memberDerivation) :
    let environments : EndpointEnvs sourceContext targetContext base := {
      source := scope.source.erase
      target := scope.target.erase
    }
    PairSubtyping.ProperMemberCompiler environments first.relation
      sourceMemberFormation.rep targetMemberFormation.rep memberDerivation := by
  let environments : EndpointEnvs sourceContext targetContext base := {
    source := scope.source.erase
    target := scope.target.erase
  }
  refine { compile := ?_ }
  intro final finalContext mapping typed sourceFirstInterface
    targetFirstInterface
  exact (compiler.compile mapping typed sourceFirstInterface
    targetFirstInterface).relation

/-- Compile a proper-member source pair rule under one sealed contextual
alignment.  The only recursive inputs are cuts indexed by the literal first
and member premises. -/
noncomputable def proper
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    {scope : Scope sourceContext targetContext .source base}
    {firstDerivation : LambdaPFC.Tau.Sub sourceContext
      (.ty sourceFirstType) (.ty targetFirstType)}
    (first : CutView scope firstDerivation sourceFirst targetFirst)
    (sourceMemberFormation : Formation
      (sourceContext.snoc sourceFirstType) (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberFormation : Formation
      (targetContext.snoc targetFirstType) (targetFirst.context base)
      targetMemberType targetMember)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (member : ProperCompiler first sourceMemberFormation
      targetMemberFormation memberDerivation) :
    CutView scope (.pair (a := label) firstDerivation memberDerivation)
      (.stable (Pair.Proper.plan sourceFirst sourceMember))
      (.stable (Pair.Proper.plan targetFirst targetMember)) :=
  let environments : EndpointEnvs sourceContext targetContext base := {
    source := scope.source.erase
    target := scope.target.erase
  }
  let firstCompilation : PairSubtyping.FirstCompilation base firstDerivation
      sourceFirst targetFirst := { relation := first.relation }
  let memberAdapter := properMemberAdapter first sourceMemberFormation
    targetMemberFormation member
  let relation := PairSubtyping.proper environments firstCompilation
    sourceMemberFormation.rep targetMemberFormation.rep memberAdapter
  CutView.ofRelation
    (.properPair first.sourceFormation sourceMemberFormation)
    (.properPair first.targetFormation targetMemberFormation)
    relation

/-! ## Exact interval-pair continuation plumbing -/

private def intervalLowerAtBinder (first : Shape sig)
    (lower : Shape first.scope) : Shape (sourceFirstAtBinder first).scope :=
  lower.rename (first.liftRename (Rename.weaken .var))

private def intervalUpperAtBinder (first : Shape sig)
    (upper : Shape first.scope) : Shape (sourceFirstAtBinder first).scope :=
  upper.rename (first.liftRename (Rename.weaken .var))

private def intervalMemberAtBinder (first : Shape sig)
    (lower upper : Shape first.scope) :
    Telescope (sourceFirstAtBinder first).scope :=
  Pair.Interval.memberTelescope
    (intervalLowerAtBinder first lower)
    (intervalUpperAtBinder first upper)

private def intervalSourceOpening (first : Shape sig)
    (lower upper : Shape first.scope) :
    Rename (sig ,, .var) (intervalMemberAtBinder first lower upper).scope :=
  (sourceFirstAtBinder first).binders.weaken.comp
    (intervalMemberAtBinder first lower upper).weaken

private def intervalOpening (first : Shape sig)
    (lower upper : Shape first.scope) :
    Rename sig (intervalMemberAtBinder first lower upper).scope :=
  (Rename.weaken .var).comp
    (intervalSourceOpening first lower upper)

private def intervalOpenedContext (base : Ctx sig) (first : Shape sig)
    (lower upper : Shape first.scope) :
    Ctx (intervalMemberAtBinder first lower upper).scope :=
  (intervalMemberAtBinder first lower upper).context
    ((sourceFirstAtBinder first).context
      (base.bindVar
        (Pair.Interval.representation first lower upper).existsTy))

private noncomputable def intervalOpening_typed (base : Ctx sig)
    (first : Shape sig) (lower upper : Shape first.scope) :
    Rename.Typed base (intervalOpenedContext base first lower upper)
      (intervalOpening first lower upper) :=
  TypedRename.comp
    (Rename.Typed.weaken base
      (.var (Pair.Interval.representation first lower upper).existsTy))
    (TypedRename.comp
      ((sourceFirstAtBinder first).binders.weaken_typed
        (base.bindVar
          (Pair.Interval.representation first lower upper).existsTy))
      ((intervalMemberAtBinder first lower upper).weaken_typed
        ((sourceFirstAtBinder first).context
          (base.bindVar
            (Pair.Interval.representation first lower upper).existsTy))))

private def intervalEndpointOpening (first : Shape sig)
    (lower upper : Shape first.scope) :
    Rename first.scope (intervalMemberAtBinder first lower upper).scope :=
  (first.liftRename (Rename.weaken .var)).comp
    (intervalMemberAtBinder first lower upper).weaken

private noncomputable def intervalEndpointOpening_typed (base : Ctx sig)
    (first : Shape sig) (lower upper : Shape first.scope) :
    Rename.Typed (first.context base)
      (intervalOpenedContext base first lower upper)
      (intervalEndpointOpening first lower upper) :=
  TypedRename.comp
    (first.liftRename_typed
      (Rename.Typed.weaken base
        (.var (Pair.Interval.representation first lower upper).existsTy)))
    ((intervalMemberAtBinder first lower upper).weaken_typed
      ((sourceFirstAtBinder first).context
        (base.bindVar
          (Pair.Interval.representation first lower upper).existsTy)))

private def intervalLowerActual (first : Shape sig)
    (lower upper : Shape first.scope) :
    Shape (intervalMemberAtBinder first lower upper).scope :=
  (intervalLowerAtBinder first lower).rename
    (intervalMemberAtBinder first lower upper).weaken

private def intervalUpperActual (first : Shape sig)
    (lower upper : Shape first.scope) :
    Shape (intervalMemberAtBinder first lower upper).scope :=
  (intervalUpperAtBinder first upper).rename
    (intervalMemberAtBinder first lower upper).weaken

private noncomputable def intervalSourceLowerFormationAt
    {sourceContext : LambdaPFC.Ctx n}
    {sourceFirstType : LambdaPFC.Ty n}
    {sourceLowerType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    (formation : Formation (sourceContext.snoc sourceFirstType)
      (sourceFirst.context base) sourceLowerType sourceLower)
    (mapping : Rename
      (intervalMemberAtBinder sourceFirst sourceLower sourceUpper).scope final)
    (typed : Rename.Typed
      (intervalOpenedContext base sourceFirst sourceLower sourceUpper)
      finalContext mapping) :
    Formation (sourceContext.snoc sourceFirstType) finalContext
      sourceLowerType
      ((intervalLowerActual sourceFirst sourceLower sourceUpper).rename
        mapping) := by
  let opened := formation.targetRename
    (intervalEndpointOpening sourceFirst sourceLower sourceUpper)
    (intervalEndpointOpening_typed base sourceFirst sourceLower sourceUpper)
  let renamed := opened.targetRename mapping typed
  unfold intervalLowerActual intervalLowerAtBinder
  change Formation _ _ _
    ((sourceLower.rename
      ((sourceFirst.liftRename (Rename.weaken .var)).comp
        (Pair.Interval.memberTelescope
          (sourceLower.rename
            (sourceFirst.liftRename (Rename.weaken .var)))
          (sourceUpper.rename
            (sourceFirst.liftRename (Rename.weaken .var)))).weaken)).rename
      mapping) at renamed
  rw [← Shape.rename_comp] at renamed
  exact renamed

private noncomputable def intervalSourceUpperFormationAt
    {sourceContext : LambdaPFC.Ctx n}
    {sourceFirstType : LambdaPFC.Ty n}
    {sourceUpperType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    (formation : Formation (sourceContext.snoc sourceFirstType)
      (sourceFirst.context base) sourceUpperType sourceUpper)
    (mapping : Rename
      (intervalMemberAtBinder sourceFirst sourceLower sourceUpper).scope final)
    (typed : Rename.Typed
      (intervalOpenedContext base sourceFirst sourceLower sourceUpper)
      finalContext mapping) :
    Formation (sourceContext.snoc sourceFirstType) finalContext
      sourceUpperType
      ((intervalUpperActual sourceFirst sourceLower sourceUpper).rename
        mapping) := by
  let opened := formation.targetRename
    (intervalEndpointOpening sourceFirst sourceLower sourceUpper)
    (intervalEndpointOpening_typed base sourceFirst sourceLower sourceUpper)
  let renamed := opened.targetRename mapping typed
  unfold intervalUpperActual intervalUpperAtBinder
  change Formation _ _ _
    ((sourceUpper.rename
      ((sourceFirst.liftRename (Rename.weaken .var)).comp
        (Pair.Interval.memberTelescope
          (sourceLower.rename
            (sourceFirst.liftRename (Rename.weaken .var)))
          (sourceUpper.rename
            (sourceFirst.liftRename (Rename.weaken .var)))).weaken)).rename
      mapping) at renamed
  rw [← Shape.rename_comp] at renamed
  exact renamed

private def targetIntervalFirstAtSource
    (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope)
    (targetFirst : Shape sig) :
    Shape (intervalMemberAtBinder sourceFirst sourceLower sourceUpper).scope :=
  (sourceFirstAtBinder targetFirst).rename
    (intervalSourceOpening sourceFirst sourceLower sourceUpper)

private def targetIntervalEndpointAtSource
    (sourceFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope)
    (targetFirst : Shape sig) (targetEndpoint : Shape targetFirst.scope) :
    Shape (targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).scope :=
  (targetEndpoint.rename
    (targetFirst.liftRename (Rename.weaken .var))).rename
      ((sourceFirstAtBinder targetFirst).liftRename
        (intervalSourceOpening sourceFirst sourceLower sourceUpper))

private noncomputable def intervalTargetEndpointFormationAt
    {targetContext : LambdaPFC.Ctx n}
    {targetFirstType : LambdaPFC.Ty n}
    {targetEndpointType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetFirst : Shape sig} {targetEndpoint : Shape targetFirst.scope}
    (formation : Formation (targetContext.snoc targetFirstType)
      (targetFirst.context base) targetEndpointType targetEndpoint)
    (mapping : Rename
      (intervalMemberAtBinder sourceFirst sourceLower sourceUpper).scope final)
    (typed : Rename.Typed
      (intervalOpenedContext base sourceFirst sourceLower sourceUpper)
      finalContext mapping)
    (targetFirstInterface : Shape.Interface finalContext
      ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).rename mapping)) :
    Formation (targetContext.snoc targetFirstType) finalContext
      targetEndpointType
      (((targetIntervalEndpointAtSource sourceFirst sourceLower sourceUpper
        targetFirst targetEndpoint).rename
          ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
            targetFirst).liftRename mapping)).subst
        targetFirstInterface.substitution) :=
  let atBinder := formation.targetRename
    (targetFirst.liftRename (Rename.weaken .var))
    (targetFirst.liftRename_typed
      (Rename.Typed.weaken base
        (.var (Pair.Interval.representation sourceFirst sourceLower
          sourceUpper).existsTy)))
  let atSource := atBinder.targetRename
    ((sourceFirstAtBinder targetFirst).liftRename
      (intervalSourceOpening sourceFirst sourceLower sourceUpper))
    ((sourceFirstAtBinder targetFirst).liftRename_typed
      (TypedRename.comp
        ((sourceFirstAtBinder sourceFirst).binders.weaken_typed
          (base.bindVar
            (Pair.Interval.representation sourceFirst sourceLower
              sourceUpper).existsTy))
        ((intervalMemberAtBinder sourceFirst sourceLower sourceUpper).weaken_typed
          ((sourceFirstAtBinder sourceFirst).context
            (base.bindVar
              (Pair.Interval.representation sourceFirst sourceLower
                sourceUpper).existsTy)))))
  let atFinal := atSource.targetRename
    ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).liftRename mapping)
    ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
      targetFirst).liftRename_typed typed)
  atFinal.targetSubst targetFirstInterface.substitution
    targetFirstInterface.arguments.substitution_typed

/-- The exact interval-member frame computed inside the first interface-map
continuation. -/
structure IntervalFrame
    (sourceContext targetContext : LambdaPFC.Ctx n)
    (sourceFirstType targetFirstType : LambdaPFC.Ty n)
    (sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1))
    (base : Ctx sig) : Type where
  members : PairSubtyping.IntervalMemberScope sourceContext targetContext
    sourceFirstType targetFirstType sourceLowerType sourceUpperType
    targetLowerType targetUpperType base
  scope : Scope (sourceContext.snoc sourceFirstType)
    (targetContext.snoc targetFirstType) .source base
  sourceLowerFormation : Formation (sourceContext.snoc sourceFirstType) base
    sourceLowerType members.source.lower
  sourceUpperFormation : Formation (sourceContext.snoc sourceFirstType) base
    sourceUpperType members.source.upper
  targetLowerFormation : Formation (targetContext.snoc targetFirstType) base
    targetLowerType members.target.lower
  targetUpperFormation : Formation (targetContext.snoc targetFirstType) base
    targetUpperType members.target.upper

noncomputable def intervalFrameAt
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {rootScope : Scope sourceContext targetContext .source base}
    {firstDerivation : LambdaPFC.Tau.Sub sourceContext
      (.ty sourceFirstType) (.ty targetFirstType)}
    (first : CutView rootScope firstDerivation sourceFirst targetFirst)
    (sourceLowerFormation : Formation
      (sourceContext.snoc sourceFirstType) (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperFormation : Formation
      (sourceContext.snoc sourceFirstType) (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerFormation : Formation
      (targetContext.snoc targetFirstType) (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperFormation : Formation
      (targetContext.snoc targetFirstType) (targetFirst.context base)
      targetUpperType targetUpper)
    (mapping : Rename
      (intervalMemberAtBinder sourceFirst sourceLower sourceUpper).scope final)
    (typed : Rename.Typed
      (intervalOpenedContext base sourceFirst sourceLower sourceUpper)
      finalContext mapping)
    (sourceFirstInterface : Shape.Interface finalContext
      (((sourceFirstAtBinder sourceFirst).rename
        (intervalSourceOpening sourceFirst sourceLower sourceUpper)).rename
          mapping))
    (targetFirstInterface : Shape.Interface finalContext
      ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).rename mapping)) :
    IntervalFrame sourceContext targetContext sourceFirstType targetFirstType
      sourceLowerType sourceUpperType targetLowerType targetUpperType
      finalContext := by
  let environments : EndpointEnvs sourceContext targetContext base := {
    source := rootScope.source.erase
    target := rootScope.target.erase
  }
  let opening := intervalOpening sourceFirst sourceLower sourceUpper
  let openingTyped := intervalOpening_typed base sourceFirst sourceLower
    sourceUpper
  let scopeAt := (rootScope.targetRename opening openingTyped).targetRename
    mapping typed
  let firstAt := (first.targetRename opening openingTyped).targetRename
    mapping typed
  let sourceFirstFormationAt :=
    (first.sourceFormation.targetRename opening openingTyped).targetRename
      mapping typed
  let targetFirstFormationAt :=
    (first.targetFormation.targetRename opening openingTyped).targetRename
      mapping typed
  let sourceFirstAt := ((sourceFirstAtBinder sourceFirst).rename
    (intervalSourceOpening sourceFirst sourceLower sourceUpper)).rename mapping
  let targetFirstAt := (targetIntervalFirstAtSource sourceFirst sourceLower
    sourceUpper targetFirst).rename mapping
  let adjustedFirst : Relation finalContext sourceFirstType targetFirstType
      sourceFirstAt targetFirstAt := by
    simpa only [intervalOpening, intervalSourceOpening, sourceFirstAtBinder,
      targetIntervalFirstAtSource, sourceFirstAt, targetFirstAt,
      Shape.rename_comp] using firstAt.relation
  let adjustedSourceFormation : Formation sourceContext finalContext
      sourceFirstType sourceFirstAt := by
    simpa only [intervalOpening, intervalSourceOpening, sourceFirstAtBinder,
      sourceFirstAt, Shape.rename_comp] using sourceFirstFormationAt
  let adjustedTargetFormation : Formation targetContext finalContext
      targetFirstType targetFirstAt := by
    simpa only [intervalOpening, intervalSourceOpening, sourceFirstAtBinder,
      targetIntervalFirstAtSource, targetFirstAt, Shape.rename_comp] using
        targetFirstFormationAt
  let members := PairSubtyping.intervalMemberScopeAt environments
    first.relation sourceLowerFormation.rep sourceUpperFormation.rep
    targetLowerFormation.rep targetUpperFormation.rep mapping typed
    sourceFirstInterface targetFirstInterface
  let sourceLowerFormationAt : Formation
      (sourceContext.snoc sourceFirstType) finalContext sourceLowerType
      members.source.lower := by
    simpa only [members, PairSubtyping.intervalMemberScopeAt] using
      intervalSourceLowerFormationAt sourceLowerFormation mapping typed
  let sourceUpperFormationAt : Formation
      (sourceContext.snoc sourceFirstType) finalContext sourceUpperType
      members.source.upper := by
    simpa only [members, PairSubtyping.intervalMemberScopeAt] using
      intervalSourceUpperFormationAt sourceUpperFormation mapping typed
  let targetLowerFormationAt : Formation
      (targetContext.snoc targetFirstType) finalContext targetLowerType
      members.target.lower := by
    simpa only [members, PairSubtyping.intervalMemberScopeAt] using
      intervalTargetEndpointFormationAt targetLowerFormation mapping typed
        targetFirstInterface
  let targetUpperFormationAt : Formation
      (targetContext.snoc targetFirstType) finalContext targetUpperType
      members.target.upper := by
    simpa only [members, PairSubtyping.intervalMemberScopeAt] using
      intervalTargetEndpointFormationAt targetUpperFormation mapping typed
        targetFirstInterface
  exact {
    members := members
    scope := scopeAt.extendPair sourceFirstInterface adjustedSourceFormation
      targetFirstInterface adjustedTargetFormation adjustedFirst
    sourceLowerFormation := sourceLowerFormationAt
    sourceUpperFormation := sourceUpperFormationAt
    targetLowerFormation := targetLowerFormationAt
    targetUpperFormation := targetUpperFormationAt
  }

/-- Literal interval-member recursion at the one exact frame constructed by
this pair rule. -/
structure IntervalCompiler
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {rootScope : Scope sourceContext targetContext .source base}
    {firstDerivation : LambdaPFC.Tau.Sub sourceContext
      (.ty sourceFirstType) (.ty targetFirstType)}
    (first : CutView rootScope firstDerivation sourceFirst targetFirst)
    (sourceLowerFormation : Formation
      (sourceContext.snoc sourceFirstType) (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperFormation : Formation
      (sourceContext.snoc sourceFirstType) (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerFormation : Formation
      (targetContext.snoc targetFirstType) (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperFormation : Formation
      (targetContext.snoc targetFirstType) (targetFirst.context base)
      targetUpperType targetUpper)
    (_derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)) : Type where
  compile : {final : Sig} -> {finalContext : Ctx final} ->
    (mapping : Rename
      (intervalMemberAtBinder sourceFirst sourceLower sourceUpper).scope final) ->
    (typed : Rename.Typed
      (intervalOpenedContext base sourceFirst sourceLower sourceUpper)
      finalContext mapping) ->
    (sourceFirstInterface : Shape.Interface finalContext
      (((sourceFirstAtBinder sourceFirst).rename
        (intervalSourceOpening sourceFirst sourceLower sourceUpper)).rename
          mapping)) ->
    (targetFirstInterface : Shape.Interface finalContext
      ((targetIntervalFirstAtSource sourceFirst sourceLower sourceUpper
        targetFirst).rename mapping)) ->
    let frame := intervalFrameAt first sourceLowerFormation
      sourceUpperFormation targetLowerFormation targetUpperFormation mapping
      typed sourceFirstInterface targetFirstInterface
    AtomicSubtyping.IntervalRelation frame.members.source
      frame.members.target

private noncomputable def intervalMemberAdapter
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {scope : Scope sourceContext targetContext .source base}
    {firstDerivation : LambdaPFC.Tau.Sub sourceContext
      (.ty sourceFirstType) (.ty targetFirstType)}
    (first : CutView scope firstDerivation sourceFirst targetFirst)
    (sourceLowerFormation : Formation
      (sourceContext.snoc sourceFirstType) (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperFormation : Formation
      (sourceContext.snoc sourceFirstType) (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerFormation : Formation
      (targetContext.snoc targetFirstType) (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperFormation : Formation
      (targetContext.snoc targetFirstType) (targetFirst.context base)
      targetUpperType targetUpper)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : IntervalCompiler first sourceLowerFormation
      sourceUpperFormation targetLowerFormation targetUpperFormation
      memberDerivation) :
    let environments : EndpointEnvs sourceContext targetContext base := {
      source := scope.source.erase
      target := scope.target.erase
    }
    PairSubtyping.IntervalMemberCompiler environments first.relation
      sourceLowerFormation.rep sourceUpperFormation.rep
      targetLowerFormation.rep targetUpperFormation.rep memberDerivation := by
  let environments : EndpointEnvs sourceContext targetContext base := {
    source := scope.source.erase
    target := scope.target.erase
  }
  refine { compile := ?_ }
  intro final finalContext mapping typed sourceFirstInterface
    targetFirstInterface
  exact compiler.compile mapping typed sourceFirstInterface
    targetFirstInterface

/-- Compile an interval-member source pair rule under one sealed contextual
alignment.  The actual opened selected shape is mapped and repackaged by the
target-only kernel; this layer supplies only exact endpoint formations. -/
noncomputable def interval
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {scope : Scope sourceContext targetContext .source base}
    {firstDerivation : LambdaPFC.Tau.Sub sourceContext
      (.ty sourceFirstType) (.ty targetFirstType)}
    (first : CutView scope firstDerivation sourceFirst targetFirst)
    (sourceLowerFormation : Formation
      (sourceContext.snoc sourceFirstType) (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperFormation : Formation
      (sourceContext.snoc sourceFirstType) (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerFormation : Formation
      (targetContext.snoc targetFirstType) (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperFormation : Formation
      (targetContext.snoc targetFirstType) (targetFirst.context base)
      targetUpperType targetUpper)
    {memberDerivation : LambdaPFC.Tau.Sub
      (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (member : IntervalCompiler first sourceLowerFormation
      sourceUpperFormation targetLowerFormation targetUpperFormation
      memberDerivation) :
    CutView scope (.pair (a := label) firstDerivation memberDerivation)
      (.stable (Pair.Interval.plan sourceFirst sourceLower sourceUpper))
      (.stable (Pair.Interval.plan targetFirst targetLower targetUpper)) :=
  let environments : EndpointEnvs sourceContext targetContext base := {
    source := scope.source.erase
    target := scope.target.erase
  }
  let firstCompilation : PairSubtyping.FirstCompilation base firstDerivation
      sourceFirst targetFirst := { relation := first.relation }
  let memberAdapter := intervalMemberAdapter first sourceLowerFormation
    sourceUpperFormation targetLowerFormation targetUpperFormation member
  let relation := PairSubtyping.interval environments firstCompilation
    sourceLowerFormation.rep sourceUpperFormation.rep
    targetLowerFormation.rep targetUpperFormation.rep memberAdapter
  CutView.ofRelation
    (.intervalPair first.sourceFormation sourceLowerFormation
      sourceUpperFormation)
    (.intervalPair first.targetFormation targetLowerFormation
      targetUpperFormation)
    relation

end LambdaPToFCo.Direct.Internal.SubtypingPair
