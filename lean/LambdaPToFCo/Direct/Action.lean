import LambdaPToFCo.Direct.SourceRenaming
import LambdaPToFCo.Direct.PairSubtyping

/-!
# Structural direct-subtyping actions

`Action` is proof-only. Its erasure is the exact proper or interval relation
emitted by a frozen direct compiler kernel. Pair nodes retain the recursive
payload returned by the enriched delayed-member callback; they never accept
an independently supplied whole-pair conversion or interface map.

This module intentionally contains no value action, path replay, or generic
adaptation API. Those consumers must preserve the concrete pair callback
opening exposed by the child-extraction operations below.
-/

namespace LambdaPToFCo.Direct.Internal

open SystemFCo
open Representation

/-- Exact relation callback accepted by the frozen proper-pair kernel. -/
abbrev Action.ProperMemberRelations
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (scope : ContextRelation.Scope sourceContext targetContext .source base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember) : Type :=
  {final : Sig} -> {finalContext : Ctx final} ->
  (mapping : Rename
    (PairSubtyping.ProperMemberCompiler.CallbackSig sourceFirst sourceMember)
    final) ->
  (typed : Rename.Typed
    (PairSubtyping.ProperMemberCompiler.CallbackContext base sourceFirst
      sourceMember) finalContext mapping) ->
  (sourceInterface : Shape.Interface finalContext
    (PairSubtyping.ProperMemberCompiler.SourceFirstAt sourceFirst sourceMember
      mapping)) ->
  (targetInterface : Shape.Interface finalContext
    (PairSubtyping.ProperMemberCompiler.TargetFirstAt sourceFirst sourceMember
      targetFirst mapping)) ->
  let members := PairSubtyping.properMemberScopeAt scope.endpointEnvs
    firstRelation sourceMemberRep targetMemberRep mapping typed
    sourceInterface targetInterface
  Relation finalContext sourceMemberType targetMemberType
    members.source.memberShape members.target.memberShape

/-- Exact interval relation callback accepted by the frozen interval-pair
kernel. -/
abbrev Action.IntervalMemberRelations
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (scope : ContextRelation.Scope sourceContext targetContext .source base)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower)
    (sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper)
    (targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower)
    (targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper) : Type :=
  {final : Sig} -> {finalContext : Ctx final} ->
  (mapping : Rename
    (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst sourceLower
      sourceUpper) final) ->
  (typed : Rename.Typed
    (PairSubtyping.IntervalMemberCompiler.CallbackContext base sourceFirst
      sourceLower sourceUpper) finalContext mapping) ->
  (sourceInterface : Shape.Interface finalContext
    (PairSubtyping.IntervalMemberCompiler.SourceFirstAt sourceFirst
      sourceLower sourceUpper mapping)) ->
  (targetInterface : Shape.Interface finalContext
    (PairSubtyping.IntervalMemberCompiler.TargetFirstAt sourceFirst
      sourceLower sourceUpper targetFirst mapping)) ->
  let members := PairSubtyping.intervalMemberScopeAt scope.endpointEnvs
    firstRelation sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
    mapping typed sourceInterface targetInterface
  AtomicSubtyping.IntervalRelation members.source members.target

/-- Kind-complete frozen target erasure.  The proper branch contains the
literal `Relation`; the interval branch contains the two exact endpoint
relations used by `AtomicSubtyping.IntervalResult` and interval pairs. -/
inductive Action.Erasure (base : Ctx sig) :
    {kind : LambdaPFC.Kind} ->
    LambdaPFC.Tau n kind -> LambdaPFC.Tau n kind -> Type where
| proper
    {sourceType targetType : LambdaPFC.Ty n}
    {source target : Shape sig}
    (relation : Relation base sourceType targetType source target) :
    Action.Erasure base (.ty sourceType) (.ty targetType)
| interval
    {sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n}
    {source : Wf.Interval base sourceLower sourceUpper}
    {target : Wf.Interval base targetLower targetUpper}
    (relation : AtomicSubtyping.IntervalRelation source target) :
    Action.Erasure base (.intv sourceLower sourceUpper)
      (.intv targetLower targetUpper)

namespace Action.Erasure

/-- Exact target renaming of a frozen erasure. -/
noncomputable def targetRename
    {sourceSig targetSig : Sig}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    {kind : LambdaPFC.Kind}
    {sourceType targetType : LambdaPFC.Tau n kind}
    (frozen : Action.Erasure sourceBase sourceType targetType)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceBase targetBase mapping) :
    Action.Erasure targetBase sourceType targetType := by
  cases frozen with
  | proper relation =>
      exact .proper (relation.targetRename mapping typed)
  | interval relation =>
      exact .interval (relation.targetRename mapping typed)

end Action.Erasure

/-- A literal source-subtyping derivation together with its exact compiled
target erasure and all structural recursive children.

The only higher-order recursive occurrences are delayed pair children. They
occur positively as callback results. -/
inductive Action :
    {n : Nat} ->
    {sourceContext targetContext : LambdaPFC.Ctx n} ->
    {side : ProofSide} -> {sig : Sig} -> {base : Ctx sig} ->
    (scope : ContextRelation.Scope sourceContext targetContext side base) ->
    {kind : LambdaPFC.Kind} ->
    {sourceType targetType : LambdaPFC.Tau n kind} ->
    (subtyping : LambdaPFC.Tau.Sub
      (side.choose sourceContext targetContext) sourceType targetType) ->
    Action.Erasure base sourceType targetType -> Type where
  | reflProper
      {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
      {side : ProofSide} {sig : Sig} {base : Ctx sig}
      (scope : ContextRelation.Scope sourceContext targetContext side base)
      {sourceType : LambdaPFC.Ty n} {shape : Shape sig}
      (rep : Rep base sourceType shape) :
      Action scope
        (LambdaPFC.Tau.Sub.refl (Γ := side.choose sourceContext targetContext)
          (τ := .ty sourceType))
        (.proper (Relation.refl rep))
  | reflInterval
      {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
      {side : ProofSide} {sig : Sig} {base : Ctx sig}
      (scope : ContextRelation.Scope sourceContext targetContext side base)
      {lower upper : LambdaPFC.Ty n}
      (interval : Wf.Interval base lower upper) :
      Action scope
        (LambdaPFC.Tau.Sub.refl (Γ := side.choose sourceContext targetContext)
          (τ := .intv lower upper))
        (.interval (AtomicSubtyping.IntervalRelation.refl interval))
  | transProper
      {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
      {side : ProofSide} {sig : Sig} {base : Ctx sig}
      {scope : ContextRelation.Scope sourceContext targetContext side base}
      {sourceType middleType targetType : LambdaPFC.Ty n}
      {source middle target : Shape sig}
      {firstSubtyping : LambdaPFC.Tau.Sub
        (side.choose sourceContext targetContext)
        (.ty sourceType) (.ty middleType)}
      {secondSubtyping : LambdaPFC.Tau.Sub
        (side.choose sourceContext targetContext)
        (.ty middleType) (.ty targetType)}
      {firstRelation : Relation base sourceType middleType source middle}
      {secondRelation : Relation base middleType targetType middle target}
      (first : Action scope firstSubtyping (.proper firstRelation))
      (second : Action scope secondSubtyping (.proper secondRelation)) :
      Action scope (.trans firstSubtyping secondSubtyping)
        (.proper (firstRelation.trans secondRelation))
  | transInterval
      {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
      {side : ProofSide} {sig : Sig} {base : Ctx sig}
      {scope : ContextRelation.Scope sourceContext targetContext side base}
      {sourceLower sourceUpper middleLower middleUpper targetLower targetUpper :
        LambdaPFC.Ty n}
      {source : Wf.Interval base sourceLower sourceUpper}
      {middle : Wf.Interval base middleLower middleUpper}
      {target : Wf.Interval base targetLower targetUpper}
      {firstSubtyping : LambdaPFC.Tau.Sub
        (side.choose sourceContext targetContext)
        (.intv sourceLower sourceUpper) (.intv middleLower middleUpper)}
      {secondSubtyping : LambdaPFC.Tau.Sub
        (side.choose sourceContext targetContext)
        (.intv middleLower middleUpper) (.intv targetLower targetUpper)}
      {firstRelation : AtomicSubtyping.IntervalRelation source middle}
      {secondRelation : AtomicSubtyping.IntervalRelation middle target}
      (first : Action scope firstSubtyping (.interval firstRelation))
      (second : Action scope secondSubtyping (.interval secondRelation)) :
      Action scope (.trans firstSubtyping secondSubtyping)
        (.interval (firstRelation.trans secondRelation))
  | targetRename
      {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
      {side : ProofSide} {sourceSig targetSig : Sig}
      {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
      {scope : ContextRelation.Scope sourceContext targetContext side sourceBase}
      {kind : LambdaPFC.Kind}
      {sourceType targetType : LambdaPFC.Tau n kind}
      {subtyping : LambdaPFC.Tau.Sub
        (side.choose sourceContext targetContext) sourceType targetType}
      {frozen : Action.Erasure sourceBase sourceType targetType}
      (action : Action scope subtyping frozen)
      (mapping : Rename sourceSig targetSig)
      (typed : Rename.Typed sourceBase targetBase mapping) :
      Action (scope.targetRename mapping typed) subtyping
        (frozen.targetRename mapping typed)
  | bot
      {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
      {side : ProofSide} {sig : Sig} {base : Ctx sig}
      (scope : ContextRelation.Scope sourceContext targetContext side base)
      {targetType : LambdaPFC.Ty n}
      (target : Wf.Proper base targetType) :
      Action scope
        (LambdaPFC.Tau.Sub.bot
          (Γ := side.choose sourceContext targetContext) (T := targetType))
        (.proper (AtomicSubtyping.bot target).relation)
  | top
      {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
      {side : ProofSide} {sig : Sig} {base : Ctx sig}
      (scope : ContextRelation.Scope sourceContext targetContext side base)
      {sourceType : LambdaPFC.Ty n}
      (source : Wf.Proper base sourceType) :
      Action scope
        (LambdaPFC.Tau.Sub.top
          (Γ := side.choose sourceContext targetContext) (T := sourceType))
        (.proper (AtomicSubtyping.top source).relation)
  | widenAt
      {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
      {side : ProofSide} {sig : Sig} {base : Ctx sig}
      (scope : ContextRelation.Scope sourceContext targetContext side base)
      {path : LambdaPFC.Path n} {targetType : LambdaPFC.Ty n}
      (typing : LambdaPFC.Path.Ty
        (side.choose sourceContext targetContext) path (.ty targetType))
      (slot : Slot base targetType) :
      Action scope (.widen typing)
        (.proper (AtomicSubtyping.widenAt path slot).relation)
  | selHiAt
      {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
      {side : ProofSide} {sig : Sig} {base : Ctx sig}
      (scope : ContextRelation.Scope sourceContext targetContext side base)
      {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
      {lowerSource upperSource : LambdaPFC.Ty n}
      (typing : LambdaPFC.Path.Ty
        (side.choose sourceContext targetContext) (.sel path label)
        (.intv lowerSource upperSource))
      (nonempty : LambdaPFC.Tau.Sub
        (side.choose sourceContext targetContext)
        (.ty lowerSource) (.ty upperSource))
      {lower upper : Shape sig} {selectedType : Ty sig}
      (interval : IntervalRep (targetContext := base)
        lowerSource upperSource lower selectedType upper) :
      Action scope (.sel_hi typing nonempty)
        (.proper (AtomicSubtyping.selHiAt interval).relation)
  | selLoAt
      {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
      {side : ProofSide} {sig : Sig} {base : Ctx sig}
      (scope : ContextRelation.Scope sourceContext targetContext side base)
      {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
      {lowerSource upperSource : LambdaPFC.Ty n}
      (typing : LambdaPFC.Path.Ty
        (side.choose sourceContext targetContext) (.sel path label)
        (.intv lowerSource upperSource))
      (nonempty : LambdaPFC.Tau.Sub
        (side.choose sourceContext targetContext)
        (.ty lowerSource) (.ty upperSource))
      {lower upper : Shape sig} {selectedType : Ty sig}
      (interval : IntervalRep (targetContext := base)
        lowerSource upperSource lower selectedType upper) :
      Action scope (.sel_lo typing nonempty)
        (.proper (AtomicSubtyping.selLoAt interval).relation)
  | bounds
      {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
      {side : ProofSide} {sig : Sig} {base : Ctx sig}
      {scope : ContextRelation.Scope sourceContext targetContext side base}
      {sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n}
      {sourceLowerShape sourceUpperShape targetLowerShape targetUpperShape :
        Shape sig}
      {lowerSubtyping : LambdaPFC.Tau.Sub
        (side.choose sourceContext targetContext)
        (.ty targetLower) (.ty sourceLower)}
      {upperSubtyping : LambdaPFC.Tau.Sub
        (side.choose sourceContext targetContext)
        (.ty sourceUpper) (.ty targetUpper)}
      {nonemptySubtyping : LambdaPFC.Tau.Sub
        (side.choose sourceContext targetContext)
        (.ty sourceLower) (.ty sourceUpper)}
      {lowerRelation : Relation base targetLower sourceLower
        targetLowerShape sourceLowerShape}
      {upperRelation : Relation base sourceUpper targetUpper
        sourceUpperShape targetUpperShape}
      (lower : Action scope lowerSubtyping (.proper lowerRelation))
      (upper : Action scope upperSubtyping (.proper upperRelation)) :
      Action scope (.bounds lowerSubtyping upperSubtyping nonemptySubtyping)
        (.interval (AtomicSubtyping.IntervalResult.bounds
          lowerRelation upperRelation).relation)
  | properPair
      {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
      {sig : Sig} {base : Ctx sig}
      (scope : ContextRelation.Scope sourceContext targetContext .source base)
      {sourceFirstType targetFirstType : LambdaPFC.Ty n}
      {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
      {label : LambdaPFC.Name}
      {sourceFirst targetFirst : Shape sig}
      {sourceMember : Shape sourceFirst.scope}
      {targetMember : Shape targetFirst.scope}
      {firstSubtyping : LambdaPFC.Tau.Sub sourceContext
        (.ty sourceFirstType) (.ty targetFirstType)}
      {memberSubtyping : LambdaPFC.Tau.Sub
        (sourceContext.snoc sourceFirstType)
        (.ty sourceMemberType) (.ty targetMemberType)}
      {firstRelation : Relation base sourceFirstType targetFirstType
        sourceFirst targetFirst}
      (first : Action scope firstSubtyping (.proper firstRelation))
      (sourceMemberRep : Rep (sourceFirst.context base)
        sourceMemberType sourceMember)
      (targetMemberRep : Rep (targetFirst.context base)
        targetMemberType targetMember)
      (memberRelation : Action.ProperMemberRelations scope firstRelation
        sourceMemberRep targetMemberRep)
      (memberAction : {final : Sig} -> {finalContext : Ctx final} ->
        (mapping : Rename
          (PairSubtyping.ProperMemberCompiler.CallbackSig sourceFirst
            sourceMember) final) ->
        (typed : Rename.Typed
          (PairSubtyping.ProperMemberCompiler.CallbackContext base
            sourceFirst sourceMember) finalContext mapping) ->
        (sourceInterface : Shape.Interface finalContext
          (PairSubtyping.ProperMemberCompiler.SourceFirstAt sourceFirst
            sourceMember mapping)) ->
        (targetInterface : Shape.Interface finalContext
          (PairSubtyping.ProperMemberCompiler.TargetFirstAt sourceFirst
            sourceMember targetFirst mapping)) ->
        Action
          (PairSubtyping.properActionScopeAt scope firstRelation mapping
            typed sourceInterface targetInterface)
          memberSubtyping
          (.proper (memberRelation mapping typed sourceInterface
            targetInterface))) :
      Action scope
        (LambdaPFC.Tau.Sub.pair (a := label) firstSubtyping memberSubtyping)
        (.proper (let enriched := ({
            Retained := fun _mapping _typed _sourceInterface _targetInterface
              _relation => PUnit
            compile := fun mapping typed sourceInterface targetInterface =>
              ⟨memberRelation mapping typed sourceInterface targetInterface,
                PUnit.unit⟩
          } : PairSubtyping.ProperMemberCompiler.Enriched scope firstRelation
              sourceMemberRep targetMemberRep memberSubtyping)
          PairSubtyping.proper (label := label) scope.endpointEnvs
            ({ relation := firstRelation } : PairSubtyping.FirstCompilation
              base firstSubtyping sourceFirst targetFirst)
            sourceMemberRep targetMemberRep enriched.erase))
  | intervalPair
      {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
      {sig : Sig} {base : Ctx sig}
      (scope : ContextRelation.Scope sourceContext targetContext .source base)
      {sourceFirstType targetFirstType : LambdaPFC.Ty n}
      {sourceLowerType sourceUpperType targetLowerType targetUpperType :
        LambdaPFC.Ty (n + 1)}
      {label : LambdaPFC.Name}
      {sourceFirst targetFirst : Shape sig}
      {sourceLower sourceUpper : Shape sourceFirst.scope}
      {targetLower targetUpper : Shape targetFirst.scope}
      {firstSubtyping : LambdaPFC.Tau.Sub sourceContext
        (.ty sourceFirstType) (.ty targetFirstType)}
      {memberSubtyping : LambdaPFC.Tau.Sub
        (sourceContext.snoc sourceFirstType)
        (.intv sourceLowerType sourceUpperType)
        (.intv targetLowerType targetUpperType)}
      {firstRelation : Relation base sourceFirstType targetFirstType
        sourceFirst targetFirst}
      (first : Action scope firstSubtyping (.proper firstRelation))
      (sourceLowerRep : Rep (sourceFirst.context base)
        sourceLowerType sourceLower)
      (sourceUpperRep : Rep (sourceFirst.context base)
        sourceUpperType sourceUpper)
      (targetLowerRep : Rep (targetFirst.context base)
        targetLowerType targetLower)
      (targetUpperRep : Rep (targetFirst.context base)
        targetUpperType targetUpper)
      (memberRelation : Action.IntervalMemberRelations scope firstRelation
        sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep)
      (memberAction : {final : Sig} -> {finalContext : Ctx final} ->
        (mapping : Rename
          (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst
            sourceLower sourceUpper) final) ->
        (typed : Rename.Typed
          (PairSubtyping.IntervalMemberCompiler.CallbackContext base
            sourceFirst sourceLower sourceUpper) finalContext mapping) ->
        (sourceInterface : Shape.Interface finalContext
          (PairSubtyping.IntervalMemberCompiler.SourceFirstAt sourceFirst
            sourceLower sourceUpper mapping)) ->
        (targetInterface : Shape.Interface finalContext
          (PairSubtyping.IntervalMemberCompiler.TargetFirstAt sourceFirst
            sourceLower sourceUpper targetFirst mapping)) ->
        Action
          (PairSubtyping.intervalActionScopeAt scope firstRelation mapping
            typed sourceInterface targetInterface)
          memberSubtyping
          (.interval (memberRelation mapping typed sourceInterface
            targetInterface))) :
      Action scope
        (LambdaPFC.Tau.Sub.pair (a := label) firstSubtyping memberSubtyping)
        (.proper (let enriched := ({
            Retained := fun _mapping _typed _sourceInterface _targetInterface
              _relation => PUnit
            compile := fun mapping typed sourceInterface targetInterface =>
              ⟨memberRelation mapping typed sourceInterface targetInterface,
                PUnit.unit⟩
          } : PairSubtyping.IntervalMemberCompiler.Enriched scope
              firstRelation sourceLowerRep sourceUpperRep targetLowerRep
              targetUpperRep memberSubtyping)
          PairSubtyping.interval (label := label) scope.endpointEnvs
            ({ relation := firstRelation } : PairSubtyping.FirstCompilation
              base firstSubtyping sourceFirst targetFirst)
            sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
            enriched.erase))
  /-- Retain an older source-oriented action through the exact lexical
  extension used by a dependent pair callback. -/
  | extendPairOlder
      {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
      {sig : Sig} {base : Ctx sig}
      (scope : ContextRelation.Scope sourceContext targetContext .source base)
      {sourceType targetType : LambdaPFC.Ty n}
      {sourceShape targetShape : Shape sig}
      (sourceInterface : Shape.Interface base sourceShape)
      (sourceRep : Rep base sourceType sourceShape)
      (targetInterface : Shape.Interface base targetShape)
      (targetRep : Rep base targetType targetShape)
      (head : Relation base sourceType targetType sourceShape targetShape)
      (older : Fin n)
      {subtyping : LambdaPFC.Tau.Sub sourceContext
        (.ty (sourceContext.lookup older))
        (.ty (targetContext.lookup older))}
      (action : Action scope subtyping (.proper (scope.aligned older))) :
      Action
        (scope.extendPair sourceInterface sourceRep targetInterface targetRep
          head)
        (subtyping.weaken (bound := sourceType))
        (.proper ((scope.extendPair sourceInterface sourceRep targetInterface
          targetRep head).aligned older.succ))
  /-- Target-oriented dual for the exact lexical extension used by a
  dependent function callback. -/
  | extendFunctionOlder
      {n : Nat} {sourceContext targetContext : LambdaPFC.Ctx n}
      {sig : Sig} {base : Ctx sig}
      (scope : ContextRelation.Scope sourceContext targetContext .target base)
      {sourceType targetType : LambdaPFC.Ty n}
      {sourceShape targetShape : Shape sig}
      (sourceInterface : Shape.Interface base sourceShape)
      (sourceRep : Rep base sourceType sourceShape)
      (targetInterface : Shape.Interface base targetShape)
      (targetRep : Rep base targetType targetShape)
      (head : Relation base targetType sourceType targetShape sourceShape)
      (older : Fin n)
      {subtyping : LambdaPFC.Tau.Sub targetContext
        (.ty (targetContext.lookup older))
        (.ty (sourceContext.lookup older))}
      (action : Action scope subtyping (.proper (scope.aligned older))) :
      Action
        (scope.extendFunction sourceInterface sourceRep targetInterface
          targetRep head)
        (subtyping.weaken (bound := targetType))
        (.proper ((scope.extendFunction sourceInterface sourceRep
          targetInterface targetRep head).aligned older.succ))

namespace Action

/-- Structural size used as the secondary component of future action
eliminators' well-founded measures. Delayed pair-member closures are omitted,
as in semantic coercion size: entering one also descends through the concrete
pair value, which supplies the primary measure decrease. Lexical wrappers add
one node and delegate to their retained older action. -/
noncomputable def treeSize
    (action : Action scope subtyping erasure) : Nat := by
  induction action with
  | reflProper => exact 1
  | reflInterval => exact 1
  | transProper _ _ firstSize secondSize =>
      exact firstSize + secondSize + 1
  | transInterval _ _ firstSize secondSize =>
      exact firstSize + secondSize + 1
  | targetRename _ _ _ size => exact size + 1
  | bot => exact 1
  | top => exact 1
  | widenAt => exact 1
  | selHiAt => exact 1
  | selLoAt => exact 1
  | bounds _ _ lowerSize upperSize => exact lowerSize + upperSize + 1
  | properPair _ _ _ _ _ _ firstSize _ => exact firstSize + 1
  | intervalPair _ _ _ _ _ _ _ _ firstSize _ => exact firstSize + 1
  | extendPairOlder _ _ _ _ _ _ _ _ size => exact size + 1
  | extendFunctionOlder _ _ _ _ _ _ _ _ size => exact size + 1

/-- Rebuild the proof-enriched proper callback from the two fields retained
by `Action.properPair`.  Its erasure is definitionally the same relation
callback used in the whole-pair `Relation`. -/
noncomputable def properEnriched
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
          targetInterface))) :
    PairSubtyping.ProperMemberCompiler.Enriched scope firstRelation
      sourceMemberRep targetMemberRep memberSubtyping where
  Retained := fun mapping typed sourceInterface targetInterface relation =>
    Action
      (PairSubtyping.properActionScopeAt scope firstRelation mapping typed
        sourceInterface targetInterface)
      memberSubtyping (.proper relation)
  compile mapping typed sourceInterface targetInterface :=
    ⟨memberRelation mapping typed sourceInterface targetInterface,
      memberAction mapping typed sourceInterface targetInterface⟩

/-- Werror gate for proper-pair `.fst`: the retained first child is already
the exact Action whose Relation generated the whole pair's first map. -/
def properFst
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
  first

/-- Rebuild the proof-enriched interval callback from an interval-pair node.
`mapAt` below consumes this callback once, so relation, Action payload, and
mapped selected witness come from the same invocation. -/
noncomputable def intervalEnriched
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
          targetInterface))) :
    PairSubtyping.IntervalMemberCompiler.Enriched scope firstRelation
      sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
      memberSubtyping where
  Retained := fun mapping typed sourceInterface targetInterface relation =>
    Action
      (PairSubtyping.intervalActionScopeAt scope firstRelation mapping typed
        sourceInterface targetInterface)
      memberSubtyping (.interval relation)
  compile mapping typed sourceInterface targetInterface :=
    ⟨memberRelation mapping typed sourceInterface targetInterface,
      memberAction mapping typed sourceInterface targetInterface⟩

/-- Same-run interval `.sel_r` extraction.

The caller supplies the source witness at the exact callback opening used by
the pair package. The result contains the exact recursive interval Action,
the target witness obtained by that Action's frozen interval relation, and a
Bridge between their selected identities. No second member callback or path
resolver run occurs. -/
noncomputable def intervalSelected
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
    {final : Sig} {finalContext : Ctx final}
    (mapping : Rename
      (PairSubtyping.IntervalMemberCompiler.CallbackSig sourceFirst
        sourceLower sourceUpper) final)
    (typed : Rename.Typed
      (PairSubtyping.IntervalMemberCompiler.CallbackContext base sourceFirst
        sourceLower sourceUpper) finalContext mapping)
    (sourceInterface : Shape.Interface finalContext
      (PairSubtyping.IntervalMemberCompiler.SourceFirstAt sourceFirst
        sourceLower sourceUpper mapping))
    (targetInterface : Shape.Interface finalContext
      (PairSubtyping.IntervalMemberCompiler.TargetFirstAt sourceFirst
        sourceLower sourceUpper targetFirst mapping))
    (sourceWitness :
      let members := PairSubtyping.intervalMemberScopeAt scope.endpointEnvs
        firstRelation sourceLowerRep sourceUpperRep targetLowerRep
        targetUpperRep mapping typed sourceInterface targetInterface
      Conversion.Interval.Witness finalContext members.source.lower
        members.source.upper) :
    let members := PairSubtyping.intervalMemberScopeAt scope.endpointEnvs
      firstRelation sourceLowerRep sourceUpperRep targetLowerRep targetUpperRep
      mapping typed sourceInterface targetInterface
    Sigma fun relation : AtomicSubtyping.IntervalRelation members.source
        members.target =>
      Action
          (PairSubtyping.intervalActionScopeAt scope firstRelation mapping
            typed sourceInterface targetInterface)
          memberSubtyping (.interval relation) ×
        Sigma fun targetWitness : Conversion.Interval.Witness finalContext
            members.target.lower members.target.upper =>
          Conversion.Bridge finalContext sourceWitness.selected.inputTy
            targetWitness.selected.inputTy := by
  let enriched := intervalEnriched memberRelation memberAction
  let mapped := enriched.mapAt mapping typed sourceInterface targetInterface
    sourceWitness
  refine ⟨mapped.1, mapped.2.1, mapped.2.2, ?_⟩
  exact {
    leftToRight := Conversion.refl finalContext sourceWitness.selected.inputTy
    rightToLeft := Conversion.refl finalContext sourceWitness.selected.inputTy
  }

end Action

end LambdaPToFCo.Direct.Internal
