import LambdaPToFCo.Direct.PairSubtyping

/-!
# Enriched pair-member callback regressions

Both enriched callback kinds are instantiated with `Unit` as their retained
proof payload.  Erasing that payload recovers the original delayed compiler;
the target relation therefore remains definitionally the callback's first
projection.
-/

namespace LambdaPToFCo.Direct.PairSubtypingActionRegression

noncomputable section

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.PairSubtyping

noncomputable def retainProperUnit
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember}
    {targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (compiler : ProperMemberCompiler root.endpointEnvs first sourceMemberRep
      targetMemberRep derivation) :
    ProperMemberCompiler.Enriched root first sourceMemberRep targetMemberRep
      derivation where
  Retained := fun _mapping _typed _sourceInterface _targetInterface
    _relation => Unit
  compile := by
    intro final finalContext mapping typed sourceInterface targetInterface
    exact ⟨compiler.compile mapping typed sourceInterface targetInterface, ()⟩

/-- Proper payload erasure is extensionally the original callback. -/
theorem retainProperUnit_erase
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember}
    {targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.ty sourceMemberType) (.ty targetMemberType)}
    (compiler : ProperMemberCompiler root.endpointEnvs first sourceMemberRep
      targetMemberRep derivation) :
    (retainProperUnit compiler).erase = compiler := by
  cases compiler
  rfl

noncomputable def retainIntervalUnit
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : IntervalMemberCompiler root.endpointEnvs first sourceLowerRep
      sourceUpperRep targetLowerRep targetUpperRep derivation) :
    IntervalMemberCompiler.Enriched root first sourceLowerRep sourceUpperRep
      targetLowerRep targetUpperRep derivation where
  Retained := fun _mapping _typed _sourceInterface _targetInterface
    _relation => Unit
  compile := by
    intro final finalContext mapping typed sourceInterface targetInterface
    exact ⟨compiler.compile mapping typed sourceInterface targetInterface, ()⟩

/-- Interval payload erasure is extensionally the original callback. -/
theorem retainIntervalUnit_erase
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {root : ContextRelation.Scope sourceContext targetContext .source base}
    {first : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst}
    {sourceLowerRep : Rep (sourceFirst.context base)
      sourceLowerType sourceLower}
    {sourceUpperRep : Rep (sourceFirst.context base)
      sourceUpperType sourceUpper}
    {targetLowerRep : Rep (targetFirst.context base)
      targetLowerType targetLower}
    {targetUpperRep : Rep (targetFirst.context base)
      targetUpperType targetUpper}
    {derivation : LambdaPFC.Tau.Sub (sourceContext.snoc sourceFirstType)
      (.intv sourceLowerType sourceUpperType)
      (.intv targetLowerType targetUpperType)}
    (compiler : IntervalMemberCompiler root.endpointEnvs first sourceLowerRep
      sourceUpperRep targetLowerRep targetUpperRep derivation) :
    (retainIntervalUnit compiler).erase = compiler := by
  cases compiler
  rfl

end

end LambdaPToFCo.Direct.PairSubtypingActionRegression
