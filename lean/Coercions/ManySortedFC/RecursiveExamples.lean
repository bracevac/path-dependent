import Coercions.ManySortedFC.EvidenceCheckerCompleteness
import Coercions.ManySortedFC.TheoryModelChecker

/-!
# Guarded recursive type-block regressions

These examples exercise the type-only recursive slice of ManySortedFC.  The
accepted block ties two type members through arrow heads.  The target checker
independently validates its canonical unfold equality and the two directed
inclusions derived from that equality.

The negative examples reject a naked alias cycle, an equality composition
whose endpoints do not meet, and a model candidate that would need to assume
the very recursive interval it is meant to realize.
-/

namespace ManySortedFC.RecursiveExamples

/-! ## A guarded two-member knot -/

def first : Fin 2 := ⟨0, by decide⟩
def second : Fin 2 := ⟨1, by decide⟩

/-- `A = Top -> B` and `B = Top -> A`, with both self references occurring
below an arrow head.  Recursive blocks and their finite indices use
newest-first order, so the final `snoc` supplies `A`. -/
def mutualBlock : RecBodies [] 2 2 :=
  .snoc
    (.snoc .nil (.arr .top (.tvar .here)))
    (.arr .top (.tvar (.there .here)))

theorem mutual_block_is_guarded : mutualBlock.headGuarded = true := by
  native_decide

theorem first_unfolds_to_second :
    mutualBlock.unfoldAt first =
      .arr .top (.recProj mutualBlock second) := by
  native_decide

theorem second_unfolds_to_first :
    mutualBlock.unfoldAt second =
      .arr .top (.recProj mutualBlock first) := by
  native_decide

/-! ## Canonical equality and its directed views -/

def firstUnfoldEquality : Evidence (.equality .type) [] :=
  .unfoldRec mutualBlock first

def firstUnfoldProposition : Proposition (.equality .type) [] :=
  .equality (.type (.recProj mutualBlock first))
    (.type (mutualBlock.unfoldAt first))

/-- The checker, rather than the example, establishes the guardedness premise
and synthesizes the exact recursive equality endpoints. -/
theorem canonical_unfold_equality_is_accepted :
    (Evidence.check Ctx.nil firstUnfoldEquality).map
        (fun checked => checked.proposition) =
      some firstUnfoldProposition := by
  native_decide

def firstUpperInclusion : Evidence (.inclusion .type) [] :=
  .equalityToInclusion firstUnfoldEquality

def firstLowerInclusion : Evidence (.inclusion .type) [] :=
  .equalityToInclusion (.equalitySymm firstUnfoldEquality)

def firstUpperProposition : Proposition (.inclusion .type) [] :=
  .inclusion (.type (.recProj mutualBlock first))
    (.type (mutualBlock.unfoldAt first))

def firstLowerProposition : Proposition (.inclusion .type) [] :=
  .inclusion (.type (mutualBlock.unfoldAt first))
    (.type (.recProj mutualBlock first))

theorem derived_upper_inclusion_is_accepted :
    (Evidence.check Ctx.nil firstUpperInclusion).map
        (fun checked => checked.proposition) =
      some firstUpperProposition := by
  native_decide

theorem derived_lower_inclusion_is_accepted :
    (Evidence.check Ctx.nil firstLowerInclusion).map
        (fun checked => checked.proposition) =
      some firstLowerProposition := by
  native_decide

/-! ## Guard and endpoint rejection -/

/-- The corresponding naked aliases `A = B` and `B = A`. -/
def directAliasBlock : RecBodies [] 2 2 :=
  .snoc
    (.snoc .nil (.tvar .here))
    (.tvar (.there .here))

theorem direct_alias_block_is_unguarded :
    directAliasBlock.headGuarded = false := by
  native_decide

/-- Even though the evidence constructor can be written, its artifact is
rejected because the checker recomputes guardedness from the block. -/
theorem direct_alias_unfold_is_rejected :
    Evidence.check Ctx.nil
      (.unfoldRec directAliasBlock first) = none := by
  native_decide

/-- The right endpoint of the first unfold equality is an arrow, not the
second recursive projection.  The structural transitivity check therefore
rejects this attempted composition. -/
def wrongEndpointComposition : Evidence (.equality .type) [] :=
  .equalityTrans
    (.unfoldRec mutualBlock first)
    (.unfoldRec mutualBlock second)

theorem wrong_endpoint_is_rejected :
    Evidence.check Ctx.nil wrongEndpointComposition = none := by
  native_decide

/-! ## Ambient model checking and no self-discharge -/

abbrev MemberSymbolScope : Sig := SymbolScope [] [.type]

def memberSymbol : Ty MemberSymbolScope :=
  .tvar .here

def firstUnfoldInMemberScope : Ty MemberSymbolScope :=
  (mutualBlock.unfoldAt first).rename (Rename.weakenSymbols [.type])

/-- One exact recursive interval, represented as its two directed
constraints around a single abstract type symbol. -/
def recursiveMemberTheory : Theory [] [.type]
    [.inclusion .type, .inclusion .type] :=
  .cons
    (.inclusion (.type firstUnfoldInMemberScope) (.type memberSymbol))
    (.cons
      (.inclusion (.type memberSymbol) (.type firstUnfoldInMemberScope))
      .nil)

def recursiveMemberWitness : SymbolArgs [] [.type] :=
  .cons (.type (.recProj mutualBlock first)) .nil

def recursiveMemberEvidence : EvidenceArgs []
    [.inclusion .type, .inclusion .type] :=
  .cons firstLowerInclusion (.cons firstUpperInclusion .nil)

/-- Both interval directions are supplied by ambient, independently checked
unfold evidence. -/
theorem recursive_member_model_is_accepted :
    (Theory.checkModel Ctx.nil recursiveMemberTheory
      recursiveMemberWitness recursiveMemberEvidence).isSome = true := by
  native_decide

/-- Reflexivity would suffice only if the recursive interval could be assumed
while constructing its own model.  `checkModel` checks this evidence in the
unchanged ambient context, sees the endpoint mismatch, and rejects it. -/
def selfDischargeShapedEvidence : EvidenceArgs []
    [.inclusion .type, .inclusion .type] :=
  .cons
    (.inclusionRefl (.type (.recProj mutualBlock first)))
    (.cons
      (.inclusionRefl (.type (.recProj mutualBlock first)))
      .nil)

theorem ambient_model_cannot_self_discharge :
    (Theory.checkModel Ctx.nil recursiveMemberTheory
      recursiveMemberWitness selfDischargeShapedEvidence).isNone = true := by
  native_decide

end ManySortedFC.RecursiveExamples
