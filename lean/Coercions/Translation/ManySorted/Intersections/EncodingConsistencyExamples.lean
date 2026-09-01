import Coercions.DOT.Captures.Intersections.SourceExamples
import Coercions.ManySortedFC.ModelConsistency
import Coercions.Translation.ManySorted.Intersections.EncodingExamples

/-!
# Consistency regression for a repeated exact member

The two source declarations below are individually exact intervals.  Label
normalization gives them one target name and retains all four inclusions.  A
closed model would therefore prove `Top ≤ Bottom` through that shared name.
-/

namespace DOTCaptureToManySortedFC.Intersections.EncodingConsistencyExamples

open ManySortedFC
open DOTCaptureToManySortedFC.Intersections.Encoding

def labelA : DOTCapture.Intersections.Source.Label := 21

def exactTopBottomSource : Preparation.Source.Interface 0 :=
  .inter
    (.typeMember labelA .top .top)
    (.typeMember labelA .bot .bot)

def exactTopBottomNormalized :
    DOTCapture.Intersections.Signature
      (DOTCapture.Intersections.Source.Interface.Expr 0) :=
  { entries :=
      [DOTCapture.Intersections.Entry.type labelA
        [⟨DOTCapture.Intersections.Source.StaticExpr.type .top,
            DOTCapture.Intersections.Source.StaticExpr.type .top⟩,
          ⟨DOTCapture.Intersections.Source.StaticExpr.type .bot,
            DOTCapture.Intersections.Source.StaticExpr.type .bot⟩]] }

theorem exact_top_bottom_normalizes_to_one_label :
    exactTopBottomSource.collect = .ok exactTopBottomNormalized := by
  rfl

def exactTopBottomPrepared : PreparedSignature [] where
  symbols := [.type]
  entries :=
    [.type labelA .here
      [⟨.type .top, .type .top⟩, ⟨.type .bot, .type .bot⟩]]

theorem exact_top_bottom_prepares_under_one_name :
    Preparation.collectAndPrepare (Preparation.emptyLayout [])
      exactTopBottomSource = .ok exactTopBottomPrepared := by
  rfl

def exactTopBottomEncoding : Encoding [] :=
  encode exactTopBottomPrepared

theorem exact_top_bottom_encoding_retains_one_name_and_four_constraints :
    exactTopBottomPrepared.members = [MemberName.type labelA .here] ∧
      exactTopBottomEncoding.openedOccurrences.length = 2 ∧
      exactTopBottomEncoding.relations.length = 4 := by
  native_decide

theorem exact_top_bottom_occurrences_use_the_shared_name :
    match exactTopBottomEncoding.openedOccurrences with
    | [topOccurrence, bottomOccurrence] =>
        topOccurrence.member = bottomOccurrence.member
    | _ => False := by
  rfl

/-- The generated target theory has no recursion-free closed model,
irrespective of the chosen witness or recursion-free evidence terms. -/
theorem no_closed_model_of_exact_top_bottom_intersection
    (model : Theory.Model Ctx.nil exactTopBottomEncoding.theory)
    (modelRecursionFree : model.RecursionFree) : False := by
  rcases model with ⟨symbols, evidence, satisfaction⟩
  cases symbols with
  | cons witness remainingSymbols =>
      cases remainingSymbols
      cases witness with
      | type witnessType =>
          cases evidence with
          | cons topLower remainingEvidence =>
              cases remainingEvidence with
              | cons _topUpper remainingEvidence =>
                  cases remainingEvidence with
                  | cons _bottomLower remainingEvidence =>
                      cases remainingEvidence with
                      | cons bottomUpper noEvidence =>
                          cases noEvidence
                          have topLowerTyping := satisfaction.head
                          have bottomUpperTyping :=
                            satisfaction.tail.tail.tail.head
                          change
                            (topLower.recursionFree &&
                              (_topUpper.recursionFree &&
                                (_bottomLower.recursionFree &&
                                  (bottomUpper.recursionFree && true)))) = true
                            at modelRecursionFree
                          simp only [Bool.and_eq_true] at modelRecursionFree
                          have collapse : Evidence.Proves Ctx.nil
                              (.inclusionTrans topLower bottomUpper)
                              (.inclusion (.type (.top : Ty []))
                                (.type (.bot : Ty []))) := by
                            apply Evidence.Proves.inclusionTrans
                            · simpa [exactTopBottomEncoding,
                                exactTopBottomPrepared, encode,
                                Encoding.theory, entriesTheory, entryTheory,
                                typeIntervalsTheory, appendTheory,
                                Proposition.instantiateSymbols,
                                StaticSubst.ofSymbolArgs,
                                StaticSubst.fromSymbolArgs,
                                StaticSubst.instantiateSymbol,
                                StaticExpr.substitute, Ty.substitute] using
                                topLowerTyping
                            · simpa [exactTopBottomEncoding,
                                exactTopBottomPrepared, encode,
                                Encoding.theory, entriesTheory, entryTheory,
                                typeIntervalsTheory, appendTheory,
                                Proposition.instantiateSymbols,
                                StaticSubst.ofSymbolArgs,
                                StaticSubst.fromSymbolArgs,
                                StaticSubst.instantiateSymbol,
                                StaticExpr.substitute, Ty.substitute] using
                                bottomUpperTyping
                          exact no_closed_top_included_in_bottom collapse (by
                            simp only [Evidence.recursionFree,
                              Bool.and_eq_true]
                            exact ⟨modelRecursionFree.1,
                              modelRecursionFree.2.2.2.1⟩)

end DOTCaptureToManySortedFC.Intersections.EncodingConsistencyExamples
