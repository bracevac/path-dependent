import Coercions.ManySortedFC.Consistency
import Coercions.ManySortedFC.StaticExamples

/-!
# Closed model consistency for characteristic bad intervals

The static examples show that one particular bogus model candidate is
rejected by the executable checker.  These corollaries quantify over every
possible witness and evidence supply: if either characteristic bad interval
had an ambient model, its two supplied certificates would compose to one of
the inclusions refuted by the Boolean consistency model.
-/

namespace ManySortedFC

namespace EvidenceArgs

/-- The evidence block covered by the finite Boolean model.  Recursive
unfold certificates remain independently checkable, but require a richer
semantic model than this file supplies. -/
def recursionFree {scope : Sig} : {relations : List Relation} ->
    EvidenceArgs scope relations -> Bool
  | [], .nil => true
  | _ :: _, .cons newest older =>
      newest.recursionFree && older.recursionFree

end EvidenceArgs

namespace Theory.Model

def RecursionFree {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    {theory : Theory scope symbols relations}
    (model : Theory.Model context theory) : Prop :=
  model.evidence.recursionFree = true

end Theory.Model

/-- No witness and ambient evidence supply can model `Top .. Bottom` in the
empty context when its certificates lie in the recursion-free fragment of
the Boolean model. -/
theorem no_closed_model_of_impossible_type_interval
    (model : Theory.Model Ctx.nil StaticExamples.impossibleTypeInterval)
    (modelRecursionFree : model.RecursionFree) : False := by
  rcases model with ⟨symbols, evidence, satisfaction⟩
  cases symbols with
  | cons witness remainingSymbols =>
      cases remainingSymbols
      cases witness with
      | type witnessType =>
          cases evidence with
          | cons lowerEvidence remainingEvidence =>
              cases remainingEvidence with
              | cons upperEvidence noEvidence =>
                  cases noEvidence
                  have lowerTyping := satisfaction.head
                  have upperTyping := satisfaction.tail.head
                  simp only [Theory.Model.RecursionFree,
                    EvidenceArgs.recursionFree, Bool.and_eq_true] at modelRecursionFree
                  have collapse : Evidence.Proves Ctx.nil
                      (.inclusionTrans lowerEvidence upperEvidence)
                      (.inclusion (.type (.top : Ty []))
                        (.type (.bot : Ty []))) := by
                    apply Evidence.Proves.inclusionTrans
                    · simpa [StaticExamples.impossibleTypeInterval,
                        Interval.between, Interval.name,
                        Proposition.instantiateSymbols,
                        StaticSubst.ofSymbolArgs,
                        StaticSubst.fromSymbolArgs,
                        StaticSubst.instantiateSymbol,
                        StaticExpr.substitute, Ty.substitute] using lowerTyping
                    · simpa [StaticExamples.impossibleTypeInterval,
                        Interval.between, Interval.name,
                        Proposition.instantiateSymbols,
                        StaticSubst.ofSymbolArgs,
                        StaticSubst.fromSymbolArgs,
                        StaticSubst.instantiateSymbol,
                        StaticExpr.substitute, Ty.substitute] using upperTyping
                  exact no_closed_top_included_in_bottom collapse (by
                    simp [Evidence.recursionFree, modelRecursionFree])

/-- In a context containing only the capability `x`, no witness and ambient
evidence supply can model `{x} .. {}`. -/
theorem no_model_of_impossible_capture_interval
    (model : Theory.Model StaticExamples.capabilityContext
      StaticExamples.impossibleCaptureInterval) : False := by
  rcases model with ⟨symbols, evidence, satisfaction⟩
  cases symbols with
  | cons witness remainingSymbols =>
      cases remainingSymbols
      cases witness with
      | capture witnessCapture =>
          cases evidence with
          | cons lowerEvidence remainingEvidence =>
              cases remainingEvidence with
              | cons upperEvidence noEvidence =>
                  cases noEvidence
                  have lowerTyping := satisfaction.head
                  have upperTyping := satisfaction.tail.head
                  have collapse : Evidence.Proves
                      StaticExamples.capabilityContext
                      (.inclusionTrans lowerEvidence upperEvidence)
                      (.inclusion
                        (.capture StaticExamples.ambientCapability)
                        (.capture (.empty : Capture
                          StaticExamples.CapabilityScope))) := by
                    apply Evidence.Proves.inclusionTrans
                    · simpa [StaticExamples.impossibleCaptureInterval,
                        Interval.between, Interval.name,
                        Proposition.instantiateSymbols,
                        StaticSubst.ofSymbolArgs,
                        StaticSubst.fromSymbolArgs,
                        StaticSubst.instantiateSymbol,
                        StaticExpr.substitute, Capture.substitute] using
                        lowerTyping
                    · simpa [StaticExamples.impossibleCaptureInterval,
                        Interval.between, Interval.name,
                        Proposition.instantiateSymbols,
                        StaticSubst.ofSymbolArgs,
                        StaticSubst.fromSymbolArgs,
                        StaticSubst.instantiateSymbol,
                        StaticExpr.substitute, Capture.substitute] using
                        upperTyping
                  exact no_singleton_included_in_empty collapse

end ManySortedFC
