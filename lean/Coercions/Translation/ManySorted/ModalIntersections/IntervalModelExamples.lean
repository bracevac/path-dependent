import Coercions.Translation.ManySorted.ModalIntersections.IntervalModel

/-!
# Executable interval-model regressions

Each positive example starts from the cumulative source
`Interval.SatisfiedBy` judgment, compiles its endpoint derivations through the
ambient evidence compiler, and crosses both standalone target checks.  The
negative examples distinguish a missing compiled source leaf from a supplied
target certificate for the wrong proposition.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.IntervalModelExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.IntervalModel

namespace Source

abbrev Interval := DOTCapture.ModalIntersections.Interval
abbrev StaticExpr := DOTCapture.ModalIntersections.StaticExpr

def witness : StaticExpr .type [] := .type .one

def unbounded : Interval .type [] := .bounds .none .none

def lower : Interval .type [] :=
  .bounds (.some (.type .bot)) .none

def upper : Interval .type [] :=
  .bounds .none (.some (.type .top))

def between : Interval .type [] :=
  .bounds (.some (.type .bot)) (.some (.type .top))

def unboundedSatisfaction : DOTCapture.ModalIntersections.Interval.SatisfiedBy
    DOTCapture.ModalIntersections.Ctx.nil witness unbounded :=
  .unbounded

def lowerProof : DOTCapture.ModalIntersections.Includes
    DOTCapture.ModalIntersections.Ctx.nil (.type .bot) witness :=
  .typeBottom

def lowerSatisfaction : DOTCapture.ModalIntersections.Interval.SatisfiedBy
    DOTCapture.ModalIntersections.Ctx.nil witness lower :=
  .lower lowerProof

def upperProof : DOTCapture.ModalIntersections.Includes
    DOTCapture.ModalIntersections.Ctx.nil witness (.type .top) :=
  .typeTop

def upperSatisfaction : DOTCapture.ModalIntersections.Interval.SatisfiedBy
    DOTCapture.ModalIntersections.Ctx.nil witness upper :=
  .upper upperProof

def betweenSatisfaction : DOTCapture.ModalIntersections.Interval.SatisfiedBy
    DOTCapture.ModalIntersections.Ctx.nil witness between :=
  .between lowerProof upperProof

end Source

def preparedWitness : PreparedStaticExpr Core.nil Source.witness where
  targetExpression := .type .one
  prepared := rfl

def preparedUnbounded : PreparedStatic Core.nil Source.unbounded where
  theory := ManySortedFC.Interval.unconstrained .type
  prepared := rfl

def preparedLower : PreparedStatic Core.nil Source.lower where
  theory := ManySortedFC.Interval.lowerBounded (.type .bot)
  prepared := rfl

def preparedUpper : PreparedStatic Core.nil Source.upper where
  theory := ManySortedFC.Interval.upperBounded (.type .top)
  prepared := rfl

def preparedBetween : PreparedStatic Core.nil Source.between where
  theory := ManySortedFC.Interval.between (.type .bot) (.type .top)
  prepared := rfl

/-! ## All four interval shapes -/

def unbounded? := compile? Context.nil preparedUnbounded preparedWitness
  Source.unboundedSatisfaction

def lower? := compile? Context.nil preparedLower preparedWitness
  Source.lowerSatisfaction

def upper? := compile? Context.nil preparedUpper preparedWitness
  Source.upperSatisfaction

def between? := compile? Context.nil preparedBetween preparedWitness
  Source.betweenSatisfaction

example : unbounded?.isSome = true := by native_decide
example : lower?.isSome = true := by native_decide
example : upper?.isSome = true := by native_decide
example : between?.isSome = true := by native_decide

def unboundedCompiled := unbounded?.get (by native_decide)
def lowerCompiled := lower?.get (by native_decide)
def upperCompiled := upper?.get (by native_decide)
def betweenCompiled := between?.get (by native_decide)

/-- The one source witness becomes exactly the one target symbol argument. -/
example : symbolArgs preparedWitness =
    (.cons (.type .one) .nil : ManySortedFC.SymbolArgs [] [.type]) := rfl

example : unboundedCompiled.compiledEvidence.evidence =
    (.nil : ManySortedFC.EvidenceArgs [] []) := rfl

example : lowerCompiled.compiledEvidence.evidence =
    (.cons (.typeBottom .one) .nil :
      ManySortedFC.EvidenceArgs [] [.inclusion .type]) := by
  native_decide

example : upperCompiled.compiledEvidence.evidence =
    (.cons (.typeTop .one) .nil :
      ManySortedFC.EvidenceArgs [] [.inclusion .type]) := by
  native_decide

example : betweenCompiled.compiledEvidence.evidence =
    (.cons (.typeBottom .one) (.cons (.typeTop .one) .nil) :
      ManySortedFC.EvidenceArgs []
        [.inclusion .type, .inclusion .type]) := by
  native_decide

/-- The retained result crosses `checkSatisfaction` and `checkModel` with the
same symbol and evidence arguments. -/
example : ManySortedFC.Theory.checkSatisfaction Core.nil.target
    (symbolArgs preparedWitness) preparedBetween.theory
      betweenCompiled.compiledEvidence.evidence =
        some betweenCompiled.model.satisfaction :=
  betweenCompiled.model.satisfactionAcceptance

example : ManySortedFC.Theory.checkModel Core.nil.target
    preparedBetween.theory (symbolArgs preparedWitness)
      betweenCompiled.compiledEvidence.evidence =
        some betweenCompiled.model.checked :=
  betweenCompiled.model.checkerAcceptance

example : betweenCompiled.model.checked.symbols =
    symbolArgs preparedWitness := betweenCompiled.model.symbolsExact

example : betweenCompiled.model.checked.evidence =
    betweenCompiled.compiledEvidence.evidence :=
  betweenCompiled.model.evidenceExact

/-! ## Rejection boundaries -/

/-- This certificate is well typed evidence, but it proves `One <= Top`
rather than the lower interval's required `Bottom <= One`. -/
def wrongLowerEvidence : ManySortedFC.EvidenceArgs [] [.inclusion .type] :=
  .cons (.typeTop .one) .nil

example : (check? preparedLower preparedWitness wrongLowerEvidence).isNone =
    true := by
  native_decide

namespace MissingSourceEvidence

def lexicalInterval : Source.Interval .capture [] :=
  .bounds (.some (.capture .empty)) (.some (.capture .empty))

def preparedLexical : PreparedStatic Core.nil lexicalInterval where
  theory := ManySortedFC.Interval.between
    (.capture .empty) (.capture .empty)
  prepared := rfl

def context := Context.nil.extendStatic lexicalInterval preparedLexical

def reference : DOTCapture.ModalIntersections.StaticExpr .capture
    ([.static .capture] : DOTCapture.ModalIntersections.Sig) :=
  .capture (.ref (.bound .here))

def lowerProof : DOTCapture.ModalIntersections.Includes
    (DOTCapture.ModalIntersections.TypingEnv.nil.extendStatic
      lexicalInterval).bindings (.capture .empty) reference :=
  .lower (DOTCapture.ModalIntersections.HasLower.bound
    (context := (DOTCapture.ModalIntersections.TypingEnv.nil.extendStatic
      lexicalInterval).bindings)
    (index := (.here : DOTCapture.ModalIntersections.BVar
      ([.static .capture] : DOTCapture.ModalIntersections.Sig)
      (.static .capture)))
    (lower := .capture .empty) (upper := .some (.capture .empty)) rfl)

def requested : Source.Interval .capture
    ([.static .capture] : DOTCapture.ModalIntersections.Sig) :=
  .bounds (.some (.capture .empty)) .none

def satisfaction : DOTCapture.ModalIntersections.Interval.SatisfiedBy
    (DOTCapture.ModalIntersections.TypingEnv.nil.extendStatic
      lexicalInterval).bindings reference requested :=
  .lower lowerProof

/-- Deliberately omit the source lower-bound leaf while keeping every other
ambient compiler component unchanged. -/
def missingLeaves : LeafCompiler context.core :=
  { context.compiler.leaves with lower := fun _ => none }

def compiler : EvidenceElaboration.Compiler context.core :=
  Compiler.ofCore context.core missingLeaves
    (ActiveLeaves.nil context.core.target context.core.captureMap)

example : (compileEvidence? compiler satisfaction).isNone = true := by
  native_decide

end MissingSourceEvidence

namespace NoSelfDischarge

def impossible : Source.Interval .type [] :=
  .bounds (.some (.type .top)) (.some (.type .bot))

def preparedImpossible : PreparedStatic Core.nil impossible where
  theory := ManySortedFC.Interval.between (.type .top) (.type .bot)
  prepared := rfl

def topWitness : PreparedStaticExpr Core.nil
    (.type .top : DOTCapture.ModalIntersections.StaticExpr .type []) where
  targetExpression := .type .top
  prepared := rfl

/-- The lower obligation is reflexive. The second certificate is also
reflexive and therefore cannot prove the modeled theory's own `Top <= Bottom`
obligation. Since checking remains in `Core.nil.target`, that obligation
cannot discharge itself. -/
def reflexiveEvidence : ManySortedFC.EvidenceArgs []
    [.inclusion .type, .inclusion .type] :=
  .cons (.inclusionRefl (.type .top))
    (.cons (.inclusionRefl (.type .top)) .nil)

example : (check? preparedImpossible topWitness reflexiveEvidence).isNone =
    true := by
  native_decide

end NoSelfDischarge

end DOTCaptureToManySortedFC.ModalIntersections.IntervalModelExamples
