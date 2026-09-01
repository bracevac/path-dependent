import Coercions.Translation.ManySorted.ModalIntersections.IntervalMorphism

/-!
# Checked cumulative interval-morphism regressions

The four positive cases cover every endpoint-presence shape.  Their
nontrivial endpoints demonstrate the direction from the available theory to
the required theory: `One .. One` supplies `Bottom .. Top`.

Malformed certificates and the reverse map are rejected.  A raw
`TheoryMorphism` cannot omit a required certificate: its `EvidenceArgs` spine
is indexed by the complete relation list, so the missing-evidence case is
excluded before checking.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.IntervalMorphismExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.IntervalMorphism

namespace Source

abbrev Interval := DOTCapture.ModalIntersections.Interval
abbrev StaticExpr := DOTCapture.ModalIntersections.StaticExpr

def one : StaticExpr .type [] := .type .one
def bottom : StaticExpr .type [] := .type .bot
def top : StaticExpr .type [] := .type .top

def unbounded : Interval .type [] := .bounds .none .none
def lowerAvailable : Interval .type [] := .bounds (.some one) .none
def lowerRequired : Interval .type [] := .bounds (.some bottom) .none
def upperAvailable : Interval .type [] := .bounds .none (.some one)
def upperRequired : Interval .type [] := .bounds .none (.some top)
def betweenAvailable : Interval .type [] :=
  .bounds (.some one) (.some one)
def betweenRequired : Interval .type [] :=
  .bounds (.some bottom) (.some top)

def unboundedEntails : DOTCapture.ModalIntersections.Interval.Entails
    DOTCapture.ModalIntersections.Ctx.nil unbounded unbounded :=
  .unbounded

def lowerAvailableBound : DOTCapture.ModalIntersections.HasLower
    (DOTCapture.ModalIntersections.Ctx.nil.extendStatic lowerAvailable)
    (.bound (.here : DOTCapture.ModalIntersections.BVar
      ([] ▹ .static .type) (.static .type))) one.weaken :=
  .bound rfl

def lowerProof : DOTCapture.ModalIntersections.Includes
    (DOTCapture.ModalIntersections.Ctx.nil.extendStatic lowerAvailable)
    bottom.weaken
    (DOTCapture.ModalIntersections.StaticExpr.bound
      (.here : DOTCapture.ModalIntersections.BVar
        ([] ▹ .static .type) (.static .type))) :=
  .trans .typeBottom (.lower lowerAvailableBound)

def lowerEntails : DOTCapture.ModalIntersections.Interval.Entails
    DOTCapture.ModalIntersections.Ctx.nil lowerAvailable lowerRequired :=
  .lower lowerProof

def upperAvailableBound : DOTCapture.ModalIntersections.HasUpper
    (DOTCapture.ModalIntersections.Ctx.nil.extendStatic upperAvailable)
    (.bound (.here : DOTCapture.ModalIntersections.BVar
      ([] ▹ .static .type) (.static .type))) one.weaken :=
  .bound rfl

def upperProof : DOTCapture.ModalIntersections.Includes
    (DOTCapture.ModalIntersections.Ctx.nil.extendStatic upperAvailable)
    (DOTCapture.ModalIntersections.StaticExpr.bound
      (.here : DOTCapture.ModalIntersections.BVar
        ([] ▹ .static .type) (.static .type)))
    top.weaken :=
  .trans (.upper upperAvailableBound) .typeTop

def upperEntails : DOTCapture.ModalIntersections.Interval.Entails
    DOTCapture.ModalIntersections.Ctx.nil upperAvailable upperRequired :=
  .upper upperProof

def betweenLowerBound : DOTCapture.ModalIntersections.HasLower
    (DOTCapture.ModalIntersections.Ctx.nil.extendStatic betweenAvailable)
    (.bound (.here : DOTCapture.ModalIntersections.BVar
      ([] ▹ .static .type) (.static .type))) one.weaken :=
  .bound rfl

def betweenUpperBound : DOTCapture.ModalIntersections.HasUpper
    (DOTCapture.ModalIntersections.Ctx.nil.extendStatic betweenAvailable)
    (.bound (.here : DOTCapture.ModalIntersections.BVar
      ([] ▹ .static .type) (.static .type))) one.weaken :=
  .bound rfl

def betweenLowerProof : DOTCapture.ModalIntersections.Includes
    (DOTCapture.ModalIntersections.Ctx.nil.extendStatic betweenAvailable)
    bottom.weaken
    (DOTCapture.ModalIntersections.StaticExpr.bound
      (.here : DOTCapture.ModalIntersections.BVar
        ([] ▹ .static .type) (.static .type))) :=
  .trans .typeBottom (.lower betweenLowerBound)

def betweenUpperProof : DOTCapture.ModalIntersections.Includes
    (DOTCapture.ModalIntersections.Ctx.nil.extendStatic betweenAvailable)
    (DOTCapture.ModalIntersections.StaticExpr.bound
      (.here : DOTCapture.ModalIntersections.BVar
        ([] ▹ .static .type) (.static .type)))
    top.weaken :=
  .trans (.upper betweenUpperBound) .typeTop

def betweenEntails : DOTCapture.ModalIntersections.Interval.Entails
    DOTCapture.ModalIntersections.Ctx.nil betweenAvailable betweenRequired :=
  .between betweenLowerProof betweenUpperProof

end Source

namespace Prepared

def unbounded : PreparedStatic Context.nil.core Source.unbounded where
  theory := ManySortedFC.Interval.unconstrained .type
  prepared := rfl

def lowerAvailable : PreparedStatic Context.nil.core Source.lowerAvailable where
  theory := ManySortedFC.Interval.lowerBounded (.type .one)
  prepared := rfl

def lowerRequired : PreparedStatic Context.nil.core Source.lowerRequired where
  theory := ManySortedFC.Interval.lowerBounded (.type .bot)
  prepared := rfl

def upperAvailable : PreparedStatic Context.nil.core Source.upperAvailable where
  theory := ManySortedFC.Interval.upperBounded (.type .one)
  prepared := rfl

def upperRequired : PreparedStatic Context.nil.core Source.upperRequired where
  theory := ManySortedFC.Interval.upperBounded (.type .top)
  prepared := rfl

def betweenAvailable : PreparedStatic Context.nil.core
    Source.betweenAvailable where
  theory := ManySortedFC.Interval.between (.type .one) (.type .one)
  prepared := rfl

def betweenRequired : PreparedStatic Context.nil.core
    Source.betweenRequired where
  theory := ManySortedFC.Interval.between (.type .bot) (.type .top)
  prepared := rfl

end Prepared

/-! ## All four source entailment shapes -/

def unbounded? := compile? Context.nil Prepared.unbounded Prepared.unbounded
  Source.unboundedEntails

def lower? := compile? Context.nil Prepared.lowerAvailable
  Prepared.lowerRequired Source.lowerEntails

def upper? := compile? Context.nil Prepared.upperAvailable
  Prepared.upperRequired Source.upperEntails

def between? := compile? Context.nil Prepared.betweenAvailable
  Prepared.betweenRequired Source.betweenEntails

example : unbounded?.isSome = true := by native_decide
example : lower?.isSome = true := by native_decide
example : upper?.isSome = true := by native_decide
example : between?.isSome = true := by native_decide

def lower := lower?.get (by native_decide)
def between := between?.get (by native_decide)

example : ManySortedFC.TheoryMorphism.check Context.nil.core.target
    lower.morphism = some lower.typing :=
  lower.checkerAcceptance

example : ManySortedFC.TheoryMorphism.check Context.nil.core.target
    between.morphism = some between.typing :=
  between.checkerAcceptance

/-- The exact source lower-bound derivation remains connected to the exact
cumulative evidence-compiler result used in the accepted morphism. -/
example : Nonempty (EvidenceCompilation Context.nil Prepared.lowerAvailable
    Source.lowerEntails lower.evidence) :=
  ⟨lower.provenance⟩

example : BodyTranslationAgreement (core := Context.nil.core)
    Source.betweenEntails
    (.one : DOTCapture.ModalIntersections.Ty ([] ▹ .static .type)) :=
  translateBody_required_eq_available (core := Context.nil.core)
    Source.betweenEntails .one

/-! ## Rejection boundaries -/

/-- Citing the available lower-bound assumption directly does not prove the
different required lower bound.  The required theory is not opened to let its
obligation discharge itself. -/
def selfDischarge : ManySortedFC.TheoryMorphism
    Prepared.lowerAvailable.theory
    (requiredTheory Prepared.lowerRequired Source.lowerEntails) where
  evidence := .cons (.var .here) .nil

example : ManySortedFC.TheoryMorphism.check Context.nil.core.target
    selfDischarge = none := by native_decide

/-- Reversing the map also fails: `Bottom <= name` does not establish the
available theory's stronger `One <= name` obligation. -/
def reverseDirection : ManySortedFC.TheoryMorphism
    Prepared.lowerRequired.theory Prepared.lowerAvailable.theory where
  evidence := .cons (.var .here) .nil

example : ManySortedFC.TheoryMorphism.check Context.nil.core.target
    reverseDirection = none := by native_decide

/-- A structurally well-sized but propositionally malformed certificate is
rejected by the standalone checker. -/
def malformed : ManySortedFC.TheoryMorphism
    Prepared.lowerAvailable.theory
    (requiredTheory Prepared.lowerRequired Source.lowerEntails) where
  evidence := .cons (.inclusionRefl (.type .one)) .nil

example : ManySortedFC.TheoryMorphism.check Context.nil.core.target
    malformed = none := by native_decide

/-- For a one-relation theory, every raw morphism necessarily contains a head
certificate.  There is no well-typed missing-evidence candidate to check. -/
def requiredHead (morphism : ManySortedFC.TheoryMorphism
    Prepared.lowerAvailable.theory
    (requiredTheory Prepared.lowerRequired Source.lowerEntails)) :
    ManySortedFC.Evidence (.inclusion .type)
      (ManySortedFC.StaticScope [] [.type] [.inclusion .type]) :=
  match morphism.evidence with
  | .cons newest .nil => newest

end DOTCaptureToManySortedFC.ModalIntersections.IntervalMorphismExamples
