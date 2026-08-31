import Coercions.ManySortedFC.Adapter
import Coercions.ManySortedFC.Intervals

/-!
# Theory-morphism and captured-adapter regressions

These examples use one ambient capability and one abstract capture name.  They
exercise the direction of quantified theory adaptation and the two small
helpers for adapting captured types.
-/

namespace ManySortedFC.TheoryMorphismExamples

abbrev OuterScope : Sig := ([] : Sig) ▹ .term

def outerContext : Ctx OuterScope :=
  Ctx.nil.extendTerm .one

def ambientCapability : Capture OuterScope :=
  .singleton .here

def strongUpper : Theory OuterScope [.capture] [.inclusion .capture] :=
  Interval.upperBounded (.capture .empty)

def weakUpper : Theory OuterScope [.capture] [.inclusion .capture] :=
  Interval.upperBounded (.capture ambientCapability)

abbrev OpenScope : Sig :=
  StaticScope OuterScope [.capture] [.inclusion .capture]

def openedCapture : Capture OpenScope :=
  .cvar (.there .here)

def openedCapability : Capture OpenScope :=
  .singleton (.there (.there .here))

/-- Under `c ⊆ ∅`, transitivity with `∅ ⊆ {x}` proves `c ⊆ {x}`. -/
def strongEntailsWeak : TheoryMorphism strongUpper weakUpper where
  evidence :=
    .cons
      (.inclusionTrans (.var .here) (.captureEmpty openedCapability))
      .nil

theorem strong_entails_weak_is_accepted :
    (TheoryMorphism.check outerContext strongEntailsWeak).isSome = true := by
  native_decide

/-- This raw certificate cites the weak source assumption `c ⊆ {x}` where
`c ⊆ ∅` is required.  The target assumption is not available to discharge
its own obligation. -/
def weakDoesNotEntailStrong : TheoryMorphism weakUpper strongUpper where
  evidence := .cons (.var .here) .nil

theorem reverse_morphism_is_rejected :
    TheoryMorphism.check outerContext weakDoesNotEntailStrong = none := by
  rfl

def capturedBody : Ty OpenScope :=
  .capturing openedCapture .one

def capturedBodyIdentity : Adapter OpenScope :=
  .identity capturedBody

/-- Universal adaptation uses the theory morphism contravariantly. -/
def contravariantForall : Adapter OuterScope :=
  .forallMorphism weakUpper strongUpper strongEntailsWeak
    capturedBodyIdentity

theorem contravariant_forall_is_accepted :
    Adapter.synth outerContext contravariantForall =
      some
        (.forallT weakUpper capturedBody,
          .forallT strongUpper capturedBody) := by
  native_decide

/-- Existential adaptation uses the same theory morphism covariantly. -/
def covariantExists : Adapter OuterScope :=
  .existsMorphism strongUpper weakUpper strongEntailsWeak
    capturedBodyIdentity

theorem covariant_exists_is_accepted :
    Adapter.synth outerContext covariantExists =
      some
        (.existsT strongUpper capturedBody,
          .existsT weakUpper capturedBody) := by
  native_decide

def wrongDirectionForall : Adapter OuterScope :=
  .forallMorphism strongUpper weakUpper weakDoesNotEntailStrong
    capturedBodyIdentity

theorem wrong_direction_forall_is_rejected :
    Adapter.check outerContext wrongDirectionForall = none := by
  rfl

def wrongDirectionExists : Adapter OuterScope :=
  .existsMorphism weakUpper strongUpper weakDoesNotEntailStrong
    capturedBodyIdentity

theorem wrong_direction_exists_is_rejected :
    Adapter.check outerContext wrongDirectionExists = none := by
  rfl

/-! ## Captured-type helpers -/

def innerOnly : Adapter OuterScope :=
  Adapter.captureMap ambientCapability (.cast (.typeTop .one))

theorem capture_map_changes_only_the_inner_type :
    Adapter.synth outerContext innerOnly =
      some
        (.capturing ambientCapability .one,
          .capturing ambientCapability .top) := by
  native_decide

def captureOnly : Adapter OuterScope :=
  Adapter.captureWiden (.captureEmpty ambientCapability) .one

theorem capture_widen_changes_only_the_capture :
    Adapter.synth outerContext captureOnly =
      some
        (.capturing .empty .one,
          .capturing ambientCapability .one) := by
  native_decide

def composedCaptured : Adapter OuterScope :=
  .compose captureOnly
    (Adapter.captureMap ambientCapability (.cast (.typeTop .one)))

theorem captured_composition_is_accepted :
    Adapter.synth outerContext composedCaptured =
      some
        (.capturing .empty .one,
          .capturing ambientCapability .top) := by
  native_decide

def invalidSubcapture : Evidence (.inclusion .capture) OuterScope :=
  .captureVariable .here

theorem invalid_subcapture_is_rejected :
    Evidence.check outerContext invalidSubcapture = none := by
  rfl

theorem inner_identity_is_accepted :
    Adapter.synth outerContext (.identity (.one : Ty OuterScope)) =
      some (.one, .one) := by
  rfl

def invalidCaptured : Adapter OuterScope :=
  .captured invalidSubcapture (.identity .one)

theorem captured_rejects_an_invalid_subcapture :
    Adapter.check outerContext invalidCaptured = none := by
  rfl

end ManySortedFC.TheoryMorphismExamples
