import Coercions.ManySortedFC.TermChecker
import Coercions.ManySortedFC.Erasure
import Coercions.ManySortedFC.StaticExamples

/-!
# Executable examples for annotated terms and erasure

These regressions exercise the proof-producing term checker at ordinary,
logical, universal, and existential boundaries.  Rejection examples differ
only at an exact structural obligation, while the erasure equations exhibit
which annotations and certificates have no runtime representation.
-/

namespace ManySortedFC.TermExamples

/-! ## Ordinary terms and explicit adaptation -/

/-- The identity function at `One`, with an empty retained closure. -/
def unitIdentity : Tm [] :=
  .lam .one .one .empty (.var .here)
    (.captureEmpty (.union .empty (.singleton .here)))

theorem unit_identity_is_accepted :
    Tm.synth Ctx.nil unitIdentity =
      some (.empty, .capturing .empty (.arr .one .one)) := by
  native_decide

/-! ## Explicit capture introduction -/

/-- Ordinary unit typing remains bare.  Capture introduction is an explicit
adapter boundary rather than an implicit change to the `unit` rule. -/
theorem ordinary_unit_remains_bare :
    Tm.synth Ctx.nil (.unit : Tm []) = some (.empty, .one) := by
  native_decide

/-- Retag a syntactic `One` payload with an explicit empty capture.  The two
certificates separately cover its actual outer capture and stripped shape. -/
def oneWithEmptyCaptureAdapter : Adapter [] :=
  .retagCapture .one .empty .one
    (.captureEmpty .empty)
    (.inclusionRefl (.type .one))

theorem empty_capture_retag_is_accepted :
    Adapter.synth Ctx.nil oneWithEmptyCaptureAdapter =
      some (.one, .capturing .empty .one) := by
  native_decide

/-- The checker compares the certificate's source capture with the recorded
source projection; a proof about `∅ ∪ ∅` cannot stand in for `One`'s exact
outer capture `∅`. -/
def wrongRetagSourceCapture : Adapter [] :=
  .retagCapture .one .empty .one
    (.captureUnionElim
      (.captureEmpty .empty)
      (.captureEmpty .empty))
    (.inclusionRefl (.type .one))

theorem retag_source_capture_mismatch_is_rejected :
    (Adapter.check Ctx.nil wrongRetagSourceCapture).isNone = true := by
  native_decide

/-- The stripped source shape is checked just as exactly. -/
def wrongRetagSourceShape : Adapter [] :=
  .retagCapture .one .empty .one
    (.captureEmpty .empty)
    (.typeBottom .one)

theorem retag_source_shape_mismatch_is_rejected :
    (Adapter.check Ctx.nil wrongRetagSourceShape).isNone = true := by
  native_decide

def unitWithEmptyCapture : Tm [] :=
  .adapt .unit oneWithEmptyCaptureAdapter

theorem syntactic_unit_can_enter_captured_payload_type :
    Tm.synth Ctx.nil unitWithEmptyCapture =
      some (.empty, .capturing .empty .one) := by
  native_decide

theorem capture_retag_erases_to_unit :
    unitWithEmptyCapture.erase = Runtime.Tm.unit := rfl

/-! ## Explicit removal of an empty capture annotation -/

/-- Empty-capture removal records the exact captured source type and the bare
target type; it carries no evidence and cannot be instantiated at a nonempty
capture. -/
def forgetEmptyOne : Adapter [] :=
  .forgetEmptyCapture .one

theorem forget_empty_capture_has_exact_endpoints :
    Adapter.synth Ctx.nil forgetEmptyOne =
      some (.capturing .empty .one, .one) := by
  native_decide

def unitAfterForgettingEmptyCapture : Tm [] :=
  .adapt unitWithEmptyCapture forgetEmptyOne

theorem empty_captured_unit_can_return_to_bare_one :
    Tm.synth Ctx.nil unitAfterForgettingEmptyCapture =
      some (.empty, .one) := by
  native_decide

theorem forgetting_empty_capture_erases_exactly :
    unitAfterForgettingEmptyCapture.erase = unitWithEmptyCapture.erase := rfl

/-- The endpoint is exact, but the ordinary adapter boundary still consumes
only values. -/
def computedEmptyCapturedUnit : Tm [] :=
  .let' (.capturing .empty .one) .empty unitWithEmptyCapture
    unitWithEmptyCapture.weaken (.captureEmpty .empty)

def rejectComputationForgettingEmptyCapture : Tm [] :=
  .adapt computedEmptyCapturedUnit forgetEmptyOne

theorem forget_empty_capture_remains_value_only :
    (Tm.check Ctx.nil rejectComputationForgettingEmptyCapture).isNone = true := by
  native_decide

/-- A free term name makes a nonempty capture expression available for the
negative structural-checker regression. -/
def singletonCaptureContext : Ctx ([] ▹ .term) :=
  Ctx.nil.extendTerm .one

def oneWithSingletonCaptureAdapter : Adapter ([] ▹ .term) :=
  .retagCapture .one (.singleton .here) .one
    (.captureEmpty (.singleton .here))
    (.inclusionRefl (.type .one))

/-- The second adapter requires `∅ · One` exactly, so it cannot directly
discard the nonempty singleton annotation produced by the first adapter. -/
def rejectForgettingNonemptyCapture : Adapter ([] ▹ .term) :=
  .compose oneWithSingletonCaptureAdapter (.forgetEmptyCapture .one)

theorem nonempty_capture_cannot_be_forgotten_directly :
    (Adapter.check singletonCaptureContext
      rejectForgettingNonemptyCapture).isNone = true := by
  native_decide

def unitWithSingletonCapture : Tm ([] ▹ .term) :=
  .adapt .unit oneWithSingletonCaptureAdapter

def rejectTermForgettingNonemptyCapture : Tm ([] ▹ .term) :=
  .adapt unitWithSingletonCapture (.forgetEmptyCapture .one)

theorem term_checker_rejects_forgetting_nonempty_capture :
    (Tm.check singletonCaptureContext
      rejectTermForgettingNonemptyCapture).isNone = true := by
  native_decide

/-- A logical cast transports `unit` along the primitive `One <= Top`
certificate. -/
def unitAsTop : Tm [] :=
  .adapt .unit (.cast (.typeTop .one))

theorem logical_unit_adaptation_is_accepted :
    Tm.synth Ctx.nil unitAsTop = some (.empty, .top) := by
  native_decide

/-- This adapter expects a function as its source, so applying it to `unit`
must fail at the checker's exact source equality test. -/
def mismatchedUnitAdaptation : Tm [] :=
  .adapt .unit
    (.cast (.typeTop (.arr .one .one)))

theorem adapter_source_mismatch_is_rejected :
    (Tm.check Ctx.nil mismatchedUnitAdaptation).isNone = true := by
  native_decide

/-- Structural adapters consume values at one uniform boundary.  Although
this application has type `One`, adapting it directly could become unsafe
after adapter composition, so the checker requires it to be let-bound first. -/
def nonValueUnitAdaptation : Tm [] :=
  .adapt (.app unitIdentity .unit) (.cast (.typeTop .one))

theorem nonvalue_adapter_application_is_rejected :
    (Tm.check Ctx.nil nonValueUnitAdaptation).isNone = true := by
  native_decide

/-! ## Capture prediction and local discharge -/

/-- A closed unary function type whose explicit outer annotation allows a
variable occurrence to receive its precise singleton root. -/
def closedUnaryType : Ty [] :=
  .capturing .empty (.arr .one .one)

/-! ### General computation operands -/

/-- A genuine computation returning the closed identity function.  Its
right-hand side and body are values, but the enclosing ordinary let is not. -/
def computedUnitIdentity : Tm [] :=
  .let' closedUnaryType .empty .unit unitIdentity.weaken
    (.captureEmpty .empty)

/-- A genuine computation returning unit. -/
def computedUnit : Tm [] :=
  .let' .one .empty .unit .unit
    (.captureEmpty .empty)

/-- Both operands of this application are computations rather than annotated
target values. -/
def applicationOfComputations : Tm [] :=
  .app computedUnitIdentity computedUnit

theorem computation_application_is_accepted :
    Tm.synth Ctx.nil applicationOfComputations =
      some
        (.union (.union .empty .empty)
          (.union (.union .empty .empty) (.union .empty .empty)),
          .one) := by
  native_decide

/-- The generalized rule still checks the argument type after independently
synthesizing both computation operands. -/
def computationApplicationWithWrongArgument : Tm [] :=
  .app computedUnitIdentity computedUnitIdentity

theorem computation_application_type_mismatch_is_rejected :
    (Tm.check Ctx.nil computationApplicationWithWrongArgument).isNone = true := by
  native_decide

def freeFunctionContext : Ctx ([] ▹ .term) :=
  Ctx.nil.extendTerm closedUnaryType

/-- Invoking a free function charges its precise root, even though the value
stored in the context was declared with an empty retained capture. -/
def callFreeFunction : Tm ([] ▹ .term) :=
  .app (.var .here) .unit

theorem free_function_call_predicts_its_root :
    Tm.synth freeFunctionContext callFreeFunction =
      some (.union (.singleton .here) .empty, .one) := by
  native_decide

/-- A lambda may export that prediction as its ambient closure. -/
def capturesFreeFunction : Tm ([] ▹ .term) :=
  .lam .one .one (.singleton .here)
    (.app (.var (.there .here)) .unit)
    (.captureUnionElim
      (.captureUnionLeft (.singleton (.there .here)) (.singleton .here))
      (.captureEmpty
        (.union (.singleton (.there .here)) (.singleton .here))))

theorem lambda_retains_its_free_function :
    Tm.synth freeFunctionContext capturesFreeFunction =
      some (.empty,
        .capturing (.singleton .here) (.arr .one .one)) := by
  native_decide

/-- Binding the free function to a local variable and invoking that variable
uses `captureVariable` to discharge the local root to the capture retained by
the bound value. -/
def letBoundCallRaw : Tm ([] ▹ .term) :=
  .let' .one (.singleton .here) (.var .here)
    (.app (.var .here) .unit)
    (.captureUnionElim
      (.captureVariable .here)
      (.captureEmpty (.singleton (.there .here))))

/-- The raw `let` prediction is `∅ ∪ {f}`; the explicit `use` certificate
normalizes that upper bound to `{f}` without changing its returned type. -/
def letBoundCall : Tm ([] ▹ .term) :=
  .use letBoundCallRaw
    (.captureUnionElim
      (.captureEmpty (.singleton .here))
      (.inclusionRefl (.capture (.singleton .here))))

theorem let_discharge_exports_only_the_outer_root :
    Tm.synth freeFunctionContext letBoundCall =
      some (.singleton .here, .one) := by
  native_decide

theorem captured_binding_exports_capture_variable_evidence :
    (Evidence.check freeFunctionContext
      (.captureVariable (.here : BVar ([] ▹ .term) .term))).isSome = true := by
  native_decide

/-- A bare binding can still be named explicitly as a capability, but its
type is pure/untracked: projecting `Ty.outerCapture = ∅` does not
manufacture a `{x} ⊆ ∅` certificate. -/
theorem bare_binding_rejects_capture_variable_evidence :
    (Evidence.check (Ctx.nil.extendTerm .one)
      (.captureVariable (.here : BVar ([] ▹ .term) .term))).isNone = true := by
  native_decide

/-- Capture introduction adapts a value; it does not add evidence to a bare
context binding or weaken the `captureVariable` checker. -/
theorem capture_retag_does_not_enable_bare_root_contraction :
    (Evidence.check (Ctx.nil.extendTerm .one)
      (.captureVariable (.here : BVar ([] ▹ .term) .term))).isNone = true := by
  native_decide

/-! The parameter singleton is a discharge boundary, not a retained closure. -/

/-- A bare outer variable supplies the capability name `a`.  Bare callable
and non-callable types alike are pure/untracked for prediction and export no
logical singleton contraction; the name may still occur explicitly in a
capturing type. -/
def outerCapabilityContext : Ctx ([] ▹ .term) :=
  Ctx.nil.extendTerm .one

def parameterCallableType : Ty ([] ▹ .term) :=
  .capturing (.singleton .here) (.arr .one .one)

/-- `λ(f : {a}(One → One)). f unit` retains no ambient closure.  The body
use `{f} ∪ ∅` is discharged through the parameter side of `∅ ∪ {f}`. -/
def callsParameter : Tm ([] ▹ .term) :=
  .lam parameterCallableType .one .empty
    (.app (.var .here) .unit)
    (.captureUnionElim
      (.captureUnionRight .empty (.singleton .here))
      (.captureEmpty (.union .empty (.singleton .here))))

theorem parameter_call_does_not_enter_lambda_closure :
    Tm.synth outerCapabilityContext callsParameter =
      some (.empty,
        .capturing .empty (.arr parameterCallableType .one)) := by
  native_decide

/-- A closed identity value widened to the parameter type. -/
def parameterArgument : Tm ([] ▹ .term) :=
  .adapt
    (.lam .one .one .empty (.var .here)
      (.captureEmpty (.union .empty (.singleton .here))))
    (.cast
      (.typeCapturing
        (.captureEmpty (.singleton .here))
        (.inclusionRefl (.type (.arr .one .one)))))

/-- Although the function closure is empty, application charges the domain's
retained `{a}` capture. -/
def callsParameterApplicationRaw : Tm ([] ▹ .term) :=
  .app callsParameter parameterArgument

theorem outer_application_charges_domain_capture_raw :
    Tm.synth outerCapabilityContext callsParameterApplicationRaw =
      some (.union .empty (.singleton .here), .one) := by
  native_decide

def callsParameterApplication : Tm ([] ▹ .term) :=
  .use callsParameterApplicationRaw
    (.captureUnionElim
      (.captureEmpty (.singleton .here))
      (.inclusionRefl (.capture (.singleton .here))))

theorem outer_application_predicts_exact_domain_capture :
    Tm.synth outerCapabilityContext callsParameterApplication =
      some (.singleton .here, .one) := by
  native_decide

/-! ## A realizable static abstraction and application -/

/-- A value body abstracted over the realizable mixed type/capture theory. -/
def mixedStaticUnit : Tm [] :=
  .slam StaticExamples.exactMixedTheory .empty .unit
    (.inclusionRefl (.capture .empty))

theorem mixed_static_abstraction_is_accepted :
    (Tm.check Ctx.nil mixedStaticUnit).isSome = true := by
  native_decide

/-- Both sorted witnesses and their ambient reflexivity certificates are
supplied simultaneously at static application. -/
def appliedMixedStaticUnit : Tm [] :=
  .sapp StaticExamples.exactMixedTheory mixedStaticUnit
    StaticExamples.exactMixedWitnesses
    StaticExamples.exactMixedEvidence

theorem realizable_static_application_is_accepted :
    Tm.synth Ctx.nil appliedMixedStaticUnit = some (.empty, .one) := by
  native_decide

/-! ## Existential packages -/

abbrev MixedStaticScope : Sig :=
  StaticScope [] [.type, .capture]
    [.equality .type, .equality .capture]

/-- The payload deliberately has a static-scope type even though `One` does
not mention either hidden symbol. -/
def mixedUnitPayloadType : Ty MixedStaticScope := .one

/-- Package formation checks the mixed theory model in the empty ambient
context, then checks the payload against its instantiated type. -/
def mixedUnitPackage : Tm [] :=
  .pack StaticExamples.exactMixedTheory mixedUnitPayloadType .empty
    StaticExamples.exactMixedWitnesses
    StaticExamples.exactMixedEvidence .unit
    (.inclusionRefl (.capture .empty))

theorem realizable_existential_package_is_accepted :
    Tm.synth Ctx.nil mixedUnitPackage =
      some (.empty,
        .capturing .empty
          (.existsT StaticExamples.exactMixedTheory mixedUnitPayloadType)) := by
  native_decide

/-- Opening exposes the theory and its payload variable only inside the body;
the explicit result remains the ambient type `One`. -/
def openedMixedUnitPackage : Tm [] :=
  .use
    (.«open» StaticExamples.exactMixedTheory mixedUnitPayloadType .one
      .empty mixedUnitPackage (.var .here)
      (.captureEmpty (.union .empty (.singleton .here))))
    (.captureUnionElim (.captureEmpty .empty) (.captureEmpty .empty))

theorem realizable_existential_open_is_accepted :
    Tm.synth Ctx.nil openedMixedUnitPackage = some (.empty, .one) := by
  native_decide

/-! ### Opening a package computation -/

/-- A non-value computation whose result is the realizable mixed package. -/
def computedMixedUnitPackage : Tm [] :=
  .let'
    (.capturing .empty
      (.existsT StaticExamples.exactMixedTheory mixedUnitPayloadType))
    .empty .unit mixedUnitPackage.weaken
    (.captureEmpty .empty)

/-- Existential opening directly sequences the package computation.  It does
not require an administrative target let merely to make the package a value. -/
def openedComputedMixedUnitPackage : Tm [] :=
  .«open» StaticExamples.exactMixedTheory mixedUnitPayloadType .one
    .empty computedMixedUnitPackage (.var .here)
    (.captureEmpty (.union .empty (.singleton .here)))

theorem computed_existential_open_is_accepted :
    Tm.synth Ctx.nil openedComputedMixedUnitPackage =
      some
        (.union (.union .empty .empty) (.union .empty .empty), .one) := by
  native_decide

/-- General opening does not weaken the existential-shape check. -/
def opensComputedNonPackage : Tm [] :=
  .«open» StaticExamples.exactMixedTheory mixedUnitPayloadType .one
    .empty computedUnit (.var .here)
    (.captureEmpty (.union .empty (.singleton .here)))

theorem computed_nonpackage_open_is_rejected :
    (Tm.check Ctx.nil opensComputedNonPackage).isNone = true := by
  native_decide

/-- The impossible interval's reflexive evidence is not a model in the empty
ambient context, so the enclosing package is rejected before its assumptions
can become available. -/
def impossibleIntervalPackage : Tm [] :=
  .pack StaticExamples.impossibleTypeInterval
    (.one : Ty StaticExamples.ImpossibleTypeOpenScope)
    .empty
    StaticExamples.impossibleTypeWitness
    StaticExamples.reflexiveTypeEvidence .unit
    (.inclusionRefl (.capture .empty))

theorem impossible_interval_package_is_rejected :
    (Tm.check Ctx.nil impossibleIntervalPackage).isNone = true := by
  native_decide

/-! ## Exact runtime shapes -/

/-- Logical evidence and the cast annotation have no runtime representation. -/
theorem logical_adaptation_erases_to_unit :
    unitAsTop.erase = Runtime.Tm.unit := rfl

/-- Static binders, sorted witnesses, and their evidence all disappear. -/
theorem static_application_erases_to_unit :
    appliedMixedStaticUnit.erase = Runtime.Tm.unit := rfl

/-- An existential package erases directly to its computational payload. -/
theorem package_erases_to_payload :
    mixedUnitPackage.erase = Runtime.Tm.unit := rfl

/-- Opening retains only the ordinary payload-binding `let`. -/
theorem package_open_erases_to_payload_let :
    openedMixedUnitPackage.erase =
      Runtime.Tm.let' .unit (.var 0) := rfl

/-- Opening a package computation retains exactly that computation followed
by the existential payload-binding let. -/
theorem computed_package_open_erases_exactly :
    openedComputedMixedUnitPackage.erase =
      Runtime.Tm.let' (.let' .unit .unit) (.var 0) := rfl

/-- Unlike logical casts, a function adapter has an explicit eta-expansion at
runtime, with an administrative let around the original call. -/
def identityFunctionAdapter : Adapter [] :=
  .function (.identity .one) (.identity .one)

theorem function_adapter_exposes_eta_shape (term : Runtime.Tm 0) :
    identityFunctionAdapter.erase term =
      .lam (.let' (.app term.weaken (.var 0)) (.var 0)) := rfl

end ManySortedFC.TermExamples
