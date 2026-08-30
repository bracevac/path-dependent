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

/-- Structural adapters consume ANF values at one uniform boundary.  Although
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

/-- Unlike logical casts, a function adapter has an explicit eta-expansion at
runtime, with an ANF let around the original call. -/
def identityFunctionAdapter : Adapter [] :=
  .function (.identity .one) (.identity .one)

theorem function_adapter_exposes_eta_shape (term : Runtime.Tm 0) :
    identityFunctionAdapter.erase term =
      .lam (.let' (.app term.weaken (.var 0)) (.var 0)) := rfl

end ManySortedFC.TermExamples
