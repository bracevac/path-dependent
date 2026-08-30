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

/-- The identity function at `One`, with its ambient codomain annotation. -/
def unitIdentity : Tm [] :=
  .lam .one .one (.var .here)

theorem unit_identity_is_accepted :
    Tm.synth Ctx.nil unitIdentity = some (.arr .one .one) := by
  native_decide

/-- A logical cast transports `unit` along the primitive `One <= Top`
certificate. -/
def unitAsTop : Tm [] :=
  .adapt .unit (.cast (.typeTop .one))

theorem logical_unit_adaptation_is_accepted :
    Tm.synth Ctx.nil unitAsTop = some .top := by
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

/-! ## A realizable static abstraction and application -/

/-- A value body abstracted over the realizable mixed type/capture theory. -/
def mixedStaticUnit : Tm [] :=
  .slam StaticExamples.exactMixedTheory .unit

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
    Tm.synth Ctx.nil appliedMixedStaticUnit = some .one := by
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
  .pack StaticExamples.exactMixedTheory mixedUnitPayloadType
    StaticExamples.exactMixedWitnesses
    StaticExamples.exactMixedEvidence .unit

theorem realizable_existential_package_is_accepted :
    Tm.synth Ctx.nil mixedUnitPackage =
      some (.existsT StaticExamples.exactMixedTheory mixedUnitPayloadType) := by
  native_decide

/-- Opening exposes the theory and its payload variable only inside the body;
the explicit result remains the ambient type `One`. -/
def openedMixedUnitPackage : Tm [] :=
  .«open» StaticExamples.exactMixedTheory mixedUnitPayloadType .one
    mixedUnitPackage (.var .here)

theorem realizable_existential_open_is_accepted :
    Tm.synth Ctx.nil openedMixedUnitPackage = some .one := by
  native_decide

/-- The impossible interval's reflexive evidence is not a model in the empty
ambient context, so the enclosing package is rejected before its assumptions
can become available. -/
def impossibleIntervalPackage : Tm [] :=
  .pack StaticExamples.impossibleTypeInterval
    (.one : Ty StaticExamples.ImpossibleTypeOpenScope)
    StaticExamples.impossibleTypeWitness
    StaticExamples.reflexiveTypeEvidence .unit

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
runtime. -/
def identityFunctionAdapter : Adapter [] :=
  .function (.identity .one) (.identity .one)

theorem function_adapter_exposes_eta_shape (term : Runtime.Tm 0) :
    identityFunctionAdapter.erase term =
      .lam (.app term.weaken (.var 0)) := rfl

end ManySortedFC.TermExamples
