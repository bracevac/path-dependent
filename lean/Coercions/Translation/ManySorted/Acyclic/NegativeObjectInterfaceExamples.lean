import Coercions.Translation.ManySorted.Acyclic.NegativeObjectInterface
import Coercions.Translation.ManySorted.Acyclic.ObjectEncoding
import Coercions.ManySortedFC.Runtime

/-!
# Negative object-interface regressions

These target-level examples instantiate the generic negative interface with
the real two-sorted object theory.  The result type of the consumer is the
model-dependent representation itself, so static application must substitute
both the abstract type and capture names before ordinary runtime application.
-/

namespace DOTCaptureToManySortedFC.Acyclic.NegativeObjectInterfaceExamples

open ManySortedFC

/-- Extract the declarative proof returned by the independent model checker.
The model uses both actual sorts and all four interval certificates. -/
def exactSatisfaction : Theory.SatisfiedBy Ctx.nil ObjectEncoding.exactSymbols
    (ObjectEncoding.theory ObjectEncoding.exactBounds)
    ObjectEncoding.exactEvidence :=
  (Theory.checkSatisfaction Ctx.nil ObjectEncoding.exactSymbols
    (ObjectEncoding.theory ObjectEncoding.exactBounds)
      ObjectEncoding.exactEvidence).get (by
      native_decide)

/-- The canonical literal payload in negative position.  It is retagged as a
value; no existential package is constructed. -/
def exactPayload : Tm [] :=
  ObjectEncoding.retagPayload .unit .one .one .empty
    (.captureEmpty .empty) (.inclusionRefl (.type .one))

def exactPayloadTyping : Tm.HasType Ctx.nil exactPayload .empty
    (ObjectEncoding.payloadType.instantiateStatic
      ObjectEncoding.exactSymbols) := by
  unfold exactPayload ObjectEncoding.retagPayload
  have typing : Tm.HasType Ctx.nil
      (.adapt .unit
        (.retagCapture .one .empty .one
          (.captureEmpty .empty) (.inclusionRefl (.type .one))))
      .empty (.capturing .empty .one) :=
    .adapt .unit .unit
      (.retagCapture (.captureEmpty .empty)
        (.inclusionRefl (.type .one)))
  simpa [ObjectEncoding.payloadType, ObjectEncoding.exactSymbols,
    ObjectEncoding.symbolArguments] using typing

def exactArgument : NegativeObjectInterface.Argument Ctx.nil
    (ObjectEncoding.theory ObjectEncoding.exactBounds)
    ObjectEncoding.payloadType where
  symbols := ObjectEncoding.exactSymbols
  evidence := ObjectEncoding.exactEvidence
  satisfies := exactSatisfaction
  payload := exactPayload
  payloadValue := .adapt .unit
  payloadTyping := exactPayloadTyping

/-! ## A genuinely model-dependent consumer -/

/-- Return the supplied representation at its abstract type and capture. -/
def dependentBody : Tm (ObjectEncoding.PayloadScope []) :=
  .adapt (.var .here)
    (.retagCapture
      (.capturing (.singleton .here) (.tvar ObjectEncoding.alphaPayloadName))
      (.cvar ObjectEncoding.chiPayloadName)
      (.tvar ObjectEncoding.alphaPayloadName)
      (.captureVariable .here)
      (.inclusionRefl (.type (.tvar ObjectEncoding.alphaPayloadName))))

def dependentBodyTyping : Tm.HasType
    ((Ctx.nil.extendTheory
      (ObjectEncoding.theory ObjectEncoding.exactBounds)).extendTerm
        ObjectEncoding.payloadType)
    dependentBody .empty ObjectEncoding.payloadType.weaken := by
  unfold dependentBody
  apply Tm.HasType.adapt (.var) (Tm.HasType.var .here)
  apply Adapter.HasType.retagCapture
  · exact .captureVariable rfl
  · exact .inclusionRefl _

def dependentConsumer : Tm [] :=
  NegativeObjectInterface.abstract
    (ObjectEncoding.theory ObjectEncoding.exactBounds)
    ObjectEncoding.payloadType ObjectEncoding.payloadType .empty .empty
    dependentBody
    (.captureEmpty (.union .empty (.singleton .here)))
    (.inclusionRefl (.capture .empty))

def dependentConsumerTyping : Tm.HasType Ctx.nil dependentConsumer .empty
    (NegativeObjectInterface.consumerType
      (ObjectEncoding.theory ObjectEncoding.exactBounds)
      ObjectEncoding.payloadType ObjectEncoding.payloadType .empty .empty) :=
  NegativeObjectInterface.abstract_hasType dependentBodyTyping
    (.captureEmpty (.union .empty (.singleton .here)))
    (.inclusionRefl (.capture .empty))

/-- Static instantiation computes the dependent result to `One` with an empty
capture, then the runtime application consumes the literal payload directly.
-/
def appliedDependentConsumer : Tm [] :=
  NegativeObjectInterface.applyArgument
    (ObjectEncoding.theory ObjectEncoding.exactBounds)
    dependentConsumer exactArgument

def appliedDependentConsumerTyping : Tm.HasType Ctx.nil
    appliedDependentConsumer (.union .empty .empty)
    (.capturing .empty .one) := by
  simpa [appliedDependentConsumer, NegativeObjectInterface.consumerType,
    NegativeObjectInterface.bodyType, ObjectEncoding.payloadType,
    ObjectEncoding.exactSymbols, ObjectEncoding.symbolArguments] using
      NegativeObjectInterface.apply_hasType dependentConsumerTyping
        exactArgument

theorem dependent_consumer_is_independently_accepted :
    Tm.synth Ctx.nil dependentConsumer =
      some (.empty,
        NegativeObjectInterface.consumerType
          (ObjectEncoding.theory ObjectEncoding.exactBounds)
          ObjectEncoding.payloadType ObjectEncoding.payloadType .empty
          .empty) :=
  Tm.synth_complete dependentConsumerTyping

theorem direct_application_is_independently_accepted :
    Tm.synth Ctx.nil appliedDependentConsumer =
      some (.union .empty .empty, .capturing .empty .one) :=
  Tm.synth_complete appliedDependentConsumerTyping

/-- The generated artifact contains static application and ordinary
application, but no existential package or open. -/
theorem direct_application_shape :
    appliedDependentConsumer =
      .app
        (.sapp (ObjectEncoding.theory ObjectEncoding.exactBounds)
          dependentConsumer ObjectEncoding.exactSymbols
          ObjectEncoding.exactEvidence)
        exactPayload := rfl

theorem direct_application_erases_exactly :
    appliedDependentConsumer.erase =
      .app dependentConsumer.erase exactPayload.erase := rfl

/-- After all static material erases, the program is the ordinary identity
application `(fun x => x) unit`; it performs a genuine beta step. -/
theorem direct_application_runtime_shape :
    appliedDependentConsumer.erase =
      .app (.lam (.var 0)) .unit := rfl

theorem direct_application_beta :
    Runtime.Step appliedDependentConsumer.erase .unit := by
  rw [direct_application_runtime_shape]
  exact .beta .unit

/-! ## A computed consumer in static-application position -/

def computedDependentConsumerRaw : Tm [] :=
  .let'
    (NegativeObjectInterface.consumerType
      (ObjectEncoding.theory ObjectEncoding.exactBounds)
      ObjectEncoding.payloadType ObjectEncoding.payloadType .empty .empty)
    .empty .unit dependentConsumer.weaken (.captureEmpty .empty)

def computedDependentConsumer : Tm [] :=
  .use computedDependentConsumerRaw
    (.captureUnionElim (.captureEmpty .empty) (.captureEmpty .empty))

theorem computed_dependent_consumer_is_not_a_value :
    Tm.checkValue computedDependentConsumer = none := rfl

theorem computed_dependent_consumer_is_accepted :
    Tm.synth Ctx.nil computedDependentConsumer =
      some (.empty,
        NegativeObjectInterface.consumerType
          (ObjectEncoding.theory ObjectEncoding.exactBounds)
          ObjectEncoding.payloadType ObjectEncoding.payloadType .empty
          .empty) := by
  native_decide

def appliedComputedConsumer : Tm [] :=
  NegativeObjectInterface.applyArgument
    (ObjectEncoding.theory ObjectEncoding.exactBounds)
    computedDependentConsumer exactArgument

theorem computed_consumer_application_is_accepted :
    Tm.synth Ctx.nil appliedComputedConsumer =
      some (.union .empty .empty, .capturing .empty .one) := by
  native_decide

/-- The function computation remains in function position after erasure, so
call-by-value runs its zeta step before the payload beta step. -/
theorem computed_consumer_runtime_shape :
    appliedComputedConsumer.erase =
      .app (.let' .unit (.lam (.var 0))) .unit := rfl

theorem computed_consumer_evaluates_function_first :
    Runtime.Step appliedComputedConsumer.erase
      (.app (.lam (.var 0)) .unit) := by
  rw [computed_consumer_runtime_shape]
  exact .appFunction (.zeta .unit)

theorem computed_consumer_then_beta :
    Runtime.Step
      ((.app (.lam (.var 0)) .unit : Runtime.Tm 0))
      (.unit : Runtime.Tm 0) :=
  .beta .unit

theorem computed_consumer_executes :
    Runtime.Steps appliedComputedConsumer.erase .unit :=
  .tail (.single computed_consumer_evaluates_function_first)
    computed_consumer_then_beta

end DOTCaptureToManySortedFC.Acyclic.NegativeObjectInterfaceExamples
