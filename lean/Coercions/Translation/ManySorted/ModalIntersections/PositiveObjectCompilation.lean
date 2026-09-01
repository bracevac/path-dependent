import Coercions.Translation.ManySorted.ModalIntersections.CompilerArtifacts
import Coercions.Translation.ManySorted.ModalIntersections.EvidenceContext
import Coercions.Translation.ManySorted.ModalIntersections.ObjectEvidence

/-!
# Checked positive objects with explicit payload captures

This module packages one already compiled source payload using the cumulative
object contract. Every package exports exactly one internal representation
capture, its checked equality with the realized representation capture, and
its checked containment in the advertised object capture.

The generated contract facts are checked before the package theory is opened.
The payload is transported only by a value adapter, and the finished artifact
crosses the standalone target checker.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.PositiveObjectCompilation

open DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
open DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence

namespace Source

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv
abbrev Value := DOTCapture.ModalIntersections.Value
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev ObjectType := DOTCapture.ModalIntersections.ObjectType

end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Ty := ManySortedFC.Ty
abbrev Tm := ManySortedFC.Tm
abbrev Adapter := ManySortedFC.Adapter

end Target

/-- Independently prepare the source representation after model realization.
This is the ordinary source type translation, before a bare representation is
made explicitly empty-captured by the cumulative package contract. -/
def prepareRealizedRepresentation? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (object : Source.ObjectType sourceScope)
    (model : DOTCapture.ModalIntersections.LocalModel.Model sourceScope) :
    Option (PreparedTerm core
      (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation
        object model)) :=
  let source :=
    DOTCapture.ModalIntersections.ObjectType.realizedRepresentation object model
  match prepared : ObjectContract.translateType core.layout source with
  | .error _ => none
  | .ok targetType => some { targetType, prepared }

/-- Install the explicit representation capture required by the contract. -/
def explicitRealizedTarget {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {object : Source.ObjectType sourceScope}
    {model : DOTCapture.ModalIntersections.LocalModel.Model sourceScope}
    (prepared : PreparedTerm core
      (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation
        object model)) : Target.Ty targetScope :=
  prepared.targetType.withCapture prepared.targetType.outerCapture

/-- The explicitly captured representation selected by a checked model. -/
def realizedTarget {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {object : Source.ObjectType sourceScope}
    {prepared : PreparedContractedObject core object}
    {ambient : AmbientCompiler core}
    {realization : DOTCapture.ModalIntersections.ObjectType.Realization
      environment.bindings object}
    {containment : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings
      (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation object
        realization.model).outerCapture object.outerCapture}
    (compiled : CompiledContractedRealization core prepared ambient realization
      containment) : Target.Ty targetScope :=
  prepared.object.representation.instantiateStatic compiled.model.symbols

/-- A retained successful comparison at the substitution boundary. -/
structure TargetAgreement {scope : Target.Sig}
    (prepared instantiated : Target.Ty scope) : Type where
  exact : prepared = instantiated

def checkTargetAgreement? {scope : Target.Sig}
    (prepared instantiated : Target.Ty scope) :
    Option (TargetAgreement prepared instantiated) :=
  if agreement : prepared = instantiated then
    some { exact := agreement }
  else
    none

/-- Value-only transport into the explicitly captured representation. -/
def payloadAdapter? {scope : Target.Sig}
    (source realized : Target.Ty scope)
    (shape : ManySortedFC.Evidence (.inclusion .type) scope)
    (capture : ManySortedFC.Evidence (.inclusion .capture) scope) :
    Option (Target.Adapter scope) :=
  match realized with
  | .capturing targetCapture targetShape =>
      some (.retagCapture source targetCapture targetShape capture shape)
  | _ => none

/-- Provenance for a checked positive object package. -/
structure CompiledObject {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {object : Source.ObjectType sourceScope}
    {payload : Source.Value sourceScope} {payloadType : Source.Ty sourceScope}
    (prepared : PreparedContractedObject context.core object)
    (ambient : AmbientCompiler context.core)
    (realization : DOTCapture.ModalIntersections.ObjectType.Realization
      environment.bindings object)
    (payloadShape : DOTCapture.ModalIntersections.TypeIncludes
      environment.bindings payloadType.stripCapture
      (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation object
        realization.model).stripCapture)
    (payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings payloadType.outerCapture
      (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation object
        realization.model).outerCapture)
    (objectCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings
      (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation object
        realization.model).outerCapture object.outerCapture)
    (compiledRealization : CompiledContractedRealization context.core prepared
      ambient realization objectCapture)
    (payloadCompiled : CompilerArtifacts.CompiledValue context.core payload
      payloadType) where
  realizedPrepared : PreparedTerm context.core
    (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation object
      realization.model)
  realizationAgreement : TargetAgreement
    (explicitRealizedTarget realizedPrepared)
    (realizedTarget compiledRealization)
  realizationAgreementChecked : checkTargetAgreement?
    (explicitRealizedTarget realizedPrepared)
    (realizedTarget compiledRealization) = some realizationAgreement
  shape : CompiledInclusion context.core
    (.type payloadType.stripCapture)
    (.type (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation
      object realization.model).stripCapture)
  shapeCompiled : compileIncludes? context.compiler.leaves payloadShape =
    some shape
  payloadCaptureEvidence : CompiledInclusion context.core
    (.capture payloadType.outerCapture)
    (.capture (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation
      object realization.model).outerCapture)
  payloadCaptureCompiled :
    compileIncludes? context.compiler.leaves payloadCapture =
      some payloadCaptureEvidence
  adapter : Target.Adapter targetScope
  adapterEquation : payloadAdapter? payloadCompiled.targetType
    (realizedTarget compiledRealization) shape.evidence
      payloadCaptureEvidence.evidence = some adapter
  adaptedPayload : Target.Tm targetScope
  adaptedPayloadEquation : adaptedPayload = .adapt payloadCompiled.term adapter
  package : Target.Tm targetScope
  packageEquation : package =
    .pack prepared.object.theory prepared.object.representation
      prepared.object.outerCapture compiledRealization.model.symbols
      compiledRealization.model.evidence adaptedPayload
      compiledRealization.containmentEvidence
  administrative : ManySortedFC.Runtime.AdministrativeEq package.erase
    (context.core.eraseValue (.object object payload))
  result : CompilerArtifacts.CompiledValue context.core
    (.object object payload) object.formedType
  finalized : CompilerArtifacts.finishValue? context.core
    (.object realization payloadCompiled.sourceTyping payloadShape
      payloadCapture objectCapture)
    package administrative = some result

/-- Finalize an already compiled payload. The complete contracted model has
already crossed the standalone model checker. -/
def compile? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {object : Source.ObjectType sourceScope}
    {payload : Source.Value sourceScope} {payloadType : Source.Ty sourceScope}
    (prepared : PreparedContractedObject context.core object)
    (ambient : AmbientCompiler context.core)
    (realization : DOTCapture.ModalIntersections.ObjectType.Realization
      environment.bindings object)
    (payloadShape : DOTCapture.ModalIntersections.TypeIncludes
      environment.bindings payloadType.stripCapture
      (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation object
        realization.model).stripCapture)
    (payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings payloadType.outerCapture
      (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation object
        realization.model).outerCapture)
    (objectCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings
      (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation object
        realization.model).outerCapture object.outerCapture)
    (compiledRealization : CompiledContractedRealization context.core prepared
      ambient realization objectCapture)
    (payloadCompiled : CompilerArtifacts.CompiledValue context.core payload
      payloadType) :
    Option (CompiledObject context prepared ambient realization payloadShape
      payloadCapture objectCapture compiledRealization payloadCompiled) := do
  match shapeCompiled : compileIncludes? context.compiler.leaves
      payloadShape with
  | none => none
  | some shape =>
      match payloadCaptureCompiled : compileIncludes? context.compiler.leaves
          payloadCapture with
      | none => none
      | some payloadCaptureEvidence =>
          match prepareRealizedRepresentation? context.core object
              realization.model with
          | none => none
          | some realizedPrepared =>
              let targetRepresentation := realizedTarget compiledRealization
              match realizationAgreementChecked : checkTargetAgreement?
                  (explicitRealizedTarget realizedPrepared)
                  targetRepresentation with
              | none => none
              | some realizationAgreement =>
                  match adapterEquation : payloadAdapter?
                      payloadCompiled.targetType targetRepresentation
                        shape.evidence payloadCaptureEvidence.evidence with
                  | none => none
                  | some adapter =>
                      let adaptedPayload : Target.Tm targetScope :=
                        .adapt payloadCompiled.term adapter
                      let package : Target.Tm targetScope :=
                        .pack prepared.object.theory
                          prepared.object.representation
                          prepared.object.outerCapture
                          compiledRealization.model.symbols
                          compiledRealization.model.evidence adaptedPayload
                          compiledRealization.containmentEvidence
                      let sourceTyping :
                          DOTCapture.ModalIntersections.Value.HasType
                            environment (.object object payload)
                              object.formedType :=
                        .object realization payloadCompiled.sourceTyping
                          payloadShape payloadCapture objectCapture
                      let adapterAdministrative := adapter.erase_admin
                        payloadCompiled.term.erase payloadCompiled.isValue.erase
                      let packageAdministrative :
                          ManySortedFC.Runtime.AdministrativeEq package.erase
                            (context.core.eraseValue
                              (.object object payload)) := by
                        change ManySortedFC.Runtime.AdministrativeEq
                          (adapter.erase payloadCompiled.term.erase)
                          (context.core.eraseValue payload)
                        exact adapterAdministrative.trans payloadCompiled.erasure
                      match finalized : CompilerArtifacts.finishValue?
                          context.core sourceTyping package packageAdministrative
                      with
                      | none => none
                      | some result =>
                          some
                            { realizedPrepared
                              realizationAgreement
                              realizationAgreementChecked
                              shape
                              shapeCompiled
                              payloadCaptureEvidence
                              payloadCaptureCompiled
                              adapter
                              adapterEquation
                              adaptedPayload
                              adaptedPayloadEquation := rfl
                              package
                              packageEquation := rfl
                              administrative := packageAdministrative
                              result
                              finalized }

end DOTCaptureToManySortedFC.ModalIntersections.PositiveObjectCompilation
