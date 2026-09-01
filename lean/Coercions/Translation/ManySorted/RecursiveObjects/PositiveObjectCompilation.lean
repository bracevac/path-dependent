import Coercions.Translation.ManySorted.RecursiveObjects.Model
import Coercions.Translation.ManySorted.ModalIntersections.CompilerArtifacts

/-!
# Recursive positive objects with arbitrary value payloads

This module is the value-only finalization boundary for cumulative recursive
objects.  Recursive signature preparation and model checking happen first.
The caller then supplies an ordinary compiled source value together with the
source shape and capture inclusions that relate its type to the recursively
realized representation.

The realized source representation is translated independently and compared
with the representation obtained by instantiating the checked recursive
model.  Only after that exact substitution-boundary check succeeds are the
two source inclusions compiled, a value-only `retagCapture` adapter built, and
the existential package submitted to the standalone target checker.  Static
recursive witnesses, evidence, adaptation, and packaging remain runtime
administrative; the payload is neither duplicated nor reordered.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.PositiveObjectCompilation

open DOTCaptureToManySortedFC.RecursiveObjects
open DOTCaptureToManySortedFC.RecursiveObjects.Encoding
open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
open DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence

namespace Src

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv
abbrev Ctx := DOTCapture.ModalIntersections.Ctx
abbrev Value := DOTCapture.ModalIntersections.Value
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Signature :=
  DOTCaptureToManySortedFC.RecursiveObjects.Source.Signature
abbrev Realization {scope : Sig} (context : Ctx scope)
    (signature : Signature scope) :=
  DOTCaptureToManySortedFC.RecursiveObjects.Source.Realization context signature

end Src

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Ty := ManySortedFC.Ty
abbrev Tm := ManySortedFC.Tm
abbrev Adapter := ManySortedFC.Adapter

end Target

/-! ## Independent representation preparation and agreement -/

/-- The only payload compiler context admitted by recursive finalization.
It changes static interpretation, not the ambient target context: type labels
denote their simultaneous `recProj` witnesses and capture labels denote the
concrete witnesses already selected during recursive preparation. -/
def payloadContext {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    (prepared : Encoding.Prepared context.core.layout signature valid
      realization) : EvidenceContext.Context environment targetScope :=
  context.withLocalModel prepared.targetLocalModel

/-- Independently translate the recursively realized source representation in
the canonical payload context. -/
def prepareRealizedRepresentation? {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (source : Src.Ty sourceScope) : Option (PreparedTerm core source) :=
  match prepared : ObjectContract.translateType core.layout source with
  | .error _ => none
  | .ok targetType => some { targetType, prepared }

/-- Install the explicit outer capture required by the cumulative object
contract on the independently translated realized representation. -/
def explicitRealizedTarget {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {source : Src.Ty sourceScope} (prepared : PreparedTerm core source) :
    Target.Ty targetScope :=
  prepared.targetType.withCapture prepared.targetType.outerCapture

/-- The recursively realized representation obtained by instantiating the
checked cumulative object model. -/
def realizedTarget {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : EvidenceContext.Context environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    {prepared : Encoding.Prepared context.core.layout signature valid
      realization}
    {ambient : AmbientCompiler context.core}
    (checkedModel : Model.CheckedModel context.core prepared ambient) :
    Target.Ty targetScope :=
  prepared.object.representation.instantiateStatic
    checkedModel.model.symbols

abbrev TargetAgreement {scope : Target.Sig} :=
  DOTCaptureToManySortedFC.ModalIntersections.PositiveObjectCompilation.TargetAgreement
    (scope := scope)

abbrev checkTargetAgreement? {scope : Target.Sig} :=
  DOTCaptureToManySortedFC.ModalIntersections.PositiveObjectCompilation.checkTargetAgreement?
    (scope := scope)

abbrev payloadAdapter? {scope : Target.Sig} :=
  DOTCaptureToManySortedFC.ModalIntersections.PositiveObjectCompilation.payloadAdapter?
    (scope := scope)

/-- The recursive finalizer only asks the ordinary positive-object adapter
builder for a capture retag.  A successful adapter therefore erases
literally, not merely up to administrative equivalence. -/
theorem payloadAdapter_erases {scope : Target.Sig}
    {source realized : Target.Ty scope}
    {shape : ManySortedFC.Evidence (.inclusion .type) scope}
    {capture : ManySortedFC.Evidence (.inclusion .capture) scope}
    {adapter : Target.Adapter scope}
    (compiled : payloadAdapter? source realized shape capture = some adapter)
    {runtimeScope : Nat} (term : ManySortedFC.Runtime.Tm runtimeScope) :
    adapter.erase term = term := by
  cases realized <;>
    simp [payloadAdapter?,
      DOTCaptureToManySortedFC.ModalIntersections.PositiveObjectCompilation.payloadAdapter?]
      at compiled
  case capturing =>
    subst adapter
    rfl

/-! ## Checked arbitrary-payload package -/

/-- A recursive object package finalized from an already compiled source
value.  The output retains every independently checked boundary needed by a
later cumulative recursive-object compiler branch. -/
structure CompiledObject {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    (prepared : Encoding.Prepared context.core.layout signature valid
      realization)
    (ambient : AmbientCompiler context.core)
    (checkedModel : Model.CheckedModel context.core prepared ambient)
    {payload : Src.Value sourceScope} {payloadType : Src.Ty sourceScope}
    (payloadShape : DOTCapture.ModalIntersections.TypeIncludes
      environment.bindings payloadType.stripCapture
        (signature.realizedRepresentation
          realization.captures).stripCapture)
    (payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings payloadType.outerCapture
        (signature.realizedRepresentation
          realization.captures).outerCapture)
    (payloadCompiled : CompilerArtifacts.CompiledValue
      (payloadContext context prepared).core payload payloadType) where
  realizedPrepared : PreparedTerm (payloadContext context prepared).core
    (signature.realizedRepresentation realization.captures)
  realizationAgreement : TargetAgreement
    (explicitRealizedTarget realizedPrepared)
    (realizedTarget checkedModel)
  realizationAgreementChecked : checkTargetAgreement?
    (explicitRealizedTarget realizedPrepared)
    (realizedTarget checkedModel) = some realizationAgreement
  shape : CompiledInclusion (payloadContext context prepared).core
    (.type payloadType.stripCapture)
    (.type (signature.realizedRepresentation
      realization.captures).stripCapture)
  shapeCompiled : compileIncludes?
    (payloadContext context prepared).compiler.leaves payloadShape = some shape
  capture : CompiledInclusion (payloadContext context prepared).core
    (.capture payloadType.outerCapture)
    (.capture (signature.realizedRepresentation
      realization.captures).outerCapture)
  captureCompiled : compileIncludes?
    (payloadContext context prepared).compiler.leaves payloadCapture =
      some capture
  adapter : Target.Adapter targetScope
  adapterEquation : payloadAdapter? payloadCompiled.targetType
    (realizedTarget checkedModel) shape.evidence capture.evidence = some adapter
  adaptedPayload : Target.Tm targetScope
  adaptedPayloadEquation : adaptedPayload =
    .adapt payloadCompiled.term adapter
  package : Target.Tm targetScope
  packageEquation : package =
    .pack prepared.object.theory prepared.object.representation
      prepared.object.outerCapture checkedModel.model.symbols
      checkedModel.model.evidence adaptedPayload
      checkedModel.packageContainmentEvidence
  administrative : ManySortedFC.Runtime.AdministrativeEq package.erase
    (context.core.eraseValue (.recursiveObject signature.objectType payload))
  result : CompilerArtifacts.CompiledValue context.core
    (.recursiveObject signature.objectType payload)
    signature.objectType.formedType
  finalized : CompilerArtifacts.finishValue? context.core
    (.recursiveObject valid realization payloadCompiled.sourceTyping
      payloadShape payloadCapture)
    package administrative = some result

/-- Finalize one recursive positive object.  All logical and structural
syntax is accepted independently; failure at any boundary is explicit in the
result rather than hidden in a trusted cast. -/
def compile? {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    (prepared : Encoding.Prepared context.core.layout signature valid
      realization)
    (ambient : AmbientCompiler context.core)
    (checkedModel : Model.CheckedModel context.core prepared ambient)
    {payload : Src.Value sourceScope} {payloadType : Src.Ty sourceScope}
    (payloadShape : DOTCapture.ModalIntersections.TypeIncludes
      environment.bindings payloadType.stripCapture
        (signature.realizedRepresentation
          realization.captures).stripCapture)
    (payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings payloadType.outerCapture
        (signature.realizedRepresentation
          realization.captures).outerCapture)
    (payloadCompiled : CompilerArtifacts.CompiledValue
      (payloadContext context prepared).core payload payloadType) :
    Option (CompiledObject context prepared ambient checkedModel payloadShape
      payloadCapture payloadCompiled) :=
  match prepareRealizedRepresentation? (payloadContext context prepared).core
      (signature.realizedRepresentation realization.captures) with
  | none => none
  | some realizedPrepared =>
      match realizationAgreementChecked : checkTargetAgreement?
          (explicitRealizedTarget realizedPrepared)
          (realizedTarget checkedModel) with
      | none => none
      | some realizationAgreement =>
          match shapeCompiled : compileIncludes?
              (payloadContext context prepared).compiler.leaves
                payloadShape with
          | none => none
          | some shape =>
              match captureCompiled : compileIncludes?
                  (payloadContext context prepared).compiler.leaves
                    payloadCapture with
              | none => none
              | some capture =>
                  match adapterEquation : payloadAdapter?
                      payloadCompiled.targetType (realizedTarget checkedModel)
                        shape.evidence capture.evidence with
                  | none => none
                  | some adapter =>
                      let adaptedPayload : Target.Tm targetScope :=
                        .adapt payloadCompiled.term adapter
                      let package : Target.Tm targetScope :=
                        checkedModel.packageTerm adaptedPayload
                      let administrative :
                          ManySortedFC.Runtime.AdministrativeEq package.erase
                            (context.core.eraseValue
                              (.recursiveObject signature.objectType payload)) := by
                        change ManySortedFC.Runtime.AdministrativeEq
                          (adapter.erase payloadCompiled.term.erase)
                          (context.core.eraseValue payload)
                        simpa only [payloadContext,
                          EvidenceContext.Context.withLocalModel_eraseValue]
                          using
                            (adapter.erase_admin
                              payloadCompiled.term.erase
                              payloadCompiled.isValue.erase).trans
                                payloadCompiled.erasure
                      let sourceTyping :
                          DOTCapture.ModalIntersections.Value.HasType
                            environment
                            (.recursiveObject signature.objectType payload)
                            signature.objectType.formedType :=
                        .recursiveObject valid realization
                          payloadCompiled.sourceTyping payloadShape
                          payloadCapture
                      match finalized : CompilerArtifacts.finishValue?
                          context.core sourceTyping package administrative with
                      | none => none
                      | some result =>
                          some
                            { realizedPrepared
                              realizationAgreement
                              realizationAgreementChecked
                              shape
                              shapeCompiled
                              capture
                              captureCompiled
                              adapter
                              adapterEquation
                              adaptedPayload
                              adaptedPayloadEquation := rfl
                              package
                              packageEquation := rfl
                              administrative
                              result
                              finalized }

namespace CompiledObject

/-- The term returned by the final standalone-checker boundary is exactly the
recursive package submitted to it.  This connects the raw-package lemmas
below to the artifact returned by the cumulative compiler. -/
theorem result_term_eq_package {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : EvidenceContext.Context environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    {prepared : Encoding.Prepared context.core.layout signature valid
      realization}
    {ambient : AmbientCompiler context.core}
    {checkedModel : Model.CheckedModel context.core prepared ambient}
    {payload : Src.Value sourceScope} {payloadType : Src.Ty sourceScope}
    {payloadShape : DOTCapture.ModalIntersections.TypeIncludes
      environment.bindings payloadType.stripCapture
        (signature.realizedRepresentation
          realization.captures).stripCapture}
    {payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings payloadType.outerCapture
        (signature.realizedRepresentation
          realization.captures).outerCapture}
    {payloadCompiled : CompilerArtifacts.CompiledValue
      (payloadContext context prepared).core payload payloadType}
    (compiled : CompiledObject context prepared ambient checkedModel
      payloadShape payloadCapture payloadCompiled) :
    compiled.result.term = compiled.package := by
  have finalized := compiled.finalized
  unfold CompilerArtifacts.finishValue? at finalized
  split at finalized <;> try contradiction
  split at finalized <;> try contradiction
  split at finalized <;> try contradiction
  split at finalized <;> try contradiction
  split at finalized <;> try contradiction
  injection finalized with objectEq
  simpa using (congrArg (fun artifact => artifact.term) objectEq).symm

/-- Recursive model instantiation, `C_rep` evidence, value retagging, and the
existential package add no runtime syntax.  Any non-literal administrative
behavior in the cumulative result can therefore come only from the already
compiled payload, not from recursive-object finalization. -/
theorem package_erases_payload {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : EvidenceContext.Context environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    {prepared : Encoding.Prepared context.core.layout signature valid
      realization}
    {ambient : AmbientCompiler context.core}
    {checkedModel : Model.CheckedModel context.core prepared ambient}
    {payload : Src.Value sourceScope} {payloadType : Src.Ty sourceScope}
    {payloadShape : DOTCapture.ModalIntersections.TypeIncludes
      environment.bindings payloadType.stripCapture
        (signature.realizedRepresentation
          realization.captures).stripCapture}
    {payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings payloadType.outerCapture
        (signature.realizedRepresentation
          realization.captures).outerCapture}
    {payloadCompiled : CompilerArtifacts.CompiledValue
      (payloadContext context prepared).core payload payloadType}
    (compiled : CompiledObject context prepared ambient checkedModel
      payloadShape payloadCapture payloadCompiled) :
    compiled.package.erase = payloadCompiled.term.erase := by
  rw [compiled.packageEquation, ManySortedFC.Tm.erase_pack,
    compiled.adaptedPayloadEquation, ManySortedFC.Tm.erase_adapt]
  exact payloadAdapter_erases compiled.adapterEquation payloadCompiled.term.erase

/-- The emitted checked artifact, not merely its pre-check candidate, erases
literally to the already compiled payload. -/
theorem result_erases_payload {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : EvidenceContext.Context environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    {prepared : Encoding.Prepared context.core.layout signature valid
      realization}
    {ambient : AmbientCompiler context.core}
    {checkedModel : Model.CheckedModel context.core prepared ambient}
    {payload : Src.Value sourceScope} {payloadType : Src.Ty sourceScope}
    {payloadShape : DOTCapture.ModalIntersections.TypeIncludes
      environment.bindings payloadType.stripCapture
        (signature.realizedRepresentation
          realization.captures).stripCapture}
    {payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings payloadType.outerCapture
        (signature.realizedRepresentation
          realization.captures).outerCapture}
    {payloadCompiled : CompilerArtifacts.CompiledValue
      (payloadContext context prepared).core payload payloadType}
    (compiled : CompiledObject context prepared ambient checkedModel
      payloadShape payloadCapture payloadCompiled) :
    compiled.result.term.erase = payloadCompiled.term.erase := by
  rw [compiled.result_term_eq_package]
  exact compiled.package_erases_payload

/-- Recursive finalization is literally transparent: the raw package has
exact source erasure exactly when the already compiled payload does.  This is
an equivalence, not merely a sufficient condition. -/
theorem package_exact_erasure_iff {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : EvidenceContext.Context environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    {prepared : Encoding.Prepared context.core.layout signature valid
      realization}
    {ambient : AmbientCompiler context.core}
    {checkedModel : Model.CheckedModel context.core prepared ambient}
    {payload : Src.Value sourceScope} {payloadType : Src.Ty sourceScope}
    {payloadShape : DOTCapture.ModalIntersections.TypeIncludes
      environment.bindings payloadType.stripCapture
        (signature.realizedRepresentation
          realization.captures).stripCapture}
    {payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings payloadType.outerCapture
        (signature.realizedRepresentation
          realization.captures).outerCapture}
    {payloadCompiled : CompilerArtifacts.CompiledValue
      (payloadContext context prepared).core payload payloadType}
    (compiled : CompiledObject context prepared ambient checkedModel
      payloadShape payloadCapture payloadCompiled) :
    compiled.package.erase = context.core.eraseValue
        (.recursiveObject signature.objectType payload) ↔
      payloadCompiled.term.erase = context.core.eraseValue payload := by
  rw [compiled.package_erases_payload]
  rfl

/-- The independently checked artifact has exact source erasure exactly when
its compiled payload does.  Recursive names, equations, representation-capture
evidence, retagging, and packaging contribute no additional discrepancy. -/
theorem result_exact_erasure_iff {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : EvidenceContext.Context environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    {prepared : Encoding.Prepared context.core.layout signature valid
      realization}
    {ambient : AmbientCompiler context.core}
    {checkedModel : Model.CheckedModel context.core prepared ambient}
    {payload : Src.Value sourceScope} {payloadType : Src.Ty sourceScope}
    {payloadShape : DOTCapture.ModalIntersections.TypeIncludes
      environment.bindings payloadType.stripCapture
        (signature.realizedRepresentation
          realization.captures).stripCapture}
    {payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings payloadType.outerCapture
        (signature.realizedRepresentation
          realization.captures).outerCapture}
    {payloadCompiled : CompilerArtifacts.CompiledValue
      (payloadContext context prepared).core payload payloadType}
    (compiled : CompiledObject context prepared ambient checkedModel
      payloadShape payloadCapture payloadCompiled) :
    compiled.result.term.erase = context.core.eraseValue
        (.recursiveObject signature.objectType payload) ↔
      payloadCompiled.term.erase = context.core.eraseValue payload := by
  rw [compiled.result_erases_payload]
  rfl

/-- Exact payload erasure lifts directly through recursive finalization.  The
source object wrapper erases to the same payload, and changing only the local
static interpretation does not alter source runtime variables. -/
theorem package_exact_erasure {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : EvidenceContext.Context environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    {prepared : Encoding.Prepared context.core.layout signature valid
      realization}
    {ambient : AmbientCompiler context.core}
    {checkedModel : Model.CheckedModel context.core prepared ambient}
    {payload : Src.Value sourceScope} {payloadType : Src.Ty sourceScope}
    {payloadShape : DOTCapture.ModalIntersections.TypeIncludes
      environment.bindings payloadType.stripCapture
        (signature.realizedRepresentation
          realization.captures).stripCapture}
    {payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings payloadType.outerCapture
        (signature.realizedRepresentation
          realization.captures).outerCapture}
    {payloadCompiled : CompilerArtifacts.CompiledValue
      (payloadContext context prepared).core payload payloadType}
    (compiled : CompiledObject context prepared ambient checkedModel
      payloadShape payloadCapture payloadCompiled)
    (payloadExact : payloadCompiled.term.erase =
      context.core.eraseValue payload) :
    compiled.package.erase = context.core.eraseValue
      (.recursiveObject signature.objectType payload) := by
  calc
    compiled.package.erase = payloadCompiled.term.erase :=
      compiled.package_erases_payload
    _ = context.core.eraseValue payload := payloadExact
    _ = context.core.eraseValue
        (.recursiveObject signature.objectType payload) := rfl

/-- Conditional literal erasure for the emitted recursive artifact.  The
condition is exactly the underlying payload compiler's literal-erasure fact;
recursive model evidence, capture retagging, and packaging add no further
runtime administration. -/
theorem result_exact_erasure {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : EvidenceContext.Context environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    {prepared : Encoding.Prepared context.core.layout signature valid
      realization}
    {ambient : AmbientCompiler context.core}
    {checkedModel : Model.CheckedModel context.core prepared ambient}
    {payload : Src.Value sourceScope} {payloadType : Src.Ty sourceScope}
    {payloadShape : DOTCapture.ModalIntersections.TypeIncludes
      environment.bindings payloadType.stripCapture
        (signature.realizedRepresentation
          realization.captures).stripCapture}
    {payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings payloadType.outerCapture
        (signature.realizedRepresentation
          realization.captures).outerCapture}
    {payloadCompiled : CompilerArtifacts.CompiledValue
      (payloadContext context prepared).core payload payloadType}
    (compiled : CompiledObject context prepared ambient checkedModel
      payloadShape payloadCapture payloadCompiled)
    (payloadExact : payloadCompiled.term.erase =
      context.core.eraseValue payload) :
    compiled.result.term.erase = context.core.eraseValue
      (.recursiveObject signature.objectType payload) := by
  rw [compiled.result_term_eq_package]
  exact compiled.package_exact_erasure payloadExact

/-- Public standalone checker certificate for the completed recursive
package. -/
theorem checkerAccepts {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : EvidenceContext.Context environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    {prepared : Encoding.Prepared context.core.layout signature valid
      realization}
    {ambient : AmbientCompiler context.core}
    {checkedModel : Model.CheckedModel context.core prepared ambient}
    {payload : Src.Value sourceScope} {payloadType : Src.Ty sourceScope}
    {payloadShape : DOTCapture.ModalIntersections.TypeIncludes
      environment.bindings payloadType.stripCapture
        (signature.realizedRepresentation
          realization.captures).stripCapture}
    {payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings payloadType.outerCapture
        (signature.realizedRepresentation
          realization.captures).outerCapture}
    {payloadCompiled : CompilerArtifacts.CompiledValue
      (payloadContext context prepared).core payload payloadType}
    (compiled : CompiledObject context prepared ambient checkedModel
      payloadShape payloadCapture payloadCompiled) :
    ManySortedFC.Tm.synth context.core.target compiled.result.term =
      some (.empty, compiled.result.targetType) :=
  compiled.result.checkerAccepts

end CompiledObject

end DOTCaptureToManySortedFC.RecursiveObjects.PositiveObjectCompilation
