import Coercions.Translation.ManySorted.ModalIntersections.PositiveObjectCompilation

/-!
# Executable positive-object finalizer regressions

The regressions cover bare, explicitly captured, member-dependent, and
genuinely capturing representations. Every package carries one runtime
payload at an explicit `C_rep` type, crosses the independent model and term
checkers, and erases to the source payload. Malformed models and packages are
rejected directly by the standalone target checker.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.PositiveObjectCompilationExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
open DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence
open DOTCaptureToManySortedFC.ModalIntersections.PositiveObjectCompilation

def ambient : AmbientCompiler Core.nil where
  compile := fun proof =>
    (compileIncludes? Context.nil.compiler.leaves proof).map
      (fun compiled => compiled.evidence)

def model : DOTCapture.ModalIntersections.LocalModel.Model [] where
  typeMember := fun _ => .one
  captureMember := fun _ => .empty

def payloadTyping : DOTCapture.ModalIntersections.Value.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil
    (.unit : DOTCapture.ModalIntersections.Value []) .one :=
  .unit

def payload? := CompilerArtifacts.finishValueExact? Core.nil payloadTyping
  (.unit : ManySortedFC.Tm []) rfl

example : payload?.isSome = true := by native_decide

def payload := payload?.get (by native_decide)

/-- A cumulative package endpoint must be explicitly captured. -/
example : payloadAdapter?
    ((.capturing .empty .one) : ManySortedFC.Ty []) .one
    (.inclusionRefl (.type .one))
    (.inclusionRefl (.capture .empty)) =
      (none : Option (ManySortedFC.Adapter [])) := by
  rfl

namespace Bare

def source : DOTCapture.ModalIntersections.ObjectType [] :=
  .mk .empty .one .empty

def target : ObjectContract.PreparedObject [] where
  encoding := DOTCaptureToManySortedFC.Intersections.Encoding.encode
    { symbols := [], entries := [] }
  sourceRepresentationAtNames := .one
  outerCapture := .empty

def prepared : PreparedContractedObject Core.nil source where
  object := target
  prepared := rfl

def realization : DOTCapture.ModalIntersections.ObjectType.Realization
    DOTCapture.ModalIntersections.Ctx.nil source where
  model := model
  constraints := .empty

def objectCapture : DOTCapture.ModalIntersections.CaptureIncludes
    DOTCapture.ModalIntersections.Ctx.nil
    (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation source
      realization.model).outerCapture source.outerCapture :=
  .refl

def realization? := ObjectEvidence.compileContractedRealization? prepared
  ambient realization objectCapture

example : realization?.isSome = true := by native_decide

def checkedRealization := realization?.get (by native_decide)

def payloadShape : DOTCapture.ModalIntersections.TypeIncludes
    DOTCapture.ModalIntersections.Ctx.nil .one
    (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation source
      realization.model).stripCapture :=
  .refl

def payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
    DOTCapture.ModalIntersections.Ctx.nil .empty
    (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation source
      realization.model).outerCapture :=
  .refl

def compiled? := PositiveObjectCompilation.compile? (payloadType := .one)
  Context.nil prepared
  ambient realization payloadShape payloadCapture objectCapture
  checkedRealization payload

example : compiled?.isSome = true := by native_decide

def compiled := compiled?.get (by native_decide)

example : compiled.adapter =
    (.retagCapture .one .empty .one
      (.inclusionRefl (.capture .empty))
      (.inclusionRefl (.type .one)) : ManySortedFC.Adapter []) := by
  native_decide

example : ManySortedFC.Tm.check Core.nil.target compiled.result.term =
    some compiled.result.checked :=
  compiled.result.accepted

example : ManySortedFC.Tm.checkValue compiled.result.term =
    some compiled.result.valueChecked :=
  compiled.result.valueAccepted

/-- The final artifact relates target erasure to the independently defined
source object erasure, not to target syntax reconstructed from compilation. -/
example : ManySortedFC.Runtime.AdministrativeEq compiled.result.term.erase
    (Core.nil.eraseValue
      (.object source (.unit : DOTCapture.ModalIntersections.Value []))) :=
  compiled.result.erasure

example : Core.nil.eraseValue
    (.object source (.unit : DOTCapture.ModalIntersections.Value [])) =
      .unit := rfl

example : compiled.package.erase = (.unit : ManySortedFC.Runtime.Tm 0) := by
  native_decide

/-- The package model interprets the unique internal capture as the realized
representation capture. -/
example : checkedRealization.model.symbols =
    .cons (.capture .empty) .nil := by
  native_decide

example : checkedRealization.candidates =
    .captureEquality (.equalityRefl
      (.capture (target.actualCapture checkedRealization.memberSymbols))) ::
    .capture checkedRealization.containmentEvidence ::
      checkedRealization.memberCandidates :=
  checkedRealization.candidates_eq

example : ManySortedFC.Theory.checkModel Core.nil.target target.theory
    checkedRealization.model.symbols checkedRealization.model.evidence =
      some checkedRealization.model.checked :=
  checkedRealization.model.checkerAcceptance

example : target.representationAtNames =
    (.capturing (.cvar .here) .one : ManySortedFC.Ty [.symbol .capture]) :=
  rfl

/-- Omitting either generated contract obligation cannot produce a checked
model, even though the user interface itself is empty. -/
example : ObjectEvidence.checkContractedModel? Core.nil target
    checkedRealization.model.symbols [] = none := by
  native_decide

example : ObjectEvidence.checkContractedModel? Core.nil target
    checkedRealization.model.symbols
      [.captureEquality (.equalityRefl (.capture .empty))] = none := by
  native_decide

/-- A bare runtime representation is rejected: the package expects the
explicit type `empty · Unit`. -/
def barePayloadPackage : ManySortedFC.Tm [] :=
  .pack target.theory target.representation target.outerCapture
    checkedRealization.model.symbols checkedRealization.model.evidence .unit
    checkedRealization.containmentEvidence

example : ManySortedFC.Tm.check ManySortedFC.Ctx.nil barePayloadPackage =
    none := by
  native_decide

/-- Package evidence is intrinsically ambient-scoped, so it cannot cite the
contract assumptions that the package would export. -/
example : ManySortedFC.BVar []
    (.evidence (.inclusion .capture)) -> False := by
  intro evidence
  nomatch evidence

end Bare

namespace Captured

def source : DOTCapture.ModalIntersections.ObjectType [] :=
  .mk .empty (.capturing .empty .one) .empty

def target : ObjectContract.PreparedObject [] where
  encoding := DOTCaptureToManySortedFC.Intersections.Encoding.encode
    { symbols := [], entries := [] }
  sourceRepresentationAtNames := .capturing .empty .one
  outerCapture := .empty

def prepared : PreparedContractedObject Core.nil source where
  object := target
  prepared := rfl

def realization : DOTCapture.ModalIntersections.ObjectType.Realization
    DOTCapture.ModalIntersections.Ctx.nil source where
  model := model
  constraints := .empty

def objectCapture : DOTCapture.ModalIntersections.CaptureIncludes
    DOTCapture.ModalIntersections.Ctx.nil
    (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation source
      realization.model).outerCapture source.outerCapture :=
  .refl

def realization? := ObjectEvidence.compileContractedRealization? prepared
  ambient realization objectCapture

example : realization?.isSome = true := by native_decide

def checkedRealization := realization?.get (by native_decide)

def payloadShape : DOTCapture.ModalIntersections.TypeIncludes
    DOTCapture.ModalIntersections.Ctx.nil .one
    (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation source
      realization.model).stripCapture :=
  .refl

def payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
    DOTCapture.ModalIntersections.Ctx.nil .empty
    (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation source
      realization.model).outerCapture :=
  .refl

def compiled? := PositiveObjectCompilation.compile? (payloadType := .one)
  Context.nil prepared
  ambient realization payloadShape payloadCapture objectCapture
  checkedRealization payload

example : compiled?.isSome = true := by native_decide

def compiled := compiled?.get (by native_decide)

/-- A captured target representation uses the explicit two-component retag
adapter rather than a computation-level transport. -/
example : compiled.adapter =
    (.retagCapture .one .empty .one
      (.inclusionRefl (.capture .empty))
      (.inclusionRefl (.type .one)) : ManySortedFC.Adapter []) := by
  native_decide

example : ManySortedFC.Tm.checkValue compiled.result.term =
    some compiled.result.valueChecked :=
  compiled.result.valueAccepted

example : ManySortedFC.Runtime.AdministrativeEq compiled.result.term.erase
    (Core.nil.eraseValue
      (.object source (.unit : DOTCapture.ModalIntersections.Value []))) :=
  compiled.result.erasure

example : compiled.package.erase = (.unit : ManySortedFC.Runtime.Tm 0) := by
  native_decide

end Captured

/-! ## A representation with an actual runtime dependency -/

namespace CapturingPayload

abbrev Scope : DOTCapture.ModalIntersections.Sig := [] ▹ .term

def boundType : DOTCapture.ModalIntersections.Ty [] :=
  .capturing .empty .one

def boundPrepared? : Option (PreparedTerm Context.nil.core boundType) :=
  match prepared : ObjectContract.translateType Context.nil.core.layout
      boundType with
  | .error _ => none
  | .ok targetType => some { targetType, prepared }

example : boundPrepared?.isSome = true := by native_decide

def boundPrepared := boundPrepared?.get (by native_decide)

def context := Context.nil.extendPlain boundType (by trivial) boundPrepared

def environment : DOTCapture.ModalIntersections.TypingEnv Scope :=
  DOTCapture.ModalIntersections.TypingEnv.nil.extendTerm boundType

def actualCapture : DOTCapture.ModalIntersections.Capture Scope :=
  .singleton (.var .here)

def source : DOTCapture.ModalIntersections.ObjectType Scope :=
  .mk .empty (.capturing actualCapture .one) actualCapture

def preparedResult := ObjectContract.prepare context.core.layout source

example : preparedResult.toOption.isSome = true := by native_decide

def target : ObjectContract.PreparedObject [ManySortedFC.BinderKind.term] :=
  preparedResult.toOption.get (by native_decide)

def prepared : PreparedContractedObject context.core source where
  object := target
  prepared := by rfl

def ambient : AmbientCompiler context.core where
  compile := fun proof =>
    (compileIncludes? context.compiler.leaves proof).map
      (fun compiled => compiled.evidence)

def model : DOTCapture.ModalIntersections.LocalModel.Model Scope where
  typeMember := fun _ => .one
  captureMember := fun _ => .empty

def realization : DOTCapture.ModalIntersections.ObjectType.Realization
    environment.bindings source where
  model := model
  constraints := .empty

def payloadTyping : DOTCapture.ModalIntersections.Value.HasType environment
    (.var .here)
    (.capturing actualCapture .one) :=
  .var

def payload? := CompilerArtifacts.finishValueExact? context.core payloadTyping
  (.var .here : ManySortedFC.Tm [ManySortedFC.BinderKind.term]) rfl

example : payload?.isSome = true := by native_decide

def payload := payload?.get (by native_decide)

def payloadShape : DOTCapture.ModalIntersections.TypeIncludes
    environment.bindings .one
    (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation source
      realization.model).stripCapture :=
  .refl

def payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
    environment.bindings actualCapture
    (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation source
      realization.model).outerCapture :=
  .refl

def objectCapture : DOTCapture.ModalIntersections.CaptureIncludes
    environment.bindings
    (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation source
      realization.model).outerCapture source.outerCapture :=
  .refl

def realization? := ObjectEvidence.compileContractedRealization? prepared
  ambient realization objectCapture

example : realization?.isSome = true := by native_decide

def checkedRealization := realization?.get (by native_decide)

def compiled? := PositiveObjectCompilation.compile?
  (payloadType := .capturing actualCapture .one) context prepared ambient
  realization payloadShape payloadCapture objectCapture checkedRealization
  payload

example : compiled?.isSome = true := by native_decide

def compiled := compiled?.get (by native_decide)

/-- `C_rep` is interpreted as the payload's real singleton dependency, not
as empty or as an inferred property of a bare representation. -/
example : checkedRealization.model.symbols =
    .cons (.capture (.singleton .here)) .nil := by
  native_decide

example : ManySortedFC.Tm.check context.core.target compiled.result.term =
    some compiled.result.checked :=
  compiled.result.accepted

example : ManySortedFC.Runtime.AdministrativeEq compiled.result.term.erase
    (context.core.eraseValue
      (.object source (.var .here : DOTCapture.ModalIntersections.Value Scope))) :=
  compiled.result.erasure

example : compiled.result.term.erase =
    (.var ⟨0, by omega⟩ : ManySortedFC.Runtime.Tm 1) := by
  native_decide

end CapturingPayload

/-! ## Wrong-direction containment is not accepted -/

namespace WrongDirection

open CapturingPayload

def source : DOTCapture.ModalIntersections.ObjectType Scope :=
  .mk .empty .one actualCapture

def preparedResult := ObjectContract.prepare context.core.layout source

example : preparedResult.toOption.isSome = true := by native_decide

def target : ObjectContract.PreparedObject [ManySortedFC.BinderKind.term] :=
  preparedResult.toOption.get (by native_decide)

def symbols : ManySortedFC.SymbolArgs
    [ManySortedFC.BinderKind.term] target.symbols :=
  .cons (.capture .empty) .nil

/-- `captureVariable` proves the reverse proposition
`{x} <= empty`. It cannot fill the required `empty <= {x}` coordinate. -/
def wrongCandidates : List (ModelEvidence
    [ManySortedFC.BinderKind.term]) :=
  [ .captureEquality (.equalityRefl (.capture .empty)),
    .capture (.captureVariable .here) ]

example : ObjectEvidence.checkContractedModel? context.core target symbols
    wrongCandidates = none := by
  native_decide

end WrongDirection

/-! ## A nonempty, member-dependent representation -/

namespace MemberDependent

/-- The runtime representation is the local type member itself, not a closed
ambient type.  Realization replaces that local occurrence with the supplied
model's `Unit` witness. -/
def source : DOTCapture.ModalIntersections.ObjectType [] :=
  .mk (.typeMember 3 .one .one) (.ref (.localTypeMember 3)) .empty

example : source.representation = .ref (.localTypeMember 3) := rfl

def preparedResult := ObjectContract.prepare Core.nil.layout source

example : preparedResult.toOption.isSome = true := by native_decide

def target : ObjectContract.PreparedObject [] :=
  preparedResult.toOption.get (by native_decide)

def prepared : PreparedContractedObject Core.nil source where
  object := target
  prepared := by rfl

def realization : DOTCapture.ModalIntersections.ObjectType.Realization
    DOTCapture.ModalIntersections.Ctx.nil source where
  model := model
  constraints := .typeMember .refl .refl

def objectCapture : DOTCapture.ModalIntersections.CaptureIncludes
    DOTCapture.ModalIntersections.Ctx.nil
    (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation source
      realization.model).outerCapture source.outerCapture :=
  .refl

def realization? := ObjectEvidence.compileContractedRealization? prepared
  ambient realization objectCapture

example : realization?.isSome = true := by native_decide

def checkedRealization := realization?.get (by native_decide)

def payloadShape : DOTCapture.ModalIntersections.TypeIncludes
    DOTCapture.ModalIntersections.Ctx.nil .one
    (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation source
      realization.model).stripCapture :=
  .refl

def payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
    DOTCapture.ModalIntersections.Ctx.nil .empty
    (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation source
      realization.model).outerCapture :=
  .refl

def compiled? := PositiveObjectCompilation.compile? (payloadType := .one)
  Context.nil prepared
  ambient realization payloadShape payloadCapture objectCapture
  checkedRealization payload

example : compiled?.isSome = true := by native_decide

def compiled := compiled?.get (by native_decide)

/-- This is the previously untested static-substitution boundary: preparation
after source realization agrees with instantiating the member-dependent target
representation by the independently checked model. -/
example : explicitRealizedTarget compiled.realizedPrepared =
    realizedTarget checkedRealization :=
  compiled.realizationAgreement.exact

example : checkTargetAgreement?
    (explicitRealizedTarget compiled.realizedPrepared)
    (realizedTarget checkedRealization) =
      some compiled.realizationAgreement :=
  compiled.realizationAgreementChecked

example : ManySortedFC.Tm.check Core.nil.target compiled.result.term =
    some compiled.result.checked :=
  compiled.result.accepted

example : ManySortedFC.Runtime.AdministrativeEq compiled.result.term.erase
    (Core.nil.eraseValue
      (.object source (.unit : DOTCapture.ModalIntersections.Value []))) :=
  compiled.result.erasure

end MemberDependent

/-! ## Static-substitution agreement rejection -/

/-- A prepared endpoint that disagrees with its instantiated representation
is rejected at the explicit comparison boundary; no equality is assumed. -/
example : checkTargetAgreement? (.top : ManySortedFC.Ty []) .one = none := by
  native_decide

/-! ## Standalone checker rejection -/

/-- The package has the right model and shape, but its value adapter claims
that the unit payload starts at `Top`. -/
def wrongPayloadAdapter : ManySortedFC.Tm [] :=
  .pack Bare.target.theory Bare.target.representation
    Bare.target.outerCapture Bare.checkedRealization.model.symbols
    Bare.checkedRealization.model.evidence
    (.adapt .unit (.identity .top))
    (.inclusionRefl (.capture .empty))

example : ManySortedFC.Tm.check ManySortedFC.Ctx.nil wrongPayloadAdapter =
    none := by
  native_decide

/-- This certificate proves `empty <= empty union empty`, not the package's
required `empty <= empty` outer-capture obligation. -/
def wrongObjectCapture : ManySortedFC.Tm [] :=
  .pack Bare.target.theory Bare.target.representation
    Bare.target.outerCapture Bare.checkedRealization.model.symbols
    Bare.checkedRealization.model.evidence .unit
    (.captureEmpty (.union .empty .empty))

example : ManySortedFC.Tm.check ManySortedFC.Ctx.nil wrongObjectCapture =
    none := by
  native_decide

/-- Even an empty user interface exports the generated exactness and
containment obligations. -/
example : Bare.target.relations =
    [.equality .capture, .inclusion .capture] := rfl

end DOTCaptureToManySortedFC.ModalIntersections.PositiveObjectCompilationExamples
