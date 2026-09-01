import Coercions.Translation.ManySorted.ModalIntersections.ObjectAdaptation
import Coercions.Translation.ManySorted.ModalIntersections.EvidenceContext
import Coercions.Translation.ManySorted.ModalIntersections.ObjectEvidenceExamples

/-!
# Checked object-adaptation regressions

The positive example compiles the source reflexive object view through the
TheoryMap, Adapter, and Evidence checkers.  The negative examples change one
checker boundary at a time: a representation adapter with the wrong source
type and outer-capture evidence with the wrong target are both rejected.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.ObjectAdaptationExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence
open DOTCaptureToManySortedFC.ModalIntersections.ObjectAdaptation

def sourceObject : DOTCapture.ModalIntersections.ObjectType [] :=
  .mk .empty .one .empty

def targetObject : Preparation.PreparedObject [] where
  encoding := DOTCaptureToManySortedFC.Intersections.Encoding.encode
    { symbols := [], entries := [] }
  representation := .one
  outerCapture := .empty

def prepared : PreparedObject Core.nil sourceObject where
  object := targetObject
  prepared := rfl

def adaptation : DOTCapture.ModalIntersections.ObjectType.Adapts
    DOTCapture.ModalIntersections.Ctx.nil sourceObject sourceObject :=
  .refl sourceObject

def ambient : AmbientCompiler Core.nil where
  compile := fun proof =>
    (EvidenceElaboration.compileIncludes? Context.nil.compiler.leaves proof).map
      (fun compiled => compiled.evidence)

def openedAmbient : OpenedAmbientCompiler Core.nil targetObject where
  compile := fun proof =>
    (EvidenceElaboration.compileIncludes? Context.nil.compiler.leaves proof).map
      (fun compiled => compiled.evidence)

def positive := compile? prepared prepared openedAmbient ambient adaptation
  (.identity (.one : ManySortedFC.Ty []))

example : positive.isSome = true := by native_decide

def checked := positive.get (by native_decide)

example : ManySortedFC.TheoryMap.check Core.nil.target
    checked.view.view.mapping = some checked.view.view.typing :=
  checked.view.view.checkerAcceptance

example : checked.representation.adapter =
    (.identity (.one : ManySortedFC.Ty [])) := by native_decide

example : checked.outerCapture.evidence =
    (.inclusionRefl (.capture .empty) :
      ManySortedFC.Evidence (.inclusion .capture) []) := by native_decide

/-! ## Nonempty cross-shape projection -/

namespace CrossShape

def adaptation : DOTCapture.ModalIntersections.ObjectType.Adapts
    DOTCapture.ModalIntersections.Ctx.nil
    ObjectEvidenceExamples.Positive.source
    ObjectEvidenceExamples.Projection.expected where
  mapping := ObjectEvidenceExamples.Projection.mapping
  theory := ObjectEvidenceExamples.Projection.derivation
  outerCapture := .refl
  packageCapture := .refl

/-- The mixed actual theory is opened once.  The projected expected member is
interpreted through the checked map, while the single runtime representation
is adapted at the resulting endpoint by a value-only identity adapter. -/
def compiled? := compile?
  ObjectEvidenceExamples.Positive.prepared
  ObjectEvidenceExamples.Projection.prepared
  (ObjectEvidenceExamples.openedAmbient
    ObjectEvidenceExamples.Positive.target)
  ObjectEvidenceExamples.ambient adaptation (.identity .one)

example : compiled?.isSome = true := by native_decide

def compiled := compiled?.get (by native_decide)

example : mappedExpectedRepresentation compiled.view = .one := by
  native_decide

example : compiled.representation.adapter = .identity .one := by
  native_decide

example : ManySortedFC.TheoryMap.check Core.nil.target
    compiled.view.view.mapping = some compiled.view.view.typing :=
  compiled.view.view.checkerAcceptance

example : Preparation.Compile.translateType
    (Core.nil.layout.renameTarget
      (ManySortedFC.Rename.weakenStatic
        ObjectEvidenceExamples.Positive.target.encoding.symbols
        ObjectEvidenceExamples.Positive.target.encoding.relations))
    ObjectEvidenceExamples.Positive.target.encoding.openedMembers
    (adaptation.mapping.mapType
      ObjectEvidenceExamples.Projection.expected.representation) =
      .ok (mappedExpectedRepresentation compiled.view) :=
  compiled.mappedExpectedRepresentationPrepared

end CrossShape

def wrongRepresentation := compile? prepared prepared openedAmbient ambient
  adaptation (.identity (.top : ManySortedFC.Ty []))

example : wrongRepresentation.isNone = true := by native_decide

/-- The target checker rejects an ambient certificate whose proposition does
not have the outer-capture endpoints required by the source adaptation. -/
def wrongOuterAmbient : AmbientCompiler Core.nil where
  compile := by
    intro sort lower upper proof
    cases sort with
    | type => exact ambient.compile proof
    | capture => exact some (.captureEmpty (.union .empty .empty))

def wrongOuter := compile? prepared prepared openedAmbient wrongOuterAmbient
  adaptation (.identity (.one : ManySortedFC.Ty []))

example : wrongOuter.isNone = true := by native_decide

end DOTCaptureToManySortedFC.ModalIntersections.ObjectAdaptationExamples
