import Coercions.Translation.ManySorted.ModalIntersections.ObjectEvidence
import Coercions.Translation.ManySorted.ModalIntersections.ObjectOccurrenceEvidence
import Coercions.Translation.ManySorted.ModalIntersections.EvidenceContext
import Coercions.ManySortedFC.TheoryMapExamples

/-!
# Executable object-evidence regressions

The positive case crosses the standalone theory-model checker. The negative
view is derived from exact source occurrences and crosses the standalone
cross-shape map checker with only the actual theory open.

The regressions check logical acceptance and source-stage provenance. They do
not assert final proof-term identity: matching equal target obligations is
non-consuming, so one valid certificate may justify repeated equal
propositions.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidenceExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence
open DOTCaptureToManySortedFC.ModalIntersections.ObjectOccurrenceEvidence

namespace Source

abbrev Interface := DOTCapture.ModalIntersections.Interface
abbrev ObjectType := DOTCapture.ModalIntersections.ObjectType
abbrev LocalModel := DOTCapture.ModalIntersections.LocalModel.Model
abbrev LocalMapping := DOTCapture.ModalIntersections.LocalModel.Mapping

end Source

/-! ## Shared executable ambient compilers -/

def ambient : AmbientCompiler Core.nil where
  compile := fun proof =>
    (compileIncludes? Context.nil.compiler.leaves proof).map
      fun compiled => compiled.evidence

def openedAmbient (object : Preparation.PreparedObject []) :
    OpenedAmbientCompiler Core.nil object where
  compile := fun proof =>
    (ambient.compile proof).map fun evidence =>
      evidence.rename (ManySortedFC.Rename.weakenStatic
        object.encoding.symbols object.encoding.relations)

/-! ## A mixed positive realization -/

namespace Positive

def source : Source.ObjectType [] :=
  .mk
    (.inter
      (.typeMember 3 .one .one)
      (.captureMember 4 .empty .empty))
    .one .empty

def preparedResult := Preparation.prepareObject Core.nil.layout source

example : preparedResult.toOption.isSome = true := by native_decide

def target : Preparation.PreparedObject [] :=
  preparedResult.toOption.get (by native_decide)

def prepared : CompilerContext.PreparedObject Core.nil source where
  object := target
  prepared := by rfl

def model : Source.LocalModel [] where
  typeMember := fun _ => .one
  captureMember := fun _ => .empty

def realization : DOTCapture.ModalIntersections.ObjectType.Realization
    DOTCapture.ModalIntersections.Ctx.nil source where
  model := model
  constraints := .inter
    (.typeMember .refl .refl)
    (.captureMember .refl .refl)

def compiled? := compileRealization? prepared ambient realization

example : compiled?.isSome = true := by native_decide

def compiled := compiled?.get (by native_decide)

example : compileSymbolArgs? Core.nil realization.model target.encoding =
    some compiled.symbols :=
  compiled.symbolsCompiled

example : compileRealizationEvidence? ambient realization.constraints =
    some compiled.candidates :=
  compiled.candidatesCompiled

example : checkModel? Core.nil target compiled.symbols compiled.candidates =
    some compiled.model :=
  compiled.modelChecked

example : ManySortedFC.Theory.checkModel Core.nil.target
    target.encoding.theory compiled.model.symbols compiled.model.evidence =
      some compiled.model.checked :=
  compiled.model.checkerAcceptance

end Positive

/-! ## A source-derived projection -/

namespace Projection

def expected : Source.ObjectType [] :=
  .mk (.typeMember 3 .one .one) .one .empty

def preparedResult := Preparation.prepareObject Core.nil.layout expected

example : preparedResult.toOption.isSome = true := by native_decide

def target : Preparation.PreparedObject [] :=
  preparedResult.toOption.get (by native_decide)

def prepared : CompilerContext.PreparedObject Core.nil expected where
  object := target
  prepared := by rfl

def occurrence : Positive.source.interface.HasTypeOccurrence 3 .one .one :=
  .left .here

def mapping : Source.LocalMapping [] :=
  DOTCapture.ModalIntersections.LocalModel.Mapping.identity

def derivation : DOTCapture.ModalIntersections.Interface.Derives
    DOTCapture.ModalIntersections.Ctx.nil Positive.source.interface mapping
      expected.interface :=
  .typeMember
    (by
      simpa using DOTCapture.ModalIntersections.LocalTheory.Includes.trans
        (.ambient (.refl : DOTCapture.ModalIntersections.TypeIncludes
          DOTCapture.ModalIntersections.Ctx.nil .one .one))
        (DOTCapture.ModalIntersections.LocalTheory.Includes.typeLower occurrence))
    (by
      simpa using DOTCapture.ModalIntersections.LocalTheory.Includes.trans
        (DOTCapture.ModalIntersections.LocalTheory.Includes.typeUpper occurrence)
        (.ambient (.refl : DOTCapture.ModalIntersections.TypeIncludes
          DOTCapture.ModalIntersections.Ctx.nil .one .one)))

def compiled? := compileView? Positive.prepared prepared
  (openedAmbient Positive.target) derivation

example : compiled?.isSome = true := by native_decide

def compiled := compiled?.get (by native_decide)

example : compileMappedSymbolArgs? Core.nil Positive.target target mapping =
    some compiled.symbols :=
  compiled.symbolsCompiled

example : compileDerivationEvidence? Positive.prepared
    (openedAmbient Positive.target) derivation = some compiled.candidates :=
  compiled.candidatesCompiled

example : checkView? Core.nil Positive.target target compiled.symbols
    compiled.candidates = some compiled.view :=
  compiled.viewChecked

def selected? := selectPreparedTypeOccurrence? Positive.prepared occurrence

example : selected?.isSome = true := by native_decide

def selected := selected?.get (by native_decide)

/-- Projection changes only the static view: the expected member is mapped
to the already allocated actual member name. -/
example : compiled.view.mapping.symbols =
    .cons (ManySortedFC.StaticExpr.symbol
      selected.selection.selected.name) .nil := by
  native_decide

example : ManySortedFC.TheoryMap.check Core.nil.target
    compiled.view.mapping = some compiled.view.typing :=
  compiled.view.checkerAcceptance

end Projection

/-! ## Rejection boundaries -/

namespace Negative

def mappedSymbols? := compileMappedSymbolArgs? Core.nil Positive.target
  Projection.target Projection.mapping

example : mappedSymbols?.isSome = true := by native_decide

def mappedSymbols := mappedSymbols?.get (by native_decide)

/-- Supplying the symbol interpretation without the expected evidence block
does not produce a view, even though the actual object has a compatible
member. -/
example : (checkView? Core.nil Positive.target Projection.target
    mappedSymbols []).isSome = false := by
  native_decide

/-- The expected theory cannot contribute evidence for its own obligations. -/
example : ManySortedFC.TheoryMap.check ManySortedFC.Ctx.nil
    ManySortedFC.TheoryMapExamples.targetSelfDischargeAttempt = none := by
  native_decide

/-- A structurally valid adapter is rejected when its synthesized target is
not the requested endpoint. -/
example : (checkRepresentationAdapter? ManySortedFC.Ctx.nil
    (.one : ManySortedFC.Ty []) .top (.identity .one)).isSome = false := by
  native_decide

/-- Capture evidence is likewise checked against both requested endpoints. -/
example : (checkCaptureEvidence? ManySortedFC.Ctx.nil
    (.empty : ManySortedFC.Capture []) (.readOnly .empty)
    (.inclusionRefl (.capture .empty))).isSome = false := by
  native_decide

end Negative

end DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidenceExamples
