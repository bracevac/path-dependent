import Coercions.Translation.ManySorted.RecursiveObjects.ModelExamples
import Coercions.Translation.ManySorted.ModalIntersections.ObjectOccurrenceEvidence

/-!
# Recursive-object completion regressions

These examples close the model-theoretic Stage 6 boundary.  A repeated
recursive capture label keeps one public name while contributing every
equation and interval certificate.  Separately, two distinct finite models
of `C = C` both cross recursive preparation and the standalone target model
checker.  The final check derives `C_rep ≤ χ_D` only from the exported
`repCapture` assumption after the object theory is opened.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.CompletionExamples

open DOTCaptureToManySortedFC.RecursiveObjects
open DOTCaptureToManySortedFC.RecursiveObjects.Model
open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
open DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence

namespace RepeatedRecursiveCapture

open SourceExamples.ExistentialCaptureModels

/-- Add an ordinary interval for `D` to the mutually recursive equations
`C = D` and `D = {a} ∪ C`.  Normalization must merge the two occurrences of
label `32`, not allocate a second `D`. -/
def declarations : Source.CaptureInterface Scope :=
  .inter equations (.member 32 .empty a)

def signature : Source.Signature Scope where
  typeDefinitions := []
  captureDeclarations := declarations
  representation := .capturing
    (.ref (.localCaptureMember 32)) .one
  outerCapture := .ref (.localCaptureMember 32)
  packageCapture := a

def valid : signature.Valid where
  nonempty := by
    right
    simp [Source.Signature.captureLabels, Source.CaptureInterface.labels,
      signature, declarations, equations]
  typeLabelsNodup := by
    simp [Source.Signature.typeLabels, Source.TypeDefinitions.labels, signature]
  labelsDisjoint := by
    intro label member
    simp [Source.Signature.typeLabels, Source.TypeDefinitions.labels, signature]
      at member
  guarded := by
    intro definition member
    simp [signature] at member
  packageCaptureAmbient := rfl

def constraints : declarations.Realizes environment.bindings singletonModel :=
  .inter SourceExamples.ExistentialCaptureModels.constraints
    (.member .captureEmpty .refl)

def realization : Source.Realization environment.bindings signature where
  captures := singletonModel
  captureConstraints := constraints
  representationContainment := .refl
  packageContainment := .refl

def layout :=
  DOTCaptureToManySortedFC.ModalIntersections.Layout.empty.extendPlain

def prepared? := Encoding.prepare layout signature valid realization

example : prepared?.isOk = true := by native_decide

def prepared := prepared?.toOption.get (by native_decide)

/-- Three raw capture declarations normalize to the two public labels `C`
and `D`; there is still only one target capture name for repeated `D`. -/
example : signature.captureLabels = [31, 32, 32] := rfl

example : prepared.object.memberSymbols = [.capture, .capture] := by
  native_decide

/-- The member theory retains all three capture interval occurrences: two
directed constraints per occurrence. -/
example : prepared.object.memberRelations.length = 6 := by native_decide

example : prepared.object.relations.length = 8 := by native_decide

def boundPrepared : PreparedTerm Context.nil.core boundType where
  targetType := .one
  prepared := rfl

def context := Context.nil.extendPlain boundType (by trivial) boundPrepared

def ambient : AmbientCompiler context.core where
  compile := fun proof =>
    (compileIncludes? context.compiler.leaves proof).map
      fun compiled => compiled.evidence

def checkedModel? := Model.check? prepared ambient

example : checkedModel?.isSome = true := by native_decide

def checkedModel := checkedModel?.get (by native_decide)

example : ManySortedFC.Theory.checkModel context.core.target
    prepared.object.theory checkedModel.model.symbols
      checkedModel.model.evidence = some checkedModel.model.checked :=
  checkedModel.model.checkerAcceptance

/-! ### Repeated-label selection after opening -/

def memberOccurrences := prepared.object.encoding.openedOccurrences

def firstD? :=
  ObjectOccurrenceEvidence.findCaptureOrdinalSelection? 32 0 memberOccurrences

def secondD? :=
  ObjectOccurrenceEvidence.findCaptureOrdinalSelection? 32 1 memberOccurrences

example : firstD?.isSome = true := by native_decide
example : secondD?.isSome = true := by native_decide

def firstD := firstD?.get (by native_decide)
def secondD := secondD?.get (by native_decide)

/-- The equation and the extra interval select different evidence coordinates
but exactly the same normalized member identity. -/
example : firstD.selected.name = secondD.selected.name := by native_decide

/-- The two retained records are not accidental duplicate certificates: one
is the recursive equation and the other is the added ordinary interval. -/
example : firstD.lower ≠ secondD.lower := by native_decide

example : firstD.upper ≠ secondD.upper := by native_decide

example : firstD.selected.lowerEvidence ≠ secondD.selected.lowerEvidence := by
  native_decide

example : firstD.selected.upperEvidence ≠ secondD.selected.upperEvidence := by
  native_decide

/-- Shift the normalized member identity and its occurrence certificates
under the cumulative `C_rep` name, `repExact`, and `repCapture`. -/
def openedRename := ObjectContract.openedBaseRename
  [ManySortedFC.BinderKind.term]
  prepared.object.memberSymbols prepared.object.memberRelations

def chiD := openedRename.var firstD.selected.name

def firstDLower : ManySortedFC.Evidence (.inclusion .capture)
    (ManySortedFC.StaticScope [ManySortedFC.BinderKind.term]
      prepared.object.symbols prepared.object.relations) :=
  .var (openedRename.var firstD.selected.lowerEvidence)

def secondDLower : ManySortedFC.Evidence (.inclusion .capture)
    (ManySortedFC.StaticScope [ManySortedFC.BinderKind.term]
      prepared.object.symbols prepared.object.relations) :=
  .var (openedRename.var secondD.selected.lowerEvidence)

example : openedRename.var firstD.selected.name =
    openedRename.var secondD.selected.name := by native_decide

/-- Both retained lower-bound variables are independently accepted in the
opened cumulative theory, while remaining distinct proof coordinates. -/
example : (ManySortedFC.Evidence.check
    (context.core.target.extendTheory prepared.object.theory) firstDLower).isSome =
      true := by native_decide

example : (ManySortedFC.Evidence.check
    (context.core.target.extendTheory prepared.object.theory) secondDLower).isSome =
      true := by native_decide

/-! ### The advertised recursive member is the actual `repCapture` target -/

def repToD : ManySortedFC.Evidence (.inclusion .capture)
    (ManySortedFC.StaticScope [ManySortedFC.BinderKind.term]
      prepared.object.symbols prepared.object.relations) :=
  .var prepared.object.repCaptureEvidence

def repToDChecked? := ManySortedFC.Evidence.check
  (context.core.target.extendTheory prepared.object.theory) repToD

example : repToDChecked?.isSome = true := by native_decide

/-- The object's advertised capture is local `D`, whereas its package
envelope is ambient `{a}`.  Thus this proposition checks that the generated
`repCapture` relation itself targets the opened recursive member; it is not a
fact reconstructed from `repExact`. -/
example : repToDChecked?.map ManySortedFC.Evidence.Checked.proposition =
    some (.inclusion
      (.capture (.cvar prepared.object.repCaptureName))
      (.capture (.cvar chiD))) := by
  native_decide

def repToDChecked := repToDChecked?.get (by native_decide)

example : ManySortedFC.Evidence.Proves
    (context.core.target.extendTheory prepared.object.theory) repToD
      (.inclusion
        (.capture (.cvar prepared.object.repCaptureName))
        (.capture (.cvar chiD))) := by
  simpa using repToDChecked.typing

/-! ### Stable opening retains that exact relation coordinate -/

def preparedContract : PreparedContractedObject context.core
    signature.objectType where
  object := prepared.object
  prepared := prepared.objectPrepared

def newestRoot? := Context.prepareNewestContractedRoot? context
  signature.objectType preparedContract

example : newestRoot?.isSome = true := by native_decide

def newestRoot := newestRoot?.get (by native_decide)

/-- Root registration consumes the exported `repCapture` variable itself. -/
example : newestRoot.captureContract.containmentEvidence =
    (.var (.there prepared.object.repCaptureEvidence) :
      ManySortedFC.Evidence (.inclusion .capture)
        (ManySortedFC.PayloadScope [ManySortedFC.BinderKind.term]
          prepared.object.symbols prepared.object.relations)) := by
  native_decide

/-- Its checked right endpoint is the opened `χ_D`, not the ambient package
envelope `{a}`. -/
example : newestRoot.objectCapture =
    prepared.object.openedAdvertisedCapture := by
  native_decide

end RepeatedRecursiveCapture

namespace MultipleSelfModels

open SourceExamples.ExistentialCaptureModels

def signature : Source.Signature Scope where
  typeDefinitions := []
  captureDeclarations := selfEquation
  representation := .one
  outerCapture := a

def valid : signature.Valid where
  nonempty := by
    right
    simp [Source.Signature.captureLabels, Source.CaptureInterface.labels,
      signature, selfEquation]
  typeLabelsNodup := by
    simp [Source.Signature.typeLabels, Source.TypeDefinitions.labels, signature]
  labelsDisjoint := by
    intro label member
    simp [Source.Signature.typeLabels, Source.TypeDefinitions.labels, signature]
      at member
  guarded := by
    intro definition member
    simp [signature] at member
  packageCaptureAmbient := rfl

def emptyRealization : Source.Realization environment.bindings signature where
  captures := emptyModel
  captureConstraints := selfEmptySolution
  representationContainment := .captureEmpty
  packageContainment := .captureEmpty

def singletonRealization : Source.Realization environment.bindings signature where
  captures := singletonModel
  captureConstraints := selfSingletonSolution
  representationContainment := .captureEmpty
  packageContainment := .captureEmpty

def layout :=
  DOTCaptureToManySortedFC.ModalIntersections.Layout.empty.extendPlain

def emptyPrepared? := Encoding.prepare layout signature valid emptyRealization
def singletonPrepared? :=
  Encoding.prepare layout signature valid singletonRealization

example : emptyPrepared?.isOk = true := by native_decide
example : singletonPrepared?.isOk = true := by native_decide

def emptyPrepared := emptyPrepared?.toOption.get (by native_decide)
def singletonPrepared := singletonPrepared?.toOption.get (by native_decide)

def boundPrepared : PreparedTerm Context.nil.core boundType where
  targetType := .one
  prepared := rfl

def context := Context.nil.extendPlain boundType (by trivial) boundPrepared

def ambient : AmbientCompiler context.core where
  compile := fun proof =>
    (compileIncludes? context.compiler.leaves proof).map
      fun compiled => compiled.evidence

def emptyChecked? := Model.check? emptyPrepared ambient
def singletonChecked? := Model.check? singletonPrepared ambient

example : emptyChecked?.isSome = true := by native_decide
example : singletonChecked?.isSome = true := by native_decide

def emptyChecked := emptyChecked?.get (by native_decide)
def singletonChecked := singletonChecked?.get (by native_decide)

/-- Both concrete choices pass the same target theory checker. -/
example : ManySortedFC.Theory.checkModel context.core.target
    emptyPrepared.object.theory emptyChecked.model.symbols
      emptyChecked.model.evidence = some emptyChecked.model.checked :=
  emptyChecked.model.checkerAcceptance

example : ManySortedFC.Theory.checkModel context.core.target
    singletonPrepared.object.theory singletonChecked.model.symbols
      singletonChecked.model.evidence = some singletonChecked.model.checked :=
  singletonChecked.model.checkerAcceptance

/-- The checked artifacts differ at the one public capture witness: `C = C`
does not select a canonical fixed point. -/
example : emptyPrepared.targetLocalModel.captureMember? 41 = some .empty := by
  native_decide

example : singletonPrepared.targetLocalModel.captureMember? 41 =
    some (.singleton .here) := by native_decide

example : emptyChecked.model.symbols ≠ singletonChecked.model.symbols := by
  native_decide

end MultipleSelfModels

/-! An unstable recursive-literal selection has no source AST node to test:
`Term.select` and every static member reference take a `Path`, whereas a
tagged recursive literal is a `Value`.  A diagnostic regression would belong
to a future untyped/raw surface parser; the present intrinsically stable-path
front end rejects the form by construction. -/

end DOTCaptureToManySortedFC.RecursiveObjects.CompletionExamples
