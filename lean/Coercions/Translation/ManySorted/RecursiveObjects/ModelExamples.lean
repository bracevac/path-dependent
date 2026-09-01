import Coercions.Translation.ManySorted.RecursiveObjects.EncodingExamples
import Coercions.Translation.ManySorted.RecursiveObjects.Model
import Coercions.Translation.ManySorted.ModalIntersections.EvidenceContext

/-!
# Checked recursive model and package regressions

The mutual `A`/`B` example crosses the ordinary cumulative theory-model
checker and term checker.  The negative regression removes the recursive
lower-bound evidence, demonstrating that exported theory assumptions are not
available to construct their own package model.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.ModelExamples

open DOTCaptureToManySortedFC.RecursiveObjects
open DOTCaptureToManySortedFC.RecursiveObjects.EncodingExamples
open DOTCaptureToManySortedFC.RecursiveObjects.Model
open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
open DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence

def ambient : AmbientCompiler Core.nil where
  compile := fun proof =>
    (compileIncludes? Context.nil.compiler.leaves proof).map
      fun compiled => compiled.evidence

def checkedModel? := Model.check? prepared ambient

example : checkedModel?.isSome = true := by native_decide

def checkedModel := checkedModel?.get (by native_decide)

/-- The complete target model, including recursive unfold evidence, is checked
in the empty ambient context. -/
example : ManySortedFC.Theory.checkModel Core.nil.target
    prepared.object.theory checkedModel.model.symbols
      checkedModel.model.evidence = some checkedModel.model.checked :=
  checkedModel.model.checkerAcceptance

/-- `C_rep` is the one additional head witness and is the empty actual capture
of the unit representation. -/
example : checkedModel.model.symbols =
    .cons (.capture .empty) prepared.memberSymbols := by native_decide

def package? := Model.package? prepared ambient checkedModel

example : package?.isSome = true := by native_decide

def package := package?.get (by native_decide)

example : ManySortedFC.Tm.check Core.nil.target package.term =
    some package.checked := package.accepted

example : ManySortedFC.Tm.checkValue package.term =
    some package.valueChecked := package.valueAccepted

example : ManySortedFC.Tm.synth Core.nil.target package.term =
    some (.empty, prepared.object.targetType) := package.checkerAccepts

/-- Exact erasure is stated against the independently defined source
recursive-object erasure. -/
example : package.term.erase =
    Source.eraseObject SourceExamples.signature :=
  package.exactErasure

/-- The strengthened recursive package has the same runtime code as the old
cumulative source object's ordinary erasure.  The target artifacts differ
statically; both erase to the one unit payload. -/
def oldCumulativeObject : DOTCapture.ModalIntersections.Value [] :=
  .object SourceExamples.signature.objectType .unit

example : package.term.erase = Core.nil.eraseValue oldCumulativeObject := by
  rw [package.exactErasure]
  rfl

/-! ## Negative ambient-model checks -/

/-- Keep only forward recursive inclusions.  Exact members also require the
reverse `unfold(W) <: W` direction; the checker cannot borrow that missing
fact from the theory being packaged. -/
def forwardOnlyCandidates : List (ModelEvidence []) :=
  .captureEquality (.equalityRefl (.capture .empty)) ::
  .capture (.inclusionRefl (.capture .empty)) ::
  (List.finRange SourceExamples.signature.typeDefinitions.length).map
    fun index => .type
      (.equalityToInclusion (.unfoldRec prepared.bodies index))

def forwardOnlyModel? := checkContractedModel? Core.nil prepared.object
  prepared.symbols forwardOnlyCandidates

example : forwardOnlyModel? = none := by native_decide

/-! ## Canonical order does not affect checked realizability -/

def reversedCheckedModel? := Model.check? reversedPrepared ambient
def reversedCheckedModel := reversedCheckedModel?.get (by native_decide)
def reversedPackage? := Model.package? reversedPrepared ambient
  reversedCheckedModel

example : reversedCheckedModel?.isSome = true := by native_decide
example : reversedPackage?.isSome = true := by native_decide

/-! ## Repeated capture constraints share one witness -/

def repeatedCheckedModel? := Model.check? repeatedPrepared ambient

example : repeatedCheckedModel?.isSome = true := by native_decide

/-! ## Simultaneously realized recursive capture constraint -/

def recursiveCaptureCheckedModel? := Model.check? recursiveCapturePrepared
  ambient

/-- The raw target theory retains the self-dependent capture bound, while
the empty concrete witness and both certificates are checked in the empty
ambient context. -/
example : recursiveCaptureCheckedModel?.isSome = true := by native_decide

/-- Omitting the realized capture certificates is rejected even though the
raw exported theory contains the self-bound.  Package assumptions cannot
discharge their own model obligations. -/
def recursiveCaptureSelfDischargeAttempt? := checkContractedModel? Core.nil
  recursiveCapturePrepared.object recursiveCapturePrepared.symbols
    (.captureEquality (.equalityRefl (.capture .empty)) ::
      .capture (.inclusionRefl (.capture .empty)) ::
        exactTypeCandidates recursiveCapturePrepared.bodies)

example : recursiveCaptureSelfDischargeAttempt? = none := by native_decide

/-! ## Explicit existential capture model

The source equations are solved by selecting both finite witnesses at once.
The target checker then validates the contracted object model in a genuine
one-term ambient context. -/

namespace ExistentialCaptureModels

def boundPrepared : PreparedTerm Context.nil.core
    SourceExamples.ExistentialCaptureModels.boundType where
  targetType := .one
  prepared := rfl

def context := Context.nil.extendPlain
  SourceExamples.ExistentialCaptureModels.boundType (by trivial) boundPrepared

def prepared := EncodingExamples.ExistentialCaptureModels.prepared

def ambient : AmbientCompiler context.core where
  compile := fun proof =>
    (compileIncludes? context.compiler.leaves proof).map
      fun compiled => compiled.evidence

def checkedModel? := Model.check? prepared ambient

example : checkedModel?.isSome = true := by native_decide

def checkedModel := checkedModel?.get (by native_decide)

/-- The distinguished representation-capture witness is the selected model
for `D`, since the source payload has type `D · Unit`.  The same singleton is
also the advertised object envelope. -/
example : checkedModel.model.symbols =
    .cons (.capture (.singleton .here)) prepared.memberSymbols := by
  native_decide

example : checkedModel.realizedRepresentation =
    (.capturing (.singleton .here) .one :
      ManySortedFC.Ty [ManySortedFC.BinderKind.term]) := by
  native_decide

example : ManySortedFC.Theory.checkModel context.core.target
    prepared.object.theory checkedModel.model.symbols
      checkedModel.model.evidence = some checkedModel.model.checked :=
  checkedModel.model.checkerAcceptance

/-- Replace both existentially selected capture witnesses by empty.  This is
not a model of `D = {a} ∪ C` in the ambient context where `a` has bare unit
type, so the standalone contracted-model checker rejects it. -/
def wrongMemberSymbols : ManySortedFC.SymbolArgs
    [ManySortedFC.BinderKind.term] prepared.object.memberSymbols :=
  .cons (.capture .empty)
    (.cons (.capture .empty) .nil)

def wrongSymbols := prepared.object.extendSymbols wrongMemberSymbols

/-- Since the representation itself mentions `D`, changing `D` also changes
the computed `C_rep`; the checker still rejects the vector because its
exported recursive capture equations cannot be proved. -/
example : wrongSymbols =
    (.cons (.capture .empty)
      (.cons (.capture .empty)
        (.cons (.capture .empty) .nil))) := by
  native_decide

def wrongModel? := checkContractedModel? context.core prepared.object
  wrongSymbols checkedModel.candidates

example : wrongModel? = none := by native_decide

end ExistentialCaptureModels

/-! ## Non-unit, recursively indexed representation -/

def dependentRepresentationCheckedModel? := Model.check?
  dependentRepresentationPrepared ambient

example : dependentRepresentationCheckedModel?.isSome = true := by
  native_decide

def dependentRepresentationCheckedModel :=
  dependentRepresentationCheckedModel?.get (by native_decide)

/-- Instantiation replaces both occurrences of the local type member by the
same recursive projection and the payload capture by its concrete witness. -/
example : dependentRepresentationCheckedModel.realizedRepresentation =
    (.capturing .empty
      (.arr
        (.recProj dependentRepresentationPrepared.bodies ⟨0, by decide⟩)
        (.recProj dependentRepresentationPrepared.bodies ⟨0, by decide⟩)) :
      ManySortedFC.Ty []) := by
  native_decide

/-- The historical unit helper is now merely partial; it cannot stand in for
the real function representation. -/
def dependentUnitPackage? := Model.package? dependentRepresentationPrepared
  ambient dependentRepresentationCheckedModel

example : dependentUnitPackage? = none := by native_decide

def dependentShapeProof : DOTCapture.ModalIntersections.TypeIncludes
    DOTCapture.ModalIntersections.Ctx.nil
    (dependentRepresentationSignature.realizedRepresentation
      dependentRepresentationRealization.captures).stripCapture
    (dependentRepresentationSignature.realizedRepresentation
      dependentRepresentationRealization.captures).stripCapture := .refl

def dependentShapeCompiled? := Model.compileRealizedIncludes?
  dependentRepresentationPrepared Context.nil.compiler.leaves
    dependentShapeProof

/-- The ordinary ambient endpoint compiler cannot resolve these local type
references; the recursive-aware compiler resolves both to `recProj` and the
standalone evidence checker accepts the resulting certificate. -/
example : dependentShapeCompiled?.isSome = true := by native_decide

end DOTCaptureToManySortedFC.RecursiveObjects.ModelExamples
