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

end DOTCaptureToManySortedFC.RecursiveObjects.ModelExamples
