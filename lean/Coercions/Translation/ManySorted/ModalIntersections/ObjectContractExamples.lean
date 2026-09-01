import Coercions.Translation.ManySorted.ModalIntersections.EvidenceContext
import Coercions.Translation.ManySorted.ModalIntersections.ObjectAdaptation

/-!
# Contracted cumulative-object regressions

These checks isolate the representation-capture contract from the term
compiler.  They cover allocation, model checking, projection identity, and
the explicit empty-capture forgetting boundary.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.ObjectContractExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence

namespace Source

abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv

def repeatedTypeMember : DOTCapture.ModalIntersections.ObjectType [] :=
  .mk
    (.inter
      (.typeMember 0 .bot .top)
      (.typeMember 0 .bot .top))
    .one .empty

def capturedOne {scope : DOTCapture.ModalIntersections.Sig} : Ty scope :=
  .capturing .empty .one

end Source

def emptyEncoding (scope : ManySortedFC.Sig) :
    DOTCaptureToManySortedFC.Intersections.Encoding.Encoding scope where
  prepared := { symbols := [], entries := [] }

def emptyContract (scope : ManySortedFC.Sig) :
    ObjectContract.PreparedObject scope where
  encoding := emptyEncoding scope
  sourceRepresentationAtNames := .one
  outerCapture := .empty

/-! ## Exactly one internal representation-capture name -/

def repeatedPrepared? := ObjectContract.prepare Layout.empty
  Source.repeatedTypeMember

example : repeatedPrepared?.toOption.map (fun object => object.symbols) =
    some [.capture, .type] := by native_decide

example : repeatedPrepared?.toOption.map (fun object => object.relations) =
    some [
      .equality .capture,
      .inclusion .capture,
      .inclusion .type,
      .inclusion .type,
      .inclusion .type,
      .inclusion .type ] := by native_decide

example (scope : ManySortedFC.Sig) :
    (emptyContract scope).symbols = [.capture] := rfl

example (scope : ManySortedFC.Sig) :
    (emptyContract scope).relations =
      [.equality .capture, .inclusion .capture] := rfl

/-! ## Package-side evidence is ambient, not self-discharged -/

def pureSymbols : ManySortedFC.SymbolArgs [] (emptyContract []).symbols :=
  .cons (.capture .empty) .nil

def pureCandidates : List (ModelEvidence []) :=
  [ .captureEquality (.equalityRefl (.capture .empty)),
    .capture (.captureEmpty .empty) ]

def checkedPureModel? := checkContractedModel? Core.nil (emptyContract [])
  pureSymbols pureCandidates

example : checkedPureModel?.isSome = true := by native_decide

/-- Omitting `repCapture` cannot be repaired by opening the theory being
packaged: `checkContractedModel?` checks candidates in `Core.nil.target`. -/
def missingRepCapture? := checkContractedModel? Core.nil (emptyContract [])
  pureSymbols
  [.captureEquality (.equalityRefl (.capture .empty))]

example : missingRepCapture? = none := by native_decide

def noAmbientContractVariable
    (index : ManySortedFC.BVar []
      (.evidence (.inclusion .capture))) : False :=
  nomatch index

/-! ## Projection reuses the actual `C_rep` -/

def selfProjectionCandidates : List (ModelEvidence
    (ManySortedFC.StaticScope [] (emptyContract []).symbols
      (emptyContract []).relations)) :=
  [ .captureEquality (.var (emptyContract []).repExactEvidence),
    .capture (.var (emptyContract []).repCaptureEvidence) ]

def checkedSelfProjection? := checkContractedProjection? Core.nil
  (emptyContract []) (emptyContract []) .nil selfProjectionCandidates

example : checkedSelfProjection?.isSome = true := by native_decide

example : projectionSymbols (emptyContract []) (emptyContract []) .nil =
    .cons (.capture (.cvar (emptyContract []).repCaptureName)) .nil := rfl

/-! A same-identity projection is intentionally partial when the expected
representation advertises a different exact outer capture.  A structural
payload adapter may widen captures, but it cannot make the preserved
`C_rep` equal to a distinct `D_expected`. -/

abbrev OneTermSource : DOTCapture.ModalIntersections.Sig := [] ▹ .term
abbrev OneTermTarget : ManySortedFC.Sig := [] ▹ .term

def oneTermCore : Core
    (DOTCapture.ModalIntersections.TypingEnv.nil.extendTerm
      (Source.capturedOne (scope := [])))
    OneTermTarget where
  layout := Layout.empty.extendPlain
  target := ManySortedFC.Ctx.nil.extendTerm (.capturing .empty .one)

def actualAtTerm : ObjectContract.PreparedObject OneTermTarget :=
  emptyContract OneTermTarget

def expectedAtTerm : ObjectContract.PreparedObject OneTermTarget where
  encoding := emptyEncoding OneTermTarget
  sourceRepresentationAtNames :=
    .capturing (.singleton .here) .one
  outerCapture := .singleton .here

def mismatchedExactCandidates : List (ModelEvidence
    (ManySortedFC.StaticScope OneTermTarget actualAtTerm.symbols
      actualAtTerm.relations)) :=
  [ .captureEquality (.var actualAtTerm.repExactEvidence),
    .capture (.captureEmpty (.singleton
      ((ManySortedFC.Rename.weakenStatic actualAtTerm.symbols
        actualAtTerm.relations).var
          (.here : ManySortedFC.BVar OneTermTarget .term)))) ]

def rejectedCaptureChangingProjection? := checkContractedProjection?
  oneTermCore actualAtTerm expectedAtTerm .nil mismatchedExactCandidates

example : rejectedCaptureChangingProjection? = none := by native_decide

/-! ## Empty-capture forgetting is exact and narrow -/

def acceptedForgetEmpty? := checkRepresentationAdapter?
  ManySortedFC.Ctx.nil (.capturing .empty .one) .one
  (.forgetEmptyCapture .one)

example : acceptedForgetEmpty?.isSome = true := by native_decide

def rejectedForgetNonempty? := checkRepresentationAdapter?
  oneTermCore.target (.capturing (.singleton .here) .one) .one
  (.forgetEmptyCapture .one)

example : rejectedForgetNonempty? = none := by native_decide

/-! ## Wrong-direction containment is rejected -/

def wrongDirectionContract? := checkRootCaptureContract? oneTermCore
  .empty .empty (.singleton .here)
  (.equalityRefl (.capture .empty))
  (.captureVariable .here)

example : wrongDirectionContract? = none := by native_decide

end DOTCaptureToManySortedFC.ModalIntersections.ObjectContractExamples
