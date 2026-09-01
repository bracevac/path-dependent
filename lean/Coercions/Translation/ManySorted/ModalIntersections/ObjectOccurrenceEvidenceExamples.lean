import Coercions.Translation.ManySorted.ModalIntersections.ObjectOccurrenceEvidence

/-!
# Executable ordinal-selection regressions

Identical same-label declarations remain distinct source occurrences.  Their
compiled selections reuse one member name but select different generated
lower/upper evidence binders.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.ObjectOccurrenceEvidenceExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.ObjectOccurrenceEvidence

namespace TypeDuplicate

def source : DOTCapture.ModalIntersections.ObjectType [] :=
  .mk
    (.inter
      (.typeMember 3 .one .one)
      (.typeMember 3 .one .one))
    .one .empty

def target : Preparation.PreparedObject [] where
  encoding := DOTCaptureToManySortedFC.Intersections.Encoding.encode
    { symbols := [.type]
      entries :=
        [.type 3 .here
          [{ lower := .type .one, upper := .type .one },
           { lower := .type .one, upper := .type .one }]] }
  representation := .one
  outerCapture := .empty

def prepared : PreparedObject Core.nil source where
  object := target
  prepared := rfl

def first : source.interface.HasTypeOccurrence 3 .one .one :=
  .left .here

def second : source.interface.HasTypeOccurrence 3 .one .one :=
  .right .here

abbrev firstResult := selectPreparedTypeOccurrence? prepared first
abbrev secondResult := selectPreparedTypeOccurrence? prepared second

example : firstResult.isSome = true := rfl
example : secondResult.isSome = true := rfl

def firstSelection := firstResult.get (by rfl)
def secondSelection := secondResult.get (by rfl)

example : firstSelection.selection.selected.name =
    secondSelection.selection.selected.name := rfl

example : firstSelection.selection.selected.lowerEvidence ≠
    secondSelection.selection.selected.lowerEvidence := by decide

example : firstSelection.selection.selected.upperEvidence ≠
    secondSelection.selection.selected.upperEvidence := by decide

end TypeDuplicate

namespace CaptureDuplicate

def source : DOTCapture.ModalIntersections.ObjectType [] :=
  .mk
    (.inter
      (.captureMember 4 .empty .empty)
      (.captureMember 4 .empty .empty))
    .one .empty

def target : Preparation.PreparedObject [] where
  encoding := DOTCaptureToManySortedFC.Intersections.Encoding.encode
    { symbols := [.capture]
      entries :=
        [.capture 4 .here
          [{ lower := .capture .empty, upper := .capture .empty },
           { lower := .capture .empty, upper := .capture .empty }]] }
  representation := .one
  outerCapture := .empty

def prepared : PreparedObject Core.nil source where
  object := target
  prepared := rfl

def first : source.interface.HasCaptureOccurrence 4 .empty .empty :=
  .left .here

def second : source.interface.HasCaptureOccurrence 4 .empty .empty :=
  .right .here

abbrev firstResult := selectPreparedCaptureOccurrence? prepared first
abbrev secondResult := selectPreparedCaptureOccurrence? prepared second

example : firstResult.isSome = true := rfl
example : secondResult.isSome = true := rfl

def firstSelection := firstResult.get (by rfl)
def secondSelection := secondResult.get (by rfl)

example : firstSelection.selection.selected.name =
    secondSelection.selection.selected.name := rfl

example : firstSelection.selection.selected.lowerEvidence ≠
    secondSelection.selection.selected.lowerEvidence := by decide

example : firstSelection.selection.selected.upperEvidence ≠
    secondSelection.selection.selected.upperEvidence := by decide

end CaptureDuplicate

end DOTCaptureToManySortedFC.ModalIntersections.ObjectOccurrenceEvidenceExamples
