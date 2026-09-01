import Coercions.Translation.ManySorted.ModalIntersections.CompilerContext

/-! Focused construction and runtime-projection regressions for compiler
contexts. -/

namespace DOTCaptureToManySortedFC.ModalIntersections.CompilerContextExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext

namespace SourceExamples

def unboundedType : DOTCapture.ModalIntersections.Interval .type [] :=
  .bounds .none .none

def emptyObject : DOTCapture.ModalIntersections.ObjectType [] :=
  .mk .empty .one .empty

def emptyRequirements :
    DOTCapture.ModalIntersections.ModalRequirements 0 [] [] :=
  .mk .nil .nil

end SourceExamples

namespace TargetExamples

def emptyEncoding :
    DOTCaptureToManySortedFC.Intersections.Encoding.Encoding [] where
  prepared := { symbols := [], entries := [] }

def emptyObject : Preparation.PreparedObject [] where
  encoding := emptyEncoding
  representation := .one
  outerCapture := .empty

def emptyObjectArrow : Preparation.PreparedObjectArrow [] where
  object := emptyObject
  result := .one

def emptyRequirements : ManySortedFC.ModalContext 0 [] [] :=
  .mk .nil .nil

end TargetExamples

/-! ## Empty context and exact preparation carriers -/

example :
    Core.nil.runtimeRenaming =
      (fun sourceVar : DOTCapture.ModalIntersections.BVar [] .term =>
        nomatch sourceVar) := by
  funext sourceVar
  nomatch sourceVar

example : Core.nil.eraseValue (.unit : DOTCapture.ModalIntersections.Value []) =
    .unit := rfl

def preparedOne :
    PreparedTerm Core.nil (.one : DOTCapture.ModalIntersections.Ty []) where
  targetType := .one
  prepared := rfl

def preparedEmptyCapture :
    PreparedCapture Core.nil
      (.empty : DOTCapture.ModalIntersections.Capture []) where
  targetCapture := .empty
  prepared := rfl

def preparedOneExpression :
    PreparedStaticExpr Core.nil
      (.type (.one : DOTCapture.ModalIntersections.Ty [])) where
  targetExpression := .type .one
  prepared := rfl

def preparedUnboundedType :
    PreparedStatic Core.nil SourceExamples.unboundedType where
  theory := ManySortedFC.Interval.unconstrained .type
  prepared := rfl

def preparedUnitPayload :
    PreparedPayload Core.nil SourceExamples.unboundedType
      (.one : DOTCapture.ModalIntersections.Ty
        ([] ▹ .static .type)) where
  theory := ManySortedFC.Interval.unconstrained .type
  intervalPrepared := rfl
  targetPayload := .one
  payloadPrepared := rfl

def preparedEmptyObject :
    PreparedObject Core.nil SourceExamples.emptyObject where
  object := TargetExamples.emptyObject
  prepared := rfl

def preparedEmptyObjectArrow :
    PreparedObjectArrow Core.nil SourceExamples.emptyObject
      (.one : DOTCapture.ModalIntersections.Ty []) where
  arrow := TargetExamples.emptyObjectArrow
  prepared := rfl

def preparedEmptyModal :
    PreparedModal Core.nil SourceExamples.emptyRequirements where
  requirements := TargetExamples.emptyRequirements
  prepared := rfl

/-! ## Runtime counts and lift laws -/

example :
    (ManySortedFC.StaticScope []
      TargetExamples.emptyObject.encoding.symbols
      TargetExamples.emptyObject.encoding.relations ▹ .term).termCount =
        1 := by
  exact TargetExamples.emptyObject.one_payload

example :
    ((Core.nil.extendObject SourceExamples.emptyObject
      TargetExamples.emptyObject).runtimeRenaming
        (.here : DOTCapture.ModalIntersections.BVar
          ([] ▹ .term) .term)).val = 0 := rfl

example : (ManySortedFC.ModalScope [] 0 []).termCount = 0 := rfl

example :
    (Core.nil.push SourceExamples.emptyRequirements
      TargetExamples.emptyRequirements).runtimeRenaming =
      SourceErasure.Renaming.castTarget
        (ManySortedFC.Sig.termCount_evidenceBlock []
          (ManySortedFC.modalRelations 0 [])).symm
        Core.nil.runtimeRenaming :=
  Core.runtimeRenaming_push Core.nil SourceExamples.emptyRequirements
    TargetExamples.emptyRequirements

end DOTCaptureToManySortedFC.ModalIntersections.CompilerContextExamples
