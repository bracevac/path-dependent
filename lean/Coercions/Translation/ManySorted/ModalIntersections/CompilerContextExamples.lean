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

def readOnlyRequirements :
    DOTCapture.ModalIntersections.ModalRequirements 0 [.readOnly] [] :=
  .mk .nil (.cons .nil .empty)

def repeatedCaptureObject : DOTCapture.ModalIntersections.ObjectType [] :=
  .mk
    (.inter
      (.captureMember 7 .empty (.readOnly .empty))
      (.captureMember 7 .empty (.readOnly .empty)))
    .one .empty

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

def readOnlyRequirements : ManySortedFC.ModalContext 0 [.readOnly] [] :=
  .mk .nil (.cons .nil .empty)

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

def preparedReadOnlyModal :
    PreparedModal Core.nil SourceExamples.readOnlyRequirements where
  requirements := TargetExamples.readOnlyRequirements
  prepared := rfl

/-! ## Canonical prepared readiness -/

example : Ready.nil.core = Core.nil := rfl

example : Core.nil.captureMap
    (.empty : DOTCapture.ModalIntersections.Capture []) = .empty := rfl

example : Core.nil.captureMap
    (.empty : DOTCapture.ModalIntersections.Capture []) =
      preparedEmptyCapture.targetCapture :=
  preparedEmptyCapture.captureMap_eq

noncomputable def readyPlain :
    Ready (DOTCapture.ModalIntersections.TypingEnv.nil.extendTerm .one)
      ([] ▹ .term) :=
  Ready.nil.extendPlain .one preparedOne

noncomputable def readyStatic :
    Ready
      (DOTCapture.ModalIntersections.TypingEnv.nil.extendStatic
        SourceExamples.unboundedType)
      (ManySortedFC.StaticScope [] [.type] []) :=
  Ready.nil.extendStatic SourceExamples.unboundedType preparedUnboundedType

noncomputable def readyPayload :
    Ready
      (DOTCapture.ModalIntersections.TypingEnv.nil.extendPayload
        SourceExamples.unboundedType .one)
      (ManySortedFC.StaticScope [] [.type] [] ▹ .term) :=
  Ready.nil.extendPayload SourceExamples.unboundedType .one
    preparedUnitPayload

noncomputable def readyObject :
    Ready
      (DOTCapture.ModalIntersections.TypingEnv.nil.extendTerm
        SourceExamples.emptyObject.formedType)
      (ManySortedFC.StaticScope [] [] [] ▹ .term) :=
  Ready.nil.extendObject SourceExamples.emptyObject preparedEmptyObject

noncomputable def readyModal :
    Ready
      (DOTCapture.ModalIntersections.TypingEnv.nil.push
        SourceExamples.emptyRequirements)
      (ManySortedFC.ModalScope [] 0 []) :=
  Ready.nil.push SourceExamples.emptyRequirements preparedEmptyModal

/-! The nonempty frame below makes every following context transport
proof-relevant rather than vacuous. -/

abbrev LockedTargetScope : ManySortedFC.Sig :=
  ManySortedFC.ModalScope [] 0 [.readOnly]

noncomputable def readyLocked :
    Ready
      (DOTCapture.ModalIntersections.TypingEnv.nil.push
        SourceExamples.readOnlyRequirements)
      LockedTargetScope :=
  Ready.nil.push SourceExamples.readOnlyRequirements preparedReadOnlyModal

noncomputable def lockedPreparedOne :
    PreparedTerm readyLocked.core
      (.one : DOTCapture.ModalIntersections.Ty []) where
  targetType := .one
  prepared := rfl

noncomputable def readyLockedPlain :
    Ready
      ((DOTCapture.ModalIntersections.TypingEnv.nil.push
        SourceExamples.readOnlyRequirements).extendTerm .one)
      (LockedTargetScope ▹ .term) :=
  readyLocked.extendPlain .one lockedPreparedOne

/-- The active frame remains directly queryable after an ordinary binder. -/
noncomputable def lockedPlainMode : CompiledMode
    readyLockedPlain.core.target .empty .readOnly :=
  readyLockedPlain.provenance.modeLock
    DOTCapture.ModalIntersections.ModalAssumptions.Lookup.here
    DOTCapture.ModalIntersections.ModeContext.Occurs.here

noncomputable def lockedPreparedStatic :
    PreparedStatic readyLocked.core SourceExamples.unboundedType where
  theory := ManySortedFC.Interval.unconstrained .type
  prepared := rfl

noncomputable def readyLockedStatic :
    Ready
      ((DOTCapture.ModalIntersections.TypingEnv.nil.push
        SourceExamples.readOnlyRequirements).extendStatic
          SourceExamples.unboundedType)
      (ManySortedFC.StaticScope LockedTargetScope [.type] []) :=
  readyLocked.extendStatic SourceExamples.unboundedType lockedPreparedStatic

/-- The same frame remains queryable after a proof-only static theory. -/
noncomputable def lockedStaticMode : CompiledMode
    readyLockedStatic.core.target .empty .readOnly :=
  readyLockedStatic.provenance.modeLock
    DOTCapture.ModalIntersections.ModalAssumptions.Lookup.here
    DOTCapture.ModalIntersections.ModeContext.Occurs.here

noncomputable def lockedPreparedPayload :
    PreparedPayload readyLocked.core SourceExamples.unboundedType
      (.one : DOTCapture.ModalIntersections.Ty
        ([] ▹ .static .type)) where
  theory := ManySortedFC.Interval.unconstrained .type
  intervalPrepared := rfl
  targetPayload := .one
  payloadPrepared := rfl

noncomputable def readyLockedPayload :
    Ready
      ((DOTCapture.ModalIntersections.TypingEnv.nil.push
        SourceExamples.readOnlyRequirements).extendPayload
          SourceExamples.unboundedType .one)
      (ManySortedFC.StaticScope LockedTargetScope [.type] [] ▹ .term) :=
  readyLocked.extendPayload SourceExamples.unboundedType .one
    lockedPreparedPayload

/-- Opening a static witness and runtime payload transports the frame through
both binders. -/
noncomputable def lockedPayloadMode : CompiledMode
    readyLockedPayload.core.target .empty .readOnly :=
  readyLockedPayload.provenance.modeLock
    DOTCapture.ModalIntersections.ModalAssumptions.Lookup.here
    DOTCapture.ModalIntersections.ModeContext.Occurs.here

def lockedRepeatedCaptureTarget : Preparation.PreparedObject
    LockedTargetScope where
  encoding := DOTCaptureToManySortedFC.Intersections.Encoding.encode
    { symbols := [.capture]
      entries :=
        [.capture 7 .here
          [{ lower := .capture .empty, upper := .capture (.readOnly .empty) },
           { lower := .capture .empty, upper := .capture (.readOnly .empty) }]] }
  representation := .one
  outerCapture := .empty

noncomputable def lockedPreparedRepeatedCaptureObject :
    PreparedObject readyLocked.core SourceExamples.repeatedCaptureObject where
  object := lockedRepeatedCaptureTarget
  prepared := rfl

noncomputable def readyLockedObject :
    Ready
      ((DOTCapture.ModalIntersections.TypingEnv.nil.push
        SourceExamples.readOnlyRequirements).extendTerm
          SourceExamples.repeatedCaptureObject.formedType)
      (ManySortedFC.StaticScope LockedTargetScope [.capture]
        [.inclusion .capture, .inclusion .capture,
          .inclusion .capture, .inclusion .capture] ▹ .term) :=
  readyLocked.extendObject SourceExamples.repeatedCaptureObject
    lockedPreparedRepeatedCaptureObject

/-- Object opening transports the frame through the complete names/evidence
theory and the single representation binder. -/
noncomputable def lockedObjectMode : CompiledMode
    readyLockedObject.core.target .empty .readOnly :=
  readyLockedObject.provenance.modeLock
    DOTCapture.ModalIntersections.ModalAssumptions.Lookup.here
    DOTCapture.ModalIntersections.ModeContext.Occurs.here

/-- Two source occurrences retain one shared capture-member identity. -/
example : lockedRepeatedCaptureTarget.encoding.openedMembers.length = 1 ∧
    lockedRepeatedCaptureTarget.encoding.openedOccurrences.length = 2 := by
  constructor <;> rfl

example :
    match readyLockedObject.core.layout.member? (.var .here) 7 with
    | some (.capture _ name) =>
        readyLockedObject.core.captureMap
          (.ref (.captureMember (.var .here) 7)) = .cvar name
    | _ => False := by
  rfl

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
