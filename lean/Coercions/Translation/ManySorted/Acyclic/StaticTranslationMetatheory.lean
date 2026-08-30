import Coercions.Translation.ManySorted.Acyclic.StaticTranslation
import Coercions.Translation.ManySorted.Acyclic.ObjectEncodingMetatheory

/-!
# One-binding naturality of acyclic static translation

Weakening a source expression below one source term binding agrees exactly
with renaming its partial target translation through the heterogeneous
extension selected by `Layout.extendRename`.  This includes the seven-binder
object expansion as one source weakening step.
-/

namespace DOTCaptureToManySortedFC.Acyclic.StaticTranslationMetatheory

/-! Short local qualifiers separate the independent source and target
syntax while keeping the naturality statements readable. -/

namespace Source

export DOTCapture.Acyclic
  (Scope Rename Path StaticRef Capture Ty ObjectSig StaticExpr Ctx Var)

namespace Rename
export DOTCapture.Acyclic.Rename (succ)
end Rename

namespace Path
export DOTCapture.Acyclic.Path (rename weaken typeMember captureMember)
end Path

namespace StaticRef
export DOTCapture.Acyclic.StaticRef (rename)
end StaticRef

namespace Capture
export DOTCapture.Acyclic.Capture (rename weaken)
end Capture

namespace Ty
export DOTCapture.Acyclic.Ty (rename weaken)
end Ty

namespace ObjectSig
export DOTCapture.Acyclic.ObjectSig (rename weaken)
end ObjectSig

namespace StaticExpr
export DOTCapture.Acyclic.StaticExpr (rename)
end StaticExpr

namespace Ctx
export DOTCapture.Acyclic.Ctx (nil)
end Ctx

end Source

namespace Target

export ManySortedFC (Rename StaticExpr Capture Ty)

end Target

namespace Translation

export DOTCaptureToManySortedFC.Acyclic.StaticTranslation
  (translatePath translateRef? translateCapture? translateTy?
    translateObjectSig? translateExpr?
    translateRef?_typeMember_of_receiverSlot
    translateRef?_captureMember_of_receiverSlot
    exactSourceContext exactReceiver)

end Translation

namespace Object

export DOTCaptureToManySortedFC.Acyclic.ObjectEncoding
  (Bounds existentialShape)

end Object

/-! ## Layout square -/

/-- Reading a generated symbol from a renamed slot agrees with renaming the
static expression read from the original slot. -/
@[simp]
theorem staticSlot_expression_rename {source target : ManySortedFC.Sig}
    {sort : ManySortedFC.StaticSort}
    (slot : ManySortedTranslation.StaticSlot source sort)
    (rho : ManySortedFC.Rename source target) :
    (slot.rename rho).expression = slot.expression.rename rho := by
  cases sort <;> rfl

/-- Total path translation commutes with one source-context extension. -/
@[simp]
theorem translatePath_rename_succ {scope : Source.Scope}
    (outer : Source.Ctx scope) (binding : Source.Ty scope)
    (path : Source.Path scope) :
    Translation.translatePath (outer.extendTerm binding)
        (path.rename Source.Rename.succ) =
      (Layout.extendRename outer binding).var
        (Translation.translatePath outer path) := by
  cases path
  rfl

/-- `Path.weaken`-facing form of `translatePath_rename_succ`. -/
@[simp]
theorem translatePath_weaken {scope : Source.Scope}
    (outer : Source.Ctx scope) (binding : Source.Ty scope)
    (path : Source.Path scope) :
    Translation.translatePath (outer.extendTerm binding) path.weaken =
      (Layout.extendRename outer binding).var
        (Translation.translatePath outer path) :=
  translatePath_rename_succ outer binding path

/-- The complete receiver slot follows the same one-step layout renaming. -/
@[simp]
theorem receiverSlot?_rename_succ {scope : Source.Scope}
    (outer : Source.Ctx scope) (binding : Source.Ty scope)
    (receiver : Source.Path scope) :
    Layout.receiverSlot? (outer.extendTerm binding)
        (receiver.rename Source.Rename.succ) =
      (Layout.receiverSlot? outer receiver).map fun slot =>
        slot.rename (Layout.extendRename outer binding) := by
  cases receiver
  rfl

/-- `Path.weaken`-facing form of `receiverSlot?_rename_succ`. -/
@[simp]
theorem receiverSlot?_weaken {scope : Source.Scope}
    (outer : Source.Ctx scope) (binding : Source.Ty scope)
    (receiver : Source.Path scope) :
    Layout.receiverSlot? (outer.extendTerm binding) receiver.weaken =
      (Layout.receiverSlot? outer receiver).map fun slot =>
        slot.rename (Layout.extendRename outer binding) :=
  receiverSlot?_rename_succ outer binding receiver

/-- Both sorted member projections commute with the receiver-slot square. -/
@[simp]
theorem memberSlot?_weaken {scope : Source.Scope}
    (outer : Source.Ctx scope) (binding : Source.Ty scope)
    {sort : DOTCapture.Acyclic.StaticSort}
    (reference : Source.StaticRef sort scope) :
    Layout.memberSlot? (outer.extendTerm binding)
        (reference.rename Source.Rename.succ) =
      (Layout.memberSlot? outer reference).map fun slot =>
        slot.rename (Layout.extendRename outer binding) := by
  cases reference with
  | typeMember receiver =>
      simp only [Source.StaticRef.rename, Layout.memberSlot?]
      rw [receiverSlot?_rename_succ]
      cases Layout.receiverSlot? outer receiver <;> rfl
  | captureMember receiver =>
      simp only [Source.StaticRef.rename, Layout.memberSlot?]
      rw [receiverSlot?_rename_succ]
      cases Layout.receiverSlot? outer receiver <;> rfl

/-! ## Static-reference square -/

/-- A selected static expression is renamed only when its slot exists. -/
@[simp]
theorem translateRef?_weaken {scope : Source.Scope}
    (outer : Source.Ctx scope) (binding : Source.Ty scope)
    {sort : DOTCapture.Acyclic.StaticSort}
    (reference : Source.StaticRef sort scope) :
    Translation.translateRef? (outer.extendTerm binding)
        (reference.rename Source.Rename.succ) =
      (Translation.translateRef? outer reference).map fun expression =>
        expression.rename (Layout.extendRename outer binding) := by
  unfold Translation.translateRef?
  rw [memberSlot?_weaken]
  cases Layout.memberSlot? outer reference <;>
    simp only [Option.map_none, Option.map_some,
      staticSlot_expression_rename]

/-! ## Syntax square -/

/-- Partial capture translation commutes with one source weakening. -/
@[simp]
theorem translateCapture?_rename_succ {scope : Source.Scope}
    (outer : Source.Ctx scope) (binding : Source.Ty scope)
    (capture : Source.Capture scope) :
    Translation.translateCapture? (outer.extendTerm binding)
        (capture.rename Source.Rename.succ) =
      (Translation.translateCapture? outer capture).map fun translated =>
        translated.rename (Layout.extendRename outer binding) := by
  induction capture with
  | empty => rfl
  | union left right leftInduction rightInduction =>
      simp only [Source.Capture.rename, Translation.translateCapture?]
      rw [leftInduction, rightInduction]
      cases Translation.translateCapture? outer left <;>
        cases Translation.translateCapture? outer right <;> rfl
  | singleton path =>
      simp only [Source.Capture.rename, Translation.translateCapture?,
        translatePath_rename_succ, Option.map_some,
        ManySortedFC.Capture.rename]
  | ref reference =>
      simp only [Source.Capture.rename, Translation.translateCapture?,
        translateRef?_weaken]
      cases Translation.translateRef? outer reference with
      | none => rfl
      | some expression =>
          cases expression
          rfl

/-- `Capture.weaken`-facing form of the explicit renaming square. -/
@[simp]
theorem translateCapture?_weaken {scope : Source.Scope}
    (outer : Source.Ctx scope) (binding : Source.Ty scope)
    (capture : Source.Capture scope) :
    Translation.translateCapture? (outer.extendTerm binding)
        capture.weaken =
      (Translation.translateCapture? outer capture).map fun translated =>
        translated.rename (Layout.extendRename outer binding) :=
  translateCapture?_rename_succ outer binding capture

mutual

/-- Partial type translation commutes with one source weakening. -/
@[simp]
theorem translateTy?_rename_succ {scope : Source.Scope}
    (outer : Source.Ctx scope) (binding : Source.Ty scope)
    (type : Source.Ty scope) :
    Translation.translateTy? (outer.extendTerm binding)
        (type.rename Source.Rename.succ) =
      (Translation.translateTy? outer type).map fun translated =>
        translated.rename (Layout.extendRename outer binding) :=
  match type with
  | .top => by rfl
  | .bot => by rfl
  | .one => by rfl
  | .ref reference => by
      simp only [Source.Ty.rename, Translation.translateTy?,
        translateRef?_weaken]
      cases Translation.translateRef? outer reference with
      | none => rfl
      | some expression =>
          cases expression
          rfl
  | .capturing captures shape => by
      simp only [Source.Ty.rename, Translation.translateTy?]
      rw [translateCapture?_rename_succ, translateTy?_rename_succ]
      cases Translation.translateCapture? outer captures <;>
        cases Translation.translateTy? outer shape <;> rfl
  | .object signature => by
      simp only [Source.Ty.rename, Translation.translateTy?]
      rw [translateObjectSig?_rename_succ]
      cases Translation.translateObjectSig? outer signature with
      | none => rfl
      | some bounds =>
          change
            some (Object.existentialShape
              (bounds.rename (Layout.extendRename outer binding))) =
              some ((Object.existentialShape bounds).rename
                (Layout.extendRename outer binding))
          rw [ObjectEncoding.existentialShape_rename]

/-- Translating all four object endpoints commutes with the same weakening. -/
@[simp]
theorem translateObjectSig?_rename_succ {scope : Source.Scope}
    (outer : Source.Ctx scope) (binding : Source.Ty scope)
    (signature : Source.ObjectSig scope) :
    Translation.translateObjectSig? (outer.extendTerm binding)
        (signature.rename Source.Rename.succ) =
      (Translation.translateObjectSig? outer signature).map fun bounds =>
        bounds.rename (Layout.extendRename outer binding) :=
  match signature with
  | .bounds typeLower typeUpper captureLower captureUpper => by
      simp only [Source.ObjectSig.rename, Translation.translateObjectSig?]
      rw [translateTy?_rename_succ, translateTy?_rename_succ,
        translateCapture?_rename_succ, translateCapture?_rename_succ]
      cases Translation.translateTy? outer typeLower <;>
        cases Translation.translateTy? outer typeUpper <;>
          cases Translation.translateCapture? outer captureLower <;>
            cases Translation.translateCapture? outer captureUpper <;> rfl

end

/-- `Ty.weaken`-facing form of the explicit renaming square. -/
@[simp]
theorem translateTy?_weaken {scope : Source.Scope}
    (outer : Source.Ctx scope) (binding : Source.Ty scope)
    (type : Source.Ty scope) :
    Translation.translateTy? (outer.extendTerm binding) type.weaken =
      (Translation.translateTy? outer type).map fun translated =>
        translated.rename (Layout.extendRename outer binding) :=
  translateTy?_rename_succ outer binding type

/-- `ObjectSig.weaken`-facing form of the explicit renaming square. -/
@[simp]
theorem translateObjectSig?_weaken {scope : Source.Scope}
    (outer : Source.Ctx scope) (binding : Source.Ty scope)
    (signature : Source.ObjectSig scope) :
    Translation.translateObjectSig? (outer.extendTerm binding)
        signature.weaken =
      (Translation.translateObjectSig? outer signature).map fun bounds =>
        bounds.rename (Layout.extendRename outer binding) :=
  translateObjectSig?_rename_succ outer binding signature

/-- Sorted source expressions preserve their sort through the square. -/
@[simp]
theorem translateExpr?_weaken {scope : Source.Scope}
    (outer : Source.Ctx scope) (binding : Source.Ty scope)
    {sort : DOTCapture.Acyclic.StaticSort}
    (expression : Source.StaticExpr sort scope) :
    Translation.translateExpr? (outer.extendTerm binding)
        (expression.rename Source.Rename.succ) =
      (Translation.translateExpr? outer expression).map fun translated =>
        translated.rename (Layout.extendRename outer binding) := by
  cases expression with
  | type type =>
      simp only [Source.StaticExpr.rename, Translation.translateExpr?]
      rw [translateTy?_rename_succ]
      cases Translation.translateTy? outer type <;> rfl
  | capture capture =>
      simp only [Source.StaticExpr.rename, Translation.translateExpr?]
      rw [translateCapture?_rename_succ]
      cases Translation.translateCapture? outer capture <;> rfl

/-! ## Older-receiver regressions -/

/-- Adding an ordinary binding weakens the existing object slot once. -/
def afterPlainBinding : Source.Ctx 2 :=
  Translation.exactSourceContext.extendTerm .one

def olderReceiverAfterPlain : Source.Path 2 :=
  Translation.exactReceiver.weaken

def slotAfterPlain : Layout.ReceiverSlot (Layout.sig afterPlainBinding) :=
  (Layout.newestReceiverSlot []).rename
    (Layout.extendRename Translation.exactSourceContext .one)

theorem older_receiver_slot_after_plain_binding :
    Layout.receiverSlot? afterPlainBinding olderReceiverAfterPlain =
      some slotAfterPlain := rfl

theorem older_members_after_plain_binding_share_renamed_slot :
    Translation.translateRef? afterPlainBinding
        olderReceiverAfterPlain.typeMember =
        some slotAfterPlain.alpha.expression ∧
      Translation.translateRef? afterPlainBinding
        olderReceiverAfterPlain.captureMember =
        some slotAfterPlain.chi.expression := by
  exact
    ⟨Translation.translateRef?_typeMember_of_receiverSlot
        older_receiver_slot_after_plain_binding,
      Translation.translateRef?_captureMember_of_receiverSlot
        older_receiver_slot_after_plain_binding⟩

/-- A newer object binding expands by the full static/payload block, but the
older receiver still names the same slot transported through that one step. -/
def newerObjectSignature : Source.ObjectSig 1 :=
  .bounds .one .one .empty .empty

def newerObjectBinding : Source.Ty 1 :=
  .capturing .empty (.object newerObjectSignature)

def afterObjectBinding : Source.Ctx 2 :=
  Translation.exactSourceContext.extendTerm newerObjectBinding

def olderReceiverAfterObject : Source.Path 2 :=
  Translation.exactReceiver.weaken

def slotAfterObject : Layout.ReceiverSlot (Layout.sig afterObjectBinding) :=
  (Layout.newestReceiverSlot []).rename
    (Layout.extendRename Translation.exactSourceContext newerObjectBinding)

theorem older_receiver_slot_after_object_binding :
    Layout.receiverSlot? afterObjectBinding olderReceiverAfterObject =
      some slotAfterObject := rfl

theorem older_members_after_object_binding_share_renamed_slot :
    Translation.translateRef? afterObjectBinding
        olderReceiverAfterObject.typeMember =
        some slotAfterObject.alpha.expression ∧
      Translation.translateRef? afterObjectBinding
        olderReceiverAfterObject.captureMember =
        some slotAfterObject.chi.expression := by
  exact
    ⟨Translation.translateRef?_typeMember_of_receiverSlot
        older_receiver_slot_after_object_binding,
      Translation.translateRef?_captureMember_of_receiverSlot
        older_receiver_slot_after_object_binding⟩

end DOTCaptureToManySortedFC.Acyclic.StaticTranslationMetatheory
