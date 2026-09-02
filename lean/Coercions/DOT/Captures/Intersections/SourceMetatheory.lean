import Coercions.DOT.Captures.Intersections.SourceSyntax
import Coercions.DOT.Captures.Intersections.SignatureMetatheory

/-!
# Static metatheory for captured-DOT intersection interfaces

This file proves structural renaming laws for the source syntax and the two
basic facts about interface collection: every successful result is normalized,
and a fixed interface has at most one successful result.  It makes no choice
about the runtime representation of object payloads.
-/

namespace DOTCapture.Intersections.Source

namespace StaticRef

@[simp]
theorem rename_id {sort : StaticSort} {scope : Scope}
    (reference : StaticRef sort scope) :
    reference.rename DOTCapture.Acyclic.Rename.id = reference := by
  cases reference <;> simp [rename]

@[simp]
theorem rename_comp {sort : StaticSort} {first second third : Scope}
    (reference : StaticRef sort first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (reference.rename rho₁).rename rho₂ =
      reference.rename (rho₁.comp rho₂) := by
  cases reference <;> simp [rename]

end StaticRef

mutual

@[simp]
theorem Capture.rename_id {scope : Scope} (capture : Capture scope) :
    capture.rename DOTCapture.Acyclic.Rename.id = capture := by
  cases capture with
  | empty => rfl
  | union left right =>
      simp [Capture.rename, Capture.rename_id left, Capture.rename_id right]
  | singleton path => simp [Capture.rename]
  | ref reference => simp [Capture.rename]

@[simp]
theorem Ty.rename_id {scope : Scope} (type : Ty scope) :
    type.rename DOTCapture.Acyclic.Rename.id = type := by
  cases type with
  | top => rfl
  | bot => rfl
  | one => rfl
  | ref reference => simp [Ty.rename]
  | arr domain codomain =>
      simp [Ty.rename, Ty.rename_id domain, Ty.rename_id codomain]
  | capturing captures shape =>
      simp [Ty.rename, Capture.rename_id, Ty.rename_id shape]
  | object object =>
      simp [Ty.rename, ObjectType.rename_id object]

@[simp]
theorem Interface.rename_id {scope : Scope} (interface : Interface scope) :
    interface.rename DOTCapture.Acyclic.Rename.id = interface := by
  cases interface with
  | empty => rfl
  | typeMember label lower upper =>
      simp [Interface.rename, Ty.rename_id lower, Ty.rename_id upper]
  | captureMember label lower upper =>
      simp [Interface.rename, Capture.rename_id]
  | inter left right =>
      simp [Interface.rename, Interface.rename_id left,
        Interface.rename_id right]

@[simp]
theorem ObjectType.rename_id {scope : Scope} (object : ObjectType scope) :
    object.rename DOTCapture.Acyclic.Rename.id = object := by
  cases object with
  | mk interface representation outerCapture =>
      simp [ObjectType.rename, Interface.rename_id interface,
        Ty.rename_id representation, Capture.rename_id outerCapture]

end

mutual

@[simp]
theorem Capture.rename_comp {first second third : Scope}
    (capture : Capture first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (capture.rename rho₁).rename rho₂ =
      capture.rename (rho₁.comp rho₂) := by
  cases capture with
  | empty => rfl
  | union left right =>
      simp [Capture.rename, Capture.rename_comp left rho₁ rho₂,
        Capture.rename_comp right rho₁ rho₂]
  | singleton path => simp [Capture.rename]
  | ref reference => simp [Capture.rename]

@[simp]
theorem Ty.rename_comp {first second third : Scope} (type : Ty first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (type.rename rho₁).rename rho₂ = type.rename (rho₁.comp rho₂) := by
  cases type with
  | top => rfl
  | bot => rfl
  | one => rfl
  | ref reference => simp [Ty.rename]
  | arr domain codomain =>
      simp [Ty.rename, Ty.rename_comp domain rho₁ rho₂,
        Ty.rename_comp codomain rho₁ rho₂]
  | capturing captures shape =>
      simp [Ty.rename, Capture.rename_comp, Ty.rename_comp shape rho₁ rho₂]
  | object object =>
      simp [Ty.rename, ObjectType.rename_comp object rho₁ rho₂]

@[simp]
theorem Interface.rename_comp {first second third : Scope}
    (interface : Interface first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (interface.rename rho₁).rename rho₂ =
      interface.rename (rho₁.comp rho₂) := by
  cases interface with
  | empty => rfl
  | typeMember label lower upper =>
      simp [Interface.rename, Ty.rename_comp lower rho₁ rho₂,
        Ty.rename_comp upper rho₁ rho₂]
  | captureMember label lower upper =>
      simp [Interface.rename, Capture.rename_comp]
  | inter left right =>
      simp [Interface.rename, Interface.rename_comp left rho₁ rho₂,
        Interface.rename_comp right rho₁ rho₂]

@[simp]
theorem ObjectType.rename_comp {first second third : Scope}
    (object : ObjectType first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (object.rename rho₁).rename rho₂ =
      object.rename (rho₁.comp rho₂) := by
  cases object with
  | mk interface representation outerCapture =>
      simp [ObjectType.rename, Interface.rename_comp interface rho₁ rho₂,
        Ty.rename_comp representation rho₁ rho₂,
        Capture.rename_comp outerCapture rho₁ rho₂]

end

namespace StaticExpr

@[simp]
theorem rename_id {sort : StaticSort} {scope : Scope}
    (expression : StaticExpr sort scope) :
    expression.rename DOTCapture.Acyclic.Rename.id = expression := by
  cases expression <;> simp [rename]

@[simp]
theorem rename_comp {sort : StaticSort} {first second third : Scope}
    (expression : StaticExpr sort first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (expression.rename rho₁).rename rho₂ =
      expression.rename (rho₁.comp rho₂) := by
  cases expression <;> simp [rename]

end StaticExpr

namespace Interface

/-- Successful collection always produces the canonical sorted, nonempty,
one-entry-per-label representation. -/
theorem collect_normalized {scope : Scope} (interface : Interface scope)
    {signature : DOTCapture.Intersections.Signature (Expr scope)}
    (success : interface.collect = .ok signature) :
    signature.Normalized := by
  cases interface with
  | empty =>
      simp only [collect, Except.ok.injEq] at success
      subst signature
      exact DOTCapture.Intersections.Signature.empty_normalized
  | typeMember label lower upper =>
      simp only [collect, Except.ok.injEq] at success
      subst signature
      exact DOTCapture.Intersections.Signature.singletonType_normalized
        (Expr := Expr scope) label (StaticExpr.type lower)
          (StaticExpr.type upper)
  | captureMember label lower upper =>
      simp only [collect, Except.ok.injEq] at success
      subst signature
      exact DOTCapture.Intersections.Signature.singletonCapture_normalized
        (Expr := Expr scope) label (StaticExpr.capture lower)
          (StaticExpr.capture upper)
  | inter left right =>
      simp only [collect] at success
      cases leftResult : left.collect with
      | error conflict =>
          rw [leftResult] at success
          nomatch success
      | ok leftSignature =>
          cases rightResult : right.collect with
          | error conflict =>
              rw [leftResult, rightResult] at success
              nomatch success
          | ok rightSignature =>
              rw [leftResult, rightResult] at success
              exact DOTCapture.Intersections.Signature.merge?_normalized
                leftSignature rightSignature signature
                (collect_normalized left leftResult)
                (collect_normalized right rightResult) success
termination_by interface

/-- Collection is an executable function, so one source interface cannot
collect successfully to two distinct signatures. -/
theorem collect_deterministic {scope : Scope} (interface : Interface scope)
    {first second : DOTCapture.Intersections.Signature (Expr scope)}
    (firstSuccess : interface.collect = .ok first)
    (secondSuccess : interface.collect = .ok second) : first = second := by
  exact Except.ok.inj (firstSuccess.symm.trans secondSuccess)

end Interface

/-! ## Fixed-interface embedding -/

/-- The canonical normalized layout assigned to one fixed M10 object
signature: type label `0`, then capture label `1`, with one interval each. -/
def embeddedM10Signature {scope : Scope} :
    DOTCapture.Acyclic.ObjectSig scope ->
      DOTCapture.Intersections.Signature (Interface.Expr scope)
  | .bounds typeLower typeUpper captureLower captureUpper =>
      { entries :=
          [DOTCapture.Intersections.Entry.type m10TypeLabel
              [⟨StaticExpr.type (embedM10Ty typeLower),
                StaticExpr.type (embedM10Ty typeUpper)⟩],
            DOTCapture.Intersections.Entry.capture m10CaptureLabel
              [⟨StaticExpr.capture (embedM10Capture captureLower),
                StaticExpr.capture (embedM10Capture captureUpper)⟩]] }

/-- Embedding an M10 object signature and collecting it produces exactly the
canonical two-entry type/capture layout. -/
theorem collect_embedM10ObjectSig {scope : Scope}
    (signature : DOTCapture.Acyclic.ObjectSig scope) :
    (embedM10ObjectSig signature).collect =
      .ok (embeddedM10Signature signature) := by
  cases signature
  simp [embedM10ObjectSig, Interface.collect, embeddedM10Signature, bind,
    Except.bind,
    DOTCapture.Intersections.Signature.merge?,
    DOTCapture.Intersections.Signature.singletonType,
    DOTCapture.Intersections.Signature.singletonCapture,
    DOTCapture.Intersections.Signature.mergeEntries?,
    DOTCapture.Intersections.Signature.insertEntry?, m10TypeLabel,
    m10CaptureLabel, DOTCapture.Intersections.Entry.label]

theorem embeddedM10Signature_has_two_entries {scope : Scope}
    (signature : DOTCapture.Acyclic.ObjectSig scope) :
    (embeddedM10Signature signature).entries.length = 2 := by
  cases signature
  rfl

theorem embeddedM10Signature_is_normalized {scope : Scope}
    (signature : DOTCapture.Acyclic.ObjectSig scope) :
    (embeddedM10Signature signature).Normalized :=
  Interface.collect_normalized (embedM10ObjectSig signature)
    (collect_embedM10ObjectSig signature)

end DOTCapture.Intersections.Source
