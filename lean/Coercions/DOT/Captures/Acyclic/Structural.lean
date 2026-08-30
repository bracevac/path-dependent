import Coercions.DOT.Captures.Acyclic.MemberTyping

/-!
# Structural metatheory for acyclic DOT captures

Renaming is functorial for every source syntax category.  Object endpoint
projections and the three fixed selections commute with renaming and
weakening.  Finally, a path exposes at most one object signature in a fixed
context.
-/

namespace DOTCapture.Acyclic

namespace StaticRef

@[simp]
theorem rename_id {sort : StaticSort} {scope : Scope}
    (reference : StaticRef sort scope) :
    reference.rename Rename.id = reference := by
  cases reference <;> simp [StaticRef.rename]

@[simp]
theorem rename_comp {sort : StaticSort} {first second third : Scope}
    (reference : StaticRef sort first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (reference.rename rho₁).rename rho₂ =
      reference.rename (rho₁.comp rho₂) := by
  cases reference <;> simp [StaticRef.rename, Path.rename_comp]

@[simp]
theorem expression_rename {sort : StaticSort} {source target : Scope}
    (reference : StaticRef sort source) (rho : Rename source target) :
    reference.expression.rename rho = (reference.rename rho).expression := by
  cases reference <;> rfl

end StaticRef

mutual

@[simp]
def Capture.rename_id {scope : Scope} (capture : Capture scope) :
    capture.rename Rename.id = capture :=
  match capture with
  | .empty => rfl
  | .union left right => by
      simp only [Capture.rename, Capture.rename_id left,
        Capture.rename_id right]
  | .singleton path => by
      simp only [Capture.rename, Path.rename_id path]
  | .ref reference => by
      simp only [Capture.rename, StaticRef.rename_id reference]

@[simp]
def Ty.rename_id {scope : Scope} (type : Ty scope) :
    type.rename Rename.id = type :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref reference => by
      simp only [Ty.rename, StaticRef.rename_id reference]
  | .capturing captures shape => by
      simp only [Ty.rename, Capture.rename_id captures, Ty.rename_id shape]
  | .object signature => by
      simp only [Ty.rename, ObjectSig.rename_id signature]

@[simp]
def ObjectSig.rename_id {scope : Scope} (signature : ObjectSig scope) :
    signature.rename Rename.id = signature :=
  match signature with
  | .bounds typeLower typeUpper captureLower captureUpper => by
      simp only [ObjectSig.rename, Ty.rename_id typeLower,
        Ty.rename_id typeUpper, Capture.rename_id captureLower,
        Capture.rename_id captureUpper]

end

mutual

@[simp]
def Capture.rename_comp {first second third : Scope}
    (capture : Capture first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (capture.rename rho₁).rename rho₂ =
      capture.rename (rho₁.comp rho₂) :=
  match capture with
  | .empty => rfl
  | .union left right => by
      simp only [Capture.rename, Capture.rename_comp left,
        Capture.rename_comp right]
  | .singleton path => by
      simp only [Capture.rename, Path.rename_comp path]
  | .ref reference => by
      simp only [Capture.rename, StaticRef.rename_comp reference]

@[simp]
def Ty.rename_comp {first second third : Scope} (type : Ty first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (type.rename rho₁).rename rho₂ =
      type.rename (rho₁.comp rho₂) :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref reference => by
      simp only [Ty.rename, StaticRef.rename_comp reference]
  | .capturing captures shape => by
      simp only [Ty.rename, Capture.rename_comp captures,
        Ty.rename_comp shape]
  | .object signature => by
      simp only [Ty.rename, ObjectSig.rename_comp signature]

@[simp]
def ObjectSig.rename_comp {first second third : Scope}
    (signature : ObjectSig first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (signature.rename rho₁).rename rho₂ =
      signature.rename (rho₁.comp rho₂) :=
  match signature with
  | .bounds typeLower typeUpper captureLower captureUpper => by
      simp only [ObjectSig.rename, Ty.rename_comp typeLower,
        Ty.rename_comp typeUpper, Capture.rename_comp captureLower,
        Capture.rename_comp captureUpper]

end

namespace StaticExpr

@[simp]
def rename_id {sort : StaticSort} {scope : Scope}
    (expression : StaticExpr sort scope) :
    expression.rename Rename.id = expression :=
  match expression with
  | @StaticExpr.type _ value => by
      simp only [StaticExpr.rename, Ty.rename_id value]
  | @StaticExpr.capture _ value => by
      simp only [StaticExpr.rename, Capture.rename_id value]

@[simp]
def rename_comp {sort : StaticSort} {first second third : Scope}
    (expression : StaticExpr sort first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (expression.rename rho₁).rename rho₂ =
      expression.rename (rho₁.comp rho₂) :=
  match expression with
  | @StaticExpr.type _ value => by
      simp only [StaticExpr.rename, Ty.rename_comp value]
  | @StaticExpr.capture _ value => by
      simp only [StaticExpr.rename, Capture.rename_comp value]

end StaticExpr

namespace Value

@[simp]
def rename_id {scope : Scope} (value : Value scope) :
    value.rename Rename.id = value :=
  match value with
  | .var _ => rfl
  | .unit => rfl
  | .object signature typeWitness captureWitness payload => by
      simp only [Value.rename, ObjectSig.rename_id signature,
        Ty.rename_id typeWitness, Capture.rename_id captureWitness,
        Value.rename_id payload]

@[simp]
def rename_comp {first second third : Scope} (value : Value first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (value.rename rho₁).rename rho₂ =
      value.rename (rho₁.comp rho₂) :=
  match value with
  | .var _ => rfl
  | .unit => rfl
  | .object signature typeWitness captureWitness payload => by
      simp only [Value.rename, ObjectSig.rename_comp signature,
        Ty.rename_comp typeWitness, Capture.rename_comp captureWitness,
        Value.rename_comp payload]

end Value

namespace Term

@[simp]
def rename_id {scope : Scope} (term : Term scope) :
    term.rename Rename.id = term :=
  match term with
  | .ret value => by simp only [Term.rename, Value.rename_id value]
  | .select receiver label => by
      simp only [Term.rename, Path.rename_id receiver]

@[simp]
def rename_comp {first second third : Scope} (term : Term first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (term.rename rho₁).rename rho₂ =
      term.rename (rho₁.comp rho₂) :=
  match term with
  | .ret value => by simp only [Term.rename, Value.rename_comp value]
  | .select receiver label => by
      simp only [Term.rename, Path.rename_comp receiver]

end Term

namespace ObjectSig

@[simp]
theorem typeLower_rename {source target : Scope}
    (signature : ObjectSig source) (rho : Rename source target) :
    (signature.rename rho).typeLower = signature.typeLower.rename rho := by
  cases signature
  rfl

@[simp]
theorem typeUpper_rename {source target : Scope}
    (signature : ObjectSig source) (rho : Rename source target) :
    (signature.rename rho).typeUpper = signature.typeUpper.rename rho := by
  cases signature
  rfl

@[simp]
theorem captureLower_rename {source target : Scope}
    (signature : ObjectSig source) (rho : Rename source target) :
    (signature.rename rho).captureLower =
      signature.captureLower.rename rho := by
  cases signature
  rfl

@[simp]
theorem captureUpper_rename {source target : Scope}
    (signature : ObjectSig source) (rho : Rename source target) :
    (signature.rename rho).captureUpper =
      signature.captureUpper.rename rho := by
  cases signature
  rfl

@[simp]
theorem typeLower_weaken {scope : Scope} (signature : ObjectSig scope) :
    signature.weaken.typeLower = signature.typeLower.weaken := by
  cases signature
  rfl

@[simp]
theorem typeUpper_weaken {scope : Scope} (signature : ObjectSig scope) :
    signature.weaken.typeUpper = signature.typeUpper.weaken := by
  cases signature
  rfl

@[simp]
theorem captureLower_weaken {scope : Scope} (signature : ObjectSig scope) :
    signature.weaken.captureLower = signature.captureLower.weaken := by
  cases signature
  rfl

@[simp]
theorem captureUpper_weaken {scope : Scope} (signature : ObjectSig scope) :
    signature.weaken.captureUpper = signature.captureUpper.weaken := by
  cases signature
  rfl

end ObjectSig

namespace Path

@[simp]
theorem typeMember_rename {source target : Scope} (receiver : Path source)
    (rho : Rename source target) :
    receiver.typeMember.rename rho = (receiver.rename rho).typeMember := rfl

@[simp]
theorem captureMember_rename {source target : Scope}
    (receiver : Path source) (rho : Rename source target) :
    receiver.captureMember.rename rho =
      (receiver.rename rho).captureMember := rfl

@[simp]
theorem selectedType_rename {source target : Scope} (receiver : Path source)
    (rho : Rename source target) :
    receiver.selectedType.rename rho =
      (receiver.rename rho).selectedType := rfl

@[simp]
theorem selectedCapture_rename {source target : Scope}
    (receiver : Path source) (rho : Rename source target) :
    receiver.selectedCapture.rename rho =
      (receiver.rename rho).selectedCapture := rfl

@[simp]
theorem valueMemberType_rename {source target : Scope}
    (receiver : Path source) (rho : Rename source target) :
    receiver.valueMemberType.rename rho =
      (receiver.rename rho).valueMemberType := rfl

@[simp]
theorem selectedType_weaken {scope : Scope} (receiver : Path scope) :
    receiver.selectedType.weaken = receiver.weaken.selectedType := rfl

@[simp]
theorem selectedCapture_weaken {scope : Scope} (receiver : Path scope) :
    receiver.selectedCapture.weaken = receiver.weaken.selectedCapture := rfl

@[simp]
theorem valueMemberType_weaken {scope : Scope} (receiver : Path scope) :
    receiver.valueMemberType.weaken = receiver.weaken.valueMemberType := rfl

end Path

namespace ExposesObject

/-- A fixed receiver path exposes at most one object signature. -/
theorem functional {scope : Scope} {context : Ctx scope}
    {receiver : Path scope} {first second : ObjectSig scope}
    (firstExposure : ExposesObject context receiver first)
    (secondExposure : ExposesObject context receiver second) :
    first = second := by
  cases firstExposure with
  | «variable» firstFound =>
      cases secondExposure with
      | «variable» secondFound =>
          have objectEquality := firstFound.symm.trans secondFound
          injection objectEquality

end ExposesObject

end DOTCapture.Acyclic
