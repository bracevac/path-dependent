import Coercions.DOT.Captures.Intersections.GeneralExpression.Typing

/-!
# M10 typing conservativity for cumulative general expressions
-/

namespace DOTCapture.Intersections.GeneralExpression

namespace Embedding

namespace M10

abbrev Ctx := DOTCapture.Acyclic.Ctx
abbrev StaticRef := DOTCapture.Acyclic.StaticRef
abbrev StaticExpr := DOTCapture.Acyclic.StaticExpr
abbrev ObjectSig := DOTCapture.Acyclic.ObjectSig

end M10

/-- Embed an M10 source context pointwise. -/
def embedCtx : {scope : Scope} -> M10.Ctx scope -> Ctx scope
  | _, .nil => .nil
  | _, .extend outer type => .extend (embedCtx outer) (Source.embedM10Ty type)

/-- Embed a fixed M10 member reference at its reserved M11 label. -/
def embedStaticRef {sort : StaticSort} {scope : Scope} :
    M10.StaticRef sort scope -> StaticRef sort scope
  | .typeMember receiver =>
      .typeMember (Source.embedM10Path receiver) Source.m10TypeLabel
  | .captureMember receiver =>
      .captureMember (Source.embedM10Path receiver) Source.m10CaptureLabel

/-- Embed a sorted M10 static expression. -/
def embedStaticExpr {sort : StaticSort} {scope : Scope} :
    M10.StaticExpr sort scope -> StaticExpr sort scope
  | .type type => .type (Source.embedM10Ty type)
  | .capture capture => .capture (Source.embedM10Capture capture)

@[simp]
theorem embedPath_rename {source target : Scope}
    (path : DOTCapture.Acyclic.Path source)
    (rho : DOTCapture.Acyclic.Rename source target) :
    Source.embedM10Path (path.rename rho) =
      (Source.embedM10Path path).rename rho := by
  cases path
  rfl

mutual

@[simp]
theorem embedCapture_rename {source target : Scope}
    (capture : DOTCapture.Acyclic.Capture source)
    (rho : DOTCapture.Acyclic.Rename source target) :
    Source.embedM10Capture (capture.rename rho) =
      (Source.embedM10Capture capture).rename rho := by
  cases capture with
  | empty => rfl
  | union left right =>
      simp [DOTCapture.Acyclic.Capture.rename, Source.Capture.rename,
        Source.embedM10Capture, embedCapture_rename left rho,
        embedCapture_rename right rho]
  | singleton path => simp [DOTCapture.Acyclic.Capture.rename,
      Source.Capture.rename, Source.embedM10Capture]
  | ref reference => cases reference <;> simp [DOTCapture.Acyclic.Capture.rename,
      DOTCapture.Acyclic.StaticRef.rename, Source.Capture.rename,
      Source.StaticRef.rename, Source.embedM10Capture]

@[simp]
theorem embedTy_rename {source target : Scope}
    (type : DOTCapture.Acyclic.Ty source)
    (rho : DOTCapture.Acyclic.Rename source target) :
    Source.embedM10Ty (type.rename rho) =
      (Source.embedM10Ty type).rename rho := by
  cases type with
  | top => simp [DOTCapture.Acyclic.Ty.rename, Source.Ty.rename,
      Source.embedM10Ty]
  | bot => simp [DOTCapture.Acyclic.Ty.rename, Source.Ty.rename,
      Source.embedM10Ty]
  | one => simp [DOTCapture.Acyclic.Ty.rename, Source.Ty.rename,
      Source.embedM10Ty]
  | ref reference => cases reference <;> simp [DOTCapture.Acyclic.Ty.rename,
      DOTCapture.Acyclic.StaticRef.rename, Source.Ty.rename,
      Source.StaticRef.rename, Source.embedM10Ty]
  | arr domain codomain =>
      simp [DOTCapture.Acyclic.Ty.rename, Source.Ty.rename,
        Source.embedM10Ty, embedTy_rename domain rho,
        embedTy_rename codomain rho]
  | capturing captures shape =>
      simp [DOTCapture.Acyclic.Ty.rename, Source.Ty.rename,
        Source.embedM10Ty, embedCapture_rename captures rho,
        embedTy_rename shape rho]
  | object signature =>
      cases signature
      simp only [DOTCapture.Acyclic.Ty.rename,
        DOTCapture.Acyclic.ObjectSig.rename,
        Source.Ty.rename, Source.ObjectType.rename,
        Source.Interface.rename, Source.embedM10Ty,
        Source.embedM10ObjectType, Source.embedM10ObjectSig,
        Source.Capture.rename, Source.StaticRef.rename,
        DOTCapture.Acyclic.ObjectSig.captureUpper,
        embedTy_rename, embedCapture_rename]

end

@[simp]
theorem embedTy_weaken {scope : Scope} (type : DOTCapture.Acyclic.Ty scope) :
    Source.embedM10Ty type.weaken =
      (Source.embedM10Ty type).rename DOTCapture.Acyclic.Rename.succ :=
  embedTy_rename type DOTCapture.Acyclic.Rename.succ

@[simp]
theorem embedCapture_weaken {scope : Scope}
    (capture : DOTCapture.Acyclic.Capture scope) :
    Source.embedM10Capture capture.weaken =
      (Source.embedM10Capture capture).rename
        DOTCapture.Acyclic.Rename.succ :=
  embedCapture_rename capture DOTCapture.Acyclic.Rename.succ

@[simp]
theorem embedObjectType_rename {source target : Scope}
    (signature : M10.ObjectSig source)
    (rho : DOTCapture.Acyclic.Rename source target) :
    Source.embedM10ObjectType (signature.rename rho) =
      (Source.embedM10ObjectType signature).rename rho := by
  cases signature
  simp [DOTCapture.Acyclic.ObjectSig.rename,
    DOTCapture.Acyclic.ObjectSig.captureUpper,
    Source.embedM10ObjectType, Source.embedM10ObjectSig,
    Source.ObjectType.rename, Source.Interface.rename,
    embedTy_rename, embedCapture_rename, Source.Ty.rename,
    Source.Capture.rename, Source.StaticRef.rename]

@[simp]
theorem embedObjectType_weaken {scope : Scope}
    (signature : M10.ObjectSig scope) :
    Source.embedM10ObjectType signature.weaken =
      (Source.embedM10ObjectType signature).rename
        DOTCapture.Acyclic.Rename.succ :=
  embedObjectType_rename signature DOTCapture.Acyclic.Rename.succ

@[simp]
theorem embedTy_stripCapture {scope : Scope}
    (type : DOTCapture.Acyclic.Ty scope) :
    Source.embedM10Ty type.stripCapture =
      (Source.embedM10Ty type).stripCapture := by
  cases type with
  | top => simp [DOTCapture.Acyclic.Ty.stripCapture,
      Source.embedM10Ty, Source.Ty.stripCapture]
  | bot => simp [DOTCapture.Acyclic.Ty.stripCapture,
      Source.embedM10Ty, Source.Ty.stripCapture]
  | one => simp [DOTCapture.Acyclic.Ty.stripCapture,
      Source.embedM10Ty, Source.Ty.stripCapture]
  | ref reference => cases reference <;>
      simp [DOTCapture.Acyclic.Ty.stripCapture,
        Source.embedM10Ty, Source.Ty.stripCapture]
  | arr => simp [DOTCapture.Acyclic.Ty.stripCapture,
      Source.embedM10Ty, Source.Ty.stripCapture]
  | capturing => simp [DOTCapture.Acyclic.Ty.stripCapture,
      Source.embedM10Ty, Source.Ty.stripCapture]
  | object => simp [DOTCapture.Acyclic.Ty.stripCapture,
      Source.embedM10Ty, Source.Ty.stripCapture]

@[simp]
theorem embedTy_outerCapture {scope : Scope}
    (type : DOTCapture.Acyclic.Ty scope) :
    Source.embedM10Capture type.outerCapture =
      (Source.embedM10Ty type).outerCapture := by
  cases type with
  | top => simp [DOTCapture.Acyclic.Ty.outerCapture,
      Source.embedM10Ty, Source.embedM10Capture, Source.Ty.outerCapture]
  | bot => simp [DOTCapture.Acyclic.Ty.outerCapture,
      Source.embedM10Ty, Source.embedM10Capture, Source.Ty.outerCapture]
  | one => simp [DOTCapture.Acyclic.Ty.outerCapture,
      Source.embedM10Ty, Source.embedM10Capture, Source.Ty.outerCapture]
  | ref reference => cases reference <;>
      simp [DOTCapture.Acyclic.Ty.outerCapture,
        Source.embedM10Ty, Source.embedM10Capture, Source.Ty.outerCapture]
  | arr => simp [DOTCapture.Acyclic.Ty.outerCapture,
      Source.embedM10Ty, Source.embedM10Capture, Source.Ty.outerCapture]
  | capturing => simp [DOTCapture.Acyclic.Ty.outerCapture,
      Source.embedM10Ty, Source.Ty.outerCapture]
  | object => simp [DOTCapture.Acyclic.Ty.outerCapture,
      Source.embedM10Ty, Source.embedM10Capture, Source.Ty.outerCapture]

@[simp]
theorem embedFormedType {scope : Scope} (signature : M10.ObjectSig scope) :
    Source.embedM10Ty
        (DOTCapture.Acyclic.GeneralExpression.ObjectSig.formedType signature) =
      (Source.embedM10ObjectType signature).formedType := by
  cases signature
  simp [DOTCapture.Acyclic.GeneralExpression.ObjectSig.formedType,
    Source.ObjectType.formedType, Source.embedM10Ty,
    Source.embedM10ObjectType, DOTCapture.Acyclic.ObjectSig.captureUpper]

@[simp]
theorem embedGeneralFormedType {scope : Scope}
    (signature : M10.ObjectSig scope) :
    Source.embedM10Ty
        (DOTCapture.Acyclic.GeneralExpression.ObjectSig.formedType signature) =
      ObjectType.formedType (Source.embedM10ObjectType signature) := by
  cases signature
  simp [DOTCapture.Acyclic.GeneralExpression.ObjectSig.formedType,
    ObjectType.formedType, Source.embedM10Ty,
    Source.embedM10ObjectType, DOTCapture.Acyclic.ObjectSig.captureUpper]

@[simp]
theorem sourceFormedType_eq_general {scope : Scope}
    (object : ObjectType scope) :
    Source.ObjectType.formedType object = ObjectType.formedType object := by
  cases object
  rfl

@[simp]
theorem embedObjectOuterCapture {scope : Scope}
    (signature : M10.ObjectSig scope) :
    (Source.embedM10ObjectType signature).outerCapture =
      Source.embedM10Capture signature.captureUpper := by
  cases signature
  simp [Source.embedM10ObjectType, Source.ObjectType.outerCapture,
    DOTCapture.Acyclic.ObjectSig.captureUpper]

@[simp]
theorem embedCapture_seq {scope : Scope}
    (first second : DOTCapture.Acyclic.Capture scope) :
    Source.embedM10Capture
        (DOTCapture.Acyclic.GeneralExpression.Capture.seq first second) =
      Source.Capture.seq (Source.embedM10Capture first)
        (Source.embedM10Capture second) := by
  cases first with
  | empty => rfl
  | union => rfl
  | singleton => rfl
  | ref reference => cases reference <;> rfl

@[simp]
theorem embedCtx_lookup {scope : Scope} (context : M10.Ctx scope)
    (name : DOTCapture.Acyclic.Var scope) :
    (embedCtx context).lookup name =
      Source.embedM10Ty (context.lookup name) := by
  induction context with
  | nil => nomatch name
  | extend outer type induction =>
      cases name with
      | here => exact (embedTy_weaken type).symm
      | there name =>
          change ((embedCtx outer).lookup name).rename
              DOTCapture.Acyclic.Rename.succ =
            Source.embedM10Ty ((outer.lookup name).weaken)
          rw [induction name, embedTy_weaken]

/-- M10's ordinary-binding side condition is preserved literally. -/
theorem embedPlain {scope : Scope} {type : DOTCapture.Acyclic.Ty scope}
    (plain : type.IsPlain) : Plain (Source.embedM10Ty type) := by
  cases type with
  | top => simp [Plain, Source.embedM10Ty, Source.Ty.stripCapture]
  | bot => simp [Plain, Source.embedM10Ty, Source.Ty.stripCapture]
  | one => simp [Plain, Source.embedM10Ty, Source.Ty.stripCapture]
  | ref reference => cases reference <;>
      simp [Plain, Source.embedM10Ty, Source.Ty.stripCapture]
  | arr => simp [Plain, Source.embedM10Ty, Source.Ty.stripCapture]
  | capturing captures shape =>
      cases shape with
      | top => simp [Plain, Source.embedM10Ty, Source.Ty.stripCapture]
      | bot => simp [Plain, Source.embedM10Ty, Source.Ty.stripCapture]
      | one => simp [Plain, Source.embedM10Ty, Source.Ty.stripCapture]
      | ref reference => cases reference <;>
          simp [Plain, Source.embedM10Ty, Source.Ty.stripCapture]
      | arr => simp [Plain, Source.embedM10Ty, Source.Ty.stripCapture]
      | capturing => simp [Plain, Source.embedM10Ty, Source.Ty.stripCapture]
      | object =>
          simp [DOTCapture.Acyclic.Ty.IsPlain,
            DOTCapture.Acyclic.Ty.objectSignature?,
            DOTCapture.Acyclic.Ty.stripCapture] at plain
  | object =>
      simp [DOTCapture.Acyclic.Ty.IsPlain,
        DOTCapture.Acyclic.Ty.objectSignature?,
        DOTCapture.Acyclic.Ty.stripCapture] at plain

/-- Stable object exposure is preserved by pointwise context embedding. -/
def embedExposes {scope : Scope} {context : M10.Ctx scope}
    {receiver : DOTCapture.Acyclic.Path scope}
    {signature : M10.ObjectSig scope}
    (exposes : DOTCapture.Acyclic.ExposesObject context receiver signature) :
    Source.ExposesObject (embedCtx context) (Source.embedM10Path receiver)
      (Source.embedM10ObjectType signature) :=
  match exposes with
  | .variable found => .variable (by
      rw [embedCtx_lookup, <- embedTy_stripCapture, found]
      simp [Source.embedM10Ty])

@[simp]
theorem embedStaticRef_expression {scope : Scope} {sort : StaticSort}
    (reference : M10.StaticRef sort scope) :
    Source.StaticRef.expression (embedStaticRef reference) =
      embedStaticExpr reference.expression := by
  cases reference <;> simp [embedStaticRef, embedStaticExpr,
    DOTCapture.Acyclic.StaticRef.expression,
    Source.StaticRef.expression, Source.embedM10Ty,
    Source.embedM10Capture]

@[simp]
theorem embedRepresentationAt {scope : Scope}
    (receiver : DOTCapture.Acyclic.Path scope)
    (signature : M10.ObjectSig scope) :
    ObjectType.representationAt (Source.embedM10ObjectType signature)
        (Source.embedM10Path receiver) =
      Source.embedM10Ty receiver.valueMemberType := by
  cases receiver
  cases signature
  simp [ObjectType.representationAt, Source.ObjectType.representation,
    Source.Ty.openAt, Source.Capture.openAt, Source.embedM10ObjectType,
    DOTCapture.Acyclic.Path.valueMemberType,
    DOTCapture.Acyclic.Path.selectedCapture,
    DOTCapture.Acyclic.Path.selectedType,
    DOTCapture.Acyclic.Path.captureMember,
    DOTCapture.Acyclic.Path.typeMember, Source.embedM10Ty,
    Source.embedM10Capture, Source.embedM10Path]

@[simp]
theorem embedRepresentationAt_outerCapture {scope : Scope}
    (receiver : DOTCapture.Acyclic.Path scope)
    (signature : M10.ObjectSig scope) :
    (ObjectType.representationAt (Source.embedM10ObjectType signature)
      (Source.embedM10Path receiver)).outerCapture =
      Source.embedM10Capture receiver.selectedCapture := by
  rw [embedRepresentationAt, ← embedTy_outerCapture]
  cases receiver
  rfl

mutual

/-- Embedded M10 capture endpoints contain no M11-local references. -/
@[simp]
theorem openAt_embedCapture {scope : Scope} (receiver : Path scope)
    (capture : DOTCapture.Acyclic.Capture scope) :
    Source.Capture.openAt receiver (Source.embedM10Capture capture) =
      Source.embedM10Capture capture := by
  cases capture with
  | empty => rfl
  | union left right =>
      simp [Source.Capture.openAt, Source.embedM10Capture,
        openAt_embedCapture receiver left,
        openAt_embedCapture receiver right]
  | singleton path => rfl
  | ref reference => cases reference <;> rfl

/-- Embedded M10 type endpoints contain no M11-local references. -/
@[simp]
theorem openAt_embedTy {scope : Scope} (receiver : Path scope)
    (type : DOTCapture.Acyclic.Ty scope) :
    Source.Ty.openAt receiver (Source.embedM10Ty type) =
      Source.embedM10Ty type := by
  cases type with
  | top => simp [Source.Ty.openAt, Source.embedM10Ty]
  | bot => simp [Source.Ty.openAt, Source.embedM10Ty]
  | one => simp [Source.Ty.openAt, Source.embedM10Ty]
  | ref reference => cases reference <;>
      simp [Source.Ty.openAt, Source.embedM10Ty]
  | arr domain codomain =>
      simp [Source.Ty.openAt, Source.embedM10Ty,
        openAt_embedTy receiver domain, openAt_embedTy receiver codomain]
  | capturing captures shape =>
      simp [Source.Ty.openAt, Source.embedM10Ty,
        openAt_embedCapture receiver captures, openAt_embedTy receiver shape]
  | object signature =>
      simp [Source.Ty.openAt, Source.embedM10Ty]

end

def embeddedTypeOccurrence {scope : Scope} (signature : M10.ObjectSig scope) :
    (Source.embedM10ObjectType signature).interface.HasTypeOccurrence
      Source.m10TypeLabel (Source.embedM10Ty signature.typeLower)
        (Source.embedM10Ty signature.typeUpper) := by
  cases signature
  simpa [Source.embedM10ObjectType, Source.embedM10ObjectSig,
    Source.ObjectType.interface, DOTCapture.Acyclic.ObjectSig.typeLower,
    DOTCapture.Acyclic.ObjectSig.typeUpper] using
    (Source.Interface.HasTypeOccurrence.left
      (Source.Interface.HasTypeOccurrence.here))

def embeddedCaptureOccurrence {scope : Scope}
    (signature : M10.ObjectSig scope) :
    (Source.embedM10ObjectType signature).interface.HasCaptureOccurrence
      Source.m10CaptureLabel (Source.embedM10Capture signature.captureLower)
        (Source.embedM10Capture signature.captureUpper) := by
  cases signature
  simpa [Source.embedM10ObjectType, Source.embedM10ObjectSig,
    Source.ObjectType.interface, DOTCapture.Acyclic.ObjectSig.captureLower,
    DOTCapture.Acyclic.ObjectSig.captureUpper] using
    (Source.Interface.HasCaptureOccurrence.right
      (Source.Interface.HasCaptureOccurrence.here))

def embedHasLower {scope : Scope} {context : M10.Ctx scope}
    {sort : StaticSort} {reference : M10.StaticRef sort scope}
    {endpoint : M10.StaticExpr sort scope}
    (bound : DOTCapture.Acyclic.HasLower context reference endpoint) :
    Source.HasLower (embedCtx context) (embedStaticRef reference)
      (embedStaticExpr endpoint) := by
  cases bound with
  | typeMember exposes =>
      simpa [embedStaticRef, embedStaticExpr] using
        (Source.HasLower.typeMember (embedExposes exposes)
          (embeddedTypeOccurrence _))
  | captureMember exposes =>
      simpa [embedStaticRef, embedStaticExpr] using
        (Source.HasLower.captureMember (embedExposes exposes)
          (embeddedCaptureOccurrence _))

def embedHasUpper {scope : Scope} {context : M10.Ctx scope}
    {sort : StaticSort} {reference : M10.StaticRef sort scope}
    {endpoint : M10.StaticExpr sort scope}
    (bound : DOTCapture.Acyclic.HasUpper context reference endpoint) :
    Source.HasUpper (embedCtx context) (embedStaticRef reference)
      (embedStaticExpr endpoint) := by
  cases bound with
  | typeMember exposes =>
      simpa [embedStaticRef, embedStaticExpr] using
        (Source.HasUpper.typeMember (embedExposes exposes)
          (embeddedTypeOccurrence _))
  | captureMember exposes =>
      simpa [embedStaticRef, embedStaticExpr] using
        (Source.HasUpper.captureMember (embedExposes exposes)
          (embeddedCaptureOccurrence _))

/-- Every proof-relevant M10 inclusion has the same proof tree after
embedding. The payload-root case uses the opened M11 representation. -/
def embedIncludes {scope : Scope} {context : M10.Ctx scope}
    {sort : StaticSort} {source target : M10.StaticExpr sort scope}
    (proof : DOTCapture.Acyclic.Includes context source target) :
    Includes (embedCtx context) (embedStaticExpr source)
      (embedStaticExpr target) :=
  match proof with
  | .refl => .refl
  | .trans first second => .trans (embedIncludes first) (embedIncludes second)
  | .lower bound => by
      simpa using Includes.source (.lower (embedHasLower bound))
  | .upper bound => by
      simpa using Includes.source (.upper (embedHasUpper bound))
  | .typeTop => by
      simpa [embedStaticExpr, Source.embedM10Ty] using Includes.typeTop
  | .typeBottom => by
      simpa [embedStaticExpr, Source.embedM10Ty] using Includes.typeBottom
  | .typeCapturing captures shape => by
      simpa [embedStaticExpr, Source.embedM10Ty] using
        Includes.typeCapturing (embedIncludes captures) (embedIncludes shape)
  | .captureEmpty => by
      simpa [embedStaticExpr, Source.embedM10Capture] using
        Includes.captureEmpty
  | .captureUnionLeft => by
      simpa [embedStaticExpr, Source.embedM10Capture] using
        Includes.captureUnionLeft
  | .captureUnionRight => by
      simpa [embedStaticExpr, Source.embedM10Capture] using
        Includes.captureUnionRight
  | .captureUnionElim left right =>
      .captureUnionElim (embedIncludes left) (embedIncludes right)
  | @DOTCapture.Acyclic.Includes.payloadRoot _ _ receiver signature exposes => by
      have mapped := Includes.payloadRoot (embedExposes exposes)
      rw [embedRepresentationAt] at mapped
      have endpoint := embedTy_outerCapture receiver.valueMemberType
      have endpoint' :
          Source.embedM10Capture receiver.selectedCapture =
            (Source.embedM10Ty receiver.valueMemberType).outerCapture := by
        simpa [DOTCapture.Acyclic.Path.valueMemberType,
          DOTCapture.Acyclic.Ty.outerCapture] using endpoint
      rw [<- endpoint'] at mapped
      simpa [embedStaticExpr, Source.embedM10Capture,
        DOTCapture.Acyclic.StaticRef.expression,
        DOTCapture.Acyclic.Path.selectedCapture,
        DOTCapture.Acyclic.Path.valueMemberType,
        DOTCapture.Acyclic.Ty.outerCapture]
        using mapped

/-! ### Realizing the fixed M10 interface -/

/-- The two M10 construction witnesses, viewed as a total labeled model.
Unused labels receive the same sort-correct witness; only reserved labels are
constrained by the embedded interface. -/
def embedModel {scope : Scope} (typeWitness : DOTCapture.Acyclic.Ty scope)
    (captureWitness : DOTCapture.Acyclic.Capture scope) :
    LocalModel.Model scope where
  typeMember := fun _ => Source.embedM10Ty typeWitness
  captureMember := fun _ => Source.embedM10Capture captureWitness

mutual

@[simp]
theorem realize_embedCapture {scope : Scope} (model : LocalModel.Model scope)
    (capture : DOTCapture.Acyclic.Capture scope) :
    Capture.realizeLocals model (Source.embedM10Capture capture) =
      Source.embedM10Capture capture := by
  cases capture with
  | empty => rfl
  | union left right =>
      simp [Source.embedM10Capture, Capture.realizeLocals,
        realize_embedCapture model left, realize_embedCapture model right]
  | singleton path => rfl
  | ref reference => cases reference <;> rfl

@[simp]
theorem realize_embedTy {scope : Scope} (model : LocalModel.Model scope)
    (type : DOTCapture.Acyclic.Ty scope) :
    Ty.realizeLocals model (Source.embedM10Ty type) =
      Source.embedM10Ty type := by
  cases type with
  | top => simp [Source.embedM10Ty, Ty.realizeLocals]
  | bot => simp [Source.embedM10Ty, Ty.realizeLocals]
  | one => simp [Source.embedM10Ty, Ty.realizeLocals]
  | ref reference => cases reference <;>
      simp [Source.embedM10Ty, Ty.realizeLocals]
  | arr domain codomain =>
      simp [Source.embedM10Ty, Ty.realizeLocals,
        realize_embedTy model domain, realize_embedTy model codomain]
  | capturing captures shape =>
      simp [Source.embedM10Ty, Ty.realizeLocals,
        realize_embedCapture model captures, realize_embedTy model shape]
  | object => simp [Source.embedM10Ty, Ty.realizeLocals]

end

@[simp]
theorem embedRealizedRepresentation {scope : Scope}
    (signature : M10.ObjectSig scope)
    (typeWitness : DOTCapture.Acyclic.Ty scope)
    (captureWitness : DOTCapture.Acyclic.Capture scope) :
    ObjectType.realizedRepresentation (Source.embedM10ObjectType signature)
        (embedModel typeWitness captureWitness) =
      .capturing (Source.embedM10Capture captureWitness)
        (Source.embedM10Ty typeWitness) := by
  cases signature
  simp [ObjectType.realizedRepresentation, Source.ObjectType.representation,
    Source.embedM10ObjectType, Ty.realizeLocals, Capture.realizeLocals,
    embedModel]

/-- The four M10 construction constraints form exactly the realization of
the embedded two-member interface. -/
def embedRealization {scope : Scope}
    {context : M10.Ctx scope} {signature : M10.ObjectSig scope}
    {typeWitness : DOTCapture.Acyclic.Ty scope}
    {captureWitness : DOTCapture.Acyclic.Capture scope}
    (typeLower : DOTCapture.Acyclic.TypeIncludes context
      signature.typeLower typeWitness)
    (typeUpper : DOTCapture.Acyclic.TypeIncludes context
      typeWitness signature.typeUpper)
    (captureLower : DOTCapture.Acyclic.CaptureIncludes context
      signature.captureLower captureWitness)
    (captureUpper : DOTCapture.Acyclic.CaptureIncludes context
      captureWitness signature.captureUpper) :
    ObjectType.Realization (embedCtx context)
      (Source.embedM10ObjectType signature) where
  model := embedModel typeWitness captureWitness
  constraints := by
    cases signature with
    | bounds lower upper captureLow captureUp =>
        simp only [Source.embedM10ObjectType, Source.ObjectType.interface,
          Source.embedM10ObjectSig]
        exact .inter
          (.typeMember
            (by simpa [embedModel] using embedIncludes typeLower)
            (by simpa [embedModel] using embedIncludes typeUpper))
          (.captureMember
            (by simpa [embedModel] using embedIncludes captureLower)
            (by simpa [embedModel] using embedIncludes captureUpper))

@[simp]
theorem embedRealization_model {scope : Scope}
    {context : M10.Ctx scope} {signature : M10.ObjectSig scope}
    {typeWitness : DOTCapture.Acyclic.Ty scope}
    {captureWitness : DOTCapture.Acyclic.Capture scope}
    (typeLower : DOTCapture.Acyclic.TypeIncludes context
      signature.typeLower typeWitness)
    (typeUpper : DOTCapture.Acyclic.TypeIncludes context
      typeWitness signature.typeUpper)
    (captureLower : DOTCapture.Acyclic.CaptureIncludes context
      signature.captureLower captureWitness)
    (captureUpper : DOTCapture.Acyclic.CaptureIncludes context
      captureWitness signature.captureUpper) :
    (embedRealization typeLower typeUpper captureLower captureUpper).model =
      embedModel typeWitness captureWitness := rfl

/-- M10 signature weakening is the fixed two-member instance of M11's
model-transforming, cross-shape object adaptation. -/
def embedAdapts {scope : Scope} {context : M10.Ctx scope}
    {available expected : M10.ObjectSig scope}
    (adaptation :
      DOTCapture.Acyclic.GeneralExpression.ObjectSig.Adapts context
        available expected) :
    ObjectType.Adapts (embedCtx context)
      (Source.embedM10ObjectType available)
      (Source.embedM10ObjectType expected) := by
  cases available with
  | bounds availableLower availableUpper availableCaptureLower
      availableCaptureUpper =>
    cases expected with
    | bounds expectedLower expectedUpper expectedCaptureLower
        expectedCaptureUpper =>
      refine
        { mapping := LocalModel.Mapping.identity
          theory := ?_
          constraints := ?_
          representation := ?_
          outerCapture := by
            simpa [Source.embedM10ObjectType, Source.ObjectType.outerCapture,
              DOTCapture.Acyclic.ObjectSig.captureUpper, embedStaticExpr]
              using (embedIncludes adaptation.captureUpper) }
      · simp only [Source.embedM10ObjectType, Source.ObjectType.interface,
          Source.embedM10ObjectSig]
        exact .inter
          (.typeMember
            (.trans
              (.ambient (by simpa [embedStaticExpr] using
                (embedIncludes adaptation.typeLower)))
              (.typeLower (.left .here)))
            (.trans
              (.typeUpper (.left .here))
              (.ambient (by simpa [embedStaticExpr] using
                (embedIncludes adaptation.typeUpper)))))
          (.captureMember
            (.trans
              (.ambient (by simpa [embedStaticExpr] using
                (embedIncludes adaptation.captureLower)))
              (.captureLower (.right .here)))
            (.trans
              (.captureUpper (.right .here))
              (.ambient (by simpa [embedStaticExpr] using
                (embedIncludes adaptation.captureUpper)))))
      · intro model realization
        simp only [Source.embedM10ObjectType, Source.ObjectType.interface,
          Source.embedM10ObjectSig] at realization ⊢
        cases realization with
        | inter typeRealization captureRealization =>
          cases typeRealization with
          | typeMember availableLowerProof availableUpperProof =>
            cases captureRealization with
            | captureMember availableCaptureLowerProof
                availableCaptureUpperProof =>
              exact .inter
                (.typeMember
                  (.trans (by
                    simpa [embedStaticExpr] using
                      (embedIncludes adaptation.typeLower))
                    availableLowerProof)
                  (.trans availableUpperProof (by
                    simpa [embedStaticExpr] using
                      (embedIncludes adaptation.typeUpper))))
                (.captureMember
                  (.trans (by
                    simpa [embedStaticExpr] using
                      (embedIncludes adaptation.captureLower))
                    availableCaptureLowerProof)
                  (.trans availableCaptureUpperProof (by
                    simpa [embedStaticExpr] using
                      (embedIncludes adaptation.captureUpper))))
      · intro model _realization
        simp only [ObjectType.realizedRepresentation,
          Source.ObjectType.representation, Source.embedM10ObjectType]
        exact .refl

@[simp]
theorem embedAdapts_mapping {scope : Scope} {context : M10.Ctx scope}
    {available expected : M10.ObjectSig scope}
    (adaptation :
      DOTCapture.Acyclic.GeneralExpression.ObjectSig.Adapts context
        available expected) :
    (embedAdapts adaptation).mapping = LocalModel.Mapping.identity := by
  cases available
  cases expected
  rfl

/-! ### Typing-constructor bridges -/

@[simp]
theorem embedCtx_extend {scope : Scope} (context : M10.Ctx scope)
    (type : DOTCapture.Acyclic.Ty scope) :
    embedCtx (context.extendTerm type) =
      (embedCtx context).extendTerm (Source.embedM10Ty type) := rfl

/-- The M10 positive-object rule is exactly M11 realization plus the same
payload shape and capture obligations. -/
def embedObjectValueTyping {scope : Scope}
    {context : M10.Ctx scope} {signature : M10.ObjectSig scope}
    {typeWitness payloadType : DOTCapture.Acyclic.Ty scope}
    {captureWitness : DOTCapture.Acyclic.Capture scope}
    {payload : DOTCapture.Acyclic.GeneralExpression.Value scope}
    (typeLower : DOTCapture.Acyclic.TypeIncludes context
      signature.typeLower typeWitness)
    (typeUpper : DOTCapture.Acyclic.TypeIncludes context
      typeWitness signature.typeUpper)
    (captureLower : DOTCapture.Acyclic.CaptureIncludes context
      signature.captureLower captureWitness)
    (captureUpper : DOTCapture.Acyclic.CaptureIncludes context
      captureWitness signature.captureUpper)
    (payloadTyping : Value.HasType (embedCtx context) (embedValue payload)
      (Source.embedM10Ty payloadType))
    (payloadShape : DOTCapture.Acyclic.TypeIncludes context
      payloadType.stripCapture typeWitness)
    (payloadCapture : DOTCapture.Acyclic.CaptureIncludes context
      payloadType.outerCapture captureWitness) :
    Value.HasType (embedCtx context)
      (embedValue (.object signature typeWitness captureWitness payload))
      (ObjectType.formedType (Source.embedM10ObjectType signature)) := by
  simp only [embedValue]
  apply Value.HasType.object
    (embedRealization typeLower typeUpper captureLower captureUpper)
    payloadTyping
  · simpa [embedRealization, embedRealizedRepresentation, embedTy_stripCapture,
      embedStaticExpr] using embedIncludes payloadShape
  · simpa [embedRealization, embedRealizedRepresentation, embedTy_outerCapture,
      embedStaticExpr] using embedIncludes payloadCapture
  · simpa [embedRealization, embedRealizedRepresentation,
      embedObjectOuterCapture, embedStaticExpr] using
      embedIncludes captureUpper

/-- Stable M10 payload selection is the reserved-label instance of M11
stable selection. -/
def embedSelectionTyping {scope : Scope}
    {context : M10.Ctx scope} {receiver : DOTCapture.Acyclic.Path scope}
    {signature : M10.ObjectSig scope}
    (exposes : DOTCapture.Acyclic.ExposesObject context receiver signature) :
    Term.HasType (embedCtx context)
      (embedTerm (.select receiver .v))
      (.singleton (Source.embedM10Path receiver))
      (Source.embedM10Ty receiver.valueMemberType) := by
  simpa [embedTerm, embedRepresentationAt] using
    (Term.HasType.select (embedExposes exposes))

/-- A canonical M10 literal remains a canonical direct negative argument. -/
def embedLiteralArgumentTyping {scope : Scope}
    {context : M10.Ctx scope} {available expected : M10.ObjectSig scope}
    {typeWitness payloadType : DOTCapture.Acyclic.Ty scope}
    {captureWitness : DOTCapture.Acyclic.Capture scope}
    {payload : DOTCapture.Acyclic.GeneralExpression.Value scope}
    (typeLower : DOTCapture.Acyclic.TypeIncludes context
      available.typeLower typeWitness)
    (typeUpper : DOTCapture.Acyclic.TypeIncludes context
      typeWitness available.typeUpper)
    (captureLower : DOTCapture.Acyclic.CaptureIncludes context
      available.captureLower captureWitness)
    (captureUpper : DOTCapture.Acyclic.CaptureIncludes context
      captureWitness available.captureUpper)
    (payloadTyping : Value.HasType (embedCtx context) (embedValue payload)
      (Source.embedM10Ty payloadType))
    (payloadShape : DOTCapture.Acyclic.TypeIncludes context
      payloadType.stripCapture typeWitness)
    (payloadCapture : DOTCapture.Acyclic.CaptureIncludes context
      payloadType.outerCapture captureWitness)
    (adaptation :
      DOTCapture.Acyclic.GeneralExpression.ObjectSig.Adapts context
        available expected) :
    ObjectArgument.HasType (embedCtx context)
      (embedTerm (.ret (.object available typeWitness captureWitness payload)))
      (Source.embedM10ObjectType expected) := by
  simp only [embedTerm, embedValue]
  refine ObjectArgument.HasType.literal
    (embedRealization typeLower typeUpper captureLower captureUpper)
    payloadTyping ?_ ?_ ?_ (embedAdapts adaptation) ?_
  · simpa [embedRealization, embedRealizedRepresentation,
      embedTy_stripCapture, embedStaticExpr] using embedIncludes payloadShape
  · simpa [embedRealization, embedRealizedRepresentation,
      embedTy_outerCapture, embedStaticExpr] using embedIncludes payloadCapture
  · simpa [embedRealization, embedRealizedRepresentation,
      embedObjectOuterCapture, embedStaticExpr] using
      embedIncludes captureUpper
  · simpa [embedRealizedRepresentation,
      embedObjectOuterCapture, embedStaticExpr] using
      embedIncludes (.trans captureUpper adaptation.captureUpper)

/-- An M10 stable variable remains a stable direct negative argument. -/
def embedStableArgumentTyping {scope : Scope}
    {context : M10.Ctx scope} {name : DOTCapture.Acyclic.Var scope}
    {available expected : M10.ObjectSig scope}
    (canonical : context.lookup name =
      DOTCapture.Acyclic.GeneralExpression.ObjectSig.formedType available)
    (adaptation :
      DOTCapture.Acyclic.GeneralExpression.ObjectSig.Adapts context
        available expected) :
    ObjectArgument.HasType (embedCtx context)
      (embedTerm (.ret (.var name)))
      (Source.embedM10ObjectType expected) := by
  have exposes : DOTCapture.Acyclic.ExposesObject context (.var name)
      available := .variable (by
    rw [canonical]
    simp [DOTCapture.Acyclic.GeneralExpression.ObjectSig.formedType,
      DOTCapture.Acyclic.Ty.stripCapture])
  simp only [embedTerm, embedValue]
  refine ObjectArgument.HasType.stable
    (available := Source.embedM10ObjectType available) ?_
      (embedAdapts adaptation) ?_
  · rw [embedCtx_lookup, canonical, embedFormedType]
    cases available
    simp [ObjectType.formedType, Source.ObjectType.formedType,
      Source.embedM10ObjectType]
  · simp only [embedAdapts_mapping, LocalModel.Mapping.apply_identity,
      ObjectType.realizedRepresentation_atPath]
    change CaptureIncludes (embedCtx context)
      (ObjectType.representationAt (Source.embedM10ObjectType expected)
        (Source.embedM10Path (.var name))).outerCapture
      (Source.embedM10ObjectType expected).outerCapture
    rw [embedRepresentationAt_outerCapture, embedObjectOuterCapture]
    simpa [embedStaticExpr] using
      embedIncludes (.trans exposes.captureUpper adaptation.captureUpper)

/-! ### Complete typing conservativity -/

mutual

/-- Every M10 value derivation embeds at the pointwise-translated context and
type. Legacy negative object lambdas use the compile-neutral M11 constructor. -/
def embedValueTyping {scope : Scope}
    {context : M10.Ctx scope}
    {value : DOTCapture.Acyclic.GeneralExpression.Value scope}
    {type : DOTCapture.Acyclic.Ty scope}
    (typing : DOTCapture.Acyclic.GeneralExpression.Value.HasType
      context value type) :
    Value.HasType (embedCtx context) (embedValue value)
      (Source.embedM10Ty type) :=
  match typing with
  | .var => by simpa [embedValue, embedCtx_lookup] using
      (Value.HasType.var (context := embedCtx context))
  | .unit => by simpa [embedValue, Source.embedM10Ty] using
      (Value.HasType.unit (context := embedCtx context))
  | @DOTCapture.Acyclic.GeneralExpression.Value.HasType.lam _ _ domain
      codomain body bodyUse closure domainPlain bodyTyping captures => by
      have embeddedBody : Term.HasType
          ((embedCtx context).extendTerm (Source.embedM10Ty domain))
          (embedTerm body) (Source.embedM10Capture bodyUse)
          ((Source.embedM10Ty codomain).rename
            DOTCapture.Acyclic.Rename.succ) := by
        simpa [embedCtx_extend, embedTy_weaken] using
          embedTermTyping bodyTyping
      have captureProof : CaptureIncludes
          ((embedCtx context).extendTerm (Source.embedM10Ty domain))
          (Source.embedM10Capture bodyUse)
          (.union ((Source.embedM10Capture closure).rename
            DOTCapture.Acyclic.Rename.succ) (.singleton (.var .here))) := by
        simpa [embedCtx_extend, embedCapture_weaken, embedStaticExpr,
          Source.embedM10Capture] using embedIncludes captures
      simpa [embedValue, Source.embedM10Ty] using
        (Value.HasType.lam (embedPlain domainPlain) embeddedBody captureProof)
  | @DOTCapture.Acyclic.GeneralExpression.Value.HasType.objectLam _ _ signature
      codomain body bodyUse closure bodyTyping captures => by
      have embeddedBody : Term.HasType
          ((embedCtx context).extendTerm
            (ObjectType.formedType (Source.embedM10ObjectType signature)))
          (embedTerm body) (Source.embedM10Capture bodyUse)
          ((Source.embedM10Ty codomain).rename
            DOTCapture.Acyclic.Rename.succ) := by
        simpa [embedCtx_extend, embedGeneralFormedType,
          embedTy_weaken] using embedTermTyping bodyTyping
      have captureProof : CaptureIncludes
          ((embedCtx context).extendTerm
            (ObjectType.formedType (Source.embedM10ObjectType signature)))
          (Source.embedM10Capture bodyUse)
          (.union ((Source.embedM10Capture closure).rename
            DOTCapture.Acyclic.Rename.succ) (.singleton (.var .here))) := by
        simpa [embedCtx_extend, embedGeneralFormedType,
          embedCapture_weaken, embedStaticExpr,
          Source.embedM10Capture] using embedIncludes captures
      simpa [embedValue, Source.embedM10Ty, embedGeneralFormedType] using
        (Value.HasType.embeddedObjectConsumer embeddedBody captureProof)
  | .object typeLower typeUpper captureLower captureUpper payloadTyping
      payloadShape payloadCapture => by
      simpa [Source.embedM10Ty, ObjectType.formedType,
        Source.embedM10ObjectType, Source.ObjectType.outerCapture,
        DOTCapture.Acyclic.ObjectSig.captureUpper] using
        (embedObjectValueTyping typeLower typeUpper captureLower captureUpper
          (embedValueTyping payloadTyping) payloadShape payloadCapture)
  | .adapt valueTyping inclusion =>
      .adapt (embedValueTyping valueTyping) (embedIncludes inclusion)

/-- Canonical and stable M10 negative arguments remain canonical and stable
after embedding. -/
def embedObjectArgumentTyping {scope : Scope}
    {context : M10.Ctx scope}
    {argument : DOTCapture.Acyclic.GeneralExpression.Term scope}
    {expected : M10.ObjectSig scope}
    (typing : DOTCapture.Acyclic.GeneralExpression.ObjectArgument.HasType
      context argument expected) :
    ObjectArgument.HasType (embedCtx context) (embedTerm argument)
      (Source.embedM10ObjectType expected) :=
  match typing with
  | .literal typeLower typeUpper captureLower captureUpper payloadTyping
      payloadShape payloadCapture adaptation =>
      embedLiteralArgumentTyping typeLower typeUpper captureLower captureUpper
        (embedValueTyping payloadTyping) payloadShape payloadCapture adaptation
  | .stable canonical adaptation =>
      embedStableArgumentTyping canonical adaptation

/-- Every M10 negative-function derivation embeds without inserting source
syntax. Administrative lets retain their original computational spine. -/
def embedObjectFunctionTyping {scope : Scope}
    {context : M10.Ctx scope}
    {function : DOTCapture.Acyclic.GeneralExpression.Term scope}
    {use : DOTCapture.Acyclic.Capture scope}
    {signature : M10.ObjectSig scope}
    {codomain : DOTCapture.Acyclic.Ty scope}
    {closure : DOTCapture.Acyclic.Capture scope}
    (typing : DOTCapture.Acyclic.GeneralExpression.ObjectFunction.HasType
      context function use signature codomain closure) :
    ObjectFunction.HasType (embedCtx context) (embedTerm function)
      (Source.embedM10Capture use) (Source.embedM10ObjectType signature)
      (Source.embedM10Ty codomain) (Source.embedM10Capture closure) :=
  match typing with
  | @DOTCapture.Acyclic.GeneralExpression.ObjectFunction.HasType.returned
      _ _ signature codomain body bodyUse closure bodyTyping captures => by
      have embeddedBody : Term.HasType
          ((embedCtx context).extendTerm
            (ObjectType.formedType (Source.embedM10ObjectType signature)))
          (embedTerm body) (Source.embedM10Capture bodyUse)
          ((Source.embedM10Ty codomain).rename
            DOTCapture.Acyclic.Rename.succ) := by
        simpa [embedCtx_extend, embedGeneralFormedType,
          embedTy_weaken] using embedTermTyping bodyTyping
      have captureProof : CaptureIncludes
          ((embedCtx context).extendTerm
            (ObjectType.formedType (Source.embedM10ObjectType signature)))
          (Source.embedM10Capture bodyUse)
          (.union ((Source.embedM10Capture closure).rename
            DOTCapture.Acyclic.Rename.succ) (.singleton (.var .here))) := by
        simpa [embedCtx_extend, embedGeneralFormedType,
          embedCapture_weaken, embedStaticExpr,
          Source.embedM10Capture] using embedIncludes captures
      simpa [embedTerm, embedValue, Source.embedM10Ty,
        embedGeneralFormedType] using
        (ObjectFunction.HasType.embeddedReturned embeddedBody captureProof)
  | @DOTCapture.Acyclic.GeneralExpression.ObjectFunction.HasType.letPlain
      _ _ signature codomain bound closure rhs body rhsUse bodyUse
      bodyOuterUse boundPlain rhsTyping bodyTyping discharge => by
      have embeddedBody : ObjectFunction.HasType
          ((embedCtx context).extendTerm (Source.embedM10Ty bound))
          (embedTerm body) (Source.embedM10Capture bodyUse)
          ((Source.embedM10ObjectType signature).rename
            DOTCapture.Acyclic.Rename.succ)
          ((Source.embedM10Ty codomain).rename
            DOTCapture.Acyclic.Rename.succ)
          ((Source.embedM10Capture closure).rename
            DOTCapture.Acyclic.Rename.succ) := by
        simpa [embedCtx_extend, embedObjectType_weaken,
          embedTy_weaken, embedCapture_weaken] using
          embedObjectFunctionTyping bodyTyping
      have dischargeProof : CaptureIncludes
          ((embedCtx context).extendTerm (Source.embedM10Ty bound))
          (Source.embedM10Capture bodyUse)
          ((Source.embedM10Capture bodyOuterUse).rename
            DOTCapture.Acyclic.Rename.succ) := by
        simpa [embedCtx_extend, embedCapture_weaken,
          embedStaticExpr] using embedIncludes discharge
      simpa [embedTerm, Source.embedM10Ty, Source.embedM10Capture,
        embedGeneralFormedType] using
        (ObjectFunction.HasType.letPlain (embedPlain boundPlain)
          (embedTermTyping rhsTyping) embeddedBody dischargeProof)
  | .use functionTyping inclusion =>
      .use (embedObjectFunctionTyping functionTyping)
        (embedIncludes inclusion)

/-- Every M10 term derivation embeds with pointwise-translated use and result
indices. The legacy constructors keep direct object application and object
opening compile-neutral at the M11 source boundary. -/
def embedTermTyping {scope : Scope}
    {context : M10.Ctx scope}
    {term : DOTCapture.Acyclic.GeneralExpression.Term scope}
    {use : DOTCapture.Acyclic.Capture scope}
    {type : DOTCapture.Acyclic.Ty scope}
    (typing : DOTCapture.Acyclic.GeneralExpression.Term.HasType
      context term use type) :
    Term.HasType (embedCtx context) (embedTerm term)
      (Source.embedM10Capture use) (Source.embedM10Ty type) :=
  match typing with
  | .ret valueTyping => .ret (embedValueTyping valueTyping)
  | .select exposes => embedSelectionTyping exposes
  | .app functionTyping functionShape domainPlain argumentTyping => by
      simpa [embedTerm, embedCapture_seq, embedTy_outerCapture,
        Source.embedM10Capture] using
        (Term.HasType.app (embedTermTyping functionTyping)
          (by simpa [embedTy_stripCapture, Source.embedM10Ty] using
            congrArg Source.embedM10Ty functionShape)
          (embedPlain domainPlain)
          (embedTermTyping argumentTyping))
  | .objectApp functionTyping argumentTyping => by
      simpa [embedTerm, embedCapture_seq, embedObjectOuterCapture,
        Source.embedM10Capture] using
        (Term.HasType.embeddedObjectApp
          (embedObjectFunctionTyping functionTyping)
          (embedObjectArgumentTyping argumentTyping))
  | @DOTCapture.Acyclic.GeneralExpression.Term.HasType.letPlain
      _ _ result bound rhs body rhsUse bodyUse bodyOuterUse boundPlain
      rhsTyping bodyTyping discharge => by
      have embeddedBody : Term.HasType
          ((embedCtx context).extendTerm (Source.embedM10Ty bound))
          (embedTerm body) (Source.embedM10Capture bodyUse)
          ((Source.embedM10Ty result).rename
            DOTCapture.Acyclic.Rename.succ) := by
        simpa [embedCtx_extend, embedTy_weaken] using
          embedTermTyping bodyTyping
      have dischargeProof : CaptureIncludes
          ((embedCtx context).extendTerm (Source.embedM10Ty bound))
          (Source.embedM10Capture bodyUse)
          ((Source.embedM10Capture bodyOuterUse).rename
            DOTCapture.Acyclic.Rename.succ) := by
        simpa [embedCtx_extend, embedCapture_weaken,
          embedStaticExpr] using embedIncludes discharge
      simpa [embedTerm, Source.embedM10Capture] using
        (Term.HasType.letPlain (embedPlain boundPlain)
          (embedTermTyping rhsTyping) embeddedBody dischargeProof)
  | @DOTCapture.Acyclic.GeneralExpression.Term.HasType.letObject
      _ _ signature result rhs rhsUse body bodyUse bodyOuterUse rhsTyping
      bodyTyping discharge => by
      have embeddedRhs : Term.HasType (embedCtx context) (embedTerm rhs)
          (Source.embedM10Capture rhsUse)
          (ObjectType.formedType
            (Source.embedM10ObjectType signature)) := by
        simpa [Source.embedM10Ty, ObjectType.formedType,
          Source.embedM10ObjectType,
          DOTCapture.Acyclic.ObjectSig.captureUpper] using
          embedTermTyping rhsTyping
      have embeddedBody : Term.HasType
          ((embedCtx context).extendTerm
            (ObjectType.formedType (Source.embedM10ObjectType signature)))
          (embedTerm body) (Source.embedM10Capture bodyUse)
          ((Source.embedM10Ty result).rename
            DOTCapture.Acyclic.Rename.succ) := by
        simpa [embedCtx_extend, Source.embedM10Ty,
          ObjectType.formedType, Source.embedM10ObjectType,
          DOTCapture.Acyclic.ObjectSig.captureUpper,
          embedTy_weaken] using embedTermTyping bodyTyping
      have dischargeProof : CaptureIncludes
          ((embedCtx context).extendTerm
            (ObjectType.formedType (Source.embedM10ObjectType signature)))
          (Source.embedM10Capture bodyUse)
          (.union ((Source.embedM10Capture bodyOuterUse).rename
            DOTCapture.Acyclic.Rename.succ) (.singleton (.var .here))) := by
        simpa [embedCtx_extend, Source.embedM10Ty,
          ObjectType.formedType, Source.embedM10ObjectType,
          DOTCapture.Acyclic.ObjectSig.captureUpper,
          embedCapture_weaken, embedStaticExpr,
          Source.embedM10Capture] using embedIncludes discharge
      simpa [embedTerm, embedCapture_seq, embedObjectOuterCapture,
        Source.embedM10Capture] using
        (Term.HasType.embeddedObjectLet embeddedRhs embeddedBody
          dischargeProof)
  | .use termTyping inclusion =>
      .use (embedTermTyping termTyping) (embedIncludes inclusion)

end

/-- A typed embedded M10 value has exactly its original runtime erasure. -/
@[simp]
theorem embedValueTyping_exactErasure {scope runtimeScope : Scope}
    {context : M10.Ctx scope}
    {value : DOTCapture.Acyclic.GeneralExpression.Value scope}
    {type : DOTCapture.Acyclic.Ty scope}
    (_typing : DOTCapture.Acyclic.GeneralExpression.Value.HasType
      context value type)
    (rho : Erasure.Renaming scope runtimeScope) :
    Erasure.eraseValueWith rho (embedValue value) =
      DOTCapture.Acyclic.GeneralExpression.Erasure.eraseValueWith rho value :=
  eraseValueWith_embed rho value

/-- A typed embedded M10 computation has exactly its original runtime
erasure; no administrative source term is introduced by typing translation. -/
@[simp]
theorem embedTermTyping_exactErasure {scope runtimeScope : Scope}
    {context : M10.Ctx scope}
    {term : DOTCapture.Acyclic.GeneralExpression.Term scope}
    {use : DOTCapture.Acyclic.Capture scope}
    {type : DOTCapture.Acyclic.Ty scope}
    (_typing : DOTCapture.Acyclic.GeneralExpression.Term.HasType
      context term use type)
    (rho : Erasure.Renaming scope runtimeScope) :
    Erasure.eraseTermWith rho (embedTerm term) =
      DOTCapture.Acyclic.GeneralExpression.Erasure.eraseTermWith rho term :=
  eraseTermWith_embed rho term

end Embedding

end DOTCapture.Intersections.GeneralExpression
