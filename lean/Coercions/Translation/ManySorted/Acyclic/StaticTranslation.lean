import Coercions.Translation.ManySorted.Acyclic.Layout

/-!
# Partial static translation for acyclic DOT objects with captures

Paths are total because the source layer has variable-only stable paths.
Selected static members are partial: their target coordinates must already
exist in the canonical context layout.  Failure is retained as `none`; this
module never fabricates a symbol or an interval endpoint.
-/

namespace DOTCaptureToManySortedFC.Acyclic.StaticTranslation

/-! Short local qualifiers keep the independently defined source and target
syntax explicit without obscuring the translation clauses. -/

namespace Source

export DOTCapture.Acyclic
  (Scope StaticSort Var Path StaticRef Capture Ty ObjectSig StaticExpr Ctx)

namespace ObjectSig
export DOTCapture.Acyclic.ObjectSig (captureUpper)
end ObjectSig

namespace Path
export DOTCapture.Acyclic.Path
  (typeMember captureMember selectedType selectedCapture valueMemberType)
end Path

namespace Ctx
export DOTCapture.Acyclic.Ctx (nil)
end Ctx

end Source

namespace Target

export ManySortedFC (StaticExpr Capture Ty Ctx Sig)

namespace Ctx
export ManySortedFC.Ctx (nil)
end Ctx

end Target

namespace Object

export DOTCaptureToManySortedFC.Acyclic.ObjectEncoding
  (Bounds PayloadScope theory payloadType payloadTypeOpened existentialShape
    objectType exactBounds)

end Object

/-- Variable-only stable paths translate totally through the layout. -/
def translatePath {scope : Source.Scope} (context : Source.Ctx scope)
    (path : Source.Path scope) :
    ManySortedFC.BVar (Layout.sig context) .term :=
  Layout.translatePath context path

/-- A genuine selected member translates only when its receiver owns a
canonical layout slot. -/
def translateRef? {scope : Source.Scope} {sort : Source.StaticSort}
    (context : Source.Ctx scope) (reference : Source.StaticRef sort scope) :
    Option (Target.StaticExpr (Layout.translateSort sort)
      (Layout.sig context)) :=
  (Layout.memberSlot? context reference).map (·.expression)

mutual

/-- Translate captures, preserving runtime singletons separately from
static capture selections. -/
def translateCapture? {scope : Source.Scope} (context : Source.Ctx scope) :
    Source.Capture scope → Option (Target.Capture (Layout.sig context))
  | .empty => some .empty
  | .union left right => do
      let left' ← translateCapture? context left
      let right' ← translateCapture? context right
      pure (.union left' right')
  | .singleton path => some (.singleton (translatePath context path))
  | .ref reference =>
      match translateRef? context reference with
      | some (.capture capture) => some capture
      | none => none

/-- Translate types.  Bare object shapes become existential packages;
an explicit outer capture remains outside that package. -/
def translateTy? {scope : Source.Scope} (context : Source.Ctx scope) :
    Source.Ty scope → Option (Target.Ty (Layout.sig context))
  | .top => some .top
  | .bot => some .bot
  | .one => some .one
  | .ref reference =>
      match translateRef? context reference with
      | some (.type type) => some type
      | none => none
  | .capturing captures shape => do
      let captures' ← translateCapture? context captures
      let shape' ← translateTy? context shape
      pure (.capturing captures' shape')
  | .object signature => do
      let bounds ← translateObjectSig? context signature
      pure (Object.existentialShape bounds)

/-- Translate all four independent object endpoints. -/
def translateObjectSig? {scope : Source.Scope}
    (context : Source.Ctx scope) :
    Source.ObjectSig scope → Option (Object.Bounds (Layout.sig context))
  | .bounds typeLower typeUpper captureLower captureUpper => do
      let typeLower' ← translateTy? context typeLower
      let typeUpper' ← translateTy? context typeUpper
      let captureLower' ← translateCapture? context captureLower
      let captureUpper' ← translateCapture? context captureUpper
      pure
        { typeLower := typeLower'
          typeUpper := typeUpper'
          captureLower := captureLower'
          captureUpper := captureUpper' }

end

/-- Translate a sort-indexed source expression without erasing its sort. -/
def translateExpr? {scope : Source.Scope} {sort : Source.StaticSort}
    (context : Source.Ctx scope) :
    Source.StaticExpr sort scope →
      Option (Target.StaticExpr (Layout.translateSort sort)
        (Layout.sig context))
  | .type type => (translateTy? context type).map fun type' => .type type'
  | .capture capture =>
      (translateCapture? context capture).map fun capture' =>
        .capture capture'

/-! ## Exact context translation -/

/-- Extend an already translated context by one ordinary source binding. -/
def extendPlain? {scope : Source.Scope} (outer : Source.Ctx scope)
    (targetOuter : Target.Ctx (Layout.sig outer))
    (type : Source.Ty scope) :
    Option (Target.Ctx ((Layout.sig outer) ▹ .term)) := do
  let type' ← translateTy? outer type
  pure (targetOuter.extendTerm type')

/-- Open one translated object theory and install its separate payload. -/
def extendObject? {scope : Source.Scope} (outer : Source.Ctx scope)
    (targetOuter : Target.Ctx (Layout.sig outer))
    (signature : Source.ObjectSig scope) :
    Option (Target.Ctx (Object.PayloadScope (Layout.sig outer))) := do
  let bounds ← translateObjectSig? outer signature
  pure ((targetOuter.extendTheory (Object.theory bounds)).extendTerm
    Object.payloadType)

/-- Compile a whole source context into the exact heterogeneous target scope
chosen by `Layout.sig`.  The direct cases deliberately mirror that layout. -/
def translateContext? : {scope : Source.Scope} →
    (context : Source.Ctx scope) →
      Option (Target.Ctx (Layout.sig context))
  | _, .nil => some .nil
  | _, .extend outer .top => do
      let targetOuter ← translateContext? outer
      extendPlain? outer targetOuter .top
  | _, .extend outer .bot => do
      let targetOuter ← translateContext? outer
      extendPlain? outer targetOuter .bot
  | _, .extend outer .one => do
      let targetOuter ← translateContext? outer
      extendPlain? outer targetOuter .one
  | _, .extend outer (.ref reference) => do
      let targetOuter ← translateContext? outer
      extendPlain? outer targetOuter (.ref reference)
  | _, .extend outer (.object signature) => do
      let targetOuter ← translateContext? outer
      extendObject? outer targetOuter signature
  | _, .extend outer (.capturing captures (.object signature)) => do
      let targetOuter ← translateContext? outer
      let _ ← translateCapture? outer captures
      extendObject? outer targetOuter signature
  | _, .extend outer (.capturing captures .top) => do
      let targetOuter ← translateContext? outer
      extendPlain? outer targetOuter (.capturing captures .top)
  | _, .extend outer (.capturing captures .bot) => do
      let targetOuter ← translateContext? outer
      extendPlain? outer targetOuter (.capturing captures .bot)
  | _, .extend outer (.capturing captures .one) => do
      let targetOuter ← translateContext? outer
      extendPlain? outer targetOuter (.capturing captures .one)
  | _, .extend outer (.capturing captures (.ref reference)) => do
      let targetOuter ← translateContext? outer
      extendPlain? outer targetOuter (.capturing captures (.ref reference))
  | _, .extend outer (.capturing captures (.capturing retained shape)) => do
      let targetOuter ← translateContext? outer
      extendPlain? outer targetOuter
        (.capturing captures (.capturing retained shape))

@[simp]
theorem translateContext?_nil :
    translateContext? (Source.Ctx.nil : Source.Ctx 0) =
      some Target.Ctx.nil := rfl

@[simp]
theorem translateContext?_extend_one {scope : Source.Scope}
    (outer : Source.Ctx scope) :
    translateContext? (outer.extendTerm .one) = (do
      let targetOuter ← translateContext? outer
      extendPlain? outer targetOuter .one) := rfl

@[simp]
theorem translateContext?_extend_object {scope : Source.Scope}
    (outer : Source.Ctx scope) (signature : Source.ObjectSig scope) :
    translateContext? (outer.extendTerm (.object signature)) = (do
      let targetOuter ← translateContext? outer
      extendObject? outer targetOuter signature) := rfl

@[simp]
theorem translateContext?_extend_capturing_object
    {scope : Source.Scope} (outer : Source.Ctx scope)
    (captures : Source.Capture scope) (signature : Source.ObjectSig scope) :
    translateContext?
        (outer.extendTerm (.capturing captures (.object signature))) = (do
      let targetOuter ← translateContext? outer
      let _ ← translateCapture? outer captures
      extendObject? outer targetOuter signature) := rfl

/-! ## Proof-relevant translation graphs -/

def TranslatesRef {scope : Source.Scope} {sort : Source.StaticSort}
    (context : Source.Ctx scope) (source : Source.StaticRef sort scope)
    (target : Target.StaticExpr (Layout.translateSort sort)
      (Layout.sig context)) : Prop :=
  translateRef? context source = some target

def TranslatesCapture {scope : Source.Scope} (context : Source.Ctx scope)
    (source : Source.Capture scope)
    (target : Target.Capture (Layout.sig context)) : Prop :=
  translateCapture? context source = some target

def TranslatesTy {scope : Source.Scope} (context : Source.Ctx scope)
    (source : Source.Ty scope)
    (target : Target.Ty (Layout.sig context)) : Prop :=
  translateTy? context source = some target

def TranslatesObjectSig {scope : Source.Scope}
    (context : Source.Ctx scope) (source : Source.ObjectSig scope)
    (target : Object.Bounds (Layout.sig context)) : Prop :=
  translateObjectSig? context source = some target

def TranslatesExpr {scope : Source.Scope} {sort : Source.StaticSort}
    (context : Source.Ctx scope) (source : Source.StaticExpr sort scope)
    (target : Target.StaticExpr (Layout.translateSort sort)
      (Layout.sig context)) : Prop :=
  translateExpr? context source = some target

def TranslatesContext {scope : Source.Scope} (source : Source.Ctx scope)
    (target : Target.Ctx (Layout.sig source)) : Prop :=
  translateContext? source = some target

abbrev ReadyRef {scope : Source.Scope} {sort : Source.StaticSort}
    (context : Source.Ctx scope) (source : Source.StaticRef sort scope) :
    Prop :=
  ∃ target, TranslatesRef context source target

abbrev ReadyCapture {scope : Source.Scope} (context : Source.Ctx scope)
    (source : Source.Capture scope) : Prop :=
  ∃ target, TranslatesCapture context source target

abbrev ReadyTy {scope : Source.Scope} (context : Source.Ctx scope)
    (source : Source.Ty scope) : Prop :=
  ∃ target, TranslatesTy context source target

abbrev ReadyObjectSig {scope : Source.Scope}
    (context : Source.Ctx scope) (source : Source.ObjectSig scope) : Prop :=
  ∃ target, TranslatesObjectSig context source target

abbrev ReadyExpr {scope : Source.Scope} {sort : Source.StaticSort}
    (context : Source.Ctx scope) (source : Source.StaticExpr sort scope) :
    Prop :=
  ∃ target, TranslatesExpr context source target

abbrev ReadyContext {scope : Source.Scope} (source : Source.Ctx scope) :
    Prop :=
  ∃ target, TranslatesContext source target

theorem TranslatesRef.functional {scope : Source.Scope}
    {sort : Source.StaticSort} {context : Source.Ctx scope}
    {source : Source.StaticRef sort scope}
    {first second : Target.StaticExpr (Layout.translateSort sort)
      (Layout.sig context)}
    (left : TranslatesRef context source first)
    (right : TranslatesRef context source second) : first = second := by
  unfold TranslatesRef at left right
  rw [left] at right
  exact Option.some.inj right

theorem TranslatesCapture.functional {scope : Source.Scope}
    {context : Source.Ctx scope} {source : Source.Capture scope}
    {first second : Target.Capture (Layout.sig context)}
    (left : TranslatesCapture context source first)
    (right : TranslatesCapture context source second) : first = second := by
  unfold TranslatesCapture at left right
  rw [left] at right
  exact Option.some.inj right

theorem TranslatesTy.functional {scope : Source.Scope}
    {context : Source.Ctx scope} {source : Source.Ty scope}
    {first second : Target.Ty (Layout.sig context)}
    (left : TranslatesTy context source first)
    (right : TranslatesTy context source second) : first = second := by
  unfold TranslatesTy at left right
  rw [left] at right
  exact Option.some.inj right

theorem TranslatesObjectSig.functional {scope : Source.Scope}
    {context : Source.Ctx scope} {source : Source.ObjectSig scope}
    {first second : Object.Bounds (Layout.sig context)}
    (left : TranslatesObjectSig context source first)
    (right : TranslatesObjectSig context source second) : first = second := by
  unfold TranslatesObjectSig at left right
  rw [left] at right
  exact Option.some.inj right

theorem TranslatesExpr.functional {scope : Source.Scope}
    {sort : Source.StaticSort} {context : Source.Ctx scope}
    {source : Source.StaticExpr sort scope}
    {first second : Target.StaticExpr (Layout.translateSort sort)
      (Layout.sig context)}
    (left : TranslatesExpr context source first)
    (right : TranslatesExpr context source second) : first = second := by
  unfold TranslatesExpr at left right
  rw [left] at right
  exact Option.some.inj right

theorem TranslatesContext.functional {scope : Source.Scope}
    {source : Source.Ctx scope}
    {first second : Target.Ctx (Layout.sig source)}
    (left : TranslatesContext source first)
    (right : TranslatesContext source second) : first = second := by
  unfold TranslatesContext at left right
  rw [left] at right
  exact Option.some.inj right

/-! ## Canonical slot consequences -/

theorem translateRef?_typeMember_of_receiverSlot
    {scope : Source.Scope} {context : Source.Ctx scope}
    {receiver : Source.Path scope}
    {slot : Layout.ReceiverSlot (Layout.sig context)}
    (lookup : Layout.receiverSlot? context receiver = some slot) :
    translateRef? context receiver.typeMember =
      some slot.alpha.expression := by
  change
    ((Layout.receiverSlot? context receiver).map (fun found => found.alpha)).map
        (fun found => found.expression) =
      some slot.alpha.expression
  simp [lookup]

theorem translateRef?_captureMember_of_receiverSlot
    {scope : Source.Scope} {context : Source.Ctx scope}
    {receiver : Source.Path scope}
    {slot : Layout.ReceiverSlot (Layout.sig context)}
    (lookup : Layout.receiverSlot? context receiver = some slot) :
    translateRef? context receiver.captureMember =
      some slot.chi.expression := by
  change
    ((Layout.receiverSlot? context receiver).map (fun found => found.chi)).map
        (fun found => found.expression) =
      some slot.chi.expression
  simp [lookup]

theorem translateTy?_selectedType_of_receiverSlot
    {scope : Source.Scope} {context : Source.Ctx scope}
    {receiver : Source.Path scope}
    {slot : Layout.ReceiverSlot (Layout.sig context)}
    (lookup : Layout.receiverSlot? context receiver = some slot) :
    translateTy? context receiver.selectedType =
      some (.tvar slot.alpha.name) := by
  rw [show receiver.selectedType = .ref receiver.typeMember from rfl]
  simp only [translateTy?]
  rw [translateRef?_typeMember_of_receiverSlot lookup]
  rfl

theorem translateCapture?_selectedCapture_of_receiverSlot
    {scope : Source.Scope} {context : Source.Ctx scope}
    {receiver : Source.Path scope}
    {slot : Layout.ReceiverSlot (Layout.sig context)}
    (lookup : Layout.receiverSlot? context receiver = some slot) :
    translateCapture? context receiver.selectedCapture =
      some (.cvar slot.chi.name) := by
  rw [show receiver.selectedCapture = .ref receiver.captureMember from rfl]
  simp only [translateCapture?]
  rw [translateRef?_captureMember_of_receiverSlot lookup]
  rfl

theorem translateTy?_valueMemberType_of_receiverSlot
    {scope : Source.Scope} {context : Source.Ctx scope}
    {receiver : Source.Path scope}
    {slot : Layout.ReceiverSlot (Layout.sig context)}
    (lookup : Layout.receiverSlot? context receiver = some slot) :
    translateTy? context receiver.valueMemberType =
      some (.capturing (.cvar slot.chi.name) (.tvar slot.alpha.name)) := by
  rw [show receiver.valueMemberType =
    .capturing receiver.selectedCapture receiver.selectedType from rfl]
  simp only [translateTy?]
  rw [translateCapture?_selectedCapture_of_receiverSlot lookup,
    translateTy?_selectedType_of_receiverSlot lookup]
  rfl

/-! ## Object-formation closure -/

/-- A bare source object is the existential shape of its translated
interface. -/
theorem translateTy?_object
    {scope : Source.Scope} {context : Source.Ctx scope}
    {signature : Source.ObjectSig scope}
    {bounds : Object.Bounds (Layout.sig context)}
    (translated : translateObjectSig? context signature = some bounds) :
    translateTy? context (.object signature) =
      some (Object.existentialShape bounds) := by
  simp [translateTy?, translated]

/-- An arbitrary explicit source closure is preserved; it does not silently
become the signature's upper endpoint. -/
theorem translateTy?_capturing_object
    {scope : Source.Scope} {context : Source.Ctx scope}
    {captures : Source.Capture scope} {signature : Source.ObjectSig scope}
    {captures' : Target.Capture (Layout.sig context)}
    {bounds : Object.Bounds (Layout.sig context)}
    (capturesTranslated : translateCapture? context captures = some captures')
    (signatureTranslated :
      translateObjectSig? context signature = some bounds) :
    translateTy? context (.capturing captures (.object signature)) =
      some (.capturing captures' (Object.existentialShape bounds)) := by
  simp [translateTy?, capturesTranslated, signatureTranslated]

/-- When the source formation type uses the signature's declared upper
capture `E`, its translation is exactly the target object convention. -/
theorem translateTy?_formedObject
    {scope : Source.Scope} {context : Source.Ctx scope}
    (signature : Source.ObjectSig scope)
    (bounds : Object.Bounds (Layout.sig context))
    (translated : translateObjectSig? context signature = some bounds) :
    translateTy? context
        (.capturing signature.captureUpper (.object signature)) =
      some (Object.objectType bounds) := by
  cases signature with
  | bounds typeLower typeUpper captureLower captureUpper =>
      generalize lowerTypeEquation :
        translateTy? context typeLower = translatedTypeLower at translated
      cases translatedTypeLower with
      | none =>
          simp [translateObjectSig?, lowerTypeEquation] at translated
      | some translatedTypeLower =>
          generalize upperTypeEquation :
            translateTy? context typeUpper = translatedTypeUpper at translated
          cases translatedTypeUpper with
          | none =>
              simp [translateObjectSig?, lowerTypeEquation,
                upperTypeEquation] at translated
          | some translatedTypeUpper =>
              generalize lowerCaptureEquation :
                translateCapture? context captureLower =
                  translatedCaptureLower at translated
              cases translatedCaptureLower with
              | none =>
                  simp [translateObjectSig?, lowerTypeEquation,
                    upperTypeEquation, lowerCaptureEquation] at translated
              | some translatedCaptureLower =>
                  generalize upperCaptureEquation :
                    translateCapture? context captureUpper =
                      translatedCaptureUpper at translated
                  cases translatedCaptureUpper with
                  | none =>
                      simp [translateObjectSig?, lowerTypeEquation,
                        upperTypeEquation, lowerCaptureEquation,
                        upperCaptureEquation] at translated
                  | some translatedCaptureUpper =>
                      simp [translateObjectSig?, lowerTypeEquation,
                        upperTypeEquation, lowerCaptureEquation,
                        upperCaptureEquation] at translated
                      subst bounds
                      simp only [Source.ObjectSig.captureUpper,
                        translateTy?]
                      rw [upperCaptureEquation]
                      simp [translateObjectSig?, lowerTypeEquation,
                        upperTypeEquation, lowerCaptureEquation,
                        upperCaptureEquation, Object.objectType]

/-- Graph-facing form of the object-formation theorem. -/
theorem TranslatesObjectSig.formedObject
    {scope : Source.Scope} {context : Source.Ctx scope}
    {signature : Source.ObjectSig scope}
    {bounds : Object.Bounds (Layout.sig context)}
    (translated : TranslatesObjectSig context signature bounds) :
    TranslatesTy context
      (.capturing signature.captureUpper (.object signature))
      (Object.objectType bounds) :=
  translateTy?_formedObject signature bounds translated

/-! ## Decisive regressions -/

def exactSourceSignature : Source.ObjectSig 0 :=
  .bounds .one .one .empty .empty

theorem exact_signature_translates :
    translateObjectSig? Source.Ctx.nil exactSourceSignature =
      some Object.exactBounds := rfl

theorem exact_object_shape_translates :
    translateTy? Source.Ctx.nil (.object exactSourceSignature) =
      some (Object.existentialShape Object.exactBounds) := rfl

theorem exact_formed_object_translates :
    translateTy? Source.Ctx.nil
        (.capturing exactSourceSignature.captureUpper
          (.object exactSourceSignature)) =
      some (Object.objectType Object.exactBounds) := rfl

def exactSourceContext : Source.Ctx 1 :=
  Source.Ctx.nil.extendTerm
    (.capturing exactSourceSignature.captureUpper
      (.object exactSourceSignature))

def exactTargetContext : Target.Ctx (Layout.sig exactSourceContext) :=
  (Target.Ctx.nil.extendTheory (Object.theory Object.exactBounds)).extendTerm
    Object.payloadType

theorem exact_context_translates :
    translateContext? exactSourceContext = some exactTargetContext := rfl

def exactReceiver : Source.Path 1 := .var .here

theorem exact_type_selection_translates :
    translateTy? exactSourceContext exactReceiver.selectedType =
      some (.tvar (Layout.newestReceiverSlot []).alpha.name) := rfl

theorem exact_capture_selection_translates :
    translateCapture? exactSourceContext exactReceiver.selectedCapture =
      some (.cvar (Layout.newestReceiverSlot []).chi.name) := rfl

theorem exact_value_member_type_translates :
    translateTy? exactSourceContext exactReceiver.valueMemberType =
      some Object.payloadTypeOpened := rfl

def plainSourceContext : Source.Ctx 1 :=
  Source.Ctx.nil.extendTerm .one

def invalidTypeSelection : Source.Ty 1 :=
  (.var (.here : Source.Var 1) : Source.Path 1).selectedType

def invalidCaptureSelection : Source.Capture 1 :=
  (.var (.here : Source.Var 1) : Source.Path 1).selectedCapture

theorem nonobject_type_receiver_is_rejected :
    translateTy? plainSourceContext invalidTypeSelection = none := rfl

theorem nonobject_capture_receiver_is_rejected :
    translateCapture? plainSourceContext invalidCaptureSelection = none := rfl

/-- Context opening validates an explicit package closure even though that
closure is not retained after the package is opened. -/
def invalidCapturedObjectContext : Source.Ctx 2 :=
  plainSourceContext.extendTerm
    (.capturing invalidCaptureSelection
      (.object (.bounds .one .one .empty .empty)))

theorem invalid_captured_object_context_is_rejected :
    translateContext? invalidCapturedObjectContext = none := rfl

end DOTCaptureToManySortedFC.Acyclic.StaticTranslation
