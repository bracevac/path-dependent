import Coercions.DOT.Captures.Acyclic.Context
import Coercions.DOT.Captures.Acyclic.MemberTyping
import Coercions.Translation.ManySorted.Acyclic.ObjectEncoding

/-!
# Target layout for acyclic DOT objects with captures

Every source binding still denotes one runtime variable.  A non-object
binding therefore contributes one target term binder, while a binding whose
shape after one outer-capture stripping step is an object contributes the
complete two-symbol/four-proof object scope and its separate payload binder.

The receiver lookup below is the sole allocation point for both selected
members.  Consequently repeated `x.A` and `x.C` translations recover the
same type/capture coordinates installed when `x` entered the context.
-/

namespace DOTCaptureToManySortedFC.Acyclic.Layout

/-! Short, local qualifiers keep the source and target universes visibly
separate without pretending that they share syntax. -/

namespace Source

export DOTCapture.Acyclic
  (Scope StaticSort Var Path StaticRef Capture Ty ObjectSig Ctx ExposesObject)

namespace Ty
export DOTCapture.Acyclic.Ty (rename weaken stripCapture)
end Ty

namespace Ctx
export DOTCapture.Acyclic.Ctx (nil)
end Ctx

end Source

namespace Target

export ManySortedFC (StaticSort Sig BVar Rename)

namespace Rename
export ManySortedFC.Rename (id succ)
end Rename

end Target

namespace Object

export DOTCaptureToManySortedFC.Acyclic.ObjectEncoding
  (PayloadScope staticWeakening alphaSlot chiSlot payloadTerm)

end Object

/-- The two source member sorts map directly to the two target sorts. -/
def translateSort : Source.StaticSort → Target.StaticSort
  | .type => .type
  | .capture => .capture

/-- Recognize exactly one stripped object shape.  In particular, this does
not recursively remove nested capture annotations. -/
def objectSignature? {scope : Source.Scope} (type : Source.Ty scope) :
    Option (Source.ObjectSig scope) :=
  match type.stripCapture with
  | .object signature => some signature
  | _ => none

@[simp]
theorem stripCapture_weaken {scope : Source.Scope} (type : Source.Ty scope) :
    type.weaken.stripCapture = type.stripCapture.weaken := by
  cases type <;> rfl

/-- Target resources shared by every selection from one source receiver. -/
structure ReceiverSlot (scope : Target.Sig) where
  alpha : ManySortedTranslation.StaticSlot scope .type
  chi : ManySortedTranslation.StaticSlot scope .capture
  payload : Target.BVar scope .term
deriving DecidableEq

namespace ReceiverSlot

/-- Transport every coordinate through a target extension. -/
def rename {source target : Target.Sig} (slot : ReceiverSlot source)
    (rho : Target.Rename source target) : ReceiverSlot target where
  alpha := slot.alpha.rename rho
  chi := slot.chi.rename rho
  payload := rho.var slot.payload

@[simp]
theorem rename_id {scope : Target.Sig} (slot : ReceiverSlot scope) :
    slot.rename Target.Rename.id = slot := by
  cases slot
  simp [rename]

@[simp]
theorem rename_comp {first second third : Target.Sig}
    (slot : ReceiverSlot first) (rho₁ : Target.Rename first second)
    (rho₂ : Target.Rename second third) :
    (slot.rename rho₁).rename rho₂ =
      slot.rename (rho₁.comp rho₂) := by
  cases slot
  simp [rename, ManySortedTranslation.StaticSlot.rename_comp]

end ReceiverSlot

/-- Target signature induced by a source context.  Each source binding is
expanded once, according to its stored (unweakened) type. -/
def sig : {scope : Source.Scope} → Source.Ctx scope → Target.Sig
  | _, .nil => []
  | _, .extend outer .top => (sig outer) ▹ .term
  | _, .extend outer .bot => (sig outer) ▹ .term
  | _, .extend outer .one => (sig outer) ▹ .term
  | _, .extend outer (.ref _) => (sig outer) ▹ .term
  | _, .extend outer (.object _) =>
      Object.PayloadScope (sig outer)
  | _, .extend outer (.capturing _ (.object _)) =>
      Object.PayloadScope (sig outer)
  | _, .extend outer (.capturing _ .top) => (sig outer) ▹ .term
  | _, .extend outer (.capturing _ .bot) => (sig outer) ▹ .term
  | _, .extend outer (.capturing _ .one) => (sig outer) ▹ .term
  | _, .extend outer (.capturing _ (.ref _)) => (sig outer) ▹ .term
  | _, .extend outer (.capturing _ (.capturing _ _)) =>
      (sig outer) ▹ .term

/-- Weakening induced by one source-context extension. -/
def extendRename {scope : Source.Scope} (outer : Source.Ctx scope)
    (type : Source.Ty scope) :
    Target.Rename (sig outer) (sig (outer.extendTerm type)) :=
  match type with
  | .top => Target.Rename.succ
  | .bot => Target.Rename.succ
  | .one => Target.Rename.succ
  | .ref _ => Target.Rename.succ
  | .object _ =>
      Object.staticWeakening.comp
        (Target.Rename.succ (kind := .term))
  | .capturing _ (.object _) =>
      Object.staticWeakening.comp
        (Target.Rename.succ (kind := .term))
  | .capturing _ .top => Target.Rename.succ
  | .capturing _ .bot => Target.Rename.succ
  | .capturing _ .one => Target.Rename.succ
  | .capturing _ (.ref _) => Target.Rename.succ
  | .capturing _ (.capturing _ _) => Target.Rename.succ

/-- Canonical resources contributed by a newest object binding.  The two
static slots are weakened once below the separate payload binder. -/
def newestReceiverSlot (scope : Target.Sig) :
    ReceiverSlot (Object.PayloadScope scope) where
  alpha := (Object.alphaSlot (scope := scope)).weaken
  chi := (Object.chiSlot (scope := scope)).weaken
  payload := Object.payloadTerm

/-- Total map from source term variables to their unique target runtime
coordinate.  Object variables map to their payload coordinate. -/
def termVar : {scope : Source.Scope} →
    (context : Source.Ctx scope) → Source.Var scope →
      Target.BVar (sig context) .term
  | _, .extend outer type, .there older =>
      (extendRename outer type).var (termVar outer older)
  | _, .extend _ .top, .here => .here
  | _, .extend _ .bot, .here => .here
  | _, .extend _ .one, .here => .here
  | _, .extend _ (.ref _), .here => .here
  | _, .extend _ (.object _), .here =>
      Object.payloadTerm
  | _, .extend _ (.capturing _ (.object _)), .here =>
      Object.payloadTerm
  | _, .extend _ (.capturing _ .top), .here => .here
  | _, .extend _ (.capturing _ .bot), .here => .here
  | _, .extend _ (.capturing _ .one), .here => .here
  | _, .extend _ (.capturing _ (.ref _)), .here => .here
  | _, .extend _ (.capturing _ (.capturing _ _)), .here => .here

/-- Total translation of the variable-only stable source paths. -/
def translatePath {scope : Source.Scope} (context : Source.Ctx scope)
    (path : Source.Path scope) : Target.BVar (sig context) .term :=
  match path with
  | .var name => termVar context name

/-- Deterministically recover the complete shared slot of a source receiver,
when that receiver was introduced with one stripped object shape. -/
def receiverVarSlot? : {scope : Source.Scope} →
    (context : Source.Ctx scope) → Source.Var scope →
      Option (ReceiverSlot (sig context))
  | _, .extend outer type, .there older =>
      (receiverVarSlot? outer older).map fun slot =>
        slot.rename (extendRename outer type)
  | _, .extend _ .top, .here => none
  | _, .extend _ .bot, .here => none
  | _, .extend _ .one, .here => none
  | _, .extend _ (.ref _), .here => none
  | _, .extend outer (.object _), .here =>
      some (newestReceiverSlot (sig outer))
  | _, .extend outer (.capturing _ (.object _)), .here =>
      some (newestReceiverSlot (sig outer))
  | _, .extend _ (.capturing _ .top), .here => none
  | _, .extend _ (.capturing _ .bot), .here => none
  | _, .extend _ (.capturing _ .one), .here => none
  | _, .extend _ (.capturing _ (.ref _)), .here => none
  | _, .extend _ (.capturing _ (.capturing _ _)), .here => none

/-- Path-facing form of `receiverVarSlot?`. -/
def receiverSlot? {scope : Source.Scope} (context : Source.Ctx scope)
    (receiver : Source.Path scope) :
    Option (ReceiverSlot (sig context)) :=
  match receiver with
  | .var name => receiverVarSlot? context name

/-- Sorted member lookup is a projection from the receiver's one shared
slot, never a second allocation. -/
def memberSlot? {scope : Source.Scope} {sort : Source.StaticSort}
    (context : Source.Ctx scope) (reference : Source.StaticRef sort scope) :
    Option
      (ManySortedTranslation.StaticSlot (sig context)
        (translateSort sort)) :=
  match reference with
  | .typeMember receiver => (receiverSlot? context receiver).map (·.alpha)
  | .captureMember receiver => (receiverSlot? context receiver).map (·.chi)

/-- Proof-relevant graph of canonical receiver lookup. -/
def ReceiverSlotAt {scope : Source.Scope} (context : Source.Ctx scope)
    (receiver : Source.Path scope) (slot : ReceiverSlot (sig context)) :
    Prop :=
  receiverSlot? context receiver = some slot

theorem ReceiverSlotAt.functional {scope : Source.Scope}
    {context : Source.Ctx scope} {receiver : Source.Path scope}
    {first second : ReceiverSlot (sig context)}
    (firstLookup : ReceiverSlotAt context receiver first)
    (secondLookup : ReceiverSlotAt context receiver second) :
    first = second := by
  unfold ReceiverSlotAt at firstLookup secondLookup
  rw [firstLookup] at secondLookup
  exact Option.some.inj secondLookup

/-- If source lookup exposes an object shape, layout lookup necessarily
finds the one slot allocated when that receiver entered the context. -/
theorem receiverSlot_exists_of_lookup_object
    {scope : Source.Scope} {context : Source.Ctx scope}
    {name : Source.Var scope} {signature : Source.ObjectSig scope}
    (found : (context.lookup name).stripCapture = .object signature) :
    ∃ slot, receiverVarSlot? context name = some slot := by
  induction context with
  | nil => exact nomatch name
  | @extend scope outer type induction =>
      cases name with
      | here =>
          cases type with
          | top => contradiction
          | bot => contradiction
          | one => contradiction
          | ref => contradiction
          | object =>
              exact ⟨newestReceiverSlot (sig outer), rfl⟩
          | capturing captures shape =>
              cases shape with
              | top => contradiction
              | bot => contradiction
              | one => contradiction
              | ref => contradiction
              | capturing => contradiction
              | object =>
                  exact ⟨newestReceiverSlot (sig outer), rfl⟩
      | there older =>
          change ((outer.lookup older).weaken).stripCapture =
            .object signature at found
          rw [stripCapture_weaken] at found
          generalize shapeEquation :
            (outer.lookup older).stripCapture = shape
          cases shape with
          | top =>
              rw [shapeEquation] at found
              simp [Source.Ty.weaken, Source.Ty.rename] at found
          | bot =>
              rw [shapeEquation] at found
              simp [Source.Ty.weaken, Source.Ty.rename] at found
          | one =>
              rw [shapeEquation] at found
              simp [Source.Ty.weaken, Source.Ty.rename] at found
          | ref =>
              rw [shapeEquation] at found
              simp [Source.Ty.weaken, Source.Ty.rename] at found
          | capturing =>
              rw [shapeEquation] at found
              simp [Source.Ty.weaken, Source.Ty.rename] at found
          | object olderSignature =>
              obtain ⟨olderSlot, olderLookup⟩ := induction shapeEquation
              exact
                ⟨olderSlot.rename (extendRename outer type),
                  Option.map_eq_some_iff.mpr
                    ⟨olderSlot, olderLookup, rfl⟩⟩

/-- The source exposure judgment therefore always has a canonical layout
witness; it cannot select a fabricated member slot. -/
theorem exposesObject_has_receiverSlot
    {scope : Source.Scope} {context : Source.Ctx scope}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (exposes : Source.ExposesObject context receiver signature) :
    ∃ slot, ReceiverSlotAt context receiver slot := by
  cases exposes with
  | «variable» found =>
      exact receiverSlot_exists_of_lookup_object found

@[simp]
theorem receiverSlot?_here_object {scope : Source.Scope}
    (outer : Source.Ctx scope) (signature : Source.ObjectSig scope) :
    receiverSlot? (outer.extendTerm (.object signature))
        (.var (.here : Source.Var (scope + 1))) =
      some (newestReceiverSlot (sig outer)) := rfl

@[simp]
theorem receiverSlot?_here_capturing_object {scope : Source.Scope}
    (outer : Source.Ctx scope) (captures : Source.Capture scope)
    (signature : Source.ObjectSig scope) :
    receiverSlot? (outer.extendTerm (.capturing captures (.object signature)))
        (.var (.here : Source.Var (scope + 1))) =
      some (newestReceiverSlot (sig outer)) := rfl

@[simp]
theorem receiverSlot?_there {scope : Source.Scope}
    (outer : Source.Ctx scope) (type : Source.Ty scope)
    (older : Source.Var scope) :
    receiverSlot? (outer.extendTerm type) (.var (.there older)) =
      (receiverSlot? outer (.var older)).map fun slot =>
        slot.rename (extendRename outer type) := rfl

@[simp]
theorem termVar_there {scope : Source.Scope}
    (outer : Source.Ctx scope) (type : Source.Ty scope)
    (older : Source.Var scope) :
    termVar (outer.extendTerm type) (.there older) =
      (extendRename outer type).var (termVar outer older) := rfl

/-- The receiver payload is definitionally the same runtime coordinate used
by total variable/path translation. -/
theorem receiverSlot_payload {scope : Source.Scope}
    {context : Source.Ctx scope} {receiver : Source.Path scope}
    {slot : ReceiverSlot (sig context)}
    (lookup : receiverSlot? context receiver = some slot) :
    slot.payload = translatePath context receiver := by
  cases receiver with
  | var name =>
      induction context with
      | nil => exact nomatch name
      | @extend scope outer type induction =>
          cases name with
          | here =>
              cases type with
              | top => simp [receiverSlot?, receiverVarSlot?] at lookup
              | bot => simp [receiverSlot?, receiverVarSlot?] at lookup
              | one => simp [receiverSlot?, receiverVarSlot?] at lookup
              | ref => simp [receiverSlot?, receiverVarSlot?] at lookup
              | object =>
                  simp only [receiverSlot?, receiverVarSlot?, translatePath,
                    termVar, Option.some.injEq] at lookup ⊢
                  subst slot
                  rfl
              | capturing captures shape =>
                  cases shape with
                  | top => simp [receiverSlot?, receiverVarSlot?] at lookup
                  | bot => simp [receiverSlot?, receiverVarSlot?] at lookup
                  | one => simp [receiverSlot?, receiverVarSlot?] at lookup
                  | ref => simp [receiverSlot?, receiverVarSlot?] at lookup
                  | capturing =>
                      simp [receiverSlot?, receiverVarSlot?] at lookup
                  | object =>
                      simp only [receiverSlot?, receiverVarSlot?,
                        translatePath, termVar, Option.some.injEq] at lookup ⊢
                      subst slot
                      rfl
          | there older =>
              simp only [receiverSlot?, receiverVarSlot?, translatePath,
                termVar] at lookup ⊢
              obtain ⟨olderSlot, olderLookup, renamed⟩ :=
                Option.map_eq_some_iff.mp lookup
              subst slot
              simp only [ReceiverSlot.rename]
              have olderLookup' :
                  receiverSlot? outer (.var older) = some olderSlot :=
                olderLookup
              rw [induction older olderLookup']
              rfl

/-- Both genuine selections are projections from the same receiver lookup. -/
theorem type_and_capture_members_share_receiver
    {scope : Source.Scope} {context : Source.Ctx scope}
    {receiver : Source.Path scope} {slot : ReceiverSlot (sig context)}
    (lookup : receiverSlot? context receiver = some slot) :
    memberSlot? context receiver.typeMember = some slot.alpha ∧
      memberSlot? context receiver.captureMember = some slot.chi := by
  change
    (receiverSlot? context receiver).map (fun found => found.alpha) =
        some slot.alpha ∧
      (receiverSlot? context receiver).map (fun found => found.chi) =
        some slot.chi
  simp [lookup]

/-- Repeating either selected-member lookup returns the very same slot. -/
theorem repeated_member_lookups_reuse_slot
    {scope : Source.Scope} {context : Source.Ctx scope}
    {receiver : Source.Path scope}
    {first second : ReceiverSlot (sig context)}
    (firstLookup : receiverSlot? context receiver = some first)
    (secondLookup : receiverSlot? context receiver = some second) :
    first = second ∧
      memberSlot? context receiver.typeMember = some first.alpha ∧
      memberSlot? context receiver.captureMember = some first.chi := by
  have same : first = second := by
    rw [firstLookup] at secondLookup
    exact Option.some.inj secondLookup
  refine ⟨same, ?_⟩
  exact type_and_capture_members_share_receiver firstLookup

@[simp]
theorem receiverSlot?_here_nonobject {scope : Source.Scope}
    (outer : Source.Ctx scope) (type : Source.Ty scope)
    (notObject : objectSignature? type = none) :
    receiverSlot? (outer.extendTerm type)
        (.var (.here : Source.Var (scope + 1))) = none := by
  cases type with
  | top => rfl
  | bot => rfl
  | one => rfl
  | ref => rfl
  | object =>
      simp [objectSignature?, Source.Ty.stripCapture] at notObject
  | capturing captures shape =>
      cases shape with
      | top => rfl
      | bot => rfl
      | one => rfl
      | ref => rfl
      | capturing => rfl
      | object =>
          simp [objectSignature?, Source.Ty.stripCapture]
            at notObject

/-! ## Decisive layout regressions -/

def regressionSignature : Source.ObjectSig 0 :=
  .bounds .bot .top .empty .empty

def regressionObjectContext : Source.Ctx 1 :=
  Source.Ctx.nil.extendTerm (.object regressionSignature)

theorem newest_object_has_exact_canonical_coordinates :
    receiverSlot? regressionObjectContext (.var .here) =
      some
        { alpha := (Object.alphaSlot (scope := [])).weaken
          chi := (Object.chiSlot (scope := [])).weaken
          payload := Object.payloadTerm } := rfl

theorem newest_object_term_coordinate_is_payload :
    translatePath regressionObjectContext (.var .here) =
      Object.payloadTerm := rfl

def regressionPlainContext : Source.Ctx 1 :=
  Source.Ctx.nil.extendTerm .one

theorem newest_plain_receiver_has_no_slot :
    receiverSlot? regressionPlainContext (.var .here) = none := rfl

end DOTCaptureToManySortedFC.Acyclic.Layout
