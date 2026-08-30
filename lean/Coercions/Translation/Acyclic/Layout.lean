import Coercions.Translation.Acyclic.MemberEncoding
import Coercions.DOT.Acyclic.Explicit.Context

/-!
# Stable DOT path/name layout in standalone FCsub scopes

This is bridge code: the source signature is `DotFC.Sig`, while every result
scope and variable is independently indexed by `FCsub.Sig`.  A direct DOT
member term expands according to `MemberEncoding`; a reusable explicit-source
member handle remains a proof-only alias and allocates no FCsub binder.
-/

namespace DotToFCsub.Layout

/-- All target resources associated with one stable DOT `(path,label)` key.
The first three fields belong to the static telescope; `payload` is the
separate runtime binder opened after it. -/
structure Slot (scope : FCsub.Sig) where
  name : FCsub.BVar scope .type
  lower : FCsub.BVar scope (.evidence .inclusion)
  upper : FCsub.BVar scope (.evidence .inclusion)
  payload : FCsub.BVar scope .term

namespace Slot

def rename {source target : FCsub.Sig} (slot : Slot source)
    (rho : FCsub.Rename source target) : Slot target where
  name := rho.var slot.name
  lower := rho.var slot.lower
  upper := rho.var slot.upper
  payload := rho.var slot.payload

end Slot

/-- Target signature induced by a mixed explicit-source context. -/
def sig : {source : DotFC.Sig} → DotFC.Explicit.Ctx source → FCsub.Sig
  | _, .nil => []
  | _, .extend outer binding =>
      match binding with
      | .term (.member _ _ _) => MemberEncoding.Payload (sig outer)
      | .term _ => FCsub.Sig.extend (sig outer) .term
      | .typeVar => FCsub.Sig.extend (sig outer) .type
      | .equality _ _ =>
          FCsub.Sig.extend (sig outer) (.evidence .equality)
      | .inclusion _ _ =>
          FCsub.Sig.extend (sig outer) (.evidence .inclusion)
      | .member _ => sig outer

/-- Weakening induced by one mixed source-context extension. -/
def extendRename {source : DotFC.Sig} {kind : DotFC.BinderKind}
    (outer : DotFC.Explicit.Ctx source)
    (binding : DotFC.Explicit.Binding source kind) :
    FCsub.Rename (sig outer) (sig (.extend outer binding)) :=
  match binding with
  | .term (.member _ _ _) => MemberEncoding.weakenPayload
  | .term .top => FCsub.Rename.succ
  | .term .bot => FCsub.Rename.succ
  | .term (.all _ _) => FCsub.Rename.succ
  | .term (.sel _ _) => FCsub.Rename.succ
  | .typeVar => FCsub.Rename.succ
  | .equality _ _ => FCsub.Rename.succ
  | .inclusion _ _ => FCsub.Rename.succ
  | .member _ => FCsub.Rename.id

/-- Map each source runtime path to the separately bound FCsub payload. -/
def termVar : {source : DotFC.Sig} →
    (context : DotFC.Explicit.Ctx source) →
    DotFC.BVar source .term → FCsub.BVar (sig context) .term
  | _, .extend _ (.term (.member _ _ _)), .here => MemberEncoding.payload
  | _, .extend _ (.term .top), .here => .here
  | _, .extend _ (.term .bot), .here => .here
  | _, .extend _ (.term (.all _ _)), .here => .here
  | _, .extend _ (.term (.sel _ _)), .here => .here
  | _, .extend outer binding, .there older =>
      (extendRename outer binding).var (termVar outer older)

/-- Look up all canonical FCsub resources for one stable source key. -/
def fullSlot? : {source : DotFC.Sig} →
    (context : DotFC.Explicit.Ctx source) →
    DotFC.BVar source .term → DotFC.Source.Name →
    Option (Slot (sig context))
  | _, .extend _ (.term (.member boundLabel _ _)), .here, label =>
      if boundLabel = label then
        some ⟨MemberEncoding.name, MemberEncoding.lower,
          MemberEncoding.upper, MemberEncoding.payload⟩
      else
        none
  | _, .extend _ (.term .top), .here, _ => none
  | _, .extend _ (.term .bot), .here, _ => none
  | _, .extend _ (.term (.all _ _)), .here, _ => none
  | _, .extend _ (.term (.sel _ _)), .here, _ => none
  | _, .extend outer binding, .there older, label =>
      (fullSlot? outer older label).map fun slot =>
        slot.rename (extendRename outer binding)

/-- Look up the one generated FCsub name for a stable source key. -/
def slot? {source : DotFC.Sig} (context : DotFC.Explicit.Ctx source)
    (path : DotFC.BVar source .term) (label : DotFC.Source.Name) :
    Option (FCsub.BVar (sig context) .type) :=
  (fullSlot? context path label).map Slot.name

/-- Look up the canonical lower and upper evidence variables. -/
def bounds? {source : DotFC.Sig} (context : DotFC.Explicit.Ctx source)
    (path : DotFC.BVar source .term) (label : DotFC.Source.Name) :
    Option
      (FCsub.BVar (sig context) (.evidence .inclusion) ×
        FCsub.BVar (sig context) (.evidence .inclusion)) :=
  (fullSlot? context path label).map fun slot => (slot.lower, slot.upper)

/-- Proof-relevant complete stable member lookup. -/
def FullSlotAt {source : DotFC.Sig}
    (context : DotFC.Explicit.Ctx source) (path : DotFC.BVar source .term)
    (label : DotFC.Source.Name) (slot : Slot (sig context)) : Prop :=
  fullSlot? context path label = some slot

theorem FullSlotAt.functional {source : DotFC.Sig}
    {context : DotFC.Explicit.Ctx source} {path : DotFC.BVar source .term}
    {label : DotFC.Source.Name} {first second : Slot (sig context)}
    (firstLookup : FullSlotAt context path label first)
    (secondLookup : FullSlotAt context path label second) : first = second := by
  unfold FullSlotAt at firstLookup secondLookup
  rw [firstLookup] at secondLookup
  exact Option.some.inj secondLookup

/-- The payload coordinate of a canonical slot is exactly the target runtime
variable assigned to the corresponding source path. -/
theorem fullSlot_payload {source : DotFC.Sig}
    {context : DotFC.Explicit.Ctx source}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {slot : Slot (sig context)}
    (lookup : fullSlot? context path label = some slot) :
    slot.payload = termVar context path := by
  induction context with
  | nil => exact nomatch path
  | @extend source kind outer binding induction =>
      cases path with
      | here =>
          cases binding with
          | term type =>
              cases type with
              | top => simp [fullSlot?] at lookup
              | bot => simp [fullSlot?] at lookup
              | all domain codomain => simp [fullSlot?] at lookup
              | sel path label => simp [fullSlot?] at lookup
              | member boundLabel lower upper =>
                  simp only [fullSlot?, termVar] at lookup ⊢
                  split at lookup
                  next same =>
                    simp only [Option.some.injEq] at lookup
                    subst slot
                    rfl
                  next different => contradiction
      | there older =>
          cases binding <;>
            simp only [fullSlot?, termVar] at lookup ⊢ <;>
            obtain ⟨olderSlot, olderLookup, renamed⟩ :=
              Option.map_eq_some_iff.mp lookup <;>
            subst slot <;>
            simp only [Slot.rename] <;>
            rw [induction olderLookup]

@[simp]
theorem fullSlot_here_member {source : DotFC.Sig}
    (outer : DotFC.Explicit.Ctx source) (label : DotFC.Source.Name)
    (lower upper : DotFC.Source.Ty source) :
    fullSlot? (outer.extendTerm (.member label lower upper))
      (.here : DotFC.BVar (DotFC.Sig.extend source .term) .term) label =
      some ⟨MemberEncoding.name, MemberEncoding.lower,
        MemberEncoding.upper, MemberEncoding.payload⟩ := by
  simp [DotFC.Explicit.Ctx.extendTerm, fullSlot?]

@[simp]
theorem bounds_here_member {source : DotFC.Sig}
    (outer : DotFC.Explicit.Ctx source) (label : DotFC.Source.Name)
    (lower upper : DotFC.Source.Ty source) :
    bounds? (outer.extendTerm (.member label lower upper))
      (.here : DotFC.BVar (DotFC.Sig.extend source .term) .term) label =
      some (MemberEncoding.lower, MemberEncoding.upper) := by
  simp [bounds?, fullSlot_here_member]
  rfl

/-- Proof-relevant lookup of the generated abstract name. -/
def SlotAt {source : DotFC.Sig} (context : DotFC.Explicit.Ctx source)
    (path : DotFC.BVar source .term) (label : DotFC.Source.Name)
    (name : FCsub.BVar (sig context) .type) : Prop :=
  slot? context path label = some name

theorem SlotAt.functional {source : DotFC.Sig}
    {context : DotFC.Explicit.Ctx source} {path : DotFC.BVar source .term}
    {label : DotFC.Source.Name}
    {first second : FCsub.BVar (sig context) .type}
    (firstLookup : SlotAt context path label first)
    (secondLookup : SlotAt context path label second) : first = second := by
  unfold SlotAt at firstLookup secondLookup
  rw [firstLookup] at secondLookup
  exact Option.some.inj secondLookup

@[simp]
theorem slot_here_member {source : DotFC.Sig}
    (outer : DotFC.Explicit.Ctx source) (label : DotFC.Source.Name)
    (lower upper : DotFC.Source.Ty source) :
    slot? (outer.extendTerm (.member label lower upper))
      (.here : DotFC.BVar (DotFC.Sig.extend source .term) .term) label =
      some MemberEncoding.name := by
  simp [slot?]
  rfl

@[simp]
theorem slot_here_member_ne {source : DotFC.Sig}
    (outer : DotFC.Explicit.Ctx source)
    (boundLabel label : DotFC.Source.Name)
    (lower upper : DotFC.Source.Ty source) (different : boundLabel ≠ label) :
    slot? (outer.extendTerm (.member boundLabel lower upper))
      (.here : DotFC.BVar (DotFC.Sig.extend source .term) .term) label =
      none := by
  simp [slot?, DotFC.Explicit.Ctx.extendTerm, fullSlot?, different]

@[simp]
theorem slot_there {source : DotFC.Sig} {kind : DotFC.BinderKind}
    (outer : DotFC.Explicit.Ctx source)
    (binding : DotFC.Explicit.Binding source kind)
    (path : DotFC.BVar source .term) (label : DotFC.Source.Name) :
    slot? (.extend outer binding) (.there path) label =
      (slot? outer path label).map (extendRename outer binding).var := by
  cases binding with
  | term type =>
      cases type <;>
        simp [slot?, fullSlot?, Slot.rename, Option.map_map,
          Function.comp_def]
  | typeVar =>
      simp [slot?, fullSlot?, Slot.rename, Option.map_map,
        Function.comp_def]
  | equality =>
      simp [slot?, fullSlot?, Slot.rename, Option.map_map,
        Function.comp_def]
  | inclusion =>
      simp [slot?, fullSlot?, Slot.rename, Option.map_map,
        Function.comp_def]
  | member =>
      simp [slot?, fullSlot?, Slot.rename, Option.map_map,
        Function.comp_def]

/-- Partial DOT type translation through the stable member layout. -/
def translateTy? : {source : DotFC.Sig} →
    (context : DotFC.Explicit.Ctx source) → DotFC.Source.Ty source →
    Option (FCsub.Ty (sig context))
  | _, _, .top => some .top
  | _, _, .bot => some .bot
  | _, context, .member _ lower upper => do
      let lower' ← translateTy? context lower
      let upper' ← translateTy? context upper
      pure (MemberEncoding.existsType lower' upper')
  | _, context, .sel path label => do
      let name ← slot? context path label
      pure (.tvar name)
  | _, context, .all .top codomain => do
      let codomain' ← translateTy? (context.extendTerm .top) codomain
      pure (.arr .top codomain')
  | _, context, .all .bot codomain => do
      let codomain' ← translateTy? (context.extendTerm .bot) codomain
      pure (.arr .bot codomain')
  | _, context, .all (.all domain result) codomain => do
      let nested' ← translateTy? context (.all domain result)
      let codomain' ←
        translateTy? (context.extendTerm (.all domain result)) codomain
      pure (.arr nested' codomain')
  | _, context, .all (.sel path label) codomain => do
      let domain' ← translateTy? context (.sel path label)
      let codomain' ←
        translateTy? (context.extendTerm (.sel path label)) codomain
      pure (.arr domain' codomain')
  | _, context, .all (.member label lower upper) codomain => do
      let lower' ← translateTy? context lower
      let upper' ← translateTy? context upper
      let codomain' ←
        translateTy? (context.extendTerm (.member label lower upper)) codomain
      pure (MemberEncoding.forallType lower' upper' codomain')

/-- Proof-relevant graph of target type translation. -/
def Translates {source : DotFC.Sig} (context : DotFC.Explicit.Ctx source)
    (sourceType : DotFC.Source.Ty source)
    (targetType : FCsub.Ty (sig context)) : Prop :=
  translateTy? context sourceType = some targetType

def ReadyTy {source : DotFC.Sig} (context : DotFC.Explicit.Ctx source)
    (type : DotFC.Source.Ty source) : Prop :=
  ∃ target, Translates context type target

theorem Translates.functional {source : DotFC.Sig}
    {context : DotFC.Explicit.Ctx source}
    {sourceType : DotFC.Source.Ty source}
    {first second : FCsub.Ty (sig context)}
    (left : Translates context sourceType first)
    (right : Translates context sourceType second) : first = second := by
  unfold Translates at left right
  rw [left] at right
  exact Option.some.inj right

/-- Readiness of a mixed explicit-source binding.  Member handles alias an existing
stable slot and therefore allocate no new target name. -/
inductive ReadyBinding {source : DotFC.Sig}
    (context : DotFC.Explicit.Ctx source) :
    {kind : DotFC.BinderKind} → DotFC.Explicit.Binding source kind → Prop where
  | term {type : DotFC.Source.Ty source} (ready : ReadyTy context type) :
      ReadyBinding context (.term type)
  | typeVar : ReadyBinding context .typeVar
  | equality {left right : DotFC.Source.Ty source}
      (leftReady : ReadyTy context left) (rightReady : ReadyTy context right) :
      ReadyBinding context (.equality left right)
  | inclusion {sourceType targetType : DotFC.Source.Ty source}
      (sourceReady : ReadyTy context sourceType)
      (targetReady : ReadyTy context targetType) :
      ReadyBinding context (.inclusion sourceType targetType)
  | member {specification : DotFC.Explicit.MemberSpec source}
      (lowerReady : ReadyTy context specification.lower)
      (upperReady : ReadyTy context specification.upper)
      {name : FCsub.BVar (sig context) .type}
      (slot : SlotAt context specification.path specification.label name) :
      ReadyBinding context (.member specification)

inductive Ready : {source : DotFC.Sig} →
    DotFC.Explicit.Ctx source → Prop where
  | nil : Ready .nil
  | extend {source : DotFC.Sig} {kind : DotFC.BinderKind}
      {outer : DotFC.Explicit.Ctx source}
      {binding : DotFC.Explicit.Binding source kind}
      (outerReady : Ready outer)
      (bindingReady : ReadyBinding outer binding) :
      Ready (.extend outer binding)

/-- Interface shapes admitted by the current direct-slot acyclic boundary. -/
inductive SameInterface {source : DotFC.Sig} :
    DotFC.Source.Ty source → DotFC.Source.Ty source → Prop where
  | plain {left right : DotFC.Source.Ty source}
      (leftPlain : ∀ label lower upper, left ≠ .member label lower upper)
      (rightPlain : ∀ label lower upper, right ≠ .member label lower upper) :
      SameInterface left right
  | member {label : DotFC.Source.Name}
      {lower₁ upper₁ lower₂ upper₂ : DotFC.Source.Ty source} :
      SameInterface (.member label lower₁ upper₁)
        (.member label lower₂ upper₂)

end DotToFCsub.Layout
