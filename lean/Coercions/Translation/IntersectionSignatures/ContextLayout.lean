import Coercions.Translation.IntersectionSignatures.Encoding

/-!
# Context-dependent intersection-signature layout

A source term binding has exactly two layout shapes.  Plain declarations add
one FCsub term binder.  A collectible member/intersection declaration opens
one complete names-first signature telescope and then one shared unit payload.
The latter case never opens one package per member occurrence.
-/

namespace DotToFCsub.IntersectionSignatures.ContextLayout

open DotFCI.Source
open Encoding

/-! ## Binding classification and target scope -/

/-- Shapes that are represented by one ordinary target term binder. -/
inductive PlainShape : DotFCI.Source.Ty sourceScope → Type where
  | top : PlainShape .top
  | bot : PlainShape .bot
  | all {domain : DotFCI.Source.Ty sourceScope}
      {codomain : DotFCI.Source.Ty (sourceScope ▹ .term)} :
      PlainShape (.all domain codomain)
  | sel {path : DotFC.BVar sourceScope .term} {label : Name} :
      PlainShape (.sel path label)

/-- A proof-relevant layout, indexed by both its source context and exact
FCsub target scope. -/
inductive Context : {sourceScope : DotFC.Sig} →
    DotFCI.Source.Ctx sourceScope → FCsub.Sig → Type where
  | nil : Context .nil []
  | plain {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
      {targetScope : FCsub.Sig} {type : DotFCI.Source.Ty sourceScope}
      (outer : Context sourceContext targetScope)
      (shape : PlainShape type) :
      Context (sourceContext.snoc type) (targetScope ▹ .term)
  | signature {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
      {targetScope : FCsub.Sig} {type : DotFCI.Source.Ty sourceScope}
      (signature : Signature sourceScope)
      (outer : Context sourceContext targetScope)
      (collectible : Collectible sourceContext type signature)
      (closed : ClosedSignature signature) :
      Context (sourceContext.snoc type)
        (FCsub.PayloadScope targetScope signature.entries.length
          (signatureConstraintCount signature.entries))

/-- Weakening across a plain source declaration. -/
def plainExtensionRename (targetScope : FCsub.Sig) :
    FCsub.Rename targetScope (targetScope ▹ .term) :=
  FCsub.Rename.succ

/-- Weakening across one complete signature package and its payload. -/
def signatureExtensionRename (targetScope : FCsub.Sig)
    (signature : Signature sourceScope) :
    FCsub.Rename targetScope
      (FCsub.PayloadScope targetScope signature.entries.length
        (signatureConstraintCount signature.entries)) :=
  FCsub.Rename.weakenPayload signature.entries.length
    (signatureConstraintCount signature.entries)

/-! ## Label-indexed member resources -/

/-- The two evidence variables contributed by one interval occurrence. -/
structure BoundSlot (scope : FCsub.Sig) where
  lower : FCsub.BVar scope (.evidence .inclusion)
  upper : FCsub.BVar scope (.evidence .inclusion)
deriving DecidableEq

namespace BoundSlot

def rename {source target : FCsub.Sig} (slot : BoundSlot source)
    (rho : FCsub.Rename source target) : BoundSlot target where
  lower := rho.var slot.lower
  upper := rho.var slot.upper

@[simp]
theorem rename_id {scope : FCsub.Sig} (slot : BoundSlot scope) :
    slot.rename FCsub.Rename.id = slot := by
  cases slot
  rfl

@[simp]
theorem rename_comp {first second third : FCsub.Sig}
    (slot : BoundSlot first) (firstRename : FCsub.Rename first second)
    (secondRename : FCsub.Rename second third) :
    (slot.rename firstRename).rename secondRename =
      slot.rename (firstRename.comp secondRename) := by
  cases slot
  rfl

end BoundSlot

/-- Every target resource for one `(path,label)` identity.  `bounds` contains
all interval occurrences accumulated under the normalized label entry. -/
structure MemberSlot (scope : FCsub.Sig) (label : Name) where
  name : FCsub.BVar scope .type
  bounds : List (BoundSlot scope)
  payload : FCsub.BVar scope .term
deriving DecidableEq

namespace MemberSlot

def rename {source target : FCsub.Sig} {label : Name}
    (slot : MemberSlot source label) (rho : FCsub.Rename source target) :
    MemberSlot target label where
  name := rho.var slot.name
  bounds := slot.bounds.map fun bound => bound.rename rho
  payload := rho.var slot.payload

@[simp]
theorem rename_id {scope : FCsub.Sig} {label : Name}
    (slot : MemberSlot scope label) :
    slot.rename FCsub.Rename.id = slot := by
  cases slot with
  | mk name bounds payload =>
      simp [rename]

@[simp]
theorem rename_comp {first second third : FCsub.Sig} {label : Name}
    (slot : MemberSlot first label)
    (firstRename : FCsub.Rename first second)
    (secondRename : FCsub.Rename second third) :
    (slot.rename firstRename).rename secondRename =
      slot.rename (firstRename.comp secondRename) := by
  cases slot with
  | mk name bounds payload =>
      simp [rename, List.map_map, Function.comp_def]

/-- Materialize canonical finite positions as exact binders in the package's
opened payload scope. -/
def ofIndex (targetScope : FCsub.Sig) (label : Name)
    {names constraints : Nat} (index : EntryIndex names constraints) :
    MemberSlot (FCsub.PayloadScope targetScope names constraints) label where
  name := .there
    ((FCsub.Rename.weakenN (.evidence .inclusion) constraints).var
      (FCsub.BVar.bound names index.name))
  bounds := index.bounds.map fun bound =>
    { lower := .there (FCsub.BVar.bound constraints bound.lower)
      upper := .there (FCsub.BVar.bound constraints bound.upper) }
  payload := .here

@[simp]
theorem ofIndex_bounds_length (targetScope : FCsub.Sig) (label : Name)
    {names constraints : Nat} (index : EntryIndex names constraints) :
    (ofIndex targetScope label index).bounds.length = index.bounds.length := by
  simp [ofIndex]

end MemberSlot

/-! ## Executable key lookup -/

/-- Every source path denotes its one runtime target binder: either the plain
term or the shared signature payload. -/
def Context.termVar {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
    {targetScope : FCsub.Sig} (layout : Context sourceContext targetScope) :
    DotFC.BVar sourceScope .term → FCsub.BVar targetScope .term :=
  match layout with
  | .nil => fun path => nomatch path
  | .plain outer _ => fun
      | .here => .here
      | .there older =>
          (plainExtensionRename _).var (outer.termVar older)
  | @Context.signature _ _ _ _ sig outer _ _ => fun
      | .here => .here
      | .there older =>
          (signatureExtensionRename _ sig).var (outer.termVar older)

/-- Lookup all resources for a stable `(path,label)` key. -/
def Context.slot? {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
    {targetScope : FCsub.Sig} (layout : Context sourceContext targetScope) :
    (path : DotFC.BVar sourceScope .term) → (label : Name) →
      Option (MemberSlot targetScope label) :=
  match layout with
  | .nil => fun path => nomatch path
  | .plain outer _ => fun
      | .here => fun _ => none
      | .there older => fun label =>
          (outer.slot? older label).map fun slot =>
            slot.rename (plainExtensionRename _)
  | @Context.signature _ _ _ _ sig outer _ _ => fun
      | .here => fun label =>
          (allocation? sig label).map fun index =>
            MemberSlot.ofIndex _ label index
      | .there older => fun label =>
          (outer.slot? older label).map fun slot =>
            slot.rename (signatureExtensionRename _ sig)

/-- Key-record form of `slot?`. -/
def Context.lookup? {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    (layout : Context sourceContext targetScope)
    (key : MemberKey sourceScope) : Option (MemberSlot targetScope key.label) :=
  layout.slot? key.path key.label

/-- Proof-relevant successful key compilation. -/
structure MemberLookup {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    (layout : Context sourceContext targetScope)
    (key : MemberKey sourceScope) : Type where
  slot : MemberSlot targetScope key.label
  compiled : layout.lookup? key = some slot

namespace MemberLookup

/-- Executable key lookup is functional, independently of occurrence proofs. -/
theorem functional {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : Context sourceContext targetScope} {key : MemberKey sourceScope}
    (first second : MemberLookup layout key) : first.slot = second.slot := by
  have equality := second.compiled
  rw [first.compiled] at equality
  injection equality

theorem name_unique {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : Context sourceContext targetScope} {key : MemberKey sourceScope}
    (first second : MemberLookup layout key) :
    first.slot.name = second.slot.name :=
  congrArg MemberSlot.name (functional first second)

/-- Weakening a successful key below one plain declaration is exactly slot
renaming by the plain extension map. -/
def weakenPlain {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : Context sourceContext targetScope} {key : MemberKey sourceScope}
    (lookup : MemberLookup layout key) {type : Ty sourceScope}
    (shape : PlainShape type) :
    MemberLookup (Context.plain layout shape) ⟨.there key.path, key.label⟩ where
  slot := lookup.slot.rename (plainExtensionRename targetScope)
  compiled := by
    change (Context.plain layout shape).slot? (.there key.path) key.label = _
    have compiled : layout.slot? key.path key.label = some lookup.slot := by
      simpa only [Context.lookup?] using lookup.compiled
    simp [Context.slot?, compiled]

/-- Weakening below a complete signature package renames an older slot once;
it never reallocates the member identity. -/
def weakenSignature {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : Context sourceContext targetScope} {key : MemberKey sourceScope}
    (lookup : MemberLookup layout key) {type : Ty sourceScope}
    {signature : Signature sourceScope}
    (collectible : Collectible sourceContext type signature)
    (closed : ClosedSignature signature) :
    MemberLookup (Context.signature signature layout collectible closed)
      ⟨.there key.path, key.label⟩ where
  slot := lookup.slot.rename (signatureExtensionRename targetScope signature)
  compiled := by
    change (Context.signature signature layout collectible closed).slot?
      (.there key.path) key.label = _
    have compiled : layout.slot? key.path key.label = some lookup.slot := by
      simpa only [Context.lookup?] using lookup.compiled
    simp [Context.slot?, compiled]

/-- A successful allocation lookup constructs the newest binding's complete
member slot without any further search or fresh-name operation. -/
def signatureHere {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    (layout : Context sourceContext targetScope) {type : Ty sourceScope}
    {signature : Signature sourceScope}
    (collectible : Collectible sourceContext type signature)
    (closed : ClosedSignature signature) (label : Name)
    (index : EntryIndex signature.entries.length
      (signatureConstraintCount signature.entries))
    (found : allocation? signature label = some index) :
    MemberLookup (Context.signature signature layout collectible closed)
      ⟨.here, label⟩ where
  slot := MemberSlot.ofIndex targetScope label index
  compiled := by
    change (allocation? signature label).map
      (fun position => MemberSlot.ofIndex targetScope label position) = _
    rw [found]
    rfl

end MemberLookup

/-! ## Structural allocation certificates -/

/-- A source key is allocated by a layout.  The constructors mirror context
extension, so successful lookup is derived from one newest allocation and
ordinary weakening; no option equation is stored by clients. -/
inductive MemberAllocated : {sourceScope : DotFC.Sig} →
    {sourceContext : Ctx sourceScope} → {targetScope : FCsub.Sig} →
    (layout : Context sourceContext targetScope) →
    DotFC.BVar sourceScope .term → Name → Type where
  | here {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
      {targetScope : FCsub.Sig} (outer : Context sourceContext targetScope)
      {type : Ty sourceScope} {signature : Signature sourceScope}
      (collectible : Collectible sourceContext type signature)
      (closed : ClosedSignature signature) (label : Name)
      (index : EntryIndex signature.entries.length
        (signatureConstraintCount signature.entries))
      (found : allocation? signature label = some index) :
      MemberAllocated
        (Context.signature signature outer collectible closed) .here label
  | plainThere {sourceScope : DotFC.Sig}
      {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
      {outer : Context sourceContext targetScope}
      {path : DotFC.BVar sourceScope .term} {label : Name}
      (allocated : MemberAllocated outer path label)
      {type : Ty sourceScope} (shape : PlainShape type) :
      MemberAllocated (Context.plain outer shape) (.there path) label
  | signatureThere {sourceScope : DotFC.Sig}
      {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
      {outer : Context sourceContext targetScope}
      {path : DotFC.BVar sourceScope .term} {label : Name}
      (allocated : MemberAllocated outer path label)
      {type : Ty sourceScope} {signature : Signature sourceScope}
      (collectible : Collectible sourceContext type signature)
      (closed : ClosedSignature signature) :
      MemberAllocated
        (Context.signature signature outer collectible closed)
        (.there path) label

namespace MemberAllocated

/-- Compile a structural allocation certificate to the executable key lookup
equation and its exact target slot. -/
def compile {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
    {targetScope : FCsub.Sig} {layout : Context sourceContext targetScope}
    {path : DotFC.BVar sourceScope .term} {label : Name}
    (allocated : MemberAllocated layout path label) :
    MemberLookup layout ⟨path, label⟩ :=
  match allocated with
  | .here outer collectible closed label index found =>
      MemberLookup.signatureHere outer collectible closed label index found
  | .plainThere older shape =>
      older.compile.weakenPlain shape
  | .signatureThere older collectible closed =>
      older.compile.weakenSignature collectible closed

/-- Context allocation certificates really do compile through `lookup?`. -/
theorem compiles {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    {layout : Context sourceContext targetScope}
    {path : DotFC.BVar sourceScope .term} {label : Name}
    (allocated : MemberAllocated layout path label) :
    layout.lookup? ⟨path, label⟩ = some allocated.compile.slot :=
  allocated.compile.compiled

end MemberAllocated

/-! ## Extension/naturality equations -/

@[simp]
theorem Context.termVar_plain_here {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    (outer : Context sourceContext targetScope) {type : Ty sourceScope}
    (shape : PlainShape type) :
    (Context.plain outer shape).termVar .here = .here := rfl

@[simp]
theorem Context.termVar_signature_here {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    (outer : Context sourceContext targetScope) {type : Ty sourceScope}
    {signature : Signature sourceScope}
    (collectible : Collectible sourceContext type signature)
    (closed : ClosedSignature signature) :
    (Context.signature signature outer collectible closed).termVar .here =
      .here := rfl

@[simp]
theorem Context.termVar_plain_there {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    (outer : Context sourceContext targetScope) {type : Ty sourceScope}
    (shape : PlainShape type) (path : DotFC.BVar sourceScope .term) :
    (Context.plain outer shape).termVar (.there path) =
      (plainExtensionRename targetScope).var (outer.termVar path) := rfl

@[simp]
theorem Context.termVar_signature_there {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    (outer : Context sourceContext targetScope) {type : Ty sourceScope}
    {signature : Signature sourceScope}
    (collectible : Collectible sourceContext type signature)
    (closed : ClosedSignature signature)
    (path : DotFC.BVar sourceScope .term) :
    (Context.signature signature outer collectible closed).termVar
        (.there path) =
      (signatureExtensionRename targetScope signature).var
        (outer.termVar path) := rfl

@[simp]
theorem Context.slot?_plain_here {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    (outer : Context sourceContext targetScope) {type : Ty sourceScope}
    (shape : PlainShape type) (label : Name) :
    (Context.plain outer shape).slot? .here label = none := rfl

@[simp]
theorem Context.slot?_plain_there {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    (outer : Context sourceContext targetScope) {type : Ty sourceScope}
    (shape : PlainShape type) (path : DotFC.BVar sourceScope .term)
    (label : Name) :
    (Context.plain outer shape).slot? (.there path) label =
      (outer.slot? path label).map fun slot =>
        slot.rename (plainExtensionRename targetScope) := rfl

@[simp]
theorem Context.slot?_signature_there {sourceScope : DotFC.Sig}
    {sourceContext : Ctx sourceScope} {targetScope : FCsub.Sig}
    (outer : Context sourceContext targetScope) {type : Ty sourceScope}
    {signature : Signature sourceScope}
    (collectible : Collectible sourceContext type signature)
    (closed : ClosedSignature signature)
    (path : DotFC.BVar sourceScope .term) (label : Name) :
    (Context.signature signature outer collectible closed).slot?
        (.there path) label =
      (outer.slot? path label).map fun slot =>
        slot.rename (signatureExtensionRename targetScope signature) := rfl

end DotToFCsub.IntersectionSignatures.ContextLayout
