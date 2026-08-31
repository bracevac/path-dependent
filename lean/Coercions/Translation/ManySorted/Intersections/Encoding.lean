import Coercions.DOT.Captures.Intersections.Signature
import Coercions.ManySortedFC.TheoryMapChecker

/-!
# Names-first encoding of prepared intersection signatures

This module is the target half of M11's two-phase interface translation.
`PreparedSignature` already contains every allocated member name and every
translated bound in the complete symbol scope.  `encode` only emits the two
primitive inclusion propositions for each retained interval occurrence.

No endpoint is combined, and no name is allocated while propositions are
emitted.
-/

namespace DOTCaptureToManySortedFC.Intersections.Encoding

namespace Source

abbrev StaticSort := DOTCapture.Intersections.StaticSort
abbrev Interval := DOTCapture.Intersections.Interval

end Source

namespace Target

open ManySortedFC

abbrev Sig := ManySortedFC.Sig
abbrev StaticSort := ManySortedFC.StaticSort
abbrev Relation := ManySortedFC.Relation
abbrev BVar := ManySortedFC.BVar
abbrev StaticExpr := ManySortedFC.StaticExpr
abbrev Proposition := ManySortedFC.Proposition
abbrev Theory := ManySortedFC.Theory
abbrev SymbolScope := ManySortedFC.SymbolScope
abbrev StaticScope := ManySortedFC.StaticScope
abbrev Rename := ManySortedFC.Rename

end Target

/-- Translate the source sort tag to the identically separated target sort. -/
def targetSort : Source.StaticSort -> Target.StaticSort
  | .type => .type
  | .capture => .capture

/-- A member name allocated in the complete names-only block. -/
inductive MemberName (scope : Target.Sig) where
  | type (label : Nat)
      (name : Target.BVar scope (.symbol .type)) : MemberName scope
  | capture (label : Nat)
      (name : Target.BVar scope (.symbol .capture)) : MemberName scope
deriving DecidableEq

namespace MemberName

def label {scope : Target.Sig} : MemberName scope -> Nat
  | .type label _ => label
  | .capture label _ => label

def sort {scope : Target.Sig} : MemberName scope -> Target.StaticSort
  | .type _ _ => .type
  | .capture _ _ => .capture

def rename {source target : Target.Sig} (member : MemberName source)
    (rho : Target.Rename source target) : MemberName target :=
  match member with
  | .type label name => .type label (rho.var name)
  | .capture label name => .capture label (rho.var name)

@[simp]
theorem rename_label {source target : Target.Sig}
    (member : MemberName source) (rho : Target.Rename source target) :
    (member.rename rho).label = member.label := by
  cases member <;> rfl

@[simp]
theorem rename_sort {source target : Target.Sig}
    (member : MemberName source) (rho : Target.Rename source target) :
    (member.rename rho).sort = member.sort := by
  cases member <;> rfl

end MemberName

/-- A normalized entry after its shared name has been allocated and every
bound has been translated into the complete symbol scope. -/
inductive PreparedEntry (scope : Target.Sig) where
  | type (label : Nat) (name : Target.BVar scope (.symbol .type))
      (intervals : List (Source.Interval (Target.StaticExpr .type scope))) :
      PreparedEntry scope
  | capture (label : Nat) (name : Target.BVar scope (.symbol .capture))
      (intervals : List (Source.Interval (Target.StaticExpr .capture scope))) :
      PreparedEntry scope
deriving DecidableEq

namespace PreparedEntry

/-- Two directed inclusion slots for each retained interval.  This recursive
form keeps the relation index definitionally aligned with the theory and
opened-occurrence recursors. -/
@[reducible]
def intervalRelations {alpha : Type} (sort : Target.StaticSort) :
    List alpha -> List Target.Relation
  | [] => []
  | _ :: remaining =>
      .inclusion sort :: .inclusion sort ::
        intervalRelations sort remaining

def label {scope : Target.Sig} : PreparedEntry scope -> Nat
  | .type label _ _ => label
  | .capture label _ _ => label

def sort {scope : Target.Sig} : PreparedEntry scope -> Target.StaticSort
  | .type _ _ _ => .type
  | .capture _ _ _ => .capture

def member {scope : Target.Sig} : PreparedEntry scope -> MemberName scope
  | .type label name _ => .type label name
  | .capture label name _ => .capture label name

/-- Two directed propositions are retained for every interval occurrence. -/
def relations {scope : Target.Sig} : PreparedEntry scope -> List Target.Relation
  | .type _ _ intervals =>
      intervalRelations .type intervals
  | .capture _ _ intervals =>
      intervalRelations .capture intervals

@[simp]
theorem member_label {scope : Target.Sig} (entry : PreparedEntry scope) :
    entry.member.label = entry.label := by
  cases entry <;> rfl

@[simp]
theorem member_sort {scope : Target.Sig} (entry : PreparedEntry scope) :
    entry.member.sort = entry.sort := by
  cases entry <;> rfl

end PreparedEntry

/-- All names are fixed before `entries` is constructed.  In particular,
every entry bound lives in the same complete symbol scope and may mention any
other member name regardless of entry order. -/
structure PreparedSignature (scope : Target.Sig) where
  symbols : List Target.StaticSort
  entries : List (PreparedEntry (Target.SymbolScope scope symbols))
deriving DecidableEq

namespace PreparedSignature

/-- Concatenate the relation spines of prepared entries in source order. -/
@[reducible]
def entriesRelations {scope : Target.Sig} :
    List (PreparedEntry scope) -> List Target.Relation
  | [] => []
  | entry :: remaining =>
      entry.relations ++ entriesRelations remaining

def relations {scope : Target.Sig} (prepared : PreparedSignature scope) :
    List Target.Relation :=
  entriesRelations prepared.entries

def members {scope : Target.Sig} (prepared : PreparedSignature scope) :
    List (MemberName (Target.SymbolScope scope prepared.symbols)) :=
  prepared.entries.map PreparedEntry.member

end PreparedSignature

/-! ## Emitting a target theory after allocation -/

def appendTheory {scope : Target.Sig}
    {symbols : List Target.StaticSort}
    {leftRelations rightRelations : List Target.Relation}
    (left : Target.Theory scope symbols leftRelations)
    (right : Target.Theory scope symbols rightRelations) :
    Target.Theory scope symbols (leftRelations ++ rightRelations) :=
  match left with
  | .nil => right
  | .cons proposition rest =>
      .cons proposition (appendTheory rest right)

def typeIntervalsTheory {scope : Target.Sig}
    {symbols : List Target.StaticSort}
    (name : Target.BVar (Target.SymbolScope scope symbols) (.symbol .type)) :
    (intervals : List (Source.Interval
      (Target.StaticExpr .type (Target.SymbolScope scope symbols)))) ->
      Target.Theory scope symbols
        (PreparedEntry.intervalRelations .type intervals)
  | [] => .nil
  | interval :: remaining =>
      .cons (.inclusion interval.lower (.type (.tvar name)))
        (.cons (.inclusion (.type (.tvar name)) interval.upper)
          (typeIntervalsTheory name remaining))

def captureIntervalsTheory {scope : Target.Sig}
    {symbols : List Target.StaticSort}
    (name : Target.BVar (Target.SymbolScope scope symbols)
      (.symbol .capture)) :
    (intervals : List (Source.Interval
      (Target.StaticExpr .capture (Target.SymbolScope scope symbols)))) ->
      Target.Theory scope symbols
        (PreparedEntry.intervalRelations .capture intervals)
  | [] => .nil
  | interval :: remaining =>
      .cons (.inclusion interval.lower (.capture (.cvar name)))
        (.cons (.inclusion (.capture (.cvar name)) interval.upper)
          (captureIntervalsTheory name remaining))

def entryTheory {scope : Target.Sig}
    {symbols : List Target.StaticSort}
    (entry : PreparedEntry (Target.SymbolScope scope symbols)) :
    Target.Theory scope symbols entry.relations :=
  match entry with
  | .type _ name intervals => typeIntervalsTheory name intervals
  | .capture _ name intervals => captureIntervalsTheory name intervals

def entriesTheory {scope : Target.Sig}
    {symbols : List Target.StaticSort} :
    (entries : List (PreparedEntry (Target.SymbolScope scope symbols))) ->
      Target.Theory scope symbols
        (PreparedSignature.entriesRelations entries)
  | [] => .nil
  | entry :: remaining =>
      appendTheory (entryTheory entry) (entriesTheory remaining)

/-- A generated names-first target theory is determined by its allocation
table.  Keeping the theory derived prevents constructing an `Encoding` whose
occurrence coordinates describe different propositions from its theory. -/
structure Encoding (scope : Target.Sig) where
  prepared : PreparedSignature scope
deriving DecidableEq

namespace Encoding

/-- The target theory emitted by this encoding's prepared signature. -/
def theory {scope : Target.Sig} (encoding : Encoding scope) :
    Target.Theory scope encoding.prepared.symbols
      encoding.prepared.relations :=
  entriesTheory encoding.prepared.entries

end Encoding

/-- Emit all propositions without allocating or inspecting another name. -/
def encode {scope : Target.Sig} (prepared : PreparedSignature scope) :
    Encoding scope where
  prepared := prepared

/-! ## Occurrence coordinates in the fully opened theory -/

/-- One retained interval after the generated theory has been fully opened.
The constructor records the shared member name, both translated bounds, and
the two exact evidence coordinates exported for that interval. -/
inductive OpenedOccurrence (scope : Target.Sig)
    (symbols : List Target.StaticSort) (relations : List Target.Relation) where
  | type (label : Nat)
      (name : Target.BVar (Target.StaticScope scope symbols relations)
        (.symbol .type))
      (lower upper : Target.StaticExpr .type
        (Target.StaticScope scope symbols relations))
      (lowerEvidence upperEvidence : Target.BVar
        (Target.StaticScope scope symbols relations)
        (.evidence (.inclusion .type))) :
      OpenedOccurrence scope symbols relations
  | capture (label : Nat)
      (name : Target.BVar (Target.StaticScope scope symbols relations)
        (.symbol .capture))
      (lower upper : Target.StaticExpr .capture
        (Target.StaticScope scope symbols relations))
      (lowerEvidence upperEvidence : Target.BVar
        (Target.StaticScope scope symbols relations)
        (.evidence (.inclusion .capture))) :
      OpenedOccurrence scope symbols relations
deriving DecidableEq

namespace OpenedOccurrence

def label {scope : Target.Sig} {symbols : List Target.StaticSort}
    {relations : List Target.Relation} :
    OpenedOccurrence scope symbols relations -> Nat
  | .type label _ _ _ _ _ => label
  | .capture label _ _ _ _ _ => label

def sort {scope : Target.Sig} {symbols : List Target.StaticSort}
    {relations : List Target.Relation} :
    OpenedOccurrence scope symbols relations -> Target.StaticSort
  | .type _ _ _ _ _ _ => .type
  | .capture _ _ _ _ _ _ => .capture

def member {scope : Target.Sig} {symbols : List Target.StaticSort}
    {relations : List Target.Relation} :
    OpenedOccurrence scope symbols relations ->
      MemberName (Target.StaticScope scope symbols relations)
  | .type label name _ _ _ _ => .type label name
  | .capture label name _ _ _ _ => .capture label name

def lowerProposition {scope : Target.Sig}
    {symbols : List Target.StaticSort} {relations : List Target.Relation} :
    (occurrence : OpenedOccurrence scope symbols relations) ->
      Target.Proposition (.inclusion occurrence.sort)
        (Target.StaticScope scope symbols relations)
  | .type _ name lower _ _ _ =>
      .inclusion lower (.type (.tvar name))
  | .capture _ name lower _ _ _ =>
      .inclusion lower (.capture (.cvar name))

def upperProposition {scope : Target.Sig}
    {symbols : List Target.StaticSort} {relations : List Target.Relation} :
    (occurrence : OpenedOccurrence scope symbols relations) ->
      Target.Proposition (.inclusion occurrence.sort)
        (Target.StaticScope scope symbols relations)
  | .type _ name _ upper _ _ =>
      .inclusion (.type (.tvar name)) upper
  | .capture _ name _ upper _ _ =>
      .inclusion (.capture (.cvar name)) upper

def lowerEvidence {scope : Target.Sig}
    {symbols : List Target.StaticSort} {relations : List Target.Relation} :
    (occurrence : OpenedOccurrence scope symbols relations) ->
      Target.BVar (Target.StaticScope scope symbols relations)
        (.evidence (.inclusion occurrence.sort))
  | .type _ _ _ _ evidence _ => evidence
  | .capture _ _ _ _ evidence _ => evidence

def upperEvidence {scope : Target.Sig}
    {symbols : List Target.StaticSort} {relations : List Target.Relation} :
    (occurrence : OpenedOccurrence scope symbols relations) ->
      Target.BVar (Target.StaticScope scope symbols relations)
        (.evidence (.inclusion occurrence.sort))
  | .type _ _ _ _ _ evidence => evidence
  | .capture _ _ _ _ _ evidence => evidence

/-- Both evidence coordinates look up the exact propositions carried by this
opened interval. -/
def EvidenceMatches {scope : Target.Sig}
    {symbols : List Target.StaticSort} {relations : List Target.Relation}
    (context : ManySortedFC.Ctx
      (Target.StaticScope scope symbols relations))
    (occurrence : OpenedOccurrence scope symbols relations) : Prop :=
  context.lookup occurrence.lowerEvidence =
      .evidence occurrence.lowerProposition ∧
    context.lookup occurrence.upperEvidence =
      .evidence occurrence.upperProposition

@[simp]
theorem member_label {scope : Target.Sig}
    {symbols : List Target.StaticSort} {relations : List Target.Relation}
    (occurrence : OpenedOccurrence scope symbols relations) :
    occurrence.member.label = occurrence.label := by
  cases occurrence <;> rfl

@[simp]
theorem member_sort {scope : Target.Sig}
    {symbols : List Target.StaticSort} {relations : List Target.Relation}
    (occurrence : OpenedOccurrence scope symbols relations) :
    occurrence.member.sort = occurrence.sort := by
  cases occurrence <;> rfl

/-- Install two newer evidence binders while retaining every coordinate of an
already-opened older occurrence. -/
def weakenTwo {scope : Target.Sig}
    {symbols : List Target.StaticSort} {relations : List Target.Relation}
    (newest older : Target.Relation)
    (occurrence : OpenedOccurrence scope symbols relations) :
    OpenedOccurrence scope symbols (newest :: older :: relations) :=
  let rho := ManySortedFC.Rename.weakenMany
    (Target.StaticScope scope symbols relations)
    [.evidence newest, .evidence older]
  match occurrence with
  | .type label name lower upper lowerEvidence upperEvidence =>
      .type label (rho.var name) (lower.rename rho) (upper.rename rho)
        (rho.var lowerEvidence) (rho.var upperEvidence)
  | .capture label name lower upper lowerEvidence upperEvidence =>
      .capture label (rho.var name) (lower.rename rho) (upper.rename rho)
        (rho.var lowerEvidence) (rho.var upperEvidence)

/-- Opening two newer assumptions preserves the exact evidence lookups of an
older retained occurrence. -/
theorem weakenTwo_evidenceMatches {scope : Target.Sig}
    {symbols : List Target.StaticSort} {relations : List Target.Relation}
    {newest older : Target.Relation}
    (context : ManySortedFC.Ctx
      (Target.StaticScope scope symbols relations))
    (olderProposition : Target.Proposition older
      (Target.StaticScope scope symbols relations))
    (newestProposition : Target.Proposition newest
      ((Target.StaticScope scope symbols relations) ▹ .evidence older))
    (occurrence : OpenedOccurrence scope symbols relations)
    (validity : occurrence.EvidenceMatches context) :
    (occurrence.weakenTwo newest older).EvidenceMatches
      (show ManySortedFC.Ctx
          (Target.StaticScope scope symbols (newest :: older :: relations))
        from (context.extendEvidence olderProposition).extendEvidence
          newestProposition) := by
  cases occurrence with
  | type label name lower upper lowerEvidence upperEvidence =>
      rcases validity with ⟨lowerValid, upperValid⟩
      simp only [OpenedOccurrence.lowerEvidence,
        OpenedOccurrence.upperEvidence, OpenedOccurrence.lowerProposition,
        OpenedOccurrence.upperProposition] at lowerValid upperValid
      constructor
      · change
          ((context.extendEvidence olderProposition).extendEvidence
            newestProposition).lookup
              (.there (.there lowerEvidence)) = _
        simp only [ManySortedFC.Ctx.extendEvidence]
        rw [ManySortedFC.Ctx.lookup_there,
          ManySortedFC.Ctx.lookup_there]
        have transported := congrArg
          (fun binding =>
            (binding.weaken (newest := .evidence older)).weaken
              (newest := .evidence newest)) lowerValid
        exact transported.trans (by
          simp [weakenTwo, lowerProposition, ManySortedFC.Binding.weaken,
            ManySortedFC.Binding.rename,
            ManySortedFC.Proposition.rename, ManySortedFC.StaticExpr.rename,
            ManySortedFC.Ty.rename,
            ManySortedFC.Rename.weakenMany, ManySortedFC.Rename.comp,
            ManySortedFC.Rename.succ]
          rfl)
      · change
          ((context.extendEvidence olderProposition).extendEvidence
            newestProposition).lookup
              (.there (.there upperEvidence)) = _
        simp only [ManySortedFC.Ctx.extendEvidence]
        rw [ManySortedFC.Ctx.lookup_there,
          ManySortedFC.Ctx.lookup_there]
        have transported := congrArg
          (fun binding =>
            (binding.weaken (newest := .evidence older)).weaken
              (newest := .evidence newest)) upperValid
        exact transported.trans (by
          simp [weakenTwo, upperProposition, ManySortedFC.Binding.weaken,
            ManySortedFC.Binding.rename,
            ManySortedFC.Proposition.rename, ManySortedFC.StaticExpr.rename,
            ManySortedFC.Ty.rename,
            ManySortedFC.Rename.weakenMany, ManySortedFC.Rename.comp,
            ManySortedFC.Rename.succ]
          rfl)
  | capture label name lower upper lowerEvidence upperEvidence =>
      rcases validity with ⟨lowerValid, upperValid⟩
      simp only [OpenedOccurrence.lowerEvidence,
        OpenedOccurrence.upperEvidence, OpenedOccurrence.lowerProposition,
        OpenedOccurrence.upperProposition] at lowerValid upperValid
      constructor
      · change
          ((context.extendEvidence olderProposition).extendEvidence
            newestProposition).lookup
              (.there (.there lowerEvidence)) = _
        simp only [ManySortedFC.Ctx.extendEvidence]
        rw [ManySortedFC.Ctx.lookup_there,
          ManySortedFC.Ctx.lookup_there]
        have transported := congrArg
          (fun binding =>
            (binding.weaken (newest := .evidence older)).weaken
              (newest := .evidence newest)) lowerValid
        exact transported.trans (by
          simp [weakenTwo, lowerProposition, ManySortedFC.Binding.weaken,
            ManySortedFC.Binding.rename,
            ManySortedFC.Proposition.rename, ManySortedFC.StaticExpr.rename,
            ManySortedFC.Capture.rename,
            ManySortedFC.Rename.weakenMany, ManySortedFC.Rename.comp,
            ManySortedFC.Rename.succ]
          rfl)
      · change
          ((context.extendEvidence olderProposition).extendEvidence
            newestProposition).lookup
              (.there (.there upperEvidence)) = _
        simp only [ManySortedFC.Ctx.extendEvidence]
        rw [ManySortedFC.Ctx.lookup_there,
          ManySortedFC.Ctx.lookup_there]
        have transported := congrArg
          (fun binding =>
            (binding.weaken (newest := .evidence older)).weaken
              (newest := .evidence newest)) upperValid
        exact transported.trans (by
          simp [weakenTwo, upperProposition, ManySortedFC.Binding.weaken,
            ManySortedFC.Binding.rename,
            ManySortedFC.Proposition.rename, ManySortedFC.StaticExpr.rename,
            ManySortedFC.Capture.rename,
            ManySortedFC.Rename.weakenMany, ManySortedFC.Rename.comp,
            ManySortedFC.Rename.succ]
          rfl)

end OpenedOccurrence

def openTypeIntervals {scope : Target.Sig}
    {symbols : List Target.StaticSort} (label : Nat)
    (name : Target.BVar (Target.SymbolScope scope symbols) (.symbol .type)) :
    (intervals : List (Source.Interval
      (Target.StaticExpr .type (Target.SymbolScope scope symbols)))) ->
    (tailRelations : List Target.Relation) ->
    List (OpenedOccurrence scope symbols tailRelations) ->
    List (OpenedOccurrence scope symbols
      (PreparedEntry.intervalRelations .type intervals ++ tailRelations))
  | [], _, tail => tail
  | interval :: remaining, tailRelations, tail =>
      let older := openTypeIntervals label name remaining tailRelations tail
      let remainingRelations : List Target.Relation :=
        PreparedEntry.intervalRelations .type remaining
      let fullRelations : List Target.Relation :=
        ManySortedFC.Relation.inclusion .type ::
          ManySortedFC.Relation.inclusion .type ::
          (remainingRelations ++ tailRelations)
      let rho := ManySortedFC.Rename.weakenMany
        (Target.SymbolScope scope symbols)
        (ManySortedFC.evidenceKinds fullRelations)
      let current : OpenedOccurrence scope symbols fullRelations :=
        .type label (rho.var name) (interval.lower.rename rho)
          (interval.upper.rename rho) .here (.there .here)
      current :: older.map fun occurrence =>
        occurrence.weakenTwo
          (ManySortedFC.Relation.inclusion .type)
          (ManySortedFC.Relation.inclusion .type)

def openCaptureIntervals {scope : Target.Sig}
    {symbols : List Target.StaticSort} (label : Nat)
    (name : Target.BVar (Target.SymbolScope scope symbols)
      (.symbol .capture)) :
    (intervals : List (Source.Interval
      (Target.StaticExpr .capture (Target.SymbolScope scope symbols)))) ->
    (tailRelations : List Target.Relation) ->
    List (OpenedOccurrence scope symbols tailRelations) ->
    List (OpenedOccurrence scope symbols
      (PreparedEntry.intervalRelations .capture intervals ++ tailRelations))
  | [], _, tail => tail
  | interval :: remaining, tailRelations, tail =>
      let older := openCaptureIntervals label name remaining tailRelations tail
      let remainingRelations : List Target.Relation :=
        PreparedEntry.intervalRelations .capture remaining
      let fullRelations : List Target.Relation :=
        ManySortedFC.Relation.inclusion .capture ::
          ManySortedFC.Relation.inclusion .capture ::
          (remainingRelations ++ tailRelations)
      let rho := ManySortedFC.Rename.weakenMany
        (Target.SymbolScope scope symbols)
        (ManySortedFC.evidenceKinds fullRelations)
      let current : OpenedOccurrence scope symbols fullRelations :=
        .capture label (rho.var name) (interval.lower.rename rho)
          (interval.upper.rename rho) .here (.there .here)
      current :: older.map fun occurrence =>
        occurrence.weakenTwo
          (ManySortedFC.Relation.inclusion .capture)
          (ManySortedFC.Relation.inclusion .capture)

def openEntries {scope : Target.Sig}
    {symbols : List Target.StaticSort} :
    (entries : List (PreparedEntry (Target.SymbolScope scope symbols))) ->
    List (OpenedOccurrence scope symbols
      (PreparedSignature.entriesRelations entries))
  | [] => []
  | .type label name intervals :: remaining =>
      openTypeIntervals label name intervals
        (PreparedSignature.entriesRelations remaining) (openEntries remaining)
  | .capture label name intervals :: remaining =>
      openCaptureIntervals label name intervals
        (PreparedSignature.entriesRelations remaining) (openEntries remaining)

namespace Encoding

def symbols {scope : Target.Sig} (encoding : Encoding scope) :
    List Target.StaticSort :=
  encoding.prepared.symbols

def relations {scope : Target.Sig} (encoding : Encoding scope) :
    List Target.Relation :=
  encoding.prepared.relations

/-- The same member coordinates after every generated evidence binder has
been opened. -/
def openedMembers {scope : Target.Sig} (encoding : Encoding scope) :
    List (MemberName
      (Target.StaticScope scope encoding.symbols encoding.relations)) :=
  encoding.prepared.members.map fun member =>
    member.rename
      (ManySortedFC.Rename.weakenMany
        (Target.SymbolScope scope encoding.symbols)
        (ManySortedFC.evidenceKinds encoding.relations))

/-- One coordinate record per retained interval occurrence, in source
occurrence order.  Repeated intervals remain repeated records. -/
def openedOccurrences {scope : Target.Sig} (encoding : Encoding scope) :
    List (OpenedOccurrence scope encoding.symbols encoding.relations) :=
  openEntries encoding.prepared.entries

end Encoding

end DOTCaptureToManySortedFC.Intersections.Encoding
