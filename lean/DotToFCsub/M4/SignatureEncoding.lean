import DotFCI
import FCsub

/-!
# Milestone 4 signature encoding

This module is the deliberately small boundary between normalized `DotFCI`
member signatures and the standalone FCsub kernel.  Collection has already
identified one entry per source label.  Encoding therefore allocates exactly
one simultaneous FCsub name per entry, and only afterwards emits the two
directed constraints contributed by each interval occurrence.

The current vertical slice accepts closed `top`/`bot` bounds.  Keeping that
test executable makes the unsupported-bound boundary explicit while leaving
the names-first telescope representation usable by later translations.
-/

namespace DotToFCsub.M4

namespace SignatureEncoding

open DotFCI.Source

/-- Translate the closed bounds supported by the first M4 vertical slice. -/
def closedBound? {scope : FCsub.Sig} :
    DotFCI.Source.Ty [] → Option (FCsub.Ty scope)
  | .top => some .top
  | .bot => some .bot
  | .all _ _ => none
  | .member _ _ _ => none
  | .sel path _ => nomatch path
  | .inter _ _ => none

/-- Emit the two directed constraints of every occurrence of one member.
The member name already exists in the complete simultaneous name block. -/
def intervalConstraints? {names : Nat}
    (name : FCsub.BVar (FCsub.TypeScope [] names) .type) :
    List (Interval []) →
      Option (List (FCsub.Proposition (FCsub.TypeScope [] names)))
  | [] => some []
  | interval :: remaining => do
      let lower : FCsub.Ty (FCsub.TypeScope [] names) ←
        closedBound? interval.lower
      let upper : FCsub.Ty (FCsub.TypeScope [] names) ←
        closedBound? interval.upper
      let tail ← intervalConstraints? name remaining
      pure (.inclusion lower (.tvar name) ::
        .inclusion (.tvar name) upper :: tail)

/-- Encode an entry list after allocating a name for every entry.  The head
entry owns the newest name; constraints for the tail are weakened below it.
No constraint binder is introduced while this function runs. -/
def entryConstraints? : (entries : List (SignatureEntry [])) →
    Option (List
      (FCsub.Proposition (FCsub.TypeScope [] entries.length)))
  | [] => some []
  | entry :: remaining => do
      let current ← intervalConstraints? (names := remaining.length + 1)
        (FCsub.BVar.here :
          FCsub.BVar (FCsub.TypeScope [] (remaining.length + 1)) .type)
        entry.intervals
      let tail ← entryConstraints? remaining
      let liftedTail : List
          (FCsub.Proposition
            (FCsub.TypeScope [] (remaining.length + 1))) :=
        tail.map fun proposition =>
          proposition.rename
            (FCsub.Rename.succ (kind := .type))
      pure (current ++ liftedTail)

/-- Turn a newest-first proposition list into the intrinsically indexed
FCsub telescope with the same `get`/`toList` order. -/
def telescopeOfList {scope : FCsub.Sig} {names : Nat} :
    (propositions : List (FCsub.Proposition (FCsub.TypeScope scope names))) →
      FCsub.Telescope scope names propositions.length
  | [] => .nil
  | proposition :: remaining =>
      .snoc (telescopeOfList remaining) proposition

@[simp]
theorem telescopeOfList_toList {scope : FCsub.Sig} {names : Nat}
    (propositions : List
      (FCsub.Proposition (FCsub.TypeScope scope names))) :
    (telescopeOfList propositions).toList = propositions := by
  induction propositions with
  | nil => rfl
  | cons proposition remaining induction =>
      simp [telescopeOfList, FCsub.Telescope.toList, induction]

/-! ## Scope-generic closed encoding -/

/-- The top/bottom bound check, generalized over both source and target
ambient scopes.  The target scope is irrelevant to success, but fixes the
intrinsic scope of the translated bound. -/
def closedBoundAt? {sourceScope : DotFC.Sig} {targetScope : FCsub.Sig} :
    DotFCI.Source.Ty sourceScope → Option (FCsub.Ty targetScope)
  | .top => some .top
  | .bot => some .bot
  | .all _ _ => none
  | .member _ _ _ => none
  | .sel _ _ => none
  | .inter _ _ => none

/-- Two directed evidence binders are emitted for every interval occurrence. -/
def intervalConstraintCount {sourceScope : DotFC.Sig}
    (intervals : List (Interval sourceScope)) : Nat :=
  2 * intervals.length

/-- Constraint arity in the same entry order as the names-first encoder. -/
def signatureConstraintCount {sourceScope : DotFC.Sig} :
    List (SignatureEntry sourceScope) → Nat
  | [] => 0
  | entry :: remaining =>
      signatureConstraintCount remaining +
        intervalConstraintCount entry.intervals

/-- Encode one entry's intervals in a scope where every signature name is
already allocated.  Newest-first constraint indices are lower, upper, then
the remaining occurrences. -/
def intervalTelescopeAt? {sourceScope : DotFC.Sig}
    {targetScope : FCsub.Sig} {names : Nat}
    (name : FCsub.BVar (FCsub.TypeScope targetScope names) .type) :
    (intervals : List (Interval sourceScope)) →
      Option (FCsub.Telescope targetScope names
        (intervalConstraintCount intervals))
  | [] => some .nil
  | interval :: remaining => do
      let tail ← intervalTelescopeAt? name remaining
      let lower : FCsub.Ty (FCsub.TypeScope targetScope names) ←
        closedBoundAt? interval.lower
      let upper : FCsub.Ty (FCsub.TypeScope targetScope names) ←
        closedBoundAt? interval.upper
      pure (.snoc
        (.snoc tail (.inclusion (.tvar name) upper))
        (.inclusion lower (.tvar name)))

/-- Scope-generic names-first compilation with an exact, source-computable
constraint arity. -/
def signatureTelescopeAt? {sourceScope : DotFC.Sig}
    {targetScope : FCsub.Sig} :
    (entries : List (SignatureEntry sourceScope)) →
      Option (FCsub.Telescope targetScope entries.length
        (signatureConstraintCount entries))
  | [] => some .nil
  | entry :: remaining => do
      let tail ← signatureTelescopeAt?
        (targetScope := targetScope) remaining
      let current ← intervalTelescopeAt?
        (sourceScope := sourceScope) (targetScope := targetScope)
        (names := remaining.length + 1)
        (FCsub.BVar.here : FCsub.BVar
          (FCsub.TypeScope targetScope (remaining.length + 1)) .type)
        entry.intervals
      let liftedTail : FCsub.Telescope targetScope (remaining.length + 1)
          (signatureConstraintCount remaining) :=
        tail.reindexNames (FCsub.Rename.succ (kind := .type))
      pure (liftedTail.append current)

/-- A generic encoding has arities determined entirely by the normalized
source signature; only its telescope depends on the target ambient scope. -/
structure EncodingAt (targetScope : FCsub.Sig)
    (signature : Signature sourceScope) where
  telescope : FCsub.Telescope targetScope signature.entries.length
    (signatureConstraintCount signature.entries)
deriving DecidableEq

namespace EncodingAt

def names {targetScope : FCsub.Sig} {signature : Signature sourceScope}
    (_ : EncodingAt targetScope signature) : Nat := signature.entries.length

def constraints {targetScope : FCsub.Sig}
    {signature : Signature sourceScope} (_ : EncodingAt targetScope signature) :
    Nat := signatureConstraintCount signature.entries

def existsType {targetScope : FCsub.Sig}
    {signature : Signature sourceScope}
    (encoding : EncodingAt targetScope signature) : FCsub.Ty targetScope :=
  .existsT encoding.telescope .one

end EncodingAt

def encodeAt? (targetScope : FCsub.Sig)
    (signature : Signature sourceScope) : Option (EncodingAt targetScope signature) :=
  (signatureTelescopeAt? (targetScope := targetScope) signature.entries).map
    fun telescope => ⟨telescope⟩

/-- Explicit totality certificate for one closed top/bottom signature.  The
chosen encoding remains computational data and `agrees` ties it to the
scope-generic executable compiler. -/
structure ClosedSignature (signature : Signature sourceScope) : Type where
  encoding : (targetScope : FCsub.Sig) → EncodingAt targetScope signature
  agrees : ∀ targetScope,
    encodeAt? targetScope signature = some (encoding targetScope)

/-! ### Allocation metadata -/

/-- Lower/upper evidence positions for one interval in a complete telescope. -/
structure BoundIndex (constraints : Nat) where
  lower : Fin constraints
  upper : Fin constraints
deriving DecidableEq

/-- The target positions owned by one normalized signature entry. -/
structure EntryIndex (names constraints : Nat) where
  label : Name
  name : Fin names
  bounds : List (BoundIndex constraints)
deriving DecidableEq

namespace BoundIndex

/-- Move an older constraint position behind one newly prefixed block. -/
def shiftRight {constraints : Nat} (index : BoundIndex constraints)
    (additional : Nat) : BoundIndex (constraints + additional) where
  lower := ⟨index.lower.val + additional, by omega⟩
  upper := ⟨index.upper.val + additional, by omega⟩

end BoundIndex

namespace EntryIndex

/-- Add one newer name and one newer constraint block. -/
def shift {names constraints : Nat} (index : EntryIndex names constraints)
    (additionalConstraints : Nat) :
    EntryIndex (names + 1) (constraints + additionalConstraints) where
  label := index.label
  name := ⟨index.name.val + 1, by omega⟩
  bounds := index.bounds.map fun bound =>
    bound.shiftRight additionalConstraints

end EntryIndex

/-- Positions of all interval pairs of the newest entry. -/
def intervalIndices {sourceScope : DotFC.Sig}
    (intervals : List (Interval sourceScope)) (olderConstraints : Nat) :
    List (BoundIndex
      (olderConstraints + intervalConstraintCount intervals)) :=
  List.ofFn fun index : Fin intervals.length =>
    { lower := ⟨2 * index.val, by
        unfold intervalConstraintCount
        omega⟩
      upper := ⟨2 * index.val + 1, by
        unfold intervalConstraintCount
        omega⟩ }

@[simp]
theorem intervalIndices_length {sourceScope : DotFC.Sig}
    (intervals : List (Interval sourceScope)) (olderConstraints : Nat) :
    (intervalIndices intervals olderConstraints).length = intervals.length := by
  simp [intervalIndices]

/-- Canonical name and evidence positions for every signature entry. -/
def allocations {sourceScope : DotFC.Sig} :
    (entries : List (SignatureEntry sourceScope)) →
      List (EntryIndex entries.length (signatureConstraintCount entries))
  | [] => []
  | entry :: remaining =>
      let currentConstraints := intervalConstraintCount entry.intervals
      let current : EntryIndex (remaining.length + 1)
          (signatureConstraintCount remaining + currentConstraints) :=
        { label := entry.label
          name := ⟨0, by omega⟩
          bounds := intervalIndices entry.intervals
            (signatureConstraintCount remaining) }
      let older : List (EntryIndex (remaining.length + 1)
          (signatureConstraintCount remaining + currentConstraints)) :=
        (allocations remaining).map fun index =>
          index.shift currentConstraints
      current :: older

@[simp]
theorem allocations_length {sourceScope : DotFC.Sig}
    (entries : List (SignatureEntry sourceScope)) :
    (allocations entries).length = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry remaining induction =>
      simp only [allocations, List.length_cons]
      congr 1
      exact (List.length_map _).trans induction

/-- Executable label lookup in canonical allocation metadata. -/
def allocation? {sourceScope : DotFC.Sig}
    (signature : Signature sourceScope) (label : Name) :
    Option (EntryIndex signature.entries.length
      (signatureConstraintCount signature.entries)) :=
  (allocations signature.entries).find? fun allocation =>
    allocation.label == label

/-- A successful encoding packages the constraint arity with its telescope.
The name arity is not existential: it is definitionally the number of
normalized signature entries. -/
structure Encoding (signature : Signature []) where
  constraints : Nat
  telescope : FCsub.Telescope [] signature.entries.length constraints
deriving DecidableEq

namespace Encoding

/-- Exactly one FCsub name is allocated for each normalized label entry. -/
def names {signature : Signature []} (_ : Encoding signature) : Nat :=
  signature.entries.length

/-- The unit-payload existential interface represented by this signature. -/
def existsType {signature : Signature []} (encoding : Encoding signature) :
    FCsub.Ty [] :=
  .existsT encoding.telescope .one

/-- A generated name before constraint assumptions have been opened. -/
def nameInTypes {signature : Signature []} (encoding : Encoding signature)
    (index : Fin encoding.names) :
    FCsub.BVar (FCsub.TypeScope [] encoding.names) .type :=
  FCsub.BVar.bound encoding.names index

/-- The very same generated name in the complete static package scope. -/
def staticName {signature : Signature []} (encoding : Encoding signature)
    (index : Fin encoding.names) :
    FCsub.BVar
      (FCsub.StaticScope [] encoding.names encoding.constraints) .type :=
  (FCsub.Rename.weakenN (.evidence .inclusion) encoding.constraints).var
    (encoding.nameInTypes index)

/-- Canonical vector of the already allocated names in the opened scope. -/
def boundNames {signature : Signature []} (encoding : Encoding signature) :
    FCsub.TypeArgs
      (FCsub.StaticScope [] encoding.names encoding.constraints)
      encoding.names :=
  FCsub.TypeArgs.boundNames [] encoding.names encoding.constraints

@[simp]
theorem boundNames_get {signature : Signature []}
    (encoding : Encoding signature) (index : Fin encoding.names) :
    encoding.boundNames.get index =
      .tvar (encoding.staticName index) := by
  simp [boundNames, staticName, nameInTypes]

end Encoding

/-- Encode one already-collected signature.  Successful collection supplies
normalization; this function remains total on raw signatures so it can also
serve executable diagnostics. -/
def encode? (signature : Signature []) : Option (Encoding signature) := do
  let propositions ← entryConstraints? signature.entries
  pure ⟨propositions.length, telescopeOfList propositions⟩

/-- The complete two-phase boundary: collect first, then allocate and encode. -/
def collectAndEncode? (type : DotFCI.Source.Ty []) :
    Option (Σ signature : Signature [], Encoding signature) := do
  let signature ← DotFCI.Source.collect? type
  let encoding ← encode? signature
  pure ⟨signature, encoding⟩

theorem Encoding.names_eq {signature : Signature []}
    (encoding : Encoding signature) :
    encoding.names = signature.entries.length := by
  rfl

end SignatureEncoding

end DotToFCsub.M4
