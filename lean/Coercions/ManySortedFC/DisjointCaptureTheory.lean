import Coercions.ManySortedFC.ModalConfinement
import Coercions.ManySortedFC.TheoryMapMetatheory
import Coercions.ManySortedFC.TheoryModelChecker

/-!
# Canonical pairwise-disjoint capture theories

`DisjointCaptureTheory.theory n` binds `n` capture symbols first and
then records one `Disjoint` proposition for every pair of distinct symbol
positions.  The construction is purely static: even for two or more symbols,
it only requires mutual `Disjoint` certificates for the supplied capture
denotations.  It does not allocate resources, grant consume or kill authority,
establish ownership, or prove disjointness from ambient captures.  For `n = 0`
and `n = 1`, the pairwise condition is vacuous.

The final section lifts modal confinement pointwise to checked models of
these theories.  Every supplied `Disjoint` certificate has an exact origin
outside the enclosing modal proof block; lock-generated `Separate` evidence
cannot be used to manufacture it.  Nested blocks can be handled by repeated
application.
-/

namespace ManySortedFC

/-- Canonical relation shape for pairwise disjointness among `count`
positions.  The newest position is paired with every older position before
the older pairs are emitted recursively. -/
def disjointCaptureRelations : Nat -> List Relation
  | 0 => []
  | count + 1 => List.replicate count .disjoint ++
      disjointCaptureRelations count

@[simp]
theorem disjointCaptureRelations_length (count : Nat) :
    (disjointCaptureRelations count).length = separationPairCount count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp [disjointCaptureRelations, separationPairCount, induction]

theorem disjointCaptureRelations_only_disjoint {count : Nat}
    {relation : Relation}
    (membership : relation ∈ disjointCaptureRelations count) :
    relation = .disjoint := by
  induction count with
  | zero => simp [disjointCaptureRelations] at membership
  | succ count induction =>
      simp only [disjointCaptureRelations, List.mem_append,
        List.mem_replicate] at membership
      cases membership with
      | inl replicated => exact replicated.2
      | inr older => exact induction older

namespace DisjointCaptureContext

/-- Disjointness obligations between one new capture and every older
position in a fixed, already bound symbol block. -/
def against {scope : Sig} {symbols : List StaticSort}
    (head : Capture (SymbolScope scope symbols)) :
    {count : Nat} -> SeparationContext count (SymbolScope scope symbols) ->
      Theory scope symbols (List.replicate count .disjoint)
  | 0, .nil => .nil
  | _ + 1, .cons rest capture =>
      .cons (.disjoint head capture) (against head rest)

/-- Canonical `i < j` expansion of all pairs in a capture-position list. -/
def toTheory {scope : Sig} {symbols : List StaticSort} :
    {count : Nat} -> SeparationContext count (SymbolScope scope symbols) ->
      Theory scope symbols (disjointCaptureRelations count)
  | 0, .nil => .nil
  | _ + 1, .cons rest capture =>
      Theory.append (against capture rest) (toTheory rest)

end DisjointCaptureContext

namespace SeparationPosition

/-- Every canonical ordered pair occurs as its exact `Disjoint` proposition
in the pairwise-disjoint theory generated from the same positions. -/
theorem disjoint_covered_by_toTheory {scope : Sig}
    {symbols : List StaticSort} {count : Nat}
    {context : SeparationContext count (SymbolScope scope symbols)}
    {left right : SeparationPosition context}
    (before : Before left right) :
    Theory.Contains (symbols := symbols)
      (.disjoint left.capture right.capture)
      (DisjointCaptureContext.toTheory context) := by
  induction before with
  | @here_there count rest capture older =>
      apply Theory.Contains.append_left
      induction older with
      | here => exact .here
      | there older induction => exact .there induction
  | @there count rest capture left right before induction =>
      exact Theory.Contains.append_right
        (DisjointCaptureContext.against capture rest) induction

/-- Any two distinct positions occur in one of the two canonical
orientations. -/
theorem distinct_disjoint_covered_by_toTheory {scope : Sig}
    {symbols : List StaticSort} {count : Nat}
    {context : SeparationContext count (SymbolScope scope symbols)}
    (left right : SeparationPosition context) (distinct : left ≠ right) :
    Theory.Contains (symbols := symbols)
        (.disjoint left.capture right.capture)
        (DisjointCaptureContext.toTheory context) ∨
      Theory.Contains (symbols := symbols)
        (.disjoint right.capture left.capture)
        (DisjointCaptureContext.toTheory context) := by
  cases distinct_comparable left right distinct with
  | inl before => exact .inl (disjoint_covered_by_toTheory before)
  | inr before => exact .inr (disjoint_covered_by_toTheory before)

end SeparationPosition

namespace DisjointCaptureTheory

/-- The names-first symbol block contains exactly `count` capture symbols. -/
def symbols (count : Nat) : List StaticSort :=
  List.replicate count .capture

@[simp]
theorem symbols_length (count : Nat) : (symbols count).length = count := by
  simp [symbols]

theorem symbols_only_capture {count : Nat} {sort : StaticSort}
    (membership : sort ∈ symbols count) : sort = .capture := by
  have shaped : count ≠ 0 ∧ sort = .capture := by
    simpa [symbols] using membership
  exact shaped.2

/-- The canonical list of the capture symbols introduced by `symbols`.
The newest symbol is the newest list position. -/
def captures (scope : Sig) : (count : Nat) ->
    SeparationContext count (SymbolScope scope (symbols count))
  | 0 => .nil
  | count + 1 =>
      .cons ((captures scope count).rename Rename.succ) (.cvar .here)

/-- The canonical names-first theory with one pairwise `Disjoint`
constraint for every two distinct capture-symbol positions. -/
def theory (scope : Sig) (count : Nat) :
    Theory scope (symbols count) (disjointCaptureRelations count) :=
  DisjointCaptureContext.toTheory (captures scope count)

/-- Exact coverage for an ordered pair of generated capture symbols. -/
theorem pair_covered {scope : Sig} {count : Nat}
    {left right : SeparationPosition (captures scope count)}
    (before : SeparationPosition.Before left right) :
    Theory.Contains (symbols := symbols count)
      (.disjoint left.capture right.capture) (theory scope count) :=
  SeparationPosition.disjoint_covered_by_toTheory before

/-- Every two distinct generated positions have an exact proposition in the
canonical orientation. -/
theorem distinct_pair_covered {scope : Sig} {count : Nat}
    (left right : SeparationPosition (captures scope count))
    (distinct : left ≠ right) :
    Theory.Contains (symbols := symbols count)
        (.disjoint left.capture right.capture) (theory scope count) ∨
      Theory.Contains (symbols := symbols count)
        (.disjoint right.capture left.capture) (theory scope count) :=
  SeparationPosition.distinct_disjoint_covered_by_toTheory left right
    distinct

/-- Exact theory membership determines some intrinsically related constraint
reference.  This is stated propositionally because `Theory.Contains` itself
lives in `Prop`. -/
theorem existsConstraintRef {scope : Sig} {symbols : List StaticSort}
    {relation : Relation}
    {proposition : Proposition relation (SymbolScope scope symbols)}
    {relations : List Relation} {theory : Theory scope symbols relations}
    (membership : Theory.Contains proposition theory) :
    ∃ reference : ConstraintRef relations relation,
      theory.propositionAt reference = proposition := by
  induction membership with
  | here => exact ⟨.here, rfl⟩
  | there membership induction =>
      obtain ⟨reference, equality⟩ := induction
      exact ⟨.there reference, equality⟩

/-- A proof-only reference selected classically from exact theory membership.
Compiler code that needs executable indices should construct them directly
from the positional pair derivation instead. -/
noncomputable def proofConstraintRef {scope : Sig}
    {symbols : List StaticSort} {relation : Relation}
    {proposition : Proposition relation (SymbolScope scope symbols)}
    {relations : List Relation} {theory : Theory scope symbols relations}
    (membership : Theory.Contains proposition theory) :
    ConstraintRef relations relation :=
  Classical.choose (existsConstraintRef membership)

@[simp]
theorem propositionAt_proofConstraintRef {scope : Sig}
    {symbols : List StaticSort} {relation : Relation}
    {proposition : Proposition relation (SymbolScope scope symbols)}
    {relations : List Relation} {theory : Theory scope symbols relations}
    (membership : Theory.Contains proposition theory) :
    theory.propositionAt (proofConstraintRef membership) = proposition := by
  exact Classical.choose_spec (existsConstraintRef membership)

/-- Pointwise modal provenance for an arbitrary declarative model
constraint.  The relation index is intrinsically `Disjoint`, so M14's exact
origin theorem applies without any conversion from `Separate`. -/
noncomputable def modelConstraintModalOrigin {scope : Sig}
    {context : Ctx scope} {separationCount : Nat}
    {modes : List CaptureMode}
    {requirements : ModalContext separationCount modes scope}
    {count : Nat}
    (model : Theory.Model (context.extendModal requirements)
      (theory (ModalScope scope separationCount modes) count))
    (reference : ConstraintRef (disjointCaptureRelations count) .disjoint) :
    Evidence.Proves.DisjointModalOrigin context requirements
      (model.evidence.lookup reference)
      (((theory (ModalScope scope separationCount modes) count).propositionAt
        reference).instantiateSymbols model.symbols) :=
  (model.satisfies.constraintAt reference).disjoint_modalOrigin

/-- The executable model checker exposes the same pointwise modal-origin
theorem through its packaged satisfaction derivation. -/
noncomputable def checkedModelConstraintModalOrigin {scope : Sig}
    {context : Ctx scope} {separationCount : Nat}
    {modes : List CaptureMode}
    {requirements : ModalContext separationCount modes scope}
    {count : Nat}
    (model : Theory.CheckedModel (context.extendModal requirements)
      (theory (ModalScope scope separationCount modes) count))
    (reference : ConstraintRef (disjointCaptureRelations count) .disjoint) :
    Evidence.Proves.DisjointModalOrigin context requirements
      (model.evidence.lookup reference)
      (((theory (ModalScope scope separationCount modes) count).propositionAt
        reference).instantiateSymbols model.symbols) :=
  (model.satisfies.constraintAt reference).disjoint_modalOrigin

/-- Pair-indexed form of the checked-model result.  It exposes the precise
generated proposition before simultaneous model instantiation. -/
noncomputable def checkedModelPairModalOrigin {scope : Sig}
    {context : Ctx scope} {separationCount : Nat}
    {modes : List CaptureMode}
    {requirements : ModalContext separationCount modes scope}
    {count : Nat}
    (model : Theory.CheckedModel (context.extendModal requirements)
      (theory (ModalScope scope separationCount modes) count))
    {left right : SeparationPosition
      (captures (ModalScope scope separationCount modes) count)}
    (before : SeparationPosition.Before left right) :
    Evidence.Proves.DisjointModalOrigin context requirements
      (model.evidence.lookup (proofConstraintRef (pair_covered before)))
      ((Proposition.disjoint left.capture right.capture).instantiateSymbols
        model.symbols) := by
  have typing := model.satisfies.constraintAt
    (proofConstraintRef (pair_covered before))
  rw [propositionAt_proofConstraintRef] at typing
  exact typing.disjoint_modalOrigin

end DisjointCaptureTheory

end ManySortedFC
