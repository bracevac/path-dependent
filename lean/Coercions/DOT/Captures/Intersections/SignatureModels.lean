import Coercions.DOT.Captures.Intersections.SignatureMetatheory

/-!
# Models of normalized signature conjunction

This semantic layer is deliberately independent of any particular type or
capture order.  One interpretation chooses a single symbol for each
`(sort, label)` and a relation for each sort.  Every retained interval is then
checked against that same chosen symbol.  Signature merge is conjunction for
one shared interpretation.
-/

namespace DOTCapture.Intersections

universe u

/-- A shared many-sorted member assignment and its two inclusion relations. -/
structure Interpretation (Expr : StaticSort -> Type u) where
  symbol : (sort : StaticSort) -> Nat -> Expr sort
  includes : (sort : StaticSort) -> Expr sort -> Expr sort -> Prop

namespace Interpretation

/-- Satisfaction of one primitive interval occurrence. -/
def SatisfiesOccurrence {Expr : StaticSort -> Type u}
    (model : Interpretation Expr) : Occurrence Expr -> Prop
  | .type label interval =>
      model.includes .type interval.lower (model.symbol .type label) ∧
        model.includes .type (model.symbol .type label) interval.upper
  | .capture label interval =>
      model.includes .capture interval.lower (model.symbol .capture label) ∧
        model.includes .capture (model.symbol .capture label) interval.upper

/-- Every primitive constraint in a signature holds under one shared member
assignment. -/
def Models {Expr : StaticSort -> Type u} (model : Interpretation Expr)
    (signature : Signature Expr) : Prop :=
  ∀ occurrence, occurrence ∈ signature.occurrences ->
    model.SatisfiesOccurrence occurrence

/-- Successful merge denotes conjunction over the same interpretation. -/
theorem models_merge_iff {Expr : StaticSort -> Type u}
    (model : Interpretation Expr) (left right merged : Signature Expr)
    (success : left.merge? right = .ok merged) :
    model.Models merged ↔ model.Models left ∧ model.Models right := by
  have retained := Signature.merge?_occurrences left right merged success
  constructor
  · intro models
    constructor
    · intro occurrence membership
      apply models occurrence
      apply retained.mem_iff.mpr
      exact List.mem_append_left _ membership
    · intro occurrence membership
      apply models occurrence
      apply retained.mem_iff.mpr
      exact List.mem_append_right _ membership
  · rintro ⟨modelsLeft, modelsRight⟩ occurrence membership
    have sourceMembership :
        occurrence ∈ left.occurrences ++ right.occurrences :=
      retained.mem_iff.mp membership
    rcases List.mem_append.mp sourceMembership with inLeft | inRight
    · exact modelsLeft occurrence inLeft
    · exact modelsRight occurrence inRight

end Interpretation

namespace InterpretationExamples

/-- A two-point type universe is enough to witness two individually
realizable exact views whose conjunction has no shared model. -/
def BoolExpr : StaticSort -> Type
  | .type => Bool
  | .capture => Unit

def exactTrue : Signature BoolExpr :=
  Signature.singletonType 0 true true

def exactFalse : Signature BoolExpr :=
  Signature.singletonType 0 false false

def incompatibleMerge : Signature BoolExpr :=
  { entries := [.type 0
      [⟨true, true⟩, ⟨false, false⟩]] }

theorem exact_views_merge :
    exactTrue.merge? exactFalse = .ok incompatibleMerge := by
  rfl

def equalityModel (chosen : Bool) : Interpretation BoolExpr where
  symbol := fun
    | .type => fun _ => chosen
    | .capture => fun _ => ()
  includes := fun
    | .type => Eq
    | .capture => Eq

theorem exactTrue_realizable : (equalityModel true).Models exactTrue := by
  intro occurrence membership
  have occurrenceEq : occurrence = .type 0 ⟨true, true⟩ := by
    simpa [exactTrue, Signature.singletonType, Signature.occurrences,
      Entry.occurrences] using membership
  subst occurrence
  simp [Interpretation.SatisfiesOccurrence, equalityModel]

theorem exactFalse_realizable : (equalityModel false).Models exactFalse := by
  intro occurrence membership
  have occurrenceEq : occurrence = .type 0 ⟨false, false⟩ := by
    simpa [exactFalse, Signature.singletonType, Signature.occurrences,
      Entry.occurrences] using membership
  subst occurrence
  simp [Interpretation.SatisfiesOccurrence, equalityModel]

/-- The merge remains a well-formed theory, but no single shared Boolean name
can equal both endpoints. -/
theorem incompatibleMerge_unrealizable :
    ¬ ∃ chosen : Bool, (equalityModel chosen).Models incompatibleMerge := by
  rintro ⟨chosen, models⟩
  have trueOccurrence := models
    (.type 0 ⟨true, true⟩) (by
      simp [incompatibleMerge, Signature.occurrences, Entry.occurrences])
  have falseOccurrence := models
    (.type 0 ⟨false, false⟩) (by
      simp [incompatibleMerge, Signature.occurrences, Entry.occurrences])
  cases chosen <;> simp [Interpretation.SatisfiesOccurrence, equalityModel] at trueOccurrence falseOccurrence

end InterpretationExamples

end DOTCapture.Intersections
