import Coercions.DOT.Captures.ModalIntersections.ObjectJudgments
import Coercions.DOT.Captures.ModalIntersections.Signature
import Coercions.Translation.ManySorted.ModalIntersections.Preparation
import Coercions.Translation.ManySorted.Intersections.EncodingMetatheory
import Coercions.Translation.ManySorted.Intersections.TheoryPermutationCoherence

/-!
# Constraint retention for cumulative object interfaces

This is the source-to-preparation correspondence needed by proof-directed
object evidence compilation.  It is per raw declaration occurrence: label
normalization may reorder and group declarations, but it retains each
interval under the one shared member name allocated for its label.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.ConstraintRetention

open DOTCaptureToManySortedFC.Intersections.Encoding
open DOTCaptureToManySortedFC.ModalIntersections.Preparation

abbrev SourceOccurrence (scope : Preparation.Source.Sig) :=
  DOTCapture.Intersections.Occurrence
    (Preparation.Source.MemberExpr scope)

/-- Flatten the raw intersection tree before label normalization. -/
def rawOccurrences {scope : Preparation.Source.Sig} :
    Preparation.Source.Interface scope -> List (SourceOccurrence scope)
  | .empty => []
  | .typeMember label lower upper =>
      [.type label
        { lower := .type lower
          upper := .type upper }]
  | .captureMember label lower upper =>
      [.capture label
        { lower := .capture lower
          upper := .capture upper }]
  | .classifierMember label lower upper =>
      [.classifier label
        { lower := lower
          upper := upper }]
  | .classifierDisjoint _ _ => []
  | .captureHasKind _ _ => []
  | .inter left right => rawOccurrences left ++ rawOccurrences right

/-- A mixed static constraint contributed by the raw interface.  These are
kept separate from member-interval occurrences because normalization stores
them in the signature's constraint tail rather than in an entry. -/
abbrev SourceConstraint (scope : Preparation.Source.Sig) :=
  DOTCapture.Intersections.Constraint
    (Preparation.Source.MemberExpr scope)

/-- Flatten mixed classifier constraints in their source order.  Unlike
member entries, normalization never sorts or combines this list. -/
def rawConstraints {scope : Preparation.Source.Sig} :
    Preparation.Source.Interface scope -> List (SourceConstraint scope)
  | .empty => []
  | .typeMember _ _ _ => []
  | .captureMember _ _ _ => []
  | .classifierMember _ _ _ => []
  | .classifierDisjoint left right =>
      [.classifierDisjoint left right]
  | .captureHasKind capture classifier =>
      [.captureHasKind (.capture capture) classifier]
  | .inter left right => rawConstraints left ++ rawConstraints right

/-- Unified raw theory occurrence.  Preparation stores the two cases in
different lists, but this view records that mixed constraints are genuine
source occurrences alongside member intervals. -/
inductive SourceTheoryOccurrence (scope : Preparation.Source.Sig) where
  | member (occurrence : SourceOccurrence scope)
  | constraint (occurrence : SourceConstraint scope)

/-- Flatten every member interval and mixed constraint in source-tree order. -/
def rawTheoryOccurrences {scope : Preparation.Source.Sig} :
    Preparation.Source.Interface scope ->
      List (SourceTheoryOccurrence scope)
  | .empty => []
  | .typeMember label lower upper =>
      [.member (.type label { lower := .type lower, upper := .type upper })]
  | .captureMember label lower upper =>
      [.member
        (.capture label { lower := .capture lower, upper := .capture upper })]
  | .classifierMember label lower upper =>
      [.member (.classifier label { lower, upper })]
  | .classifierDisjoint left right =>
      [.constraint (.classifierDisjoint left right)]
  | .captureHasKind capture classifier =>
      [.constraint (.captureHasKind (.capture capture) classifier)]
  | .inter left right =>
      rawTheoryOccurrences left ++ rawTheoryOccurrences right

/-- Type intervals for one label in raw left-to-right source order.  This is
the order used to distinguish even syntactically identical declarations. -/
def rawTypeIntervals {scope : Preparation.Source.Sig} (label : Nat) :
    Preparation.Source.Interface scope ->
      List (Preparation.Source.MemberInterval
        (Preparation.Source.MemberExpr scope .type))
  | .empty => []
  | .typeMember candidate lower upper =>
      if candidate = label then
        [{ lower := .type lower, upper := .type upper }]
      else []
  | .captureMember _ _ _ => []
  | .classifierMember _ _ _ => []
  | .classifierDisjoint _ _ => []
  | .captureHasKind _ _ => []
  | .inter left right =>
      rawTypeIntervals label left ++ rawTypeIntervals label right

/-- Capture intervals for one label in raw left-to-right source order. -/
def rawCaptureIntervals {scope : Preparation.Source.Sig} (label : Nat) :
    Preparation.Source.Interface scope ->
      List (Preparation.Source.MemberInterval
        (Preparation.Source.MemberExpr scope .capture))
  | .empty => []
  | .typeMember _ _ _ => []
  | .captureMember candidate lower upper =>
      if candidate = label then
        [{ lower := .capture lower, upper := .capture upper }]
      else []
  | .classifierMember _ _ _ => []
  | .classifierDisjoint _ _ => []
  | .captureHasKind _ _ => []
  | .inter left right =>
      rawCaptureIntervals label left ++ rawCaptureIntervals label right

/-- Classifier intervals for one label in raw left-to-right source order. -/
def rawClassifierIntervals {scope : Preparation.Source.Sig} (label : Nat) :
    Preparation.Source.Interface scope ->
      List (Preparation.Source.MemberInterval
        (Preparation.Source.MemberExpr scope .classifier))
  | .empty => []
  | .typeMember _ _ _ => []
  | .captureMember _ _ _ => []
  | .classifierMember candidate lower upper =>
      if candidate = label then
        [{ lower := lower, upper := upper }]
      else []
  | .classifierDisjoint _ _ => []
  | .captureHasKind _ _ => []
  | .inter left right =>
      rawClassifierIntervals label left ++ rawClassifierIntervals label right

namespace RawOccurrence

/-- Same-label ordinal selected by a type-occurrence derivation. -/
def typeOrdinal {scope : Preparation.Source.Sig}
    {interface : Preparation.Source.Interface scope}
    {label : Nat} {lower upper : Preparation.Source.Ty scope} :
    interface.HasTypeOccurrence label lower upper -> Nat
  | .here => 0
  | .left occurrence => typeOrdinal occurrence
  | .right (left := left) occurrence =>
      (rawTypeIntervals label left).length + typeOrdinal occurrence

/-- Same-label ordinal selected by a capture-occurrence derivation. -/
def captureOrdinal {scope : Preparation.Source.Sig}
    {interface : Preparation.Source.Interface scope}
    {label : Nat}
    {lower upper : Preparation.Source.Capture scope} :
    interface.HasCaptureOccurrence label lower upper -> Nat
  | .here => 0
  | .left occurrence => captureOrdinal occurrence
  | .right (left := left) occurrence =>
      (rawCaptureIntervals label left).length + captureOrdinal occurrence

/-- Same-label ordinal selected by a classifier-occurrence derivation. -/
def classifierOrdinal {scope : Preparation.Source.Sig}
    {interface : Preparation.Source.Interface scope}
    {label : Nat}
    {lower upper : Preparation.Source.ClassifierExpr scope} :
    interface.HasClassifierOccurrence label lower upper -> Nat
  | .here => 0
  | .left occurrence => classifierOrdinal occurrence
  | .right (left := left) occurrence =>
      (rawClassifierIntervals label left).length +
        classifierOrdinal occurrence

/-- The structural type ordinal retrieves exactly the declaration named by
the proof, including when adjacent declarations have identical endpoints. -/
theorem type_getElem?_ordinal {scope : Preparation.Source.Sig}
    {interface : Preparation.Source.Interface scope}
    {label : Nat} {lower upper : Preparation.Source.Ty scope}
    (occurrence : interface.HasTypeOccurrence label lower upper) :
    (rawTypeIntervals label interface)[typeOrdinal occurrence]? =
      some { lower := .type lower, upper := .type upper } := by
  induction occurrence with
  | here => simp [rawTypeIntervals, typeOrdinal]
  | left occurrence induction =>
      simp only [rawTypeIntervals, typeOrdinal]
      have inBounds := (List.getElem?_eq_some_iff.mp induction).choose
      rw [List.getElem?_append_left inBounds]
      exact induction
  | right occurrence induction =>
      simp only [rawTypeIntervals, typeOrdinal]
      rw [List.getElem?_append_right (Nat.le_add_right _ _)]
      simpa using induction

/-- Capture-sorted counterpart of `type_getElem?_ordinal`. -/
theorem capture_getElem?_ordinal {scope : Preparation.Source.Sig}
    {interface : Preparation.Source.Interface scope}
    {label : Nat}
    {lower upper : Preparation.Source.Capture scope}
    (occurrence : interface.HasCaptureOccurrence label lower upper) :
    (rawCaptureIntervals label interface)[captureOrdinal occurrence]? =
      some { lower := .capture lower, upper := .capture upper } := by
  induction occurrence with
  | here => simp [rawCaptureIntervals, captureOrdinal]
  | left occurrence induction =>
      simp only [rawCaptureIntervals, captureOrdinal]
      have inBounds := (List.getElem?_eq_some_iff.mp induction).choose
      rw [List.getElem?_append_left inBounds]
      exact induction
  | right occurrence induction =>
      simp only [rawCaptureIntervals, captureOrdinal]
      rw [List.getElem?_append_right (Nat.le_add_right _ _)]
      simpa using induction

/-- Classifier-sorted counterpart of `type_getElem?_ordinal`. -/
theorem classifier_getElem?_ordinal {scope : Preparation.Source.Sig}
    {interface : Preparation.Source.Interface scope}
    {label : Nat}
    {lower upper : Preparation.Source.ClassifierExpr scope}
    (occurrence : interface.HasClassifierOccurrence label lower upper) :
    (rawClassifierIntervals label interface)[classifierOrdinal occurrence]? =
      some { lower := lower, upper := upper } := by
  induction occurrence with
  | here => simp [rawClassifierIntervals, classifierOrdinal]
  | left occurrence induction =>
      simp only [rawClassifierIntervals, classifierOrdinal]
      have inBounds := (List.getElem?_eq_some_iff.mp induction).choose
      rw [List.getElem?_append_left inBounds]
      exact induction
  | right occurrence induction =>
      simp only [rawClassifierIntervals, classifierOrdinal]
      rw [List.getElem?_append_right (Nat.le_add_right _ _)]
      simpa using induction

end RawOccurrence

namespace RawConstraintOccurrence

/-- A proof-selected classifier-disjointness declaration is a genuine raw
theory occurrence, not normalization metadata. -/
theorem classifierDisjoint_mem_theory
    {scope : Preparation.Source.Sig}
    {interface : Preparation.Source.Interface scope}
    {left right : Preparation.Source.ClassifierExpr scope}
    (occurrence : interface.HasClassifierDisjointOccurrence left right) :
    SourceTheoryOccurrence.constraint (.classifierDisjoint left right) ∈
      rawTheoryOccurrences interface := by
  induction occurrence with
  | here => exact .head _
  | left occurrence induction =>
      exact List.mem_append.mpr (.inl induction)
  | right occurrence induction =>
      exact List.mem_append.mpr (.inr induction)

/-- A proof-selected capture-kind declaration is a genuine raw theory
occurrence. -/
theorem captureHasKind_mem_theory
    {scope : Preparation.Source.Sig}
    {interface : Preparation.Source.Interface scope}
    {capture : Preparation.Source.Capture scope}
    {classifier : Preparation.Source.ClassifierExpr scope}
    (occurrence : interface.HasCaptureKindOccurrence capture classifier) :
    SourceTheoryOccurrence.constraint
        (.captureHasKind (.capture capture) classifier) ∈
      rawTheoryOccurrences interface := by
  induction occurrence with
  | here => exact .head _
  | left occurrence induction =>
      exact List.mem_append.mpr (.inl induction)
  | right occurrence induction =>
      exact List.mem_append.mpr (.inr induction)

/-- Source-order ordinal selected by one classifier-disjointness occurrence. -/
def classifierDisjointOrdinal {scope : Preparation.Source.Sig}
    {interface : Preparation.Source.Interface scope}
    {left right : Preparation.Source.ClassifierExpr scope} :
    interface.HasClassifierDisjointOccurrence left right -> Nat
  | .here => 0
  | .left occurrence => classifierDisjointOrdinal occurrence
  | .right (first := first) occurrence =>
      (rawConstraints first).length + classifierDisjointOrdinal occurrence

/-- Source-order ordinal selected by one capture-kind occurrence. -/
def captureHasKindOrdinal {scope : Preparation.Source.Sig}
    {interface : Preparation.Source.Interface scope}
    {capture : Preparation.Source.Capture scope}
    {classifier : Preparation.Source.ClassifierExpr scope} :
    interface.HasCaptureKindOccurrence capture classifier -> Nat
  | .here => 0
  | .left occurrence => captureHasKindOrdinal occurrence
  | .right (left := left) occurrence =>
      (rawConstraints left).length + captureHasKindOrdinal occurrence

/-- The selected classifier-disjointness occurrence is present at its exact
raw mixed-constraint coordinate. -/
theorem classifierDisjoint_getElem?_ordinal
    {scope : Preparation.Source.Sig}
    {interface : Preparation.Source.Interface scope}
    {left right : Preparation.Source.ClassifierExpr scope}
    (occurrence : interface.HasClassifierDisjointOccurrence left right) :
    (rawConstraints interface)[classifierDisjointOrdinal occurrence]? =
      some (.classifierDisjoint left right) := by
  induction occurrence with
  | here => simp [rawConstraints, classifierDisjointOrdinal]
  | left occurrence induction =>
      simp only [rawConstraints, classifierDisjointOrdinal]
      have inBounds := (List.getElem?_eq_some_iff.mp induction).choose
      rw [List.getElem?_append_left inBounds]
      exact induction
  | right occurrence induction =>
      simp only [rawConstraints, classifierDisjointOrdinal]
      rw [List.getElem?_append_right (Nat.le_add_right _ _)]
      simpa using induction

/-- Capture-kind counterpart of `classifierDisjoint_getElem?_ordinal`. -/
theorem captureHasKind_getElem?_ordinal
    {scope : Preparation.Source.Sig}
    {interface : Preparation.Source.Interface scope}
    {capture : Preparation.Source.Capture scope}
    {classifier : Preparation.Source.ClassifierExpr scope}
    (occurrence : interface.HasCaptureKindOccurrence capture classifier) :
    (rawConstraints interface)[captureHasKindOrdinal occurrence]? =
      some (.captureHasKind (.capture capture) classifier) := by
  induction occurrence with
  | here => simp [rawConstraints, captureHasKindOrdinal]
  | left occurrence induction =>
      simp only [rawConstraints, captureHasKindOrdinal]
      have inBounds := (List.getElem?_eq_some_iff.mp induction).choose
      rw [List.getElem?_append_left inBounds]
      exact induction
  | right occurrence induction =>
      simp only [rawConstraints, captureHasKindOrdinal]
      rw [List.getElem?_append_right (Nat.le_add_right _ _)]
      simpa using induction

end RawConstraintOccurrence

/-- Successful collection preserves every raw occurrence up to canonical
reordering and grouping. -/
theorem collect_occurrences {scope : Preparation.Source.Sig}
    (interface : Preparation.Source.Interface scope)
    {signature : Preparation.Source.MemberSignature
      (Preparation.Source.MemberExpr scope)}
    (success : interface.collect = .ok signature) :
    signature.occurrences.Perm (rawOccurrences interface) := by
  cases interface with
  | empty =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | typeMember label lower upper =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | captureMember label lower upper =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | classifierMember label lower upper =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | classifierDisjoint left right =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | captureHasKind capture classifier =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | inter left right =>
      simp only [DOTCapture.ModalIntersections.Interface.collect] at success
      cases leftResult : left.collect with
      | error conflict =>
          rw [leftResult] at success
          nomatch success
      | ok leftSignature =>
          cases rightResult : right.collect with
          | error conflict =>
              rw [leftResult, rightResult] at success
              nomatch success
          | ok rightSignature =>
              rw [leftResult, rightResult] at success
              exact
                (DOTCapture.Intersections.Signature.merge?_occurrences
                    leftSignature rightSignature signature success).trans
                  ((collect_occurrences left leftResult).append
                    (collect_occurrences right rightResult))
termination_by interface

/-- Successful collection retains the complete mixed-constraint stream in
source order.  In particular, neither classifier disjointness nor
capture-kind membership is discharged by normalization. -/
theorem collect_constraints {scope : Preparation.Source.Sig}
    (interface : Preparation.Source.Interface scope)
    {signature : Preparation.Source.MemberSignature
      (Preparation.Source.MemberExpr scope)}
    (success : interface.collect = .ok signature) :
    signature.constraints = rawConstraints interface := by
  cases interface with
  | empty =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | typeMember label lower upper =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | captureMember label lower upper =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | classifierMember label lower upper =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | classifierDisjoint left right =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | captureHasKind capture classifier =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | inter left right =>
      simp only [DOTCapture.ModalIntersections.Interface.collect] at success
      cases leftResult : left.collect with
      | error conflict =>
          rw [leftResult] at success
          nomatch success
      | ok leftSignature =>
          cases rightResult : right.collect with
          | error conflict =>
              rw [leftResult, rightResult] at success
              nomatch success
          | ok rightSignature =>
              rw [leftResult, rightResult] at success
              rw [DOTCapture.Intersections.Signature.merge?_constraints success,
                collect_constraints left leftResult,
                collect_constraints right rightResult]
              rfl
termination_by interface

/-! ## Per-label occurrence order

`Signature.merge?_occurrences` intentionally exposes only permutation because
whole signatures are canonically reordered by label.  Within one label,
however, `combineSameLabel?` appends intervals.  The following projections
record and prove that stronger order fact. -/

namespace Ordered

def entryTypeIntervalsAt {scope : Preparation.Source.Sig} (label : Nat) :
    Preparation.Source.MemberEntry (Preparation.Source.MemberExpr scope) ->
      List (Preparation.Source.MemberInterval
        (Preparation.Source.MemberExpr scope .type))
  | .type candidate intervals =>
      if candidate = label then intervals else []
  | .capture _ _ => []
  | .classifier _ _ => []

def entryCaptureIntervalsAt {scope : Preparation.Source.Sig} (label : Nat) :
    Preparation.Source.MemberEntry (Preparation.Source.MemberExpr scope) ->
      List (Preparation.Source.MemberInterval
        (Preparation.Source.MemberExpr scope .capture))
  | .type _ _ => []
  | .capture candidate intervals =>
      if candidate = label then intervals else []
  | .classifier _ _ => []

def entryClassifierIntervalsAt {scope : Preparation.Source.Sig} (label : Nat) :
    Preparation.Source.MemberEntry (Preparation.Source.MemberExpr scope) ->
      List (Preparation.Source.MemberInterval
        (Preparation.Source.MemberExpr scope .classifier))
  | .type _ _ => []
  | .capture _ _ => []
  | .classifier candidate intervals =>
      if candidate = label then intervals else []

def typeIntervalsAtEntries {scope : Preparation.Source.Sig} (label : Nat) :
    List (Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr scope)) ->
      List (Preparation.Source.MemberInterval
        (Preparation.Source.MemberExpr scope .type))
  | [] => []
  | entry :: remaining =>
      entryTypeIntervalsAt label entry ++
        typeIntervalsAtEntries label remaining

def captureIntervalsAtEntries {scope : Preparation.Source.Sig}
    (label : Nat) :
    List (Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr scope)) ->
      List (Preparation.Source.MemberInterval
        (Preparation.Source.MemberExpr scope .capture))
  | [] => []
  | entry :: remaining =>
      entryCaptureIntervalsAt label entry ++
        captureIntervalsAtEntries label remaining

def classifierIntervalsAtEntries {scope : Preparation.Source.Sig}
    (label : Nat) :
    List (Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr scope)) ->
      List (Preparation.Source.MemberInterval
        (Preparation.Source.MemberExpr scope .classifier))
  | [] => []
  | entry :: remaining =>
      entryClassifierIntervalsAt label entry ++
        classifierIntervalsAtEntries label remaining

def typeIntervalsAt {scope : Preparation.Source.Sig}
    (signature : Preparation.Source.MemberSignature
      (Preparation.Source.MemberExpr scope)) (label : Nat) :=
  typeIntervalsAtEntries label signature.entries

def captureIntervalsAt {scope : Preparation.Source.Sig}
    (signature : Preparation.Source.MemberSignature
      (Preparation.Source.MemberExpr scope)) (label : Nat) :=
  captureIntervalsAtEntries label signature.entries

def classifierIntervalsAt {scope : Preparation.Source.Sig}
    (signature : Preparation.Source.MemberSignature
      (Preparation.Source.MemberExpr scope)) (label : Nat) :=
  classifierIntervalsAtEntries label signature.entries

def preparedTypeIntervalsAtEntries {scope : Preparation.Target.Sig}
    (label : Nat) : List (PreparedEntry scope) ->
      List (Preparation.Source.MemberInterval
        (ManySortedFC.StaticExpr .type scope))
  | [] => []
  | .type candidate _ intervals :: remaining =>
      (if candidate = label then intervals else []) ++
        preparedTypeIntervalsAtEntries label remaining
  | .capture _ _ _ :: remaining =>
      preparedTypeIntervalsAtEntries label remaining
  | .classifier _ _ _ :: remaining =>
      preparedTypeIntervalsAtEntries label remaining

def preparedCaptureIntervalsAtEntries {scope : Preparation.Target.Sig}
    (label : Nat) : List (PreparedEntry scope) ->
      List (Preparation.Source.MemberInterval
        (ManySortedFC.StaticExpr .capture scope))
  | [] => []
  | .type _ _ _ :: remaining =>
      preparedCaptureIntervalsAtEntries label remaining
  | .capture candidate _ intervals :: remaining =>
      (if candidate = label then intervals else []) ++
        preparedCaptureIntervalsAtEntries label remaining
  | .classifier _ _ _ :: remaining =>
      preparedCaptureIntervalsAtEntries label remaining

def preparedClassifierIntervalsAtEntries {scope : Preparation.Target.Sig}
    (label : Nat) : List (PreparedEntry scope) ->
      List (Preparation.Source.MemberInterval
        (ManySortedFC.StaticExpr .classifier scope))
  | [] => []
  | .type _ _ _ :: remaining =>
      preparedClassifierIntervalsAtEntries label remaining
  | .capture _ _ _ :: remaining =>
      preparedClassifierIntervalsAtEntries label remaining
  | .classifier candidate _ intervals :: remaining =>
      (if candidate = label then intervals else []) ++
        preparedClassifierIntervalsAtEntries label remaining

private theorem translateMemberIntervals_append_of_success
    {sort : DOTCapture.Intersections.StaticSort}
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (left right : List (Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope sort)))
    {translatedLeft translatedRight : List (Preparation.Source.MemberInterval
      (Preparation.Target.StaticExpr
        (DOTCaptureToManySortedFC.Intersections.Encoding.targetSort sort)
        targetScope))}
    (leftSuccess : Preparation.Compile.translateMemberIntervals layout members
      left = .ok translatedLeft)
    (rightSuccess : Preparation.Compile.translateMemberIntervals layout members
      right = .ok translatedRight) :
    Preparation.Compile.translateMemberIntervals layout members
      (left ++ right) = .ok (translatedLeft ++ translatedRight) := by
  induction left generalizing translatedLeft with
  | nil =>
      simp only [Preparation.Compile.translateMemberIntervals_nil,
        Except.ok.injEq] at leftSuccess
      subst translatedLeft
      simpa using rightSuccess
  | cons current remaining induction =>
      rw [Preparation.Compile.translateMemberIntervals_cons] at leftSuccess
      cases lowerResult : Preparation.Compile.translateMemberExpr layout
          members current.lower with
      | error failure => rw [lowerResult] at leftSuccess; nomatch leftSuccess
      | ok translatedLower =>
          cases upperResult : Preparation.Compile.translateMemberExpr layout
              members current.upper with
          | error failure =>
              rw [lowerResult, upperResult] at leftSuccess
              nomatch leftSuccess
          | ok translatedUpper =>
              cases tailResult :
                  Preparation.Compile.translateMemberIntervals layout members
                    remaining with
              | error failure =>
                  rw [lowerResult, upperResult, tailResult] at leftSuccess
                  nomatch leftSuccess
              | ok translatedRemaining =>
                  rw [lowerResult, upperResult, tailResult] at leftSuccess
                  injection leftSuccess with translatedLeftEq
                  subst translatedLeft
                  rw [List.cons_append,
                    Preparation.Compile.translateMemberIntervals_cons,
                    lowerResult, upperResult,
                    induction tailResult]
                  rfl

/-- Successful interval translation preserves list coordinates exactly. -/
theorem translateMemberIntervals_getElem?
    {sort : DOTCapture.Intersections.StaticSort}
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (sourceIntervals : List (Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope sort)))
    {targetIntervals : List (Preparation.Source.MemberInterval
      (Preparation.Target.StaticExpr
        (DOTCaptureToManySortedFC.Intersections.Encoding.targetSort sort)
        targetScope))}
    (success : Preparation.Compile.translateMemberIntervals layout members
      sourceIntervals = .ok targetIntervals)
    {ordinal : Nat}
    {sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope sort)}
    (sourceAt : sourceIntervals[ordinal]? = some sourceInterval) :
    ∃ targetInterval,
      targetIntervals[ordinal]? = some targetInterval ∧
        Preparation.Compile.translateMemberIntervals layout members
          [sourceInterval] = .ok [targetInterval] := by
  induction sourceIntervals generalizing ordinal targetIntervals with
  | nil => simp at sourceAt
  | cons current remaining induction =>
      rw [Preparation.Compile.translateMemberIntervals_cons] at success
      cases lowerResult : Preparation.Compile.translateMemberExpr layout
          members current.lower with
      | error failure => rw [lowerResult] at success; nomatch success
      | ok translatedLower =>
          cases upperResult : Preparation.Compile.translateMemberExpr layout
              members current.upper with
          | error failure =>
              rw [lowerResult, upperResult] at success
              nomatch success
          | ok translatedUpper =>
              cases tailResult :
                  Preparation.Compile.translateMemberIntervals layout members
                    remaining with
              | error failure =>
                  rw [lowerResult, upperResult, tailResult] at success
                  nomatch success
              | ok translatedRemaining =>
                  rw [lowerResult, upperResult, tailResult] at success
                  injection success with targetIntervalsEq
                  subst targetIntervals
                  cases ordinal with
                  | zero =>
                      simp only [List.getElem?_cons_zero,
                        Option.some.injEq] at sourceAt
                      subst sourceInterval
                      let translated : Preparation.Source.MemberInterval
                          (Preparation.Target.StaticExpr
                            (DOTCaptureToManySortedFC.Intersections.Encoding.targetSort
                              sort) targetScope) :=
                        { lower := translatedLower, upper := translatedUpper }
                      refine ⟨translated, rfl, ?_⟩
                      rw [Preparation.Compile.translateMemberIntervals_cons,
                        lowerResult, upperResult,
                        Preparation.Compile.translateMemberIntervals_nil]
                      rfl
                  | succ ordinal =>
                      simp only [List.getElem?_cons_succ] at sourceAt
                      obtain ⟨translated, targetAt, singleton⟩ :=
                        induction tailResult sourceAt
                      exact ⟨translated, by simpa using targetAt, singleton⟩

/-- Mixed-constraint translation preserves list coordinates exactly. -/
theorem translateMemberConstraints_getElem?
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (sourceConstraints : List (SourceConstraint sourceScope))
    {targetConstraints : List (PreparedConstraint targetScope)}
    (success : Preparation.Compile.translateMemberConstraints layout members
      sourceConstraints = .ok targetConstraints)
    {ordinal : Nat} {sourceConstraint : SourceConstraint sourceScope}
    (sourceAt : sourceConstraints[ordinal]? = some sourceConstraint) :
    ∃ targetConstraint,
      targetConstraints[ordinal]? = some targetConstraint ∧
        Preparation.Compile.translateMemberConstraint layout members
          sourceConstraint = .ok targetConstraint := by
  induction sourceConstraints generalizing ordinal targetConstraints with
  | nil => simp at sourceAt
  | cons current remaining induction =>
      simp only [Preparation.Compile.translateMemberConstraints] at success
      cases currentResult :
          Preparation.Compile.translateMemberConstraint layout members current with
      | error failure =>
          rw [currentResult] at success
          nomatch success
      | ok translatedCurrent =>
          cases tailResult :
              Preparation.Compile.translateMemberConstraints layout members
                remaining with
          | error failure =>
              rw [currentResult, tailResult] at success
              nomatch success
          | ok translatedRemaining =>
              rw [currentResult, tailResult] at success
              injection success with targetConstraintsEq
              subst targetConstraints
              cases ordinal with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq]
                    at sourceAt
                  subst sourceConstraint
                  exact ⟨translatedCurrent, rfl, currentResult⟩
              | succ ordinal =>
                  simp only [List.getElem?_cons_succ] at sourceAt
                  obtain ⟨translated, targetAt, translation⟩ :=
                    induction tailResult sourceAt
                  exact ⟨translated, by simpa using targetAt, translation⟩

/-- Entry preparation preserves every per-label interval ordinal. -/
theorem entries_ordered
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (allMembers : List (MemberName targetScope))
    (sourceEntries : List (Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr sourceScope)))
    (allocated : List (MemberName targetScope))
    {preparedEntries : List (PreparedEntry targetScope)}
    (success : Preparation.Compile.entries layout allMembers sourceEntries
      allocated = .ok preparedEntries) (label : Nat) :
    Preparation.Compile.translateMemberIntervals layout allMembers
        (typeIntervalsAtEntries label sourceEntries) =
          .ok (preparedTypeIntervalsAtEntries label preparedEntries) ∧
      Preparation.Compile.translateMemberIntervals layout allMembers
        (captureIntervalsAtEntries label sourceEntries) =
          .ok (preparedCaptureIntervalsAtEntries label preparedEntries) := by
  induction sourceEntries generalizing allocated preparedEntries with
  | nil =>
      cases allocated with
      | nil =>
          simp only [Preparation.Compile.entries, Except.ok.injEq] at success
          subst preparedEntries
          constructor <;> rfl
      | cons member remaining =>
          simp [Preparation.Compile.entries] at success
  | cons sourceEntry remaining induction =>
      cases allocated with
      | nil => simp [Preparation.Compile.entries] at success
      | cons allocatedHead allocatedRemaining =>
          cases sourceEntry with
          | type sourceLabel sourceIntervals =>
              cases allocatedHead with
              | capture => simp [Preparation.Compile.entries] at success
              | classifier => simp [Preparation.Compile.entries] at success
              | type allocatedLabel name =>
                  by_cases labelsMatch : sourceLabel = allocatedLabel
                  · subst allocatedLabel
                    simp only [Preparation.Compile.entries,
                      dite_true] at success
                    cases intervalResult :
                        Preparation.Compile.translateMemberIntervals layout
                          allMembers sourceIntervals with
                    | error failure => rw [intervalResult] at success; nomatch success
                    | ok translatedIntervals =>
                        cases tailResult : Preparation.Compile.entries layout
                            allMembers remaining allocatedRemaining with
                        | error failure =>
                            rw [intervalResult, tailResult] at success
                            nomatch success
                        | ok translatedRemaining =>
                            rw [intervalResult, tailResult] at success
                            injection success with preparedEntriesEq
                            subst preparedEntries
                            obtain ⟨typeTail, captureTail⟩ :=
                              induction allocatedRemaining tailResult
                            constructor
                            · by_cases atLabel : sourceLabel = label
                              · subst sourceLabel
                                simp only [typeIntervalsAtEntries,
                                  entryTypeIntervalsAt,
                                  preparedTypeIntervalsAtEntries]
                                exact translateMemberIntervals_append_of_success
                                  layout allMembers _ _ intervalResult typeTail
                              · simp [typeIntervalsAtEntries,
                                  entryTypeIntervalsAt,
                                  preparedTypeIntervalsAtEntries, atLabel]
                                  at typeTail ⊢
                                exact typeTail
                            · simpa [captureIntervalsAtEntries,
                                entryCaptureIntervalsAt,
                                preparedCaptureIntervalsAtEntries] using captureTail
                  · simp [Preparation.Compile.entries, labelsMatch] at success

          | capture sourceLabel sourceIntervals =>
              cases allocatedHead with
              | type => simp [Preparation.Compile.entries] at success
              | classifier => simp [Preparation.Compile.entries] at success
              | capture allocatedLabel name =>
                  by_cases labelsMatch : sourceLabel = allocatedLabel
                  · subst allocatedLabel
                    simp only [Preparation.Compile.entries,
                      dite_true] at success
                    cases intervalResult :
                        Preparation.Compile.translateMemberIntervals layout
                          allMembers sourceIntervals with
                    | error failure => rw [intervalResult] at success; nomatch success
                    | ok translatedIntervals =>
                        cases tailResult : Preparation.Compile.entries layout
                            allMembers remaining allocatedRemaining with
                        | error failure =>
                            rw [intervalResult, tailResult] at success
                            nomatch success
                        | ok translatedRemaining =>
                            rw [intervalResult, tailResult] at success
                            injection success with preparedEntriesEq
                            subst preparedEntries
                            obtain ⟨typeTail, captureTail⟩ :=
                              induction allocatedRemaining tailResult
                            constructor
                            · simpa [typeIntervalsAtEntries,
                                entryTypeIntervalsAt,
                                preparedTypeIntervalsAtEntries] using typeTail
                            · by_cases atLabel : sourceLabel = label
                              · subst sourceLabel
                                simp only [captureIntervalsAtEntries,
                                  entryCaptureIntervalsAt,
                                  preparedCaptureIntervalsAtEntries]
                                exact translateMemberIntervals_append_of_success
                                  layout allMembers _ _ intervalResult captureTail
                              · simp [captureIntervalsAtEntries,
                                  entryCaptureIntervalsAt,
                                  preparedCaptureIntervalsAtEntries, atLabel]
                                  at captureTail ⊢
                                exact captureTail
                  · simp [Preparation.Compile.entries, labelsMatch] at success
          | classifier sourceLabel sourceIntervals =>
              cases allocatedHead with
              | type => simp [Preparation.Compile.entries] at success
              | capture => simp [Preparation.Compile.entries] at success
              | classifier allocatedLabel name =>
                  by_cases labelsMatch : sourceLabel = allocatedLabel
                  · subst allocatedLabel
                    simp only [Preparation.Compile.entries,
                      dite_true] at success
                    cases intervalResult :
                        Preparation.Compile.translateMemberIntervals layout
                          allMembers sourceIntervals with
                    | error failure =>
                        rw [intervalResult] at success
                        nomatch success
                    | ok translatedIntervals =>
                        cases tailResult : Preparation.Compile.entries layout
                            allMembers remaining allocatedRemaining with
                        | error failure =>
                            rw [intervalResult, tailResult] at success
                            nomatch success
                        | ok translatedRemaining =>
                            rw [intervalResult, tailResult] at success
                            injection success with preparedEntriesEq
                            subst preparedEntries
                            obtain ⟨typeTail, captureTail⟩ :=
                              induction allocatedRemaining tailResult
                            constructor
                            · simpa [typeIntervalsAtEntries,
                                entryTypeIntervalsAt,
                                preparedTypeIntervalsAtEntries] using typeTail
                            · simpa [captureIntervalsAtEntries,
                                entryCaptureIntervalsAt,
                                preparedCaptureIntervalsAtEntries] using
                                captureTail
                  · simp [Preparation.Compile.entries, labelsMatch] at success

/-- Classifier-sorted counterpart of `entries_ordered`. -/
theorem entries_classifier_ordered
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (allMembers : List (MemberName targetScope))
    (sourceEntries : List (Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr sourceScope)))
    (allocated : List (MemberName targetScope))
    {preparedEntries : List (PreparedEntry targetScope)}
    (success : Preparation.Compile.entries layout allMembers sourceEntries
      allocated = .ok preparedEntries) (label : Nat) :
    Preparation.Compile.translateMemberIntervals layout allMembers
        (classifierIntervalsAtEntries label sourceEntries) =
      .ok (preparedClassifierIntervalsAtEntries label preparedEntries) := by
  induction sourceEntries generalizing allocated preparedEntries with
  | nil =>
      cases allocated with
      | nil =>
          simp only [Preparation.Compile.entries, Except.ok.injEq] at success
          subst preparedEntries
          rfl
      | cons member remaining =>
          simp [Preparation.Compile.entries] at success
  | cons sourceEntry remaining induction =>
      cases allocated with
      | nil => simp [Preparation.Compile.entries] at success
      | cons allocatedHead allocatedRemaining =>
          cases sourceEntry with
          | type sourceLabel sourceIntervals =>
              cases allocatedHead with
              | capture => simp [Preparation.Compile.entries] at success
              | classifier => simp [Preparation.Compile.entries] at success
              | type allocatedLabel name =>
                  by_cases labelsMatch : sourceLabel = allocatedLabel
                  · subst allocatedLabel
                    simp only [Preparation.Compile.entries, dite_true] at success
                    cases intervalResult :
                        Preparation.Compile.translateMemberIntervals layout
                          allMembers sourceIntervals with
                    | error failure => rw [intervalResult] at success; nomatch success
                    | ok translatedIntervals =>
                        cases tailResult : Preparation.Compile.entries layout
                            allMembers remaining allocatedRemaining with
                        | error failure =>
                            rw [intervalResult, tailResult] at success
                            nomatch success
                        | ok translatedRemaining =>
                            rw [intervalResult, tailResult] at success
                            injection success with preparedEntriesEq
                            subst preparedEntries
                            simpa [classifierIntervalsAtEntries,
                              entryClassifierIntervalsAt,
                              preparedClassifierIntervalsAtEntries] using
                                induction allocatedRemaining tailResult
                  · simp [Preparation.Compile.entries, labelsMatch] at success
          | capture sourceLabel sourceIntervals =>
              cases allocatedHead with
              | type => simp [Preparation.Compile.entries] at success
              | classifier => simp [Preparation.Compile.entries] at success
              | capture allocatedLabel name =>
                  by_cases labelsMatch : sourceLabel = allocatedLabel
                  · subst allocatedLabel
                    simp only [Preparation.Compile.entries, dite_true] at success
                    cases intervalResult :
                        Preparation.Compile.translateMemberIntervals layout
                          allMembers sourceIntervals with
                    | error failure => rw [intervalResult] at success; nomatch success
                    | ok translatedIntervals =>
                        cases tailResult : Preparation.Compile.entries layout
                            allMembers remaining allocatedRemaining with
                        | error failure =>
                            rw [intervalResult, tailResult] at success
                            nomatch success
                        | ok translatedRemaining =>
                            rw [intervalResult, tailResult] at success
                            injection success with preparedEntriesEq
                            subst preparedEntries
                            simpa [classifierIntervalsAtEntries,
                              entryClassifierIntervalsAt,
                              preparedClassifierIntervalsAtEntries] using
                                induction allocatedRemaining tailResult
                  · simp [Preparation.Compile.entries, labelsMatch] at success
          | classifier sourceLabel sourceIntervals =>
              cases allocatedHead with
              | type => simp [Preparation.Compile.entries] at success
              | capture => simp [Preparation.Compile.entries] at success
              | classifier allocatedLabel name =>
                  by_cases labelsMatch : sourceLabel = allocatedLabel
                  · subst allocatedLabel
                    simp only [Preparation.Compile.entries, dite_true] at success
                    cases intervalResult :
                        Preparation.Compile.translateMemberIntervals layout
                          allMembers sourceIntervals with
                    | error failure => rw [intervalResult] at success; nomatch success
                    | ok translatedIntervals =>
                        cases tailResult : Preparation.Compile.entries layout
                            allMembers remaining allocatedRemaining with
                        | error failure =>
                            rw [intervalResult, tailResult] at success
                            nomatch success
                        | ok translatedRemaining =>
                            rw [intervalResult, tailResult] at success
                            injection success with preparedEntriesEq
                            subst preparedEntries
                            have classifierTail :=
                              induction allocatedRemaining tailResult
                            by_cases atLabel : sourceLabel = label
                            · subst sourceLabel
                              simp only [classifierIntervalsAtEntries,
                                entryClassifierIntervalsAt,
                                preparedClassifierIntervalsAtEntries]
                              exact translateMemberIntervals_append_of_success
                                layout allMembers _ _ intervalResult classifierTail
                            · simp [classifierIntervalsAtEntries,
                                entryClassifierIntervalsAt,
                                preparedClassifierIntervalsAtEntries, atLabel]
                                at classifierTail ⊢
                              exact classifierTail
                  · simp [Preparation.Compile.entries, labelsMatch] at success

private theorem typeIntervalsAtEntries_eq_nil_of_lt
    {scope : Preparation.Source.Sig} {label : Nat}
    (entries : List (Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr scope)))
    (later : ∀ entry ∈ entries, label < entry.label) :
    typeIntervalsAtEntries label entries = [] := by
  induction entries with
  | nil => rfl
  | cons current remaining induction =>
      have currentLater := later current (.head _)
      have remainingLater : ∀ entry ∈ remaining, label < entry.label :=
        fun entry membership => later entry (.tail _ membership)
      rw [show typeIntervalsAtEntries label (current :: remaining) =
        entryTypeIntervalsAt label current ++
          typeIntervalsAtEntries label remaining from rfl,
        induction remainingLater]
      cases current with
      | type candidate intervals =>
          have different : candidate ≠ label := by
            intro equality
            have strict : label < candidate := by
              simpa only [DOTCapture.Intersections.Entry.label] using
                currentLater
            rw [equality] at strict
            exact (Nat.lt_irrefl label) strict
          simp [entryTypeIntervalsAt, different]
      | capture => rfl
      | classifier => rfl

private theorem captureIntervalsAtEntries_eq_nil_of_lt
    {scope : Preparation.Source.Sig} {label : Nat}
    (entries : List (Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr scope)))
    (later : ∀ entry ∈ entries, label < entry.label) :
    captureIntervalsAtEntries label entries = [] := by
  induction entries with
  | nil => rfl
  | cons current remaining induction =>
      have currentLater := later current (.head _)
      have remainingLater : ∀ entry ∈ remaining, label < entry.label :=
        fun entry membership => later entry (.tail _ membership)
      rw [show captureIntervalsAtEntries label (current :: remaining) =
        entryCaptureIntervalsAt label current ++
          captureIntervalsAtEntries label remaining from rfl,
        induction remainingLater]
      cases current with
      | type => rfl
      | capture candidate intervals =>
          have different : candidate ≠ label := by
            intro equality
            have strict : label < candidate := by
              simpa only [DOTCapture.Intersections.Entry.label] using
                currentLater
            rw [equality] at strict
            exact (Nat.lt_irrefl label) strict
          simp [entryCaptureIntervalsAt, different]
      | classifier => rfl

private theorem classifierIntervalsAtEntries_eq_nil_of_lt
    {scope : Preparation.Source.Sig} {label : Nat}
    (entries : List (Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr scope)))
    (later : ∀ entry ∈ entries, label < entry.label) :
    classifierIntervalsAtEntries label entries = [] := by
  induction entries with
  | nil => rfl
  | cons current remaining induction =>
      have currentLater := later current (.head _)
      have remainingLater : ∀ entry ∈ remaining, label < entry.label :=
        fun entry membership => later entry (.tail _ membership)
      rw [show classifierIntervalsAtEntries label (current :: remaining) =
        entryClassifierIntervalsAt label current ++
          classifierIntervalsAtEntries label remaining from rfl,
        induction remainingLater]
      cases current with
      | type => rfl
      | capture => rfl
      | classifier candidate intervals =>
          have different : candidate ≠ label := by
            intro equality
            have strict : label < candidate := by
              simpa only [DOTCapture.Intersections.Entry.label] using
                currentLater
            rw [equality] at strict
            exact (Nat.lt_irrefl label) strict
          simp [entryClassifierIntervalsAt, different]

private theorem insertEntry?_typeIntervalsAt
    {scope : Preparation.Source.Sig}
    (incoming : Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr scope))
    (entries result : List (Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr scope)))
    (normalized :
      ({ entries } : Preparation.Source.MemberSignature
        (Preparation.Source.MemberExpr scope)).Normalized)
    (success : DOTCapture.Intersections.Signature.insertEntry? incoming
      entries = .ok result) (label : Nat) :
    typeIntervalsAtEntries label result =
      typeIntervalsAtEntries label entries ++
        entryTypeIntervalsAt label incoming := by
  induction entries generalizing result with
  | nil =>
      simp [DOTCapture.Intersections.Signature.insertEntry?] at success
      subst result
      simp [typeIntervalsAtEntries]
  | cons current remaining induction =>
      cases normalized.sorted with
      | cons currentBefore remainingSorted =>
          have remainingNormalized :
              ({ entries := remaining } : Preparation.Source.MemberSignature
                (Preparation.Source.MemberExpr scope)).Normalized :=
            { sorted := remainingSorted
              nonempty := fun entry membership =>
                normalized.nonempty entry (.tail current membership) }
          simp only [DOTCapture.Intersections.Signature.insertEntry?] at success
          split at success
          next before =>
            simp only [Except.ok.injEq] at success
            subst result
            cases incoming with
            | type incomingLabel incomingIntervals =>
                by_cases sameLabel : incomingLabel = label
                · subst incomingLabel
                  have oldEmpty : typeIntervalsAtEntries label
                      (current :: remaining) = [] :=
                    typeIntervalsAtEntries_eq_nil_of_lt _ fun entry membership =>
                      match List.mem_cons.mp membership with
                      | .inl equality => equality ▸ before
                      | .inr tailMembership =>
                          Nat.lt_trans before
                            (currentBefore entry tailMembership)
                  have oldDecomposition :
                      entryTypeIntervalsAt label current ++
                        typeIntervalsAtEntries label remaining = [] := by
                    simpa only [typeIntervalsAtEntries] using oldEmpty
                  change entryTypeIntervalsAt label
                        (.type label incomingIntervals) ++
                      (entryTypeIntervalsAt label current ++
                        typeIntervalsAtEntries label remaining) =
                    (entryTypeIntervalsAt label current ++
                        typeIntervalsAtEntries label remaining) ++
                      entryTypeIntervalsAt label
                        (.type label incomingIntervals)
                  rw [oldDecomposition]
                  simp [entryTypeIntervalsAt]
                · simp [typeIntervalsAtEntries, entryTypeIntervalsAt,
                    sameLabel]
            | capture =>
                simp [typeIntervalsAtEntries, entryTypeIntervalsAt]
            | classifier =>
                simp [typeIntervalsAtEntries, entryTypeIntervalsAt]
          next notBefore =>
            split at success
            next same =>
              cases combinedResult :
                  DOTCapture.Intersections.Signature.combineSameLabel?
                    current incoming with
              | error conflict => simp [combinedResult] at success
              | ok combined =>
                  simp [combinedResult] at success
                  subst result
                  cases current with
                  | type currentLabel currentIntervals =>
                      cases incoming with
                      | type incomingLabel incomingIntervals =>
                          simp only [DOTCapture.Intersections.Entry.label] at same
                          subst incomingLabel
                          simp only [DOTCapture.Intersections.Signature.combineSameLabel?,
                            Except.ok.injEq] at combinedResult
                          subst combined
                          by_cases atLabel : currentLabel = label
                          · have tailEmpty : typeIntervalsAtEntries label
                                remaining = [] :=
                              typeIntervalsAtEntries_eq_nil_of_lt _
                                fun entry membership => by
                                  have later := currentBefore entry membership
                                  simpa only [atLabel,
                                    DOTCapture.Intersections.Signature.Before,
                                    DOTCapture.Intersections.Entry.label] using later
                            simp [typeIntervalsAtEntries,
                              entryTypeIntervalsAt, atLabel, tailEmpty]
                          · simp [typeIntervalsAtEntries,
                              entryTypeIntervalsAt, atLabel]
                      | capture =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                      | classifier =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                  | capture currentLabel currentIntervals =>
                      cases incoming with
                      | type =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                      | capture incomingLabel incomingIntervals =>
                          simp only [DOTCapture.Intersections.Entry.label] at same
                          subst incomingLabel
                          simp only [DOTCapture.Intersections.Signature.combineSameLabel?,
                            Except.ok.injEq] at combinedResult
                          subst combined
                          simp [typeIntervalsAtEntries,
                            entryTypeIntervalsAt]
                      | classifier =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                  | classifier currentLabel currentIntervals =>
                      cases incoming with
                      | type =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                      | capture =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                      | classifier incomingLabel incomingIntervals =>
                          simp only [DOTCapture.Intersections.Entry.label] at same
                          subst incomingLabel
                          simp only [DOTCapture.Intersections.Signature.combineSameLabel?,
                            Except.ok.injEq] at combinedResult
                          subst combined
                          simp [typeIntervalsAtEntries, entryTypeIntervalsAt]
            next different =>
              cases recursive :
                  DOTCapture.Intersections.Signature.insertEntry? incoming
                    remaining with
              | error conflict => simp [recursive] at success
              | ok inserted =>
                  simp [recursive] at success
                  subst result
                  rw [show typeIntervalsAtEntries label
                      (current :: inserted) =
                    entryTypeIntervalsAt label current ++
                      typeIntervalsAtEntries label inserted from rfl,
                    induction inserted remainingNormalized recursive]
                  simp [typeIntervalsAtEntries, List.append_assoc]

private theorem insertEntry?_captureIntervalsAt
    {scope : Preparation.Source.Sig}
    (incoming : Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr scope))
    (entries result : List (Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr scope)))
    (normalized :
      ({ entries } : Preparation.Source.MemberSignature
        (Preparation.Source.MemberExpr scope)).Normalized)
    (success : DOTCapture.Intersections.Signature.insertEntry? incoming
      entries = .ok result) (label : Nat) :
    captureIntervalsAtEntries label result =
      captureIntervalsAtEntries label entries ++
        entryCaptureIntervalsAt label incoming := by
  induction entries generalizing result with
  | nil =>
      simp [DOTCapture.Intersections.Signature.insertEntry?] at success
      subst result
      simp [captureIntervalsAtEntries]
  | cons current remaining induction =>
      cases normalized.sorted with
      | cons currentBefore remainingSorted =>
          have remainingNormalized :
              ({ entries := remaining } : Preparation.Source.MemberSignature
                (Preparation.Source.MemberExpr scope)).Normalized :=
            { sorted := remainingSorted
              nonempty := fun entry membership =>
                normalized.nonempty entry (.tail current membership) }
          simp only [DOTCapture.Intersections.Signature.insertEntry?] at success
          split at success
          next before =>
            simp only [Except.ok.injEq] at success
            subst result
            cases incoming with
            | type =>
                simp [captureIntervalsAtEntries, entryCaptureIntervalsAt]
            | capture incomingLabel incomingIntervals =>
                by_cases sameLabel : incomingLabel = label
                · subst incomingLabel
                  have oldEmpty : captureIntervalsAtEntries label
                      (current :: remaining) = [] :=
                    captureIntervalsAtEntries_eq_nil_of_lt _ fun entry membership =>
                      match List.mem_cons.mp membership with
                      | .inl equality => equality ▸ before
                      | .inr tailMembership =>
                          Nat.lt_trans before
                            (currentBefore entry tailMembership)
                  have oldDecomposition :
                      entryCaptureIntervalsAt label current ++
                        captureIntervalsAtEntries label remaining = [] := by
                    simpa only [captureIntervalsAtEntries] using oldEmpty
                  change entryCaptureIntervalsAt label
                        (.capture label incomingIntervals) ++
                      (entryCaptureIntervalsAt label current ++
                        captureIntervalsAtEntries label remaining) =
                    (entryCaptureIntervalsAt label current ++
                        captureIntervalsAtEntries label remaining) ++
                      entryCaptureIntervalsAt label
                        (.capture label incomingIntervals)
                  rw [oldDecomposition]
                  simp [entryCaptureIntervalsAt]
                · simp [captureIntervalsAtEntries, entryCaptureIntervalsAt,
                    sameLabel]
            | classifier =>
                simp [captureIntervalsAtEntries, entryCaptureIntervalsAt]
          next notBefore =>
            split at success
            next same =>
              cases combinedResult :
                  DOTCapture.Intersections.Signature.combineSameLabel?
                    current incoming with
              | error conflict => simp [combinedResult] at success
              | ok combined =>
                  simp [combinedResult] at success
                  subst result
                  cases current with
                  | type currentLabel currentIntervals =>
                      cases incoming with
                      | type incomingLabel incomingIntervals =>
                          simp only [DOTCapture.Intersections.Entry.label] at same
                          subst incomingLabel
                          simp only [DOTCapture.Intersections.Signature.combineSameLabel?,
                            Except.ok.injEq] at combinedResult
                          subst combined
                          simp [captureIntervalsAtEntries,
                            entryCaptureIntervalsAt]
                      | capture =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                      | classifier =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                  | capture currentLabel currentIntervals =>
                      cases incoming with
                      | type =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                      | capture incomingLabel incomingIntervals =>
                          simp only [DOTCapture.Intersections.Entry.label] at same
                          subst incomingLabel
                          simp only [DOTCapture.Intersections.Signature.combineSameLabel?,
                            Except.ok.injEq] at combinedResult
                          subst combined
                          by_cases atLabel : currentLabel = label
                          · have tailEmpty : captureIntervalsAtEntries label
                                remaining = [] :=
                              captureIntervalsAtEntries_eq_nil_of_lt _
                                fun entry membership => by
                                  have later := currentBefore entry membership
                                  simpa only [atLabel,
                                    DOTCapture.Intersections.Signature.Before,
                                    DOTCapture.Intersections.Entry.label] using later
                            simp [captureIntervalsAtEntries,
                              entryCaptureIntervalsAt, atLabel, tailEmpty]
                          · simp [captureIntervalsAtEntries,
                              entryCaptureIntervalsAt, atLabel]
                      | classifier =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                  | classifier currentLabel currentIntervals =>
                      cases incoming with
                      | type =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                      | capture =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                      | classifier incomingLabel incomingIntervals =>
                          simp only [DOTCapture.Intersections.Entry.label] at same
                          subst incomingLabel
                          simp only [DOTCapture.Intersections.Signature.combineSameLabel?,
                            Except.ok.injEq] at combinedResult
                          subst combined
                          simp [captureIntervalsAtEntries,
                            entryCaptureIntervalsAt]
            next different =>
              cases recursive :
                  DOTCapture.Intersections.Signature.insertEntry? incoming
                    remaining with
              | error conflict => simp [recursive] at success
              | ok inserted =>
                  simp [recursive] at success
                  subst result
                  rw [show captureIntervalsAtEntries label
                      (current :: inserted) =
                    entryCaptureIntervalsAt label current ++
                      captureIntervalsAtEntries label inserted from rfl,
                    induction inserted remainingNormalized recursive]
                  simp [captureIntervalsAtEntries, List.append_assoc]

private theorem insertEntry?_classifierIntervalsAt
    {scope : Preparation.Source.Sig}
    (incoming : Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr scope))
    (entries result : List (Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr scope)))
    (normalized :
      ({ entries } : Preparation.Source.MemberSignature
        (Preparation.Source.MemberExpr scope)).Normalized)
    (success : DOTCapture.Intersections.Signature.insertEntry? incoming
      entries = .ok result) (label : Nat) :
    classifierIntervalsAtEntries label result =
      classifierIntervalsAtEntries label entries ++
        entryClassifierIntervalsAt label incoming := by
  induction entries generalizing result with
  | nil =>
      simp [DOTCapture.Intersections.Signature.insertEntry?] at success
      subst result
      simp [classifierIntervalsAtEntries]
  | cons current remaining induction =>
      cases normalized.sorted with
      | cons currentBefore remainingSorted =>
          have remainingNormalized :
              ({ entries := remaining } : Preparation.Source.MemberSignature
                (Preparation.Source.MemberExpr scope)).Normalized :=
            { sorted := remainingSorted
              nonempty := fun entry membership =>
                normalized.nonempty entry (.tail current membership) }
          simp only [DOTCapture.Intersections.Signature.insertEntry?] at success
          split at success
          next before =>
            simp only [Except.ok.injEq] at success
            subst result
            cases incoming with
            | type =>
                simp [classifierIntervalsAtEntries,
                  entryClassifierIntervalsAt]
            | capture =>
                simp [classifierIntervalsAtEntries,
                  entryClassifierIntervalsAt]
            | classifier incomingLabel incomingIntervals =>
                by_cases sameLabel : incomingLabel = label
                · subst incomingLabel
                  have oldEmpty : classifierIntervalsAtEntries label
                      (current :: remaining) = [] :=
                    classifierIntervalsAtEntries_eq_nil_of_lt _
                      fun entry membership =>
                        match List.mem_cons.mp membership with
                        | .inl equality => equality ▸ before
                        | .inr tailMembership =>
                            Nat.lt_trans before
                              (currentBefore entry tailMembership)
                  have oldDecomposition :
                      entryClassifierIntervalsAt label current ++
                        classifierIntervalsAtEntries label remaining = [] := by
                    simpa only [classifierIntervalsAtEntries] using oldEmpty
                  change entryClassifierIntervalsAt label
                        (.classifier label incomingIntervals) ++
                      (entryClassifierIntervalsAt label current ++
                        classifierIntervalsAtEntries label remaining) =
                    (entryClassifierIntervalsAt label current ++
                        classifierIntervalsAtEntries label remaining) ++
                      entryClassifierIntervalsAt label
                        (.classifier label incomingIntervals)
                  rw [oldDecomposition]
                  simp [entryClassifierIntervalsAt]
                · simp [classifierIntervalsAtEntries,
                    entryClassifierIntervalsAt, sameLabel]
          next notBefore =>
            split at success
            next same =>
              cases combinedResult :
                  DOTCapture.Intersections.Signature.combineSameLabel?
                    current incoming with
              | error conflict => simp [combinedResult] at success
              | ok combined =>
                  simp [combinedResult] at success
                  subst result
                  cases current with
                  | type currentLabel currentIntervals =>
                      cases incoming with
                      | type incomingLabel incomingIntervals =>
                          simp only [DOTCapture.Intersections.Entry.label] at same
                          subst incomingLabel
                          simp only [DOTCapture.Intersections.Signature.combineSameLabel?,
                            Except.ok.injEq] at combinedResult
                          subst combined
                          simp [classifierIntervalsAtEntries,
                            entryClassifierIntervalsAt]
                      | capture =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                      | classifier =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                  | capture currentLabel currentIntervals =>
                      cases incoming with
                      | type =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                      | capture incomingLabel incomingIntervals =>
                          simp only [DOTCapture.Intersections.Entry.label] at same
                          subst incomingLabel
                          simp only [DOTCapture.Intersections.Signature.combineSameLabel?,
                            Except.ok.injEq] at combinedResult
                          subst combined
                          simp [classifierIntervalsAtEntries,
                            entryClassifierIntervalsAt]
                      | classifier =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                  | classifier currentLabel currentIntervals =>
                      cases incoming with
                      | type =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                      | capture =>
                          simp [DOTCapture.Intersections.Signature.combineSameLabel?]
                            at combinedResult
                      | classifier incomingLabel incomingIntervals =>
                          simp only [DOTCapture.Intersections.Entry.label] at same
                          subst incomingLabel
                          simp only [DOTCapture.Intersections.Signature.combineSameLabel?,
                            Except.ok.injEq] at combinedResult
                          subst combined
                          by_cases atLabel : currentLabel = label
                          · have tailEmpty : classifierIntervalsAtEntries label
                                remaining = [] :=
                              classifierIntervalsAtEntries_eq_nil_of_lt _
                                fun entry membership => by
                                  have later := currentBefore entry membership
                                  simpa only [atLabel,
                                    DOTCapture.Intersections.Signature.Before,
                                    DOTCapture.Intersections.Entry.label] using
                                      later
                            simp [classifierIntervalsAtEntries,
                              entryClassifierIntervalsAt, atLabel, tailEmpty]
                          · simp [classifierIntervalsAtEntries,
                              entryClassifierIntervalsAt, atLabel]
            next different =>
              cases recursive :
                  DOTCapture.Intersections.Signature.insertEntry? incoming
                    remaining with
              | error conflict => simp [recursive] at success
              | ok inserted =>
                  simp [recursive] at success
                  subst result
                  rw [show classifierIntervalsAtEntries label
                      (current :: inserted) =
                    entryClassifierIntervalsAt label current ++
                      classifierIntervalsAtEntries label inserted from rfl,
                    induction inserted remainingNormalized recursive]
                  simp [classifierIntervalsAtEntries, List.append_assoc]

private theorem mergeEntries?_ordered
    {scope : Preparation.Source.Sig}
    (accumulated incoming result : List (Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr scope)))
    (accumulatedNormalized :
      ({ entries := accumulated } : Preparation.Source.MemberSignature
        (Preparation.Source.MemberExpr scope)).Normalized)
    (incomingNormalized :
      ({ entries := incoming } : Preparation.Source.MemberSignature
        (Preparation.Source.MemberExpr scope)).Normalized)
    (success : DOTCapture.Intersections.Signature.mergeEntries? accumulated
      incoming = .ok result) (label : Nat) :
    typeIntervalsAtEntries label result =
        typeIntervalsAtEntries label accumulated ++
          typeIntervalsAtEntries label incoming ∧
      captureIntervalsAtEntries label result =
        captureIntervalsAtEntries label accumulated ++
          captureIntervalsAtEntries label incoming := by
  induction incoming generalizing accumulated result with
  | nil =>
      simp [DOTCapture.Intersections.Signature.mergeEntries?] at success
      subst result
      constructor <;>
        simp only [typeIntervalsAtEntries, captureIntervalsAtEntries,
          List.append_nil]
  | cons entry remaining induction =>
      cases incomingNormalized.sorted with
      | cons entryBefore remainingSorted =>
          have entryNonempty := incomingNormalized.nonempty entry (.head _)
          have remainingNormalized :
              ({ entries := remaining } : Preparation.Source.MemberSignature
                (Preparation.Source.MemberExpr scope)).Normalized :=
            { sorted := remainingSorted
              nonempty := fun current membership =>
                incomingNormalized.nonempty current (.tail entry membership) }
          simp only [DOTCapture.Intersections.Signature.mergeEntries?] at success
          cases insertedResult :
              DOTCapture.Intersections.Signature.insertEntry? entry accumulated with
          | error conflict => simp [insertedResult] at success
          | ok inserted =>
              simp [insertedResult] at success
              have insertedNormalized :=
                DOTCapture.Intersections.Signature.insertEntry?_normalized entry
                  ({ entries := accumulated } :
                    Preparation.Source.MemberSignature
                      (Preparation.Source.MemberExpr scope))
                  entryNonempty accumulatedNormalized insertedResult
              obtain ⟨typeTail, captureTail⟩ :=
                induction inserted result insertedNormalized
                  remainingNormalized success
              constructor
              · rw [typeTail,
                  insertEntry?_typeIntervalsAt entry accumulated inserted
                    accumulatedNormalized insertedResult]
                simp [typeIntervalsAtEntries, List.append_assoc]
              · rw [captureTail,
                  insertEntry?_captureIntervalsAt entry accumulated inserted
                    accumulatedNormalized insertedResult]
                simp [captureIntervalsAtEntries, List.append_assoc]

private theorem mergeEntries?_classifier_ordered
    {scope : Preparation.Source.Sig}
    (accumulated incoming result : List (Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr scope)))
    (accumulatedNormalized :
      ({ entries := accumulated } : Preparation.Source.MemberSignature
        (Preparation.Source.MemberExpr scope)).Normalized)
    (incomingNormalized :
      ({ entries := incoming } : Preparation.Source.MemberSignature
        (Preparation.Source.MemberExpr scope)).Normalized)
    (success : DOTCapture.Intersections.Signature.mergeEntries? accumulated
      incoming = .ok result) (label : Nat) :
    classifierIntervalsAtEntries label result =
      classifierIntervalsAtEntries label accumulated ++
        classifierIntervalsAtEntries label incoming := by
  induction incoming generalizing accumulated result with
  | nil =>
      simp [DOTCapture.Intersections.Signature.mergeEntries?] at success
      subst result
      simp only [classifierIntervalsAtEntries, List.append_nil]
  | cons entry remaining induction =>
      cases incomingNormalized.sorted with
      | cons entryBefore remainingSorted =>
          have entryNonempty := incomingNormalized.nonempty entry (.head _)
          have remainingNormalized :
              ({ entries := remaining } : Preparation.Source.MemberSignature
                (Preparation.Source.MemberExpr scope)).Normalized :=
            { sorted := remainingSorted
              nonempty := fun current membership =>
                incomingNormalized.nonempty current (.tail entry membership) }
          simp only [DOTCapture.Intersections.Signature.mergeEntries?] at success
          cases insertedResult :
              DOTCapture.Intersections.Signature.insertEntry? entry accumulated with
          | error conflict => simp [insertedResult] at success
          | ok inserted =>
              simp [insertedResult] at success
              have insertedNormalized :=
                DOTCapture.Intersections.Signature.insertEntry?_normalized entry
                  ({ entries := accumulated } :
                    Preparation.Source.MemberSignature
                      (Preparation.Source.MemberExpr scope))
                  entryNonempty accumulatedNormalized insertedResult
              rw [induction inserted result insertedNormalized
                    remainingNormalized success,
                insertEntry?_classifierIntervalsAt entry accumulated inserted
                  accumulatedNormalized insertedResult]
              simp [classifierIntervalsAtEntries, List.append_assoc]

theorem merge?_classifier_ordered {scope : Preparation.Source.Sig}
    (left right result : Preparation.Source.MemberSignature
      (Preparation.Source.MemberExpr scope))
    (leftNormalized : left.Normalized)
    (rightNormalized : right.Normalized)
    (success : left.merge? right = .ok result) (label : Nat) :
    classifierIntervalsAt result label =
      classifierIntervalsAt left label ++
        classifierIntervalsAt right label := by
  unfold DOTCapture.Intersections.Signature.merge? at success
  cases merged : DOTCapture.Intersections.Signature.mergeEntries?
      left.entries right.entries with
  | error conflict => simp [merged] at success
  | ok entries =>
      simp [merged] at success
      subst result
      exact mergeEntries?_classifier_ordered left.entries right.entries entries
        { sorted := leftNormalized.sorted
          nonempty := leftNormalized.nonempty }
        { sorted := rightNormalized.sorted
          nonempty := rightNormalized.nonempty }
        merged label

theorem merge?_ordered {scope : Preparation.Source.Sig}
    (left right result : Preparation.Source.MemberSignature
      (Preparation.Source.MemberExpr scope))
    (leftNormalized : left.Normalized)
    (rightNormalized : right.Normalized)
    (success : left.merge? right = .ok result) (label : Nat) :
    typeIntervalsAt result label =
        typeIntervalsAt left label ++ typeIntervalsAt right label ∧
      captureIntervalsAt result label =
        captureIntervalsAt left label ++ captureIntervalsAt right label := by
  unfold DOTCapture.Intersections.Signature.merge? at success
  cases merged : DOTCapture.Intersections.Signature.mergeEntries?
      left.entries right.entries with
  | error conflict => simp [merged] at success
  | ok entries =>
      simp [merged] at success
      subst result
      exact mergeEntries?_ordered left.entries right.entries entries
        { sorted := leftNormalized.sorted
          nonempty := leftNormalized.nonempty }
        { sorted := rightNormalized.sorted
          nonempty := rightNormalized.nonempty }
        merged label

/-- Successful normalization preserves same-label type declarations in exact
left-to-right source order. -/
theorem collect_typeIntervalsAt {scope : Preparation.Source.Sig}
    (interface : Preparation.Source.Interface scope)
    {signature : Preparation.Source.MemberSignature
      (Preparation.Source.MemberExpr scope)}
    (success : interface.collect = .ok signature) (label : Nat) :
    typeIntervalsAt signature label = rawTypeIntervals label interface := by
  cases interface with
  | empty =>
      simp [DOTCapture.ModalIntersections.Interface.collect] at success
      subst signature
      rfl
  | typeMember candidate lower upper =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      simp [typeIntervalsAt, typeIntervalsAtEntries, entryTypeIntervalsAt,
        rawTypeIntervals, DOTCapture.Intersections.Signature.singletonType]
  | captureMember candidate lower upper =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | classifierMember candidate lower upper =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | classifierDisjoint left right =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | captureHasKind capture classifier =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | inter left right =>
      simp only [DOTCapture.ModalIntersections.Interface.collect] at success
      cases leftResult : left.collect with
      | error conflict => rw [leftResult] at success; nomatch success
      | ok leftSignature =>
          cases rightResult : right.collect with
          | error conflict =>
              rw [leftResult, rightResult] at success
              nomatch success
          | ok rightSignature =>
              rw [leftResult, rightResult] at success
              have ordered := (merge?_ordered leftSignature rightSignature
                signature
                (DOTCapture.ModalIntersections.Interface.collect_normalized
                  left leftResult)
                (DOTCapture.ModalIntersections.Interface.collect_normalized
                  right rightResult)
                success label).1
              rw [ordered,
                collect_typeIntervalsAt left leftResult label,
                collect_typeIntervalsAt right rightResult label]
              rfl
termination_by interface

/-- Capture-sorted counterpart of `collect_typeIntervalsAt`. -/
theorem collect_captureIntervalsAt {scope : Preparation.Source.Sig}
    (interface : Preparation.Source.Interface scope)
    {signature : Preparation.Source.MemberSignature
      (Preparation.Source.MemberExpr scope)}
    (success : interface.collect = .ok signature) (label : Nat) :
    captureIntervalsAt signature label =
      rawCaptureIntervals label interface := by
  cases interface with
  | empty =>
      simp [DOTCapture.ModalIntersections.Interface.collect] at success
      subst signature
      rfl
  | typeMember candidate lower upper =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | captureMember candidate lower upper =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      simp [captureIntervalsAt, captureIntervalsAtEntries,
        entryCaptureIntervalsAt, rawCaptureIntervals,
        DOTCapture.Intersections.Signature.singletonCapture]
  | classifierMember candidate lower upper =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | classifierDisjoint left right =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | captureHasKind capture classifier =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | inter left right =>
      simp only [DOTCapture.ModalIntersections.Interface.collect] at success
      cases leftResult : left.collect with
      | error conflict => rw [leftResult] at success; nomatch success
      | ok leftSignature =>
          cases rightResult : right.collect with
          | error conflict =>
              rw [leftResult, rightResult] at success
              nomatch success
          | ok rightSignature =>
              rw [leftResult, rightResult] at success
              have ordered := (merge?_ordered leftSignature rightSignature
                signature
                (DOTCapture.ModalIntersections.Interface.collect_normalized
                  left leftResult)
                (DOTCapture.ModalIntersections.Interface.collect_normalized
                  right rightResult)
                success label).2
              rw [ordered,
                collect_captureIntervalsAt left leftResult label,
                collect_captureIntervalsAt right rightResult label]
              rfl
termination_by interface

/-- Classifier-sorted counterpart of `collect_typeIntervalsAt`. -/
theorem collect_classifierIntervalsAt {scope : Preparation.Source.Sig}
    (interface : Preparation.Source.Interface scope)
    {signature : Preparation.Source.MemberSignature
      (Preparation.Source.MemberExpr scope)}
    (success : interface.collect = .ok signature) (label : Nat) :
    classifierIntervalsAt signature label =
      rawClassifierIntervals label interface := by
  cases interface with
  | empty =>
      simp [DOTCapture.ModalIntersections.Interface.collect] at success
      subst signature
      rfl
  | typeMember candidate lower upper =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | captureMember candidate lower upper =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | classifierMember candidate lower upper =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      simp [classifierIntervalsAt, classifierIntervalsAtEntries,
        entryClassifierIntervalsAt, rawClassifierIntervals,
        DOTCapture.Intersections.Signature.singletonClassifier]
  | classifierDisjoint left right =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | captureHasKind capture classifier =>
      simp only [DOTCapture.ModalIntersections.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | inter left right =>
      simp only [DOTCapture.ModalIntersections.Interface.collect] at success
      cases leftResult : left.collect with
      | error conflict => rw [leftResult] at success; nomatch success
      | ok leftSignature =>
          cases rightResult : right.collect with
          | error conflict =>
              rw [leftResult, rightResult] at success
              nomatch success
          | ok rightSignature =>
              rw [leftResult, rightResult] at success
              have ordered := merge?_classifier_ordered leftSignature
                rightSignature signature
                (DOTCapture.ModalIntersections.Interface.collect_normalized
                  left leftResult)
                (DOTCapture.ModalIntersections.Interface.collect_normalized
                  right rightResult)
                success label
              rw [ordered,
                collect_classifierIntervalsAt left leftResult label,
                collect_classifierIntervalsAt right rightResult label]
              rfl
termination_by interface

end Ordered

namespace RawOccurrence

/-- A proof-relevant raw type occurrence determines membership in the
flattened occurrence list. -/
theorem type_mem {scope : Preparation.Source.Sig}
    {interface : Preparation.Source.Interface scope}
    {label : Nat} {lower upper : Preparation.Source.Ty scope}
    (occurrence : interface.HasTypeOccurrence label lower upper) :
    DOTCapture.Intersections.Occurrence.type label
      ({ lower := .type lower, upper := .type upper } :
        Preparation.Source.MemberInterval
          (Preparation.Source.MemberExpr scope .type)) ∈
      rawOccurrences interface := by
  induction occurrence with
  | here => exact .head _
  | left occurrence induction =>
      exact List.mem_append.mpr (.inl induction)
  | right occurrence induction =>
      exact List.mem_append.mpr (.inr induction)

/-- Capture-sorted counterpart of `type_mem`. -/
theorem capture_mem {scope : Preparation.Source.Sig}
    {interface : Preparation.Source.Interface scope}
    {label : Nat}
    {lower upper : Preparation.Source.Capture scope}
    (occurrence : interface.HasCaptureOccurrence label lower upper) :
    DOTCapture.Intersections.Occurrence.capture label
      ({ lower := .capture lower, upper := .capture upper } :
        Preparation.Source.MemberInterval
          (Preparation.Source.MemberExpr scope .capture)) ∈
      rawOccurrences interface := by
  induction occurrence with
  | here => exact .head _
  | left occurrence induction =>
      exact List.mem_append.mpr (.inl induction)
  | right occurrence induction =>
      exact List.mem_append.mpr (.inr induction)

/-- Classifier-sorted counterpart of `type_mem`. -/
theorem classifier_mem {scope : Preparation.Source.Sig}
    {interface : Preparation.Source.Interface scope}
    {label : Nat}
    {lower upper : Preparation.Source.ClassifierExpr scope}
    (occurrence : interface.HasClassifierOccurrence label lower upper) :
    DOTCapture.Intersections.Occurrence.classifier label
      ({ lower := lower, upper := upper } :
        Preparation.Source.MemberInterval
          (Preparation.Source.MemberExpr scope .classifier)) ∈
      rawOccurrences interface := by
  induction occurrence with
  | here => exact .head _
  | left occurrence induction =>
      exact List.mem_append.mpr (.inl induction)
  | right occurrence induction =>
      exact List.mem_append.mpr (.inr induction)

end RawOccurrence

/-! ## Preparation retention -/

/-- One normalized source interval appears, translated, under its label's
allocated target member. -/
def Retained {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : SourceOccurrence sourceScope)
    (entries : List (PreparedEntry targetScope)) : Prop :=
  match source with
  | .type label interval =>
      ∃ name, ∃ intervals, ∃ translated,
        PreparedEntry.type label name intervals ∈ entries ∧
        translated ∈ intervals ∧
        Preparation.Compile.translateMemberIntervals layout members
          [interval] = .ok [translated]
  | .capture label interval =>
      ∃ name, ∃ intervals, ∃ translated,
        PreparedEntry.capture label name intervals ∈ entries ∧
        translated ∈ intervals ∧
        Preparation.Compile.translateMemberIntervals layout members
          [interval] = .ok [translated]
  | .classifier label interval =>
      ∃ name, ∃ intervals, ∃ translated,
        PreparedEntry.classifier label name intervals ∈ entries ∧
        translated ∈ intervals ∧
        Preparation.Compile.translateMemberIntervals layout members
          [interval] = .ok [translated]

private theorem Retained.cons
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    {layout : Layout sourceScope targetScope}
    {members : List (MemberName targetScope)}
    {source : SourceOccurrence sourceScope}
    {entries : List (PreparedEntry targetScope)}
    (head : PreparedEntry targetScope)
    (retained : Retained layout members source entries) :
    Retained layout members source (head :: entries) := by
  cases source with
  | type label interval =>
      obtain ⟨name, intervals, translated, entryMember, intervalMember,
        translatedResult⟩ := retained
      exact ⟨name, intervals, translated, .tail _ entryMember,
        intervalMember, translatedResult⟩
  | capture label interval =>
      obtain ⟨name, intervals, translated, entryMember, intervalMember,
        translatedResult⟩ := retained
      exact ⟨name, intervals, translated, .tail _ entryMember,
        intervalMember, translatedResult⟩
  | classifier label interval =>
      obtain ⟨name, intervals, translated, entryMember, intervalMember,
        translatedResult⟩ := retained
      exact ⟨name, intervals, translated, .tail _ entryMember,
        intervalMember, translatedResult⟩

/-- List translation retains each input interval and records the exact
singleton translation equation used by a raw occurrence. -/
private theorem translateMemberIntervals_retains
    {sort : DOTCapture.Intersections.StaticSort}
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (sourceIntervals : List (Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope sort)))
    {targetIntervals : List (Preparation.Source.MemberInterval
      (Preparation.Target.StaticExpr
        (DOTCaptureToManySortedFC.Intersections.Encoding.targetSort sort)
        targetScope))}
    (success : Preparation.Compile.translateMemberIntervals layout members
      sourceIntervals = .ok targetIntervals)
    {sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope sort)}
    (membership : sourceInterval ∈ sourceIntervals) :
    ∃ targetInterval ∈ targetIntervals,
      Preparation.Compile.translateMemberIntervals layout members
        [sourceInterval] = .ok [targetInterval] := by
  induction sourceIntervals generalizing targetIntervals with
  | nil => cases membership
  | cons current remaining induction =>
      rw [Preparation.Compile.translateMemberIntervals_cons] at success
      cases lowerResult : Preparation.Compile.translateMemberExpr layout
          members current.lower with
      | error failure =>
          rw [lowerResult] at success
          nomatch success
      | ok translatedLower =>
          cases upperResult : Preparation.Compile.translateMemberExpr layout
              members current.upper with
          | error failure =>
              rw [lowerResult, upperResult] at success
              nomatch success
          | ok translatedUpper =>
              cases tailResult :
                  Preparation.Compile.translateMemberIntervals layout members
                    remaining with
              | error failure =>
                  rw [lowerResult, upperResult, tailResult] at success
                  nomatch success
              | ok translatedRemaining =>
                  rw [lowerResult, upperResult, tailResult] at success
                  injection success with targetIntervalsEq
                  subst targetIntervals
                  rcases List.mem_cons.mp membership with rfl | tailMembership
                  · refine ⟨⟨translatedLower, translatedUpper⟩, .head _, ?_⟩
                    rw [Preparation.Compile.translateMemberIntervals_cons,
                      lowerResult, upperResult,
                      Preparation.Compile.translateMemberIntervals_nil]
                    rfl
                  · obtain ⟨translated, translatedMember,
                        singletonResult⟩ :=
                      induction tailResult tailMembership
                    exact ⟨translated, .tail _ translatedMember,
                      singletonResult⟩

/-- Successful entry preparation retains every normalized occurrence under
the entry's one allocated name. -/
theorem entries_retain_occurrence
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (allMembers : List (MemberName targetScope))
    (sourceEntries : List (Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr sourceScope)))
    (allocated : List (MemberName targetScope))
    {preparedEntries : List (PreparedEntry targetScope)}
    (success : Preparation.Compile.entries layout allMembers sourceEntries
      allocated = .ok preparedEntries)
    (source : SourceOccurrence sourceScope)
    (membership : source ∈
      ({ entries := sourceEntries } : Preparation.Source.MemberSignature
        (Preparation.Source.MemberExpr sourceScope)).occurrences) :
    Retained layout allMembers source preparedEntries := by
  induction sourceEntries generalizing allocated preparedEntries with
  | nil => cases membership
  | cons sourceEntry remaining induction =>
      simp only [DOTCapture.Intersections.Signature.occurrences,
        List.flatMap_cons, List.mem_append] at membership
      rcases membership with headMembership | tailMembership
      · cases sourceEntry with
        | type label sourceIntervals =>
            obtain ⟨sourceInterval, sourceIntervalMember, rfl⟩ :=
              List.mem_map.mp headMembership
            cases allocated with
            | nil => simp [Preparation.Compile.entries] at success
            | cons allocatedHead allocatedRemaining =>
                cases allocatedHead with
                | capture allocatedLabel name =>
                    simp [Preparation.Compile.entries] at success
                | classifier allocatedLabel name =>
                    simp [Preparation.Compile.entries] at success
                | type allocatedLabel name =>
                    by_cases labelsMatch : label = allocatedLabel
                    · subst allocatedLabel
                      simp only [Preparation.Compile.entries] at success
                      cases intervalResult :
                          Preparation.Compile.translateMemberIntervals layout
                            allMembers sourceIntervals with
                      | error failure =>
                          rw [intervalResult] at success
                          nomatch success
                      | ok translatedIntervals =>
                          cases remainingResult :
                              Preparation.Compile.entries layout allMembers
                                remaining allocatedRemaining with
                          | error failure =>
                              rw [intervalResult, remainingResult] at success
                              nomatch success
                          | ok translatedRemaining =>
                              rw [intervalResult, remainingResult] at success
                              injection success with preparedEntriesEq
                              subst preparedEntries
                              obtain ⟨translated, translatedMember,
                                  singletonResult⟩ :=
                                translateMemberIntervals_retains layout
                                  allMembers sourceIntervals intervalResult
                                  sourceIntervalMember
                              exact ⟨name, translatedIntervals, translated,
                                .head _, translatedMember, singletonResult⟩
                    · simp [Preparation.Compile.entries, labelsMatch]
                        at success
        | capture label sourceIntervals =>
            obtain ⟨sourceInterval, sourceIntervalMember, rfl⟩ :=
              List.mem_map.mp headMembership
            cases allocated with
            | nil => simp [Preparation.Compile.entries] at success
            | cons allocatedHead allocatedRemaining =>
                cases allocatedHead with
                | type allocatedLabel name =>
                    simp [Preparation.Compile.entries] at success
                | classifier allocatedLabel name =>
                    simp [Preparation.Compile.entries] at success
                | capture allocatedLabel name =>
                    by_cases labelsMatch : label = allocatedLabel
                    · subst allocatedLabel
                      simp only [Preparation.Compile.entries] at success
                      cases intervalResult :
                          Preparation.Compile.translateMemberIntervals layout
                            allMembers sourceIntervals with
                      | error failure =>
                          rw [intervalResult] at success
                          nomatch success
                      | ok translatedIntervals =>
                          cases remainingResult :
                              Preparation.Compile.entries layout allMembers
                                remaining allocatedRemaining with
                          | error failure =>
                              rw [intervalResult, remainingResult] at success
                              nomatch success
                          | ok translatedRemaining =>
                              rw [intervalResult, remainingResult] at success
                              injection success with preparedEntriesEq
                              subst preparedEntries
                              obtain ⟨translated, translatedMember,
                                  singletonResult⟩ :=
                                translateMemberIntervals_retains layout
                                  allMembers sourceIntervals intervalResult
                                  sourceIntervalMember
                              exact ⟨name, translatedIntervals, translated,
                                .head _, translatedMember, singletonResult⟩
                    · simp [Preparation.Compile.entries, labelsMatch]
                        at success
        | classifier label sourceIntervals =>
            obtain ⟨sourceInterval, sourceIntervalMember, rfl⟩ :=
              List.mem_map.mp headMembership
            cases allocated with
            | nil => simp [Preparation.Compile.entries] at success
            | cons allocatedHead allocatedRemaining =>
                cases allocatedHead with
                | type allocatedLabel name =>
                    simp [Preparation.Compile.entries] at success
                | capture allocatedLabel name =>
                    simp [Preparation.Compile.entries] at success
                | classifier allocatedLabel name =>
                    by_cases labelsMatch : label = allocatedLabel
                    · subst allocatedLabel
                      simp only [Preparation.Compile.entries] at success
                      cases intervalResult :
                          Preparation.Compile.translateMemberIntervals layout
                            allMembers sourceIntervals with
                      | error failure =>
                          rw [intervalResult] at success
                          nomatch success
                      | ok translatedIntervals =>
                          cases remainingResult :
                              Preparation.Compile.entries layout allMembers
                                remaining allocatedRemaining with
                          | error failure =>
                              rw [intervalResult, remainingResult] at success
                              nomatch success
                          | ok translatedRemaining =>
                              rw [intervalResult, remainingResult] at success
                              injection success with preparedEntriesEq
                              subst preparedEntries
                              obtain ⟨translated, translatedMember,
                                  singletonResult⟩ :=
                                translateMemberIntervals_retains layout
                                  allMembers sourceIntervals intervalResult
                                  sourceIntervalMember
                              exact ⟨name, translatedIntervals, translated,
                                .head _, translatedMember, singletonResult⟩
                    · simp [Preparation.Compile.entries, labelsMatch]
                        at success
      · cases allocated with
        | nil =>
            cases sourceEntry <;>
              simp [Preparation.Compile.entries] at success
        | cons allocatedHead allocatedRemaining =>
            cases sourceEntry with
            | type label sourceIntervals =>
                cases allocatedHead with
                | capture allocatedLabel name =>
                    simp [Preparation.Compile.entries] at success
                | classifier allocatedLabel name =>
                    simp [Preparation.Compile.entries] at success
                | type allocatedLabel name =>
                    by_cases labelsMatch : label = allocatedLabel
                    · simp only [Preparation.Compile.entries, labelsMatch]
                        at success
                      cases intervalResult :
                          Preparation.Compile.translateMemberIntervals layout
                            allMembers sourceIntervals with
                      | error failure =>
                          rw [intervalResult] at success
                          nomatch success
                      | ok translatedIntervals =>
                          cases remainingResult :
                              Preparation.Compile.entries layout allMembers
                                remaining allocatedRemaining with
                          | error failure =>
                              rw [intervalResult, remainingResult] at success
                              nomatch success
                          | ok translatedRemaining =>
                              rw [intervalResult, remainingResult] at success
                              injection success with preparedEntriesEq
                              subst preparedEntries
                              exact Retained.cons _
                                (induction allocatedRemaining
                                  remainingResult tailMembership)
                    · simp [Preparation.Compile.entries, labelsMatch]
                        at success
            | capture label sourceIntervals =>
                cases allocatedHead with
                | type allocatedLabel name =>
                    simp [Preparation.Compile.entries] at success
                | classifier allocatedLabel name =>
                    simp [Preparation.Compile.entries] at success
                | capture allocatedLabel name =>
                    by_cases labelsMatch : label = allocatedLabel
                    · simp only [Preparation.Compile.entries, labelsMatch]
                        at success
                      cases intervalResult :
                          Preparation.Compile.translateMemberIntervals layout
                            allMembers sourceIntervals with
                      | error failure =>
                          rw [intervalResult] at success
                          nomatch success
                      | ok translatedIntervals =>
                          cases remainingResult :
                              Preparation.Compile.entries layout allMembers
                                remaining allocatedRemaining with
                          | error failure =>
                              rw [intervalResult, remainingResult] at success
                              nomatch success
                          | ok translatedRemaining =>
                              rw [intervalResult, remainingResult] at success
                              injection success with preparedEntriesEq
                              subst preparedEntries
                              exact Retained.cons _
                                (induction allocatedRemaining
                                  remainingResult tailMembership)
                    · simp [Preparation.Compile.entries, labelsMatch]
                        at success
            | classifier label sourceIntervals =>
                cases allocatedHead with
                | type allocatedLabel name =>
                    simp [Preparation.Compile.entries] at success
                | capture allocatedLabel name =>
                    simp [Preparation.Compile.entries] at success
                | classifier allocatedLabel name =>
                    by_cases labelsMatch : label = allocatedLabel
                    · simp only [Preparation.Compile.entries, labelsMatch]
                        at success
                      cases intervalResult :
                          Preparation.Compile.translateMemberIntervals layout
                            allMembers sourceIntervals with
                      | error failure =>
                          rw [intervalResult] at success
                          nomatch success
                      | ok translatedIntervals =>
                          cases remainingResult :
                              Preparation.Compile.entries layout allMembers
                                remaining allocatedRemaining with
                          | error failure =>
                              rw [intervalResult, remainingResult] at success
                              nomatch success
                          | ok translatedRemaining =>
                              rw [intervalResult, remainingResult] at success
                              injection success with preparedEntriesEq
                              subst preparedEntries
                              exact Retained.cons _
                                (induction allocatedRemaining
                                  remainingResult tailMembership)
                    · simp [Preparation.Compile.entries, labelsMatch]
                        at success

/-- Entry preparation copies the allocation table exactly. -/
theorem entries_preserve_members
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (allMembers : List (MemberName targetScope))
    (sourceEntries : List (Preparation.Source.MemberEntry
      (Preparation.Source.MemberExpr sourceScope)))
    (allocated : List (MemberName targetScope))
    {preparedEntries : List (PreparedEntry targetScope)}
    (success : Preparation.Compile.entries layout allMembers sourceEntries
      allocated = .ok preparedEntries) :
    preparedEntries.map PreparedEntry.member = allocated := by
  induction sourceEntries generalizing allocated preparedEntries with
  | nil =>
      cases allocated with
      | nil =>
          simp only [Preparation.Compile.entries, Except.ok.injEq] at success
          subst preparedEntries
          rfl
      | cons head tail => simp [Preparation.Compile.entries] at success
  | cons sourceEntry remaining induction =>
      cases allocated with
      | nil =>
          cases sourceEntry <;>
            simp [Preparation.Compile.entries] at success
      | cons allocatedHead allocatedRemaining =>
          cases sourceEntry with
          | type label sourceIntervals =>
              cases allocatedHead with
              | capture allocatedLabel name =>
                  simp [Preparation.Compile.entries] at success
              | classifier allocatedLabel name =>
                  simp [Preparation.Compile.entries] at success
              | type allocatedLabel name =>
                  by_cases labelsMatch : label = allocatedLabel
                  · subst allocatedLabel
                    simp only [Preparation.Compile.entries] at success
                    cases intervalResult :
                        Preparation.Compile.translateMemberIntervals layout
                          allMembers sourceIntervals with
                    | error failure =>
                        rw [intervalResult] at success
                        nomatch success
                    | ok translatedIntervals =>
                        cases remainingResult :
                            Preparation.Compile.entries layout allMembers
                              remaining allocatedRemaining with
                        | error failure =>
                            rw [intervalResult, remainingResult] at success
                            nomatch success
                        | ok translatedRemaining =>
                            rw [intervalResult, remainingResult] at success
                            injection success with preparedEntriesEq
                            subst preparedEntries
                            simpa [PreparedEntry.member] using congrArg
                              (fun tail => MemberName.type label name :: tail)
                              (induction allocatedRemaining remainingResult)
                  · simp [Preparation.Compile.entries, labelsMatch]
                      at success
          | capture label sourceIntervals =>
              cases allocatedHead with
              | type allocatedLabel name =>
                  simp [Preparation.Compile.entries] at success
              | classifier allocatedLabel name =>
                  simp [Preparation.Compile.entries] at success
              | capture allocatedLabel name =>
                  by_cases labelsMatch : label = allocatedLabel
                  · subst allocatedLabel
                    simp only [Preparation.Compile.entries] at success
                    cases intervalResult :
                        Preparation.Compile.translateMemberIntervals layout
                          allMembers sourceIntervals with
                    | error failure =>
                        rw [intervalResult] at success
                        nomatch success
                    | ok translatedIntervals =>
                        cases remainingResult :
                            Preparation.Compile.entries layout allMembers
                              remaining allocatedRemaining with
                        | error failure =>
                            rw [intervalResult, remainingResult] at success
                            nomatch success
                        | ok translatedRemaining =>
                            rw [intervalResult, remainingResult] at success
                            injection success with preparedEntriesEq
                            subst preparedEntries
                            simpa [PreparedEntry.member] using congrArg
                              (fun tail =>
                                MemberName.capture label name :: tail)
                              (induction allocatedRemaining remainingResult)
                  · simp [Preparation.Compile.entries, labelsMatch]
                      at success
          | classifier label sourceIntervals =>
              cases allocatedHead with
              | type allocatedLabel name =>
                  simp [Preparation.Compile.entries] at success
              | capture allocatedLabel name =>
                  simp [Preparation.Compile.entries] at success
              | classifier allocatedLabel name =>
                  by_cases labelsMatch : label = allocatedLabel
                  · subst allocatedLabel
                    simp only [Preparation.Compile.entries] at success
                    cases intervalResult :
                        Preparation.Compile.translateMemberIntervals layout
                          allMembers sourceIntervals with
                    | error failure =>
                        rw [intervalResult] at success
                        nomatch success
                    | ok translatedIntervals =>
                        cases remainingResult :
                            Preparation.Compile.entries layout allMembers
                              remaining allocatedRemaining with
                        | error failure =>
                            rw [intervalResult, remainingResult] at success
                            nomatch success
                        | ok translatedRemaining =>
                            rw [intervalResult, remainingResult] at success
                            injection success with preparedEntriesEq
                            subst preparedEntries
                            simpa [PreparedEntry.member] using congrArg
                              (fun tail =>
                                MemberName.classifier label name :: tail)
                              (induction allocatedRemaining remainingResult)
                  · simp [Preparation.Compile.entries, labelsMatch]
                      at success

/-- Successful preparation retains every normalized occurrence in the exact
prepared signature it emits. -/
theorem prepare_retains_occurrence
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (signature : Preparation.Source.MemberSignature
      (Preparation.Source.MemberExpr sourceScope))
    {prepared : PreparedSignature targetScope}
    (success : Preparation.prepare layout signature = .ok prepared)
    (source : SourceOccurrence sourceScope)
    (membership : source ∈ signature.occurrences) :
    Retained
      (layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols prepared.symbols))
      prepared.members source prepared.entries := by
  unfold Preparation.prepare at success
  let symbols := Preparation.Allocation.symbols signature.entries
  let allocated := Preparation.Allocation.members targetScope
    signature.entries
  let namesLayout := layout.renameTarget
    (ManySortedFC.Rename.weakenSymbols symbols)
  cases entriesResult : Preparation.Compile.entries namesLayout allocated
      signature.entries allocated with
  | error failure =>
      simp only [symbols, allocated, namesLayout, entriesResult, bind,
        Except.bind] at success
      nomatch success
  | ok preparedEntries =>
      cases constraintsResult :
          Preparation.Compile.translateMemberConstraints namesLayout allocated
            signature.constraints with
      | error failure =>
          simp only [symbols, allocated, namesLayout, entriesResult,
            constraintsResult, bind, Except.bind] at success
          nomatch success
      | ok preparedConstraints =>
          simp only [symbols, allocated, namesLayout, entriesResult,
            constraintsResult, bind, Except.bind, pure, Except.pure] at success
          injection success with preparedEq
          subst prepared
          have retained := entries_retain_occurrence namesLayout allocated
            signature.entries allocated entriesResult source membership
          have membersEq := entries_preserve_members namesLayout allocated
            signature.entries allocated entriesResult
          simpa [PreparedSignature.members, membersEq] using retained

/-- Collection followed by preparation retains every raw declaration
occurrence. -/
theorem collectAndPrepare_retains_raw_occurrence
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    (source : SourceOccurrence sourceScope)
    (membership : source ∈ rawOccurrences interface) :
    Retained
      (layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols prepared.symbols))
      prepared.members source prepared.entries := by
  unfold Preparation.collectAndPrepare at success
  cases collected : interface.collect with
  | error conflict =>
      rw [collected] at success
      nomatch success
  | ok signature =>
      rw [collected] at success
      have normalizedMembership : source ∈ signature.occurrences :=
        (collect_occurrences interface collected).mem_iff.mpr membership
      exact prepare_retains_occurrence layout signature success source
        normalizedMembership

/-! ## Ordinal-preserving prepared intervals -/

structure PreparedTypeIntervalAt {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label ordinal : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .type)) where
  translated : Preparation.Source.MemberInterval
    (ManySortedFC.StaticExpr .type
      (ManySortedFC.SymbolScope targetScope prepared.symbols))
  targetAt :
    (Ordered.preparedTypeIntervalsAtEntries label prepared.entries)[ordinal]? =
      some translated
  translation : Preparation.Compile.translateMemberIntervals
    (layout.renameTarget
      (ManySortedFC.Rename.weakenSymbols prepared.symbols))
    prepared.members [sourceInterval] = .ok [translated]

structure PreparedCaptureIntervalAt {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label ordinal : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .capture)) where
  translated : Preparation.Source.MemberInterval
    (ManySortedFC.StaticExpr .capture
      (ManySortedFC.SymbolScope targetScope prepared.symbols))
  targetAt :
    (Ordered.preparedCaptureIntervalsAtEntries label
      prepared.entries)[ordinal]? = some translated
  translation : Preparation.Compile.translateMemberIntervals
    (layout.renameTarget
      (ManySortedFC.Rename.weakenSymbols prepared.symbols))
    prepared.members [sourceInterval] = .ok [translated]

structure PreparedClassifierIntervalAt {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label ordinal : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .classifier)) where
  translated : Preparation.Source.MemberInterval
    (ManySortedFC.StaticExpr .classifier
      (ManySortedFC.SymbolScope targetScope prepared.symbols))
  targetAt :
    (Ordered.preparedClassifierIntervalsAtEntries label
      prepared.entries)[ordinal]? = some translated
  translation : Preparation.Compile.translateMemberIntervals
    (layout.renameTarget
      (ManySortedFC.Rename.weakenSymbols prepared.symbols))
    prepared.members [sourceInterval] = .ok [translated]

/-- Exact prepared-list coordinate for one raw mixed constraint. -/
structure PreparedConstraintAt {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (ordinal : Nat) (source : SourceConstraint sourceScope) where
  translated : PreparedConstraint
    (ManySortedFC.SymbolScope targetScope prepared.symbols)
  targetAt : prepared.constraints[ordinal]? = some translated
  translation : Preparation.Compile.translateMemberConstraint
    (layout.renameTarget
      (ManySortedFC.Rename.weakenSymbols prepared.symbols))
    prepared.members source = .ok translated

/-- A raw mixed-constraint coordinate survives collection and preparation
at the same ordinal. -/
theorem preparedConstraintAt_of_raw
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {ordinal : Nat} {source : SourceConstraint sourceScope}
    (sourceAt : (rawConstraints interface)[ordinal]? = some source) :
    Nonempty (PreparedConstraintAt layout prepared ordinal source) := by
  unfold Preparation.collectAndPrepare at success
  cases collected : interface.collect with
  | error conflict => rw [collected] at success; nomatch success
  | ok signature =>
      rw [collected] at success
      simp only [Except.mapError, bind, Except.bind] at success
      unfold Preparation.prepare at success
      let symbols := Preparation.Allocation.symbols signature.entries
      let allocated := Preparation.Allocation.members targetScope
        signature.entries
      let namesLayout := layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols symbols)
      cases entriesResult : Preparation.Compile.entries namesLayout allocated
          signature.entries allocated with
      | error failure =>
          simp only [symbols, allocated, namesLayout, entriesResult, bind,
            Except.bind] at success
          nomatch success
      | ok preparedEntries =>
          cases constraintsResult :
              Preparation.Compile.translateMemberConstraints namesLayout
                allocated signature.constraints with
          | error failure =>
              simp only [symbols, allocated, namesLayout, entriesResult,
                constraintsResult, bind, Except.bind] at success
              nomatch success
          | ok preparedConstraints =>
              simp only [symbols, allocated, namesLayout, entriesResult,
                constraintsResult, bind, Except.bind, pure, Except.pure]
                at success
              injection success with preparedEq
              subst prepared
              have normalizedAt : signature.constraints[ordinal]? =
                  some source := by
                rw [collect_constraints interface collected]
                exact sourceAt
              obtain ⟨translated, targetAt, translation⟩ :=
                Ordered.translateMemberConstraints_getElem? namesLayout
                  allocated signature.constraints constraintsResult normalizedAt
              have membersEq := entries_preserve_members namesLayout allocated
                signature.entries allocated entriesResult
              exact ⟨
                { translated, targetAt
                  translation := by
                    simpa [PreparedSignature.members, membersEq] using
                      translation }⟩

/-- The classifier-disjointness occurrence selected by the source proof
survives at its exact prepared-list coordinate. -/
theorem preparedClassifierDisjointAt_of_raw
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {left right : Preparation.Source.ClassifierExpr sourceScope}
    (occurrence : interface.HasClassifierDisjointOccurrence left right) :
    Nonempty (PreparedConstraintAt layout prepared
      (RawConstraintOccurrence.classifierDisjointOrdinal occurrence)
      (.classifierDisjoint left right)) :=
  preparedConstraintAt_of_raw layout interface success
    (RawConstraintOccurrence.classifierDisjoint_getElem?_ordinal occurrence)

/-- The capture-kind occurrence selected by the source proof survives at its
exact prepared-list coordinate. -/
theorem preparedCaptureHasKindAt_of_raw
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {capture : Preparation.Source.Capture sourceScope}
    {classifier : Preparation.Source.ClassifierExpr sourceScope}
    (occurrence : interface.HasCaptureKindOccurrence capture classifier) :
    Nonempty (PreparedConstraintAt layout prepared
      (RawConstraintOccurrence.captureHasKindOrdinal occurrence)
      (.captureHasKind (.capture capture) classifier)) :=
  preparedConstraintAt_of_raw layout interface success
    (RawConstraintOccurrence.captureHasKind_getElem?_ordinal occurrence)

/-- Exact source-to-target correspondence for a prepared mixed constraint:
the translated proposition is literally a proposition of the emitted
target theory. -/
structure ConstraintCoordinates {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (ordinal : Nat) (source : SourceConstraint sourceScope) extends
      PreparedConstraintAt layout prepared ordinal source where
  propositionMembership : translated.packed ∈
    DOTCaptureToManySortedFC.Intersections.Encoding.Target.Theory.propositions
      (encode prepared).theory
  reference : ManySortedFC.ConstraintRef prepared.relations
    translated.relation
  propositionAt : (encode prepared).theory.propositionAt reference =
    translated.proposition

/-- Promote an exact prepared coordinate to an emitted target-theory
coordinate. -/
noncomputable def constraintCoordinatesOfPrepared
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (ordinal : Nat) (source : SourceConstraint sourceScope)
    (coordinate : PreparedConstraintAt layout prepared ordinal source) :
    ConstraintCoordinates layout prepared ordinal source := by
  have membership : coordinate.translated ∈ prepared.constraints := by
    obtain ⟨inBounds, atIndex⟩ :=
      List.getElem?_eq_some_iff.mp coordinate.targetAt
    rw [← atIndex]
    exact List.getElem_mem inBounds
  have propositionMembership :=
    Encoding.contains_constraint prepared membership
  let reference := Classical.choose
    (DOTCaptureToManySortedFC.Intersections.TheoryPermutationCoherence.PackedTheory.exists_matching_reference
      (encode prepared).theory coordinate.translated.proposition
      propositionMembership)
  have propositionAt := Classical.choose_spec
    (DOTCaptureToManySortedFC.Intersections.TheoryPermutationCoherence.PackedTheory.exists_matching_reference
      (encode prepared).theory coordinate.translated.proposition
      propositionMembership)
  exact { coordinate with propositionMembership, reference, propositionAt }

/-- Total source classifier-disjointness occurrence to exact emitted target
proposition correspondence. -/
noncomputable def classifierDisjointCoordinatesOfRaw
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {left right : Preparation.Source.ClassifierExpr sourceScope}
    (occurrence : interface.HasClassifierDisjointOccurrence left right) :
    ConstraintCoordinates layout prepared
      (RawConstraintOccurrence.classifierDisjointOrdinal occurrence)
      (.classifierDisjoint left right) :=
  constraintCoordinatesOfPrepared layout prepared _ _
    (Classical.choice
      (preparedClassifierDisjointAt_of_raw layout interface success occurrence))

/-- Total source capture-kind occurrence to exact emitted target proposition
correspondence. -/
noncomputable def captureHasKindCoordinatesOfRaw
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {capture : Preparation.Source.Capture sourceScope}
    {classifier : Preparation.Source.ClassifierExpr sourceScope}
    (occurrence : interface.HasCaptureKindOccurrence capture classifier) :
    ConstraintCoordinates layout prepared
      (RawConstraintOccurrence.captureHasKindOrdinal occurrence)
      (.captureHasKind (.capture capture) classifier) :=
  constraintCoordinatesOfPrepared layout prepared _ _
    (Classical.choice
      (preparedCaptureHasKindAt_of_raw layout interface success occurrence))

namespace ConstraintCoordinates

/-- The exact mixed-constraint reference looks up the translated proposition
in every ambient context extended by the generated theory. -/
theorem lookup
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    {layout : Layout sourceScope targetScope}
    {prepared : PreparedSignature targetScope}
    {ordinal : Nat} {source : SourceConstraint sourceScope}
    (coordinate : ConstraintCoordinates layout prepared ordinal source)
    (context : ManySortedFC.Ctx targetScope) :
    (context.extendTheory (encode prepared).theory).lookup
        (coordinate.reference.toEvidenceBVar
          (ManySortedFC.SymbolScope targetScope prepared.symbols)) =
      .evidence
        (coordinate.translated.proposition.rename
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope targetScope prepared.symbols)
            (ManySortedFC.evidenceKinds prepared.relations))) := by
  unfold ManySortedFC.Ctx.extendTheory
  change
    (ManySortedFC.Ctx.extendTheoryEvidence
      (context.extendSymbols prepared.symbols) (encode prepared).theory).lookup
        (coordinate.reference.toEvidenceBVar
          (ManySortedFC.SymbolScope targetScope prepared.symbols)) = _
  have found := ManySortedFC.Ctx.lookup_extendTheoryEvidence_constraint
    (context.extendSymbols prepared.symbols) (encode prepared).theory
      coordinate.reference
  have propositionAt := coordinate.propositionAt
  simp only [encode] at propositionAt found ⊢
  rw [propositionAt] at found
  exact found

end ConstraintCoordinates

/-- A raw type-occurrence proof selects the same ordinal after collection
and preparation. -/
theorem preparedTypeIntervalAt_of_raw
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {label : Nat} {lower upper : Preparation.Source.Ty sourceScope}
    (occurrence : interface.HasTypeOccurrence label lower upper) :
    Nonempty (PreparedTypeIntervalAt layout prepared label
      (RawOccurrence.typeOrdinal occurrence)
      { lower := .type lower, upper := .type upper }) := by
  unfold Preparation.collectAndPrepare at success
  cases collected : interface.collect with
  | error conflict => rw [collected] at success; nomatch success
  | ok signature =>
      rw [collected] at success
      simp only [Except.mapError, bind, Except.bind] at success
      unfold Preparation.prepare at success
      let symbols := Preparation.Allocation.symbols signature.entries
      let allocated := Preparation.Allocation.members targetScope
        signature.entries
      let namesLayout := layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols symbols)
      cases entriesResult : Preparation.Compile.entries namesLayout allocated
          signature.entries allocated with
      | error failure =>
          simp only [symbols, allocated, namesLayout, entriesResult, bind,
            Except.bind] at success
          nomatch success
      | ok preparedEntries =>
          cases constraintsResult :
              Preparation.Compile.translateMemberConstraints namesLayout
                allocated signature.constraints with
          | error failure =>
              simp only [symbols, allocated, namesLayout, entriesResult,
                constraintsResult, bind, Except.bind] at success
              nomatch success
          | ok preparedConstraints =>
            simp only [symbols, allocated, namesLayout, entriesResult,
              constraintsResult, bind, Except.bind, pure, Except.pure] at success
            injection success with preparedEq
            subst prepared
            have normalizedAt :
              (Ordered.typeIntervalsAt signature label)[
                  RawOccurrence.typeOrdinal occurrence]? =
                some { lower := .type lower, upper := .type upper } := by
              rw [Ordered.collect_typeIntervalsAt interface collected label]
              exact RawOccurrence.type_getElem?_ordinal occurrence
            have translatedAll :=
              (Ordered.entries_ordered namesLayout allocated signature.entries
                allocated entriesResult label).1
            obtain ⟨translated, targetAt, singleton⟩ :=
              Ordered.translateMemberIntervals_getElem? namesLayout allocated
                (Ordered.typeIntervalsAt signature label) translatedAll
                  normalizedAt
            have membersEq := entries_preserve_members namesLayout allocated
              signature.entries allocated entriesResult
            exact ⟨
              { translated, targetAt
                translation := by
                  simpa [PreparedSignature.members, membersEq] using singleton }⟩

/-- Capture-sorted counterpart of `preparedTypeIntervalAt_of_raw`. -/
theorem preparedCaptureIntervalAt_of_raw
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {label : Nat}
    {lower upper : Preparation.Source.Capture sourceScope}
    (occurrence : interface.HasCaptureOccurrence label lower upper) :
    Nonempty (PreparedCaptureIntervalAt layout prepared label
      (RawOccurrence.captureOrdinal occurrence)
      { lower := .capture lower, upper := .capture upper }) := by
  unfold Preparation.collectAndPrepare at success
  cases collected : interface.collect with
  | error conflict => rw [collected] at success; nomatch success
  | ok signature =>
      rw [collected] at success
      simp only [Except.mapError, bind, Except.bind] at success
      unfold Preparation.prepare at success
      let symbols := Preparation.Allocation.symbols signature.entries
      let allocated := Preparation.Allocation.members targetScope
        signature.entries
      let namesLayout := layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols symbols)
      cases entriesResult : Preparation.Compile.entries namesLayout allocated
          signature.entries allocated with
      | error failure =>
          simp only [symbols, allocated, namesLayout, entriesResult, bind,
            Except.bind] at success
          nomatch success
      | ok preparedEntries =>
          cases constraintsResult :
              Preparation.Compile.translateMemberConstraints namesLayout
                allocated signature.constraints with
          | error failure =>
              simp only [symbols, allocated, namesLayout, entriesResult,
                constraintsResult, bind, Except.bind] at success
              nomatch success
          | ok preparedConstraints =>
            simp only [symbols, allocated, namesLayout, entriesResult,
              constraintsResult, bind, Except.bind, pure, Except.pure] at success
            injection success with preparedEq
            subst prepared
            have normalizedAt :
              (Ordered.captureIntervalsAt signature label)[
                  RawOccurrence.captureOrdinal occurrence]? =
                some { lower := .capture lower, upper := .capture upper } := by
              rw [Ordered.collect_captureIntervalsAt interface collected label]
              exact RawOccurrence.capture_getElem?_ordinal occurrence
            have translatedAll :=
              (Ordered.entries_ordered namesLayout allocated signature.entries
                allocated entriesResult label).2
            obtain ⟨translated, targetAt, singleton⟩ :=
              Ordered.translateMemberIntervals_getElem? namesLayout allocated
                (Ordered.captureIntervalsAt signature label) translatedAll
                  normalizedAt
            have membersEq := entries_preserve_members namesLayout allocated
              signature.entries allocated entriesResult
            exact ⟨
              { translated, targetAt
                translation := by
                  simpa [PreparedSignature.members, membersEq] using singleton }⟩

/-- Classifier-sorted counterpart of `preparedTypeIntervalAt_of_raw`.  This
uses the proof-selected same-label ordinal, so duplicate declarations do not
collapse onto one existentially chosen target occurrence. -/
theorem preparedClassifierIntervalAt_of_raw
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {label : Nat}
    {lower upper : Preparation.Source.ClassifierExpr sourceScope}
    (occurrence : interface.HasClassifierOccurrence label lower upper) :
    Nonempty (PreparedClassifierIntervalAt layout prepared label
      (RawOccurrence.classifierOrdinal occurrence)
      { lower, upper }) := by
  unfold Preparation.collectAndPrepare at success
  cases collected : interface.collect with
  | error conflict => rw [collected] at success; nomatch success
  | ok signature =>
      rw [collected] at success
      simp only [Except.mapError, bind, Except.bind] at success
      unfold Preparation.prepare at success
      let symbols := Preparation.Allocation.symbols signature.entries
      let allocated := Preparation.Allocation.members targetScope
        signature.entries
      let namesLayout := layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols symbols)
      cases entriesResult : Preparation.Compile.entries namesLayout allocated
          signature.entries allocated with
      | error failure =>
          simp only [symbols, allocated, namesLayout, entriesResult, bind,
            Except.bind] at success
          nomatch success
      | ok preparedEntries =>
          cases constraintsResult :
              Preparation.Compile.translateMemberConstraints namesLayout
                allocated signature.constraints with
          | error failure =>
              simp only [symbols, allocated, namesLayout, entriesResult,
                constraintsResult, bind, Except.bind] at success
              nomatch success
          | ok preparedConstraints =>
            simp only [symbols, allocated, namesLayout, entriesResult,
              constraintsResult, bind, Except.bind, pure, Except.pure] at success
            injection success with preparedEq
            subst prepared
            have normalizedAt :
              (Ordered.classifierIntervalsAt signature label)[
                  RawOccurrence.classifierOrdinal occurrence]? =
                some { lower, upper } := by
              rw [Ordered.collect_classifierIntervalsAt interface collected
                label]
              exact RawOccurrence.classifier_getElem?_ordinal occurrence
            have translatedAll :=
              Ordered.entries_classifier_ordered namesLayout allocated
                signature.entries allocated entriesResult label
            obtain ⟨translated, targetAt, singleton⟩ :=
              Ordered.translateMemberIntervals_getElem? namesLayout allocated
                (Ordered.classifierIntervalsAt signature label) translatedAll
                  normalizedAt
            have membersEq := entries_preserve_members namesLayout allocated
              signature.entries allocated entriesResult
            exact ⟨
              { translated, targetAt
                translation := by
                  simpa [PreparedSignature.members, membersEq] using singleton }⟩

/-! ## Exact target constraint coordinates -/

/-! The executable compiler consumes `Encoding.openedOccurrences`, whereas
the retention proof above is phrased over prepared entries.  These two
lemmas connect one retained interval to the exact occurrence enumeration.
They retain the concrete evidence binders generated for the occurrence; no
search through an ambient context is involved. -/

private theorem openTypeIntervals_contains
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (label : Nat)
    (name : ManySortedFC.BVar (ManySortedFC.SymbolScope scope symbols)
      (.symbol .type))
    (intervals : List (Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .type
        (ManySortedFC.SymbolScope scope symbols))))
    (tailRelations : List ManySortedFC.Relation)
    (tail : List (OpenedOccurrence scope symbols tailRelations))
    {interval : Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .type
        (ManySortedFC.SymbolScope scope symbols))}
    (membership : interval ∈ intervals) :
    ∃ lowerEvidence upperEvidence,
      OpenedOccurrence.type label
        ((ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope scope symbols)
          (ManySortedFC.evidenceKinds
            (PreparedEntry.intervalRelations .type intervals ++
              tailRelations))).var name)
        (interval.lower.rename
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedEntry.intervalRelations .type intervals ++
                tailRelations))))
        (interval.upper.rename
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedEntry.intervalRelations .type intervals ++
                tailRelations))))
        lowerEvidence upperEvidence ∈
          openTypeIntervals label name intervals tailRelations tail := by
  induction intervals with
  | nil => cases membership
  | cons current remaining induction =>
      rcases List.mem_cons.mp membership with rfl | membership
      · exact ⟨.here, .there .here, .head _⟩
      · obtain ⟨lowerEvidence, upperEvidence, retained⟩ :=
          induction membership
        let older := OpenedOccurrence.type label
          ((ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedEntry.intervalRelations .type remaining ++
                tailRelations))).var name)
          (interval.lower.rename
            (ManySortedFC.Rename.weakenMany
              (ManySortedFC.SymbolScope scope symbols)
              (ManySortedFC.evidenceKinds
                (PreparedEntry.intervalRelations .type remaining ++
                  tailRelations))))
          (interval.upper.rename
            (ManySortedFC.Rename.weakenMany
              (ManySortedFC.SymbolScope scope symbols)
              (ManySortedFC.evidenceKinds
                (PreparedEntry.intervalRelations .type remaining ++
                  tailRelations))))
          lowerEvidence upperEvidence
        have mapped : older.weakenTwo (.inclusion .type) (.inclusion .type) ∈
            (openTypeIntervals label name remaining tailRelations tail).map
              (fun occurrence => occurrence.weakenTwo
                (.inclusion .type) (.inclusion .type)) :=
          List.mem_map.mpr ⟨older, retained, rfl⟩
        have olderShape : older.weakenTwo (.inclusion .type)
            (.inclusion .type) =
            OpenedOccurrence.type label
              ((ManySortedFC.Rename.weakenMany
                (ManySortedFC.SymbolScope scope symbols)
                (ManySortedFC.evidenceKinds
                  (PreparedEntry.intervalRelations .type
                    (current :: remaining) ++ tailRelations))).var name)
              (interval.lower.rename
                (ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .type
                      (current :: remaining) ++ tailRelations))))
              (interval.upper.rename
                (ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .type
                      (current :: remaining) ++ tailRelations))))
              (older.weakenTwo (.inclusion .type)
                (.inclusion .type)).lowerEvidence
              (older.weakenTwo (.inclusion .type)
                (.inclusion .type)).upperEvidence := by
          simp only [older, OpenedOccurrence.weakenTwo,
            OpenedOccurrence.lowerEvidence, OpenedOccurrence.upperEvidence]
          congr 1 <;>
            simp [PreparedEntry.intervalRelations,
              ManySortedFC.evidenceKinds, ManySortedFC.Rename.weakenMany,
              ManySortedFC.Rename.comp, ManySortedFC.Rename.succ,
              ManySortedFC.StaticExpr.rename_comp] <;> rfl
        refine ⟨(older.weakenTwo (.inclusion .type)
            (.inclusion .type)).lowerEvidence,
          (older.weakenTwo (.inclusion .type)
            (.inclusion .type)).upperEvidence, ?_⟩
        simp only [openTypeIntervals]
        exact List.mem_cons.mpr (.inr (olderShape ▸ mapped))

private theorem openCaptureIntervals_contains
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (label : Nat)
    (name : ManySortedFC.BVar (ManySortedFC.SymbolScope scope symbols)
      (.symbol .capture))
    (intervals : List (Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .capture
        (ManySortedFC.SymbolScope scope symbols))))
    (tailRelations : List ManySortedFC.Relation)
    (tail : List (OpenedOccurrence scope symbols tailRelations))
    {interval : Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .capture
        (ManySortedFC.SymbolScope scope symbols))}
    (membership : interval ∈ intervals) :
    ∃ lowerEvidence upperEvidence,
      OpenedOccurrence.capture label
        ((ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope scope symbols)
          (ManySortedFC.evidenceKinds
            (PreparedEntry.intervalRelations .capture intervals ++
              tailRelations))).var name)
        (interval.lower.rename
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedEntry.intervalRelations .capture intervals ++
                tailRelations))))
        (interval.upper.rename
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedEntry.intervalRelations .capture intervals ++
                tailRelations))))
        lowerEvidence upperEvidence ∈
          openCaptureIntervals label name intervals tailRelations tail := by
  induction intervals with
  | nil => cases membership
  | cons current remaining induction =>
      rcases List.mem_cons.mp membership with rfl | membership
      · exact ⟨.here, .there .here, .head _⟩
      · obtain ⟨lowerEvidence, upperEvidence, retained⟩ :=
          induction membership
        let older := OpenedOccurrence.capture label
          ((ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedEntry.intervalRelations .capture remaining ++
                tailRelations))).var name)
          (interval.lower.rename
            (ManySortedFC.Rename.weakenMany
              (ManySortedFC.SymbolScope scope symbols)
              (ManySortedFC.evidenceKinds
                (PreparedEntry.intervalRelations .capture remaining ++
                  tailRelations))))
          (interval.upper.rename
            (ManySortedFC.Rename.weakenMany
              (ManySortedFC.SymbolScope scope symbols)
              (ManySortedFC.evidenceKinds
                (PreparedEntry.intervalRelations .capture remaining ++
                  tailRelations))))
          lowerEvidence upperEvidence
        have mapped : older.weakenTwo (.inclusion .capture)
            (.inclusion .capture) ∈
            (openCaptureIntervals label name remaining tailRelations tail).map
              (fun occurrence => occurrence.weakenTwo
                (.inclusion .capture) (.inclusion .capture)) :=
          List.mem_map.mpr ⟨older, retained, rfl⟩
        have olderShape : older.weakenTwo (.inclusion .capture)
            (.inclusion .capture) =
            OpenedOccurrence.capture label
              ((ManySortedFC.Rename.weakenMany
                (ManySortedFC.SymbolScope scope symbols)
                (ManySortedFC.evidenceKinds
                  (PreparedEntry.intervalRelations .capture
                    (current :: remaining) ++ tailRelations))).var name)
              (interval.lower.rename
                (ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .capture
                      (current :: remaining) ++ tailRelations))))
              (interval.upper.rename
                (ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .capture
                      (current :: remaining) ++ tailRelations))))
              (older.weakenTwo (.inclusion .capture)
                (.inclusion .capture)).lowerEvidence
              (older.weakenTwo (.inclusion .capture)
                (.inclusion .capture)).upperEvidence := by
          simp only [older, OpenedOccurrence.weakenTwo,
            OpenedOccurrence.lowerEvidence, OpenedOccurrence.upperEvidence]
          congr 1 <;>
            simp [PreparedEntry.intervalRelations,
              ManySortedFC.evidenceKinds, ManySortedFC.Rename.weakenMany,
              ManySortedFC.Rename.comp, ManySortedFC.Rename.succ,
              ManySortedFC.StaticExpr.rename_comp] <;> rfl
        refine ⟨(older.weakenTwo (.inclusion .capture)
            (.inclusion .capture)).lowerEvidence,
          (older.weakenTwo (.inclusion .capture)
            (.inclusion .capture)).upperEvidence, ?_⟩
        simp only [openCaptureIntervals]
        exact List.mem_cons.mpr (.inr (olderShape ▸ mapped))

private def renameOpenedOccurrence {scope : ManySortedFC.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {firstRelations secondRelations : List ManySortedFC.Relation}
    (rho : ManySortedFC.Rename
      (ManySortedFC.StaticScope scope symbols firstRelations)
      (ManySortedFC.StaticScope scope symbols secondRelations)) :
    OpenedOccurrence scope symbols firstRelations ->
      OpenedOccurrence scope symbols secondRelations
  | .type label name lower upper lowerEvidence upperEvidence =>
      .type label (rho.var name) (lower.rename rho) (upper.rename rho)
        (rho.var lowerEvidence) (rho.var upperEvidence)
  | .capture label name lower upper lowerEvidence upperEvidence =>
      .capture label (rho.var name) (lower.rename rho) (upper.rename rho)
        (rho.var lowerEvidence) (rho.var upperEvidence)
  | .classifier label name lower upper lowerEvidence upperEvidence =>
      .classifier label (rho.var name) (lower.rename rho) (upper.rename rho)
        (rho.var lowerEvidence) (rho.var upperEvidence)

def openedTypeIntervalsAt {scope : ManySortedFC.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation} (label : Nat) :
    List (OpenedOccurrence scope symbols relations) ->
      List (Preparation.Source.MemberInterval
        (ManySortedFC.StaticExpr .type
          (ManySortedFC.StaticScope scope symbols relations)))
  | [] => []
  | .type candidate _ lower upper _ _ :: remaining =>
      (if candidate = label then [{ lower, upper }] else []) ++
        openedTypeIntervalsAt label remaining
  | .capture _ _ _ _ _ _ :: remaining =>
      openedTypeIntervalsAt label remaining
  | .classifier _ _ _ _ _ _ :: remaining =>
      openedTypeIntervalsAt label remaining

def openedCaptureIntervalsAt {scope : ManySortedFC.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation} (label : Nat) :
    List (OpenedOccurrence scope symbols relations) ->
      List (Preparation.Source.MemberInterval
        (ManySortedFC.StaticExpr .capture
          (ManySortedFC.StaticScope scope symbols relations)))
  | [] => []
  | .type _ _ _ _ _ _ :: remaining =>
      openedCaptureIntervalsAt label remaining
  | .capture candidate _ lower upper _ _ :: remaining =>
      (if candidate = label then [{ lower, upper }] else []) ++
        openedCaptureIntervalsAt label remaining
  | .classifier _ _ _ _ _ _ :: remaining =>
      openedCaptureIntervalsAt label remaining

def openedClassifierIntervalsAt {scope : ManySortedFC.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation} (label : Nat) :
    List (OpenedOccurrence scope symbols relations) ->
      List (Preparation.Source.MemberInterval
        (ManySortedFC.StaticExpr .classifier
          (ManySortedFC.StaticScope scope symbols relations)))
  | [] => []
  | .type _ _ _ _ _ _ :: remaining =>
      openedClassifierIntervalsAt label remaining
  | .capture _ _ _ _ _ _ :: remaining =>
      openedClassifierIntervalsAt label remaining
  | .classifier candidate _ lower upper _ _ :: remaining =>
      (if candidate = label then [{ lower, upper }] else []) ++
        openedClassifierIntervalsAt label remaining

private def renameTypeInterval {first second : ManySortedFC.Sig}
    (rho : ManySortedFC.Rename first second)
    (interval : Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .type first)) :
    Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .type second) :=
  { lower := interval.lower.rename rho, upper := interval.upper.rename rho }

private def renameCaptureInterval {first second : ManySortedFC.Sig}
    (rho : ManySortedFC.Rename first second)
    (interval : Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .capture first)) :
    Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .capture second) :=
  { lower := interval.lower.rename rho, upper := interval.upper.rename rho }

private def renameClassifierInterval {first second : ManySortedFC.Sig}
    (rho : ManySortedFC.Rename first second)
    (interval : Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .classifier first)) :
    Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .classifier second) :=
  { lower := interval.lower.rename rho, upper := interval.upper.rename rho }

private theorem openedTypeIntervalsAt_rename {scope : ManySortedFC.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {firstRelations secondRelations : List ManySortedFC.Relation}
    (rho : ManySortedFC.Rename
      (ManySortedFC.StaticScope scope symbols firstRelations)
      (ManySortedFC.StaticScope scope symbols secondRelations))
    (label : Nat)
    (occurrences : List (OpenedOccurrence scope symbols firstRelations)) :
    openedTypeIntervalsAt label
        (occurrences.map (renameOpenedOccurrence rho)) =
      (openedTypeIntervalsAt label occurrences).map
        (renameTypeInterval rho) := by
  induction occurrences with
  | nil => rfl
  | cons occurrence remaining induction =>
      cases occurrence with
      | type candidate name lower upper lowerEvidence upperEvidence =>
          by_cases same : candidate = label <;>
            simp [openedTypeIntervalsAt, renameOpenedOccurrence,
              renameTypeInterval, same, induction]
      | capture =>
          simpa [openedTypeIntervalsAt, renameOpenedOccurrence] using induction
      | classifier =>
          simpa [openedTypeIntervalsAt, renameOpenedOccurrence] using induction

private theorem openedCaptureIntervalsAt_rename {scope : ManySortedFC.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {firstRelations secondRelations : List ManySortedFC.Relation}
    (rho : ManySortedFC.Rename
      (ManySortedFC.StaticScope scope symbols firstRelations)
      (ManySortedFC.StaticScope scope symbols secondRelations))
    (label : Nat)
    (occurrences : List (OpenedOccurrence scope symbols firstRelations)) :
    openedCaptureIntervalsAt label
        (occurrences.map (renameOpenedOccurrence rho)) =
      (openedCaptureIntervalsAt label occurrences).map
        (renameCaptureInterval rho) := by
  induction occurrences with
  | nil => rfl
  | cons occurrence remaining induction =>
      cases occurrence with
      | type =>
          simpa [openedCaptureIntervalsAt, renameOpenedOccurrence] using induction
      | capture candidate name lower upper lowerEvidence upperEvidence =>
          by_cases same : candidate = label <;>
            simp [openedCaptureIntervalsAt, renameOpenedOccurrence,
              renameCaptureInterval, same, induction]
      | classifier =>
          simpa [openedCaptureIntervalsAt, renameOpenedOccurrence] using
            induction

private theorem openedClassifierIntervalsAt_rename {scope : ManySortedFC.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {firstRelations secondRelations : List ManySortedFC.Relation}
    (rho : ManySortedFC.Rename
      (ManySortedFC.StaticScope scope symbols firstRelations)
      (ManySortedFC.StaticScope scope symbols secondRelations))
    (label : Nat)
    (occurrences : List (OpenedOccurrence scope symbols firstRelations)) :
    openedClassifierIntervalsAt label
        (occurrences.map (renameOpenedOccurrence rho)) =
      (openedClassifierIntervalsAt label occurrences).map
        (renameClassifierInterval rho) := by
  induction occurrences with
  | nil => rfl
  | cons occurrence remaining induction =>
      cases occurrence with
      | type =>
          simpa [openedClassifierIntervalsAt, renameOpenedOccurrence] using
            induction
      | capture =>
          simpa [openedClassifierIntervalsAt, renameOpenedOccurrence] using
            induction
      | classifier candidate name lower upper lowerEvidence upperEvidence =>
          by_cases same : candidate = label <;>
            simp [openedClassifierIntervalsAt, renameOpenedOccurrence,
              renameClassifierInterval, same, induction]

private theorem renameOpenedOccurrence_id {scope : ManySortedFC.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    (occurrence : OpenedOccurrence scope symbols relations) :
    renameOpenedOccurrence ManySortedFC.Rename.id occurrence = occurrence := by
  cases occurrence <;> simp [renameOpenedOccurrence]

private theorem renameOpenedOccurrence_comp {scope : ManySortedFC.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {firstRelations secondRelations thirdRelations :
      List ManySortedFC.Relation}
    (first : ManySortedFC.Rename
      (ManySortedFC.StaticScope scope symbols firstRelations)
      (ManySortedFC.StaticScope scope symbols secondRelations))
    (second : ManySortedFC.Rename
      (ManySortedFC.StaticScope scope symbols secondRelations)
      (ManySortedFC.StaticScope scope symbols thirdRelations))
    (occurrence : OpenedOccurrence scope symbols firstRelations) :
    renameOpenedOccurrence second
        (renameOpenedOccurrence first occurrence) =
      renameOpenedOccurrence (first.comp second) occurrence := by
  cases occurrence <;>
    simp [renameOpenedOccurrence, ManySortedFC.StaticExpr.rename_comp]

private theorem weakenTwo_eq_renameOpenedOccurrence
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    (newest older : ManySortedFC.Relation)
    (occurrence : OpenedOccurrence scope symbols relations) :
    occurrence.weakenTwo newest older =
      renameOpenedOccurrence
        (ManySortedFC.Rename.weakenMany
          (ManySortedFC.StaticScope scope symbols relations)
          [.evidence newest, .evidence older]) occurrence := by
  cases occurrence <;> rfl

private def evidencePrefixRename (scope : ManySortedFC.Sig)
    (symbols : List ManySortedFC.StaticSort)
    (tail : List ManySortedFC.Relation) :
    (newRelations : List ManySortedFC.Relation) ->
      ManySortedFC.Rename
        (ManySortedFC.StaticScope scope symbols tail)
        (ManySortedFC.StaticScope scope symbols (newRelations ++ tail))
  | [] => ManySortedFC.Rename.id
  | relation :: remaining =>
      (evidencePrefixRename scope symbols tail remaining).comp
        (ManySortedFC.Rename.succ (kind := .evidence relation))

private theorem weakenMany_comp_evidencePrefix
    (scope : ManySortedFC.Sig) (symbols : List ManySortedFC.StaticSort)
    (newRelations tail : List ManySortedFC.Relation) :
    (ManySortedFC.Rename.weakenMany
      (ManySortedFC.SymbolScope scope symbols)
      (ManySortedFC.evidenceKinds tail)).comp
        (evidencePrefixRename scope symbols tail newRelations) =
      ManySortedFC.Rename.weakenMany
        (ManySortedFC.SymbolScope scope symbols)
        (ManySortedFC.evidenceKinds (newRelations ++ tail)) := by
  apply ManySortedFC.Rename.ext
  intro kind index
  induction newRelations with
  | nil => rfl
  | cons relation remaining induction =>
      change ManySortedFC.BVar.there _ = ManySortedFC.BVar.there _
      exact congrArg ManySortedFC.BVar.there induction

private theorem openedTypeIntervalsAt_openTypeIntervals_same
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (label : Nat)
    (name : ManySortedFC.BVar (ManySortedFC.SymbolScope scope symbols)
      (.symbol .type))
    (intervals : List (Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .type
        (ManySortedFC.SymbolScope scope symbols))))
    (tailRelations : List ManySortedFC.Relation)
    (tail : List (OpenedOccurrence scope symbols tailRelations)) :
    openedTypeIntervalsAt label
        (openTypeIntervals label name intervals tailRelations tail) =
      intervals.map (renameTypeInterval
        (ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope scope symbols)
          (ManySortedFC.evidenceKinds
            (PreparedEntry.intervalRelations .type intervals ++
              tailRelations)))) ++
      (openedTypeIntervalsAt label tail).map (renameTypeInterval
        (evidencePrefixRename scope symbols tailRelations
          (PreparedEntry.intervalRelations .type intervals))) := by
  induction intervals with
  | nil =>
      simp only [openTypeIntervals, List.map_nil, List.nil_append,
        evidencePrefixRename]
      have renameId : renameTypeInterval
          (ManySortedFC.Rename.id : ManySortedFC.Rename
            (ManySortedFC.StaticScope scope symbols tailRelations)
            (ManySortedFC.StaticScope scope symbols tailRelations)) = id := by
        funext interval
        cases interval
        simp [renameTypeInterval]
      rw [renameId, List.map_id]
      rfl
  | cons current remaining induction =>
      simp only [openTypeIntervals, openedTypeIntervalsAt, if_true]
      let twoRho : ManySortedFC.Rename
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .type remaining ++ tailRelations))
          (ManySortedFC.StaticScope scope symbols
            (.inclusion .type :: .inclusion .type ::
              (PreparedEntry.intervalRelations .type remaining ++
                tailRelations))) :=
        ManySortedFC.Rename.weakenMany
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .type remaining ++ tailRelations))
          [.evidence (.inclusion .type), .evidence (.inclusion .type)]
      have weakenFunction :
          (fun occurrence => occurrence.weakenTwo (.inclusion .type)
            (.inclusion .type)) = renameOpenedOccurrence twoRho := by
        funext occurrence
        exact weakenTwo_eq_renameOpenedOccurrence _ _ occurrence
      have renamedProjection : openedTypeIntervalsAt label
          ((openTypeIntervals label name remaining tailRelations tail).map
            (fun occurrence => occurrence.weakenTwo (.inclusion .type)
              (.inclusion .type))) =
        (openedTypeIntervalsAt label
          (openTypeIntervals label name remaining tailRelations tail)).map
            (renameTypeInterval twoRho) := by
        rw [weakenFunction]
        exact openedTypeIntervalsAt_rename twoRho label _
      have remainingRhoEq :
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedEntry.intervalRelations .type remaining ++
                tailRelations))).comp twoRho =
            ManySortedFC.Rename.weakenMany
              (ManySortedFC.SymbolScope scope symbols)
              (ManySortedFC.evidenceKinds
                (PreparedEntry.intervalRelations .type
                  (current :: remaining) ++ tailRelations)) := by
        apply ManySortedFC.Rename.ext
        intro kind index
        rfl
      have tailRhoEq :
          (evidencePrefixRename scope symbols tailRelations
            (PreparedEntry.intervalRelations .type remaining)).comp twoRho =
            evidencePrefixRename scope symbols tailRelations
              (PreparedEntry.intervalRelations .type
                (current :: remaining)) := by
        apply ManySortedFC.Rename.ext
        intro kind index
        rfl
      have restEq : openedTypeIntervalsAt label
          ((openTypeIntervals label name remaining tailRelations tail).map
            (fun occurrence => occurrence.weakenTwo (.inclusion .type)
              (.inclusion .type))) =
        remaining.map (renameTypeInterval
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedEntry.intervalRelations .type
                (current :: remaining) ++ tailRelations)))) ++
        (openedTypeIntervalsAt label tail).map (renameTypeInterval
          (evidencePrefixRename scope symbols tailRelations
            (PreparedEntry.intervalRelations .type
              (current :: remaining)))) := by
        calc
          _ = (openedTypeIntervalsAt label
                (openTypeIntervals label name remaining tailRelations tail)).map
                (renameTypeInterval twoRho) := renamedProjection
          _ = (remaining.map (renameTypeInterval
                  (ManySortedFC.Rename.weakenMany
                    (ManySortedFC.SymbolScope scope symbols)
                    (ManySortedFC.evidenceKinds
                      (PreparedEntry.intervalRelations .type remaining ++
                        tailRelations)))) ++
                (openedTypeIntervalsAt label tail).map (renameTypeInterval
                  (evidencePrefixRename scope symbols tailRelations
                    (PreparedEntry.intervalRelations .type remaining)))).map
                (renameTypeInterval twoRho) := by rw [induction]
          _ = _ := by
            simp only [List.map_append, List.map_map]
            congr 1
            · apply List.map_congr_left
              intro interval membership
              cases interval
              simp [renameTypeInterval,
                ManySortedFC.StaticExpr.rename_comp, remainingRhoEq]
            · apply List.map_congr_left
              intro interval membership
              cases interval
              simp [renameTypeInterval,
                ManySortedFC.StaticExpr.rename_comp, tailRhoEq]
      calc
        _ = [{
              lower := current.lower.rename
                (ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .type
                      (current :: remaining) ++ tailRelations)))
              upper := current.upper.rename
                (ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .type
                      (current :: remaining) ++ tailRelations))) }] ++
            (remaining.map (renameTypeInterval
                (ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .type
                      (current :: remaining) ++ tailRelations)))) ++
              (openedTypeIntervalsAt label tail).map (renameTypeInterval
                (evidencePrefixRename scope symbols tailRelations
                  (PreparedEntry.intervalRelations .type
                    (current :: remaining))))) := by
              exact congrArg (fun rest => [{
                lower := current.lower.rename
                  (ManySortedFC.Rename.weakenMany
                    (ManySortedFC.SymbolScope scope symbols)
                    (ManySortedFC.evidenceKinds
                      (PreparedEntry.intervalRelations .type
                        (current :: remaining) ++ tailRelations)))
                upper := current.upper.rename
                  (ManySortedFC.Rename.weakenMany
                    (ManySortedFC.SymbolScope scope symbols)
                    (ManySortedFC.evidenceKinds
                      (PreparedEntry.intervalRelations .type
                        (current :: remaining) ++ tailRelations))) }] ++ rest)
                restEq
        _ = _ := by
          rfl

private theorem openedTypeIntervalsAt_openTypeIntervals_different
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (query entryLabel : Nat) (different : entryLabel ≠ query)
    (name : ManySortedFC.BVar (ManySortedFC.SymbolScope scope symbols)
      (.symbol .type))
    (intervals : List (Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .type
        (ManySortedFC.SymbolScope scope symbols))))
    (tailRelations : List ManySortedFC.Relation)
    (tail : List (OpenedOccurrence scope symbols tailRelations)) :
    openedTypeIntervalsAt query
        (openTypeIntervals entryLabel name intervals tailRelations tail) =
      (openedTypeIntervalsAt query tail).map (renameTypeInterval
        (evidencePrefixRename scope symbols tailRelations
          (PreparedEntry.intervalRelations .type intervals))) := by
  induction intervals with
  | nil =>
      simp only [openTypeIntervals, evidencePrefixRename]
      have renameId : renameTypeInterval
          (ManySortedFC.Rename.id : ManySortedFC.Rename
            (ManySortedFC.StaticScope scope symbols tailRelations)
            (ManySortedFC.StaticScope scope symbols tailRelations)) = id := by
        funext interval
        cases interval
        simp [renameTypeInterval]
      calc
        _ = List.map id (openedTypeIntervalsAt query tail) :=
          (List.map_id _).symm
        _ = _ := by
          apply List.map_congr_left
          intro interval membership
          exact (congrFun renameId interval).symm
  | cons current remaining induction =>
      simp only [openTypeIntervals, openedTypeIntervalsAt, if_neg different]
      let twoRho : ManySortedFC.Rename
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .type remaining ++ tailRelations))
          (ManySortedFC.StaticScope scope symbols
            (.inclusion .type :: .inclusion .type ::
              (PreparedEntry.intervalRelations .type remaining ++
                tailRelations))) :=
        ManySortedFC.Rename.weakenMany
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .type remaining ++ tailRelations))
          [.evidence (.inclusion .type), .evidence (.inclusion .type)]
      have weakenFunction :
          (fun occurrence => occurrence.weakenTwo (.inclusion .type)
            (.inclusion .type)) = renameOpenedOccurrence twoRho := by
        funext occurrence
        exact weakenTwo_eq_renameOpenedOccurrence _ _ occurrence
      have renamedProjection : openedTypeIntervalsAt query
          ((openTypeIntervals entryLabel name remaining tailRelations tail).map
            (fun occurrence => occurrence.weakenTwo (.inclusion .type)
              (.inclusion .type))) =
        (openedTypeIntervalsAt query
          (openTypeIntervals entryLabel name remaining tailRelations tail)).map
            (renameTypeInterval twoRho) := by
        rw [weakenFunction]
        exact openedTypeIntervalsAt_rename twoRho query _
      have tailRhoEq :
          (evidencePrefixRename scope symbols tailRelations
            (PreparedEntry.intervalRelations .type remaining)).comp twoRho =
            evidencePrefixRename scope symbols tailRelations
              (PreparedEntry.intervalRelations .type
                (current :: remaining)) := by
        apply ManySortedFC.Rename.ext
        intro kind index
        rfl
      calc
        _ = (openedTypeIntervalsAt query
              (openTypeIntervals entryLabel name remaining tailRelations tail)).map
              (renameTypeInterval twoRho) := renamedProjection
        _ = ((openedTypeIntervalsAt query tail).map (renameTypeInterval
              (evidencePrefixRename scope symbols tailRelations
                (PreparedEntry.intervalRelations .type remaining)))).map
              (renameTypeInterval twoRho) := by rw [induction]
        _ = _ := by
          simp only [List.map_map]
          apply List.map_congr_left
          intro interval membership
          cases interval
          simp [renameTypeInterval, ManySortedFC.StaticExpr.rename_comp,
            tailRhoEq]

private theorem openedTypeIntervalsAt_openCaptureIntervals
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (query entryLabel : Nat)
    (name : ManySortedFC.BVar (ManySortedFC.SymbolScope scope symbols)
      (.symbol .capture))
    (intervals : List (Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .capture
        (ManySortedFC.SymbolScope scope symbols))))
    (tailRelations : List ManySortedFC.Relation)
    (tail : List (OpenedOccurrence scope symbols tailRelations)) :
    openedTypeIntervalsAt query
        (openCaptureIntervals entryLabel name intervals tailRelations tail) =
      (openedTypeIntervalsAt query tail).map (renameTypeInterval
        (evidencePrefixRename scope symbols tailRelations
          (PreparedEntry.intervalRelations .capture intervals))) := by
  induction intervals with
  | nil =>
      simp only [openCaptureIntervals, evidencePrefixRename]
      have renameId : renameTypeInterval
          (ManySortedFC.Rename.id : ManySortedFC.Rename
            (ManySortedFC.StaticScope scope symbols tailRelations)
            (ManySortedFC.StaticScope scope symbols tailRelations)) = id := by
        funext interval
        cases interval
        simp [renameTypeInterval]
      calc
        _ = List.map id (openedTypeIntervalsAt query tail) :=
          (List.map_id _).symm
        _ = _ := by
          apply List.map_congr_left
          intro interval membership
          exact (congrFun renameId interval).symm
  | cons current remaining induction =>
      simp only [openCaptureIntervals, openedTypeIntervalsAt]
      let twoRho : ManySortedFC.Rename
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .capture remaining ++ tailRelations))
          (ManySortedFC.StaticScope scope symbols
            (.inclusion .capture :: .inclusion .capture ::
              (PreparedEntry.intervalRelations .capture remaining ++
                tailRelations))) :=
        ManySortedFC.Rename.weakenMany
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .capture remaining ++ tailRelations))
          [.evidence (.inclusion .capture), .evidence (.inclusion .capture)]
      have weakenFunction :
          (fun occurrence => occurrence.weakenTwo (.inclusion .capture)
            (.inclusion .capture)) = renameOpenedOccurrence twoRho := by
        funext occurrence
        exact weakenTwo_eq_renameOpenedOccurrence _ _ occurrence
      have renamedProjection : openedTypeIntervalsAt query
          ((openCaptureIntervals entryLabel name remaining tailRelations tail).map
            (fun occurrence => occurrence.weakenTwo (.inclusion .capture)
              (.inclusion .capture))) =
        (openedTypeIntervalsAt query
          (openCaptureIntervals entryLabel name remaining tailRelations tail)).map
            (renameTypeInterval twoRho) := by
        rw [weakenFunction]
        exact openedTypeIntervalsAt_rename twoRho query _
      have tailRhoEq :
          (evidencePrefixRename scope symbols tailRelations
            (PreparedEntry.intervalRelations .capture remaining)).comp twoRho =
            evidencePrefixRename scope symbols tailRelations
              (PreparedEntry.intervalRelations .capture
                (current :: remaining)) := by
        apply ManySortedFC.Rename.ext
        intro kind index
        rfl
      calc
        _ = (openedTypeIntervalsAt query
              (openCaptureIntervals entryLabel name remaining tailRelations tail)).map
              (renameTypeInterval twoRho) := renamedProjection
        _ = ((openedTypeIntervalsAt query tail).map (renameTypeInterval
              (evidencePrefixRename scope symbols tailRelations
                (PreparedEntry.intervalRelations .capture remaining)))).map
              (renameTypeInterval twoRho) := by rw [induction]
        _ = _ := by
          simp only [List.map_map]
          apply List.map_congr_left
          intro interval membership
          cases interval
          simp [renameTypeInterval, ManySortedFC.StaticExpr.rename_comp,
            tailRhoEq]

private theorem openedTypeIntervalsAt_openClassifierIntervals
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (query entryLabel : Nat)
    (name : ManySortedFC.BVar (ManySortedFC.SymbolScope scope symbols)
      (.symbol .classifier))
    (intervals : List (Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .classifier
        (ManySortedFC.SymbolScope scope symbols))))
    (tailRelations : List ManySortedFC.Relation)
    (tail : List (OpenedOccurrence scope symbols tailRelations)) :
    openedTypeIntervalsAt query
        (openClassifierIntervals entryLabel name intervals tailRelations tail) =
      (openedTypeIntervalsAt query tail).map (renameTypeInterval
        (evidencePrefixRename scope symbols tailRelations
          (PreparedEntry.intervalRelations .classifier intervals))) := by
  induction intervals with
  | nil =>
      simp only [openClassifierIntervals, evidencePrefixRename]
      have renameId : renameTypeInterval
          (ManySortedFC.Rename.id : ManySortedFC.Rename
            (ManySortedFC.StaticScope scope symbols tailRelations)
            (ManySortedFC.StaticScope scope symbols tailRelations)) = id := by
        funext interval
        cases interval
        simp [renameTypeInterval]
      calc
        _ = List.map id (openedTypeIntervalsAt query tail) :=
          (List.map_id _).symm
        _ = _ := by
          apply List.map_congr_left
          intro interval membership
          exact (congrFun renameId interval).symm
  | cons current remaining induction =>
      simp only [openClassifierIntervals, openedTypeIntervalsAt]
      let twoRho : ManySortedFC.Rename
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .classifier remaining ++
              tailRelations))
          (ManySortedFC.StaticScope scope symbols
            (.inclusion .classifier :: .inclusion .classifier ::
              (PreparedEntry.intervalRelations .classifier remaining ++
                tailRelations))) :=
        ManySortedFC.Rename.weakenMany
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .classifier remaining ++
              tailRelations))
          [.evidence (.inclusion .classifier),
            .evidence (.inclusion .classifier)]
      have weakenFunction :
          (fun occurrence => occurrence.weakenTwo (.inclusion .classifier)
            (.inclusion .classifier)) = renameOpenedOccurrence twoRho := by
        funext occurrence
        exact weakenTwo_eq_renameOpenedOccurrence _ _ occurrence
      have renamedProjection : openedTypeIntervalsAt query
          ((openClassifierIntervals entryLabel name remaining tailRelations
            tail).map
              (fun occurrence => occurrence.weakenTwo (.inclusion .classifier)
                (.inclusion .classifier))) =
        (openedTypeIntervalsAt query
          (openClassifierIntervals entryLabel name remaining tailRelations
            tail)).map (renameTypeInterval twoRho) := by
        rw [weakenFunction]
        exact openedTypeIntervalsAt_rename twoRho query _
      have tailRhoEq :
          (evidencePrefixRename scope symbols tailRelations
            (PreparedEntry.intervalRelations .classifier remaining)).comp
              twoRho =
            evidencePrefixRename scope symbols tailRelations
              (PreparedEntry.intervalRelations .classifier
                (current :: remaining)) := by
        apply ManySortedFC.Rename.ext
        intro kind index
        rfl
      calc
        _ = (openedTypeIntervalsAt query
              (openClassifierIntervals entryLabel name remaining tailRelations
                tail)).map (renameTypeInterval twoRho) := renamedProjection
        _ = ((openedTypeIntervalsAt query tail).map (renameTypeInterval
              (evidencePrefixRename scope symbols tailRelations
                (PreparedEntry.intervalRelations .classifier remaining)))).map
              (renameTypeInterval twoRho) := by rw [induction]
        _ = _ := by
          simp only [List.map_map]
          apply List.map_congr_left
          intro interval membership
          cases interval
          simp [renameTypeInterval, ManySortedFC.StaticExpr.rename_comp,
            tailRhoEq]

theorem openedTypeIntervalsAt_openEntriesWithTail
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (label : Nat)
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope scope symbols)))
    (tailRelations : List ManySortedFC.Relation) :
    openedTypeIntervalsAt label
        (openEntriesWithTail entries tailRelations []) =
      (Ordered.preparedTypeIntervalsAtEntries label entries).map
        (renameTypeInterval
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedSignature.entriesRelationsWithTail entries
                tailRelations)))) := by
  induction entries with
  | nil => rfl
  | cons current remaining induction =>
      cases current with
      | type currentLabel currentName currentIntervals =>
          by_cases same : currentLabel = label
          · subst currentLabel
            simp only [openEntriesWithTail,
              PreparedSignature.entriesRelationsWithTail,
              PreparedEntry.relations]
            rw [openedTypeIntervalsAt_openTypeIntervals_same]
            have tailRhoEq :
                (ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedSignature.entriesRelationsWithTail remaining
                      tailRelations))).comp
                    (evidencePrefixRename scope symbols
                      (PreparedSignature.entriesRelationsWithTail remaining
                        tailRelations)
                      (PreparedEntry.intervalRelations .type
                        currentIntervals)) =
                  ManySortedFC.Rename.weakenMany
                    (ManySortedFC.SymbolScope scope symbols)
                    (ManySortedFC.evidenceKinds
                      (PreparedEntry.intervalRelations .type currentIntervals ++
                        PreparedSignature.entriesRelationsWithTail remaining
                          tailRelations)) :=
              weakenMany_comp_evidencePrefix scope symbols
                (PreparedEntry.intervalRelations .type currentIntervals)
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
            rw [induction]
            simp only [Ordered.preparedTypeIntervalsAtEntries, if_true,
              List.map_append, List.map_map]
            congr 1
            apply List.map_congr_left
            intro interval membership
            cases interval
            simp [renameTypeInterval, ManySortedFC.StaticExpr.rename_comp,
              tailRhoEq]
          · simp only [openEntriesWithTail,
              PreparedSignature.entriesRelationsWithTail,
              PreparedEntry.relations]
            rw [openedTypeIntervalsAt_openTypeIntervals_different
                label currentLabel same]
            have tailRhoEq :
                (ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedSignature.entriesRelationsWithTail remaining
                      tailRelations))).comp
                    (evidencePrefixRename scope symbols
                      (PreparedSignature.entriesRelationsWithTail remaining
                        tailRelations)
                      (PreparedEntry.intervalRelations .type
                        currentIntervals)) =
                  ManySortedFC.Rename.weakenMany
                    (ManySortedFC.SymbolScope scope symbols)
                    (ManySortedFC.evidenceKinds
                      (PreparedEntry.intervalRelations .type currentIntervals ++
                        PreparedSignature.entriesRelationsWithTail remaining
                          tailRelations)) :=
              weakenMany_comp_evidencePrefix scope symbols
                (PreparedEntry.intervalRelations .type currentIntervals)
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
            rw [induction]
            simp only [Ordered.preparedTypeIntervalsAtEntries, if_neg same,
              List.nil_append, List.map_map]
            apply List.map_congr_left
            intro interval membership
            cases interval
            simp [renameTypeInterval, ManySortedFC.StaticExpr.rename_comp,
              tailRhoEq]
      | capture currentLabel currentName currentIntervals =>
          simp only [openEntriesWithTail,
            PreparedSignature.entriesRelationsWithTail,
            PreparedEntry.relations]
          rw [openedTypeIntervalsAt_openCaptureIntervals]
          have tailRhoEq :
              (ManySortedFC.Rename.weakenMany
                (ManySortedFC.SymbolScope scope symbols)
                (ManySortedFC.evidenceKinds
                  (PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations))).comp
                  (evidencePrefixRename scope symbols
                    (PreparedSignature.entriesRelationsWithTail remaining
                      tailRelations)
                    (PreparedEntry.intervalRelations .capture
                      currentIntervals)) =
                ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .capture currentIntervals ++
                      PreparedSignature.entriesRelationsWithTail remaining
                        tailRelations)) :=
            weakenMany_comp_evidencePrefix scope symbols
              (PreparedEntry.intervalRelations .capture currentIntervals)
              (PreparedSignature.entriesRelationsWithTail remaining
                tailRelations)
          rw [induction]
          simp only [Ordered.preparedTypeIntervalsAtEntries, List.map_map]
          apply List.map_congr_left
          intro interval membership
          cases interval
          simp [renameTypeInterval, ManySortedFC.StaticExpr.rename_comp,
            tailRhoEq]
      | classifier currentLabel currentName currentIntervals =>
          simp only [openEntriesWithTail,
            PreparedSignature.entriesRelationsWithTail,
            PreparedEntry.relations]
          rw [openedTypeIntervalsAt_openClassifierIntervals]
          have tailRhoEq :
              (ManySortedFC.Rename.weakenMany
                (ManySortedFC.SymbolScope scope symbols)
                (ManySortedFC.evidenceKinds
                  (PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations))).comp
                  (evidencePrefixRename scope symbols
                    (PreparedSignature.entriesRelationsWithTail remaining
                      tailRelations)
                    (PreparedEntry.intervalRelations .classifier
                      currentIntervals)) =
                ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .classifier
                      currentIntervals ++
                        PreparedSignature.entriesRelationsWithTail remaining
                          tailRelations)) :=
            weakenMany_comp_evidencePrefix scope symbols
              (PreparedEntry.intervalRelations .classifier currentIntervals)
              (PreparedSignature.entriesRelationsWithTail remaining
                tailRelations)
          rw [induction]
          simp only [Ordered.preparedTypeIntervalsAtEntries, List.map_map]
          apply List.map_congr_left
          intro interval membership
          cases interval
          simp [renameTypeInterval, ManySortedFC.StaticExpr.rename_comp,
            tailRhoEq]

private theorem openedCaptureIntervalsAt_openCaptureIntervals_same
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (label : Nat)
    (name : ManySortedFC.BVar (ManySortedFC.SymbolScope scope symbols)
      (.symbol .capture))
    (intervals : List (Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .capture
        (ManySortedFC.SymbolScope scope symbols))))
    (tailRelations : List ManySortedFC.Relation)
    (tail : List (OpenedOccurrence scope symbols tailRelations)) :
    openedCaptureIntervalsAt label
        (openCaptureIntervals label name intervals tailRelations tail) =
      intervals.map (renameCaptureInterval
        (ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope scope symbols)
          (ManySortedFC.evidenceKinds
            (PreparedEntry.intervalRelations .capture intervals ++
              tailRelations)))) ++
      (openedCaptureIntervalsAt label tail).map (renameCaptureInterval
        (evidencePrefixRename scope symbols tailRelations
          (PreparedEntry.intervalRelations .capture intervals))) := by
  induction intervals with
  | nil =>
      simp only [openCaptureIntervals, List.map_nil, List.nil_append,
        evidencePrefixRename]
      have renameId : renameCaptureInterval
          (ManySortedFC.Rename.id : ManySortedFC.Rename
            (ManySortedFC.StaticScope scope symbols tailRelations)
            (ManySortedFC.StaticScope scope symbols tailRelations)) = id := by
        funext interval
        cases interval
        simp [renameCaptureInterval]
      rw [renameId, List.map_id]
      rfl
  | cons current remaining induction =>
      simp only [openCaptureIntervals, openedCaptureIntervalsAt, if_true]
      let twoRho : ManySortedFC.Rename
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .capture remaining ++ tailRelations))
          (ManySortedFC.StaticScope scope symbols
            (.inclusion .capture :: .inclusion .capture ::
              (PreparedEntry.intervalRelations .capture remaining ++
                tailRelations))) :=
        ManySortedFC.Rename.weakenMany
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .capture remaining ++ tailRelations))
          [.evidence (.inclusion .capture), .evidence (.inclusion .capture)]
      have weakenFunction :
          (fun occurrence => occurrence.weakenTwo (.inclusion .capture)
            (.inclusion .capture)) = renameOpenedOccurrence twoRho := by
        funext occurrence
        exact weakenTwo_eq_renameOpenedOccurrence _ _ occurrence
      have renamedProjection : openedCaptureIntervalsAt label
          ((openCaptureIntervals label name remaining tailRelations tail).map
            (fun occurrence => occurrence.weakenTwo (.inclusion .capture)
              (.inclusion .capture))) =
        (openedCaptureIntervalsAt label
          (openCaptureIntervals label name remaining tailRelations tail)).map
            (renameCaptureInterval twoRho) := by
        rw [weakenFunction]
        exact openedCaptureIntervalsAt_rename twoRho label _
      have remainingRhoEq :
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedEntry.intervalRelations .capture remaining ++
                tailRelations))).comp twoRho =
            ManySortedFC.Rename.weakenMany
              (ManySortedFC.SymbolScope scope symbols)
              (ManySortedFC.evidenceKinds
                (PreparedEntry.intervalRelations .capture
                  (current :: remaining) ++ tailRelations)) := by
        apply ManySortedFC.Rename.ext
        intro kind index
        rfl
      have tailRhoEq :
          (evidencePrefixRename scope symbols tailRelations
            (PreparedEntry.intervalRelations .capture remaining)).comp twoRho =
            evidencePrefixRename scope symbols tailRelations
              (PreparedEntry.intervalRelations .capture
                (current :: remaining)) := by
        apply ManySortedFC.Rename.ext
        intro kind index
        rfl
      have restEq : openedCaptureIntervalsAt label
          ((openCaptureIntervals label name remaining tailRelations tail).map
            (fun occurrence => occurrence.weakenTwo (.inclusion .capture)
              (.inclusion .capture))) =
        remaining.map (renameCaptureInterval
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedEntry.intervalRelations .capture
                (current :: remaining) ++ tailRelations)))) ++
        (openedCaptureIntervalsAt label tail).map (renameCaptureInterval
          (evidencePrefixRename scope symbols tailRelations
            (PreparedEntry.intervalRelations .capture
              (current :: remaining)))) := by
        calc
          _ = (openedCaptureIntervalsAt label
                (openCaptureIntervals label name remaining tailRelations tail)).map
                (renameCaptureInterval twoRho) := renamedProjection
          _ = (remaining.map (renameCaptureInterval
                  (ManySortedFC.Rename.weakenMany
                    (ManySortedFC.SymbolScope scope symbols)
                    (ManySortedFC.evidenceKinds
                      (PreparedEntry.intervalRelations .capture remaining ++
                        tailRelations)))) ++
                (openedCaptureIntervalsAt label tail).map (renameCaptureInterval
                  (evidencePrefixRename scope symbols tailRelations
                    (PreparedEntry.intervalRelations .capture remaining)))).map
                (renameCaptureInterval twoRho) := by rw [induction]
          _ = _ := by
            simp only [List.map_append, List.map_map]
            congr 1
            · apply List.map_congr_left
              intro interval membership
              cases interval
              simp [renameCaptureInterval,
                ManySortedFC.StaticExpr.rename_comp, remainingRhoEq]
            · apply List.map_congr_left
              intro interval membership
              cases interval
              simp [renameCaptureInterval,
                ManySortedFC.StaticExpr.rename_comp, tailRhoEq]
      calc
        _ = [{
              lower := current.lower.rename
                (ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .capture
                      (current :: remaining) ++ tailRelations)))
              upper := current.upper.rename
                (ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .capture
                      (current :: remaining) ++ tailRelations))) }] ++
            (remaining.map (renameCaptureInterval
                (ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .capture
                      (current :: remaining) ++ tailRelations)))) ++
              (openedCaptureIntervalsAt label tail).map (renameCaptureInterval
                (evidencePrefixRename scope symbols tailRelations
                  (PreparedEntry.intervalRelations .capture
                    (current :: remaining))))) := by
              exact congrArg (fun rest => [{
                lower := current.lower.rename
                  (ManySortedFC.Rename.weakenMany
                    (ManySortedFC.SymbolScope scope symbols)
                    (ManySortedFC.evidenceKinds
                      (PreparedEntry.intervalRelations .capture
                        (current :: remaining) ++ tailRelations)))
                upper := current.upper.rename
                  (ManySortedFC.Rename.weakenMany
                    (ManySortedFC.SymbolScope scope symbols)
                    (ManySortedFC.evidenceKinds
                      (PreparedEntry.intervalRelations .capture
                        (current :: remaining) ++ tailRelations))) }] ++ rest)
                restEq
        _ = _ := by
          rfl

private theorem openedCaptureIntervalsAt_openCaptureIntervals_different
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (query entryLabel : Nat) (different : entryLabel ≠ query)
    (name : ManySortedFC.BVar (ManySortedFC.SymbolScope scope symbols)
      (.symbol .capture))
    (intervals : List (Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .capture
        (ManySortedFC.SymbolScope scope symbols))))
    (tailRelations : List ManySortedFC.Relation)
    (tail : List (OpenedOccurrence scope symbols tailRelations)) :
    openedCaptureIntervalsAt query
        (openCaptureIntervals entryLabel name intervals tailRelations tail) =
      (openedCaptureIntervalsAt query tail).map (renameCaptureInterval
        (evidencePrefixRename scope symbols tailRelations
          (PreparedEntry.intervalRelations .capture intervals))) := by
  induction intervals with
  | nil =>
      simp only [openCaptureIntervals, evidencePrefixRename]
      have renameId : renameCaptureInterval
          (ManySortedFC.Rename.id : ManySortedFC.Rename
            (ManySortedFC.StaticScope scope symbols tailRelations)
            (ManySortedFC.StaticScope scope symbols tailRelations)) = id := by
        funext interval
        cases interval
        simp [renameCaptureInterval]
      calc
        _ = List.map id (openedCaptureIntervalsAt query tail) :=
          (List.map_id _).symm
        _ = _ := by
          apply List.map_congr_left
          intro interval membership
          exact (congrFun renameId interval).symm
  | cons current remaining induction =>
      simp only [openCaptureIntervals, openedCaptureIntervalsAt,
        if_neg different]
      let twoRho : ManySortedFC.Rename
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .capture remaining ++ tailRelations))
          (ManySortedFC.StaticScope scope symbols
            (.inclusion .capture :: .inclusion .capture ::
              (PreparedEntry.intervalRelations .capture remaining ++
                tailRelations))) :=
        ManySortedFC.Rename.weakenMany
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .capture remaining ++ tailRelations))
          [.evidence (.inclusion .capture), .evidence (.inclusion .capture)]
      have weakenFunction :
          (fun occurrence => occurrence.weakenTwo (.inclusion .capture)
            (.inclusion .capture)) = renameOpenedOccurrence twoRho := by
        funext occurrence
        exact weakenTwo_eq_renameOpenedOccurrence _ _ occurrence
      have renamedProjection : openedCaptureIntervalsAt query
          ((openCaptureIntervals entryLabel name remaining tailRelations tail).map
            (fun occurrence => occurrence.weakenTwo (.inclusion .capture)
              (.inclusion .capture))) =
        (openedCaptureIntervalsAt query
          (openCaptureIntervals entryLabel name remaining tailRelations tail)).map
            (renameCaptureInterval twoRho) := by
        rw [weakenFunction]
        exact openedCaptureIntervalsAt_rename twoRho query _
      have tailRhoEq :
          (evidencePrefixRename scope symbols tailRelations
            (PreparedEntry.intervalRelations .capture remaining)).comp twoRho =
            evidencePrefixRename scope symbols tailRelations
              (PreparedEntry.intervalRelations .capture
                (current :: remaining)) := by
        apply ManySortedFC.Rename.ext
        intro kind index
        rfl
      calc
        _ = (openedCaptureIntervalsAt query
              (openCaptureIntervals entryLabel name remaining tailRelations tail)).map
              (renameCaptureInterval twoRho) := renamedProjection
        _ = ((openedCaptureIntervalsAt query tail).map (renameCaptureInterval
              (evidencePrefixRename scope symbols tailRelations
                (PreparedEntry.intervalRelations .capture remaining)))).map
              (renameCaptureInterval twoRho) := by rw [induction]
        _ = _ := by
          simp only [List.map_map]
          apply List.map_congr_left
          intro interval membership
          cases interval
          simp [renameCaptureInterval, ManySortedFC.StaticExpr.rename_comp,
            tailRhoEq]

private theorem openedCaptureIntervalsAt_openTypeIntervals
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (query entryLabel : Nat)
    (name : ManySortedFC.BVar (ManySortedFC.SymbolScope scope symbols)
      (.symbol .type))
    (intervals : List (Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .type
        (ManySortedFC.SymbolScope scope symbols))))
    (tailRelations : List ManySortedFC.Relation)
    (tail : List (OpenedOccurrence scope symbols tailRelations)) :
    openedCaptureIntervalsAt query
        (openTypeIntervals entryLabel name intervals tailRelations tail) =
      (openedCaptureIntervalsAt query tail).map (renameCaptureInterval
        (evidencePrefixRename scope symbols tailRelations
          (PreparedEntry.intervalRelations .type intervals))) := by
  induction intervals with
  | nil =>
      simp only [openTypeIntervals, evidencePrefixRename]
      have renameId : renameCaptureInterval
          (ManySortedFC.Rename.id : ManySortedFC.Rename
            (ManySortedFC.StaticScope scope symbols tailRelations)
            (ManySortedFC.StaticScope scope symbols tailRelations)) = id := by
        funext interval
        cases interval
        simp [renameCaptureInterval]
      calc
        _ = List.map id (openedCaptureIntervalsAt query tail) :=
          (List.map_id _).symm
        _ = _ := by
          apply List.map_congr_left
          intro interval membership
          exact (congrFun renameId interval).symm
  | cons current remaining induction =>
      simp only [openTypeIntervals, openedCaptureIntervalsAt]
      let twoRho : ManySortedFC.Rename
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .type remaining ++ tailRelations))
          (ManySortedFC.StaticScope scope symbols
            (.inclusion .type :: .inclusion .type ::
              (PreparedEntry.intervalRelations .type remaining ++
                tailRelations))) :=
        ManySortedFC.Rename.weakenMany
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .type remaining ++ tailRelations))
          [.evidence (.inclusion .type), .evidence (.inclusion .type)]
      have weakenFunction :
          (fun occurrence => occurrence.weakenTwo (.inclusion .type)
            (.inclusion .type)) = renameOpenedOccurrence twoRho := by
        funext occurrence
        exact weakenTwo_eq_renameOpenedOccurrence _ _ occurrence
      have renamedProjection : openedCaptureIntervalsAt query
          ((openTypeIntervals entryLabel name remaining tailRelations tail).map
            (fun occurrence => occurrence.weakenTwo (.inclusion .type)
              (.inclusion .type))) =
        (openedCaptureIntervalsAt query
          (openTypeIntervals entryLabel name remaining tailRelations tail)).map
            (renameCaptureInterval twoRho) := by
        rw [weakenFunction]
        exact openedCaptureIntervalsAt_rename twoRho query _
      have tailRhoEq :
          (evidencePrefixRename scope symbols tailRelations
            (PreparedEntry.intervalRelations .type remaining)).comp twoRho =
            evidencePrefixRename scope symbols tailRelations
              (PreparedEntry.intervalRelations .type
                (current :: remaining)) := by
        apply ManySortedFC.Rename.ext
        intro kind index
        rfl
      calc
        _ = (openedCaptureIntervalsAt query
              (openTypeIntervals entryLabel name remaining tailRelations tail)).map
              (renameCaptureInterval twoRho) := renamedProjection
        _ = ((openedCaptureIntervalsAt query tail).map (renameCaptureInterval
              (evidencePrefixRename scope symbols tailRelations
                (PreparedEntry.intervalRelations .type remaining)))).map
              (renameCaptureInterval twoRho) := by rw [induction]
        _ = _ := by
          simp only [List.map_map]
          apply List.map_congr_left
          intro interval membership
          cases interval
          simp [renameCaptureInterval, ManySortedFC.StaticExpr.rename_comp,
            tailRhoEq]

private theorem openedCaptureIntervalsAt_openClassifierIntervals
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (query entryLabel : Nat)
    (name : ManySortedFC.BVar (ManySortedFC.SymbolScope scope symbols)
      (.symbol .classifier))
    (intervals : List (Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .classifier
        (ManySortedFC.SymbolScope scope symbols))))
    (tailRelations : List ManySortedFC.Relation)
    (tail : List (OpenedOccurrence scope symbols tailRelations)) :
    openedCaptureIntervalsAt query
        (openClassifierIntervals entryLabel name intervals tailRelations tail) =
      (openedCaptureIntervalsAt query tail).map (renameCaptureInterval
        (evidencePrefixRename scope symbols tailRelations
          (PreparedEntry.intervalRelations .classifier intervals))) := by
  induction intervals with
  | nil =>
      simp only [openClassifierIntervals, evidencePrefixRename]
      have renameId : renameCaptureInterval
          (ManySortedFC.Rename.id : ManySortedFC.Rename
            (ManySortedFC.StaticScope scope symbols tailRelations)
            (ManySortedFC.StaticScope scope symbols tailRelations)) = id := by
        funext interval
        cases interval
        simp [renameCaptureInterval]
      calc
        _ = List.map id (openedCaptureIntervalsAt query tail) :=
          (List.map_id _).symm
        _ = _ := by
          apply List.map_congr_left
          intro interval membership
          exact (congrFun renameId interval).symm
  | cons current remaining induction =>
      simp only [openClassifierIntervals, openedCaptureIntervalsAt]
      let twoRho : ManySortedFC.Rename
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .classifier remaining ++
              tailRelations))
          (ManySortedFC.StaticScope scope symbols
            (.inclusion .classifier :: .inclusion .classifier ::
              (PreparedEntry.intervalRelations .classifier remaining ++
                tailRelations))) :=
        ManySortedFC.Rename.weakenMany
          (ManySortedFC.StaticScope scope symbols
            (PreparedEntry.intervalRelations .classifier remaining ++
              tailRelations))
          [.evidence (.inclusion .classifier),
            .evidence (.inclusion .classifier)]
      have weakenFunction :
          (fun occurrence => occurrence.weakenTwo (.inclusion .classifier)
            (.inclusion .classifier)) = renameOpenedOccurrence twoRho := by
        funext occurrence
        exact weakenTwo_eq_renameOpenedOccurrence _ _ occurrence
      have renamedProjection : openedCaptureIntervalsAt query
          ((openClassifierIntervals entryLabel name remaining tailRelations
            tail).map
              (fun occurrence => occurrence.weakenTwo (.inclusion .classifier)
                (.inclusion .classifier))) =
        (openedCaptureIntervalsAt query
          (openClassifierIntervals entryLabel name remaining tailRelations
            tail)).map (renameCaptureInterval twoRho) := by
        rw [weakenFunction]
        exact openedCaptureIntervalsAt_rename twoRho query _
      have tailRhoEq :
          (evidencePrefixRename scope symbols tailRelations
            (PreparedEntry.intervalRelations .classifier remaining)).comp
              twoRho =
            evidencePrefixRename scope symbols tailRelations
              (PreparedEntry.intervalRelations .classifier
                (current :: remaining)) := by
        apply ManySortedFC.Rename.ext
        intro kind index
        rfl
      calc
        _ = (openedCaptureIntervalsAt query
              (openClassifierIntervals entryLabel name remaining tailRelations
                tail)).map (renameCaptureInterval twoRho) := renamedProjection
        _ = ((openedCaptureIntervalsAt query tail).map (renameCaptureInterval
              (evidencePrefixRename scope symbols tailRelations
                (PreparedEntry.intervalRelations .classifier remaining)))).map
              (renameCaptureInterval twoRho) := by rw [induction]
        _ = _ := by
          simp only [List.map_map]
          apply List.map_congr_left
          intro interval membership
          cases interval
          simp [renameCaptureInterval, ManySortedFC.StaticExpr.rename_comp,
            tailRhoEq]

theorem openedCaptureIntervalsAt_openEntriesWithTail
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (label : Nat)
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope scope symbols)))
    (tailRelations : List ManySortedFC.Relation) :
    openedCaptureIntervalsAt label
        (openEntriesWithTail entries tailRelations []) =
      (Ordered.preparedCaptureIntervalsAtEntries label entries).map
        (renameCaptureInterval
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedSignature.entriesRelationsWithTail entries
                tailRelations)))) := by
  induction entries with
  | nil => rfl
  | cons current remaining induction =>
      cases current with
      | type currentLabel currentName currentIntervals =>
          simp only [openEntriesWithTail,
            PreparedSignature.entriesRelationsWithTail,
            PreparedEntry.relations]
          rw [openedCaptureIntervalsAt_openTypeIntervals]
          have tailRhoEq :
              (ManySortedFC.Rename.weakenMany
                (ManySortedFC.SymbolScope scope symbols)
                (ManySortedFC.evidenceKinds
                  (PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations))).comp
                  (evidencePrefixRename scope symbols
                    (PreparedSignature.entriesRelationsWithTail remaining
                      tailRelations)
                    (PreparedEntry.intervalRelations .type
                      currentIntervals)) =
                ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .type currentIntervals ++
                      PreparedSignature.entriesRelationsWithTail remaining
                        tailRelations)) :=
            weakenMany_comp_evidencePrefix scope symbols
              (PreparedEntry.intervalRelations .type currentIntervals)
              (PreparedSignature.entriesRelationsWithTail remaining
                tailRelations)
          rw [induction]
          simp only [Ordered.preparedCaptureIntervalsAtEntries, List.map_map]
          apply List.map_congr_left
          intro interval membership
          cases interval
          simp [renameCaptureInterval, ManySortedFC.StaticExpr.rename_comp,
            tailRhoEq]
      | capture currentLabel currentName currentIntervals =>
          by_cases same : currentLabel = label
          · subst currentLabel
            simp only [openEntriesWithTail,
              PreparedSignature.entriesRelationsWithTail,
              PreparedEntry.relations]
            rw [openedCaptureIntervalsAt_openCaptureIntervals_same]
            have tailRhoEq :
                (ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedSignature.entriesRelationsWithTail remaining
                      tailRelations))).comp
                    (evidencePrefixRename scope symbols
                      (PreparedSignature.entriesRelationsWithTail remaining
                        tailRelations)
                      (PreparedEntry.intervalRelations .capture
                        currentIntervals)) =
                  ManySortedFC.Rename.weakenMany
                    (ManySortedFC.SymbolScope scope symbols)
                    (ManySortedFC.evidenceKinds
                      (PreparedEntry.intervalRelations .capture currentIntervals ++
                        PreparedSignature.entriesRelationsWithTail remaining
                          tailRelations)) :=
              weakenMany_comp_evidencePrefix scope symbols
                (PreparedEntry.intervalRelations .capture currentIntervals)
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
            rw [induction]
            simp only [Ordered.preparedCaptureIntervalsAtEntries, if_true,
              List.map_append, List.map_map]
            congr 1
            apply List.map_congr_left
            intro interval membership
            cases interval
            simp [renameCaptureInterval, ManySortedFC.StaticExpr.rename_comp,
              tailRhoEq]

          · simp only [openEntriesWithTail,
              PreparedSignature.entriesRelationsWithTail,
              PreparedEntry.relations]
            rw [openedCaptureIntervalsAt_openCaptureIntervals_different
                label currentLabel same]
            have tailRhoEq :
                (ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedSignature.entriesRelationsWithTail remaining
                      tailRelations))).comp
                    (evidencePrefixRename scope symbols
                      (PreparedSignature.entriesRelationsWithTail remaining
                        tailRelations)
                      (PreparedEntry.intervalRelations .capture
                        currentIntervals)) =
                  ManySortedFC.Rename.weakenMany
                    (ManySortedFC.SymbolScope scope symbols)
                    (ManySortedFC.evidenceKinds
                      (PreparedEntry.intervalRelations .capture currentIntervals ++
                        PreparedSignature.entriesRelationsWithTail remaining
                          tailRelations)) :=
              weakenMany_comp_evidencePrefix scope symbols
                (PreparedEntry.intervalRelations .capture currentIntervals)
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
            rw [induction]
            simp only [Ordered.preparedCaptureIntervalsAtEntries, if_neg same,
              List.nil_append, List.map_map]
            apply List.map_congr_left
            intro interval membership
            cases interval
            simp [renameCaptureInterval, ManySortedFC.StaticExpr.rename_comp,
              tailRhoEq]
      | classifier currentLabel currentName currentIntervals =>
          simp only [openEntriesWithTail,
            PreparedSignature.entriesRelationsWithTail,
            PreparedEntry.relations]
          rw [openedCaptureIntervalsAt_openClassifierIntervals]
          have tailRhoEq :
              (ManySortedFC.Rename.weakenMany
                (ManySortedFC.SymbolScope scope symbols)
                (ManySortedFC.evidenceKinds
                  (PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations))).comp
                  (evidencePrefixRename scope symbols
                    (PreparedSignature.entriesRelationsWithTail remaining
                      tailRelations)
                    (PreparedEntry.intervalRelations .classifier
                      currentIntervals)) =
                ManySortedFC.Rename.weakenMany
                  (ManySortedFC.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .classifier
                      currentIntervals ++
                        PreparedSignature.entriesRelationsWithTail remaining
                          tailRelations)) :=
            weakenMany_comp_evidencePrefix scope symbols
              (PreparedEntry.intervalRelations .classifier currentIntervals)
              (PreparedSignature.entriesRelationsWithTail remaining
                tailRelations)
          rw [induction]
          simp only [Ordered.preparedCaptureIntervalsAtEntries, List.map_map]
          apply List.map_congr_left
          intro interval membership
          cases interval
          simp [renameCaptureInterval, ManySortedFC.StaticExpr.rename_comp,
            tailRhoEq]

theorem openedTypeIntervalsAt_openEntries
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (label : Nat)
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope scope symbols))) :
    openedTypeIntervalsAt label (openEntries entries) =
      (Ordered.preparedTypeIntervalsAtEntries label entries).map
        (renameTypeInterval
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedSignature.entriesRelations entries)))) := by
  rw [openEntries_eq_openEntriesWithTail]
  exact openedTypeIntervalsAt_openEntriesWithTail label entries []

theorem openedCaptureIntervalsAt_openEntries
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (label : Nat)
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope scope symbols))) :
    openedCaptureIntervalsAt label (openEntries entries) =
      (Ordered.preparedCaptureIntervalsAtEntries label entries).map
        (renameCaptureInterval
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedSignature.entriesRelations entries)))) := by
  rw [openEntries_eq_openEntriesWithTail]
  exact openedCaptureIntervalsAt_openEntriesWithTail label entries []

theorem openedTypeIntervalsAt_openEntriesWithTail_getElem
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (label ordinal : Nat)
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope scope symbols)))
    (tailRelations : List ManySortedFC.Relation)
    (interval : Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .type
        (ManySortedFC.SymbolScope scope symbols)))
    (sourceAt :
      (Ordered.preparedTypeIntervalsAtEntries label entries)[ordinal]? =
        some interval) :
    (openedTypeIntervalsAt label
      (openEntriesWithTail entries tailRelations []))[ordinal]? = some {
        lower := interval.lower.rename
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedSignature.entriesRelationsWithTail entries
                tailRelations)))
        upper := interval.upper.rename
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedSignature.entriesRelationsWithTail entries
                tailRelations))) } := by
  rw [openedTypeIntervalsAt_openEntriesWithTail]
  simp [sourceAt, renameTypeInterval]

theorem openedCaptureIntervalsAt_openEntriesWithTail_getElem
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (label ordinal : Nat)
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope scope symbols)))
    (tailRelations : List ManySortedFC.Relation)
    (interval : Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .capture
        (ManySortedFC.SymbolScope scope symbols)))
    (sourceAt :
      (Ordered.preparedCaptureIntervalsAtEntries label entries)[ordinal]? =
        some interval) :
    (openedCaptureIntervalsAt label
      (openEntriesWithTail entries tailRelations []))[ordinal]? = some {
        lower := interval.lower.rename
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedSignature.entriesRelationsWithTail entries
                tailRelations)))
        upper := interval.upper.rename
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedSignature.entriesRelationsWithTail entries
                tailRelations))) } := by
  rw [openedCaptureIntervalsAt_openEntriesWithTail]
  simp [sourceAt, renameCaptureInterval]

theorem openedTypeIntervalsAt_openEntries_getElem
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (label ordinal : Nat)
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope scope symbols)))
    (interval : Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .type
        (ManySortedFC.SymbolScope scope symbols)))
    (sourceAt :
      (Ordered.preparedTypeIntervalsAtEntries label entries)[ordinal]? =
        some interval) :
    (openedTypeIntervalsAt label (openEntries entries))[ordinal]? = some {
      lower := interval.lower.rename
        (ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope scope symbols)
          (ManySortedFC.evidenceKinds
            (PreparedSignature.entriesRelations entries)))
      upper := interval.upper.rename
        (ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope scope symbols)
          (ManySortedFC.evidenceKinds
            (PreparedSignature.entriesRelations entries))) } := by
  rw [openedTypeIntervalsAt_openEntries]
  simp [sourceAt, renameTypeInterval]

theorem openedCaptureIntervalsAt_openEntries_getElem
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (label ordinal : Nat)
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope scope symbols)))
    (interval : Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .capture
        (ManySortedFC.SymbolScope scope symbols)))
    (sourceAt :
      (Ordered.preparedCaptureIntervalsAtEntries label entries)[ordinal]? =
        some interval) :
    (openedCaptureIntervalsAt label (openEntries entries))[ordinal]? = some {
      lower := interval.lower.rename
        (ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope scope symbols)
          (ManySortedFC.evidenceKinds
            (PreparedSignature.entriesRelations entries)))
      upper := interval.upper.rename
        (ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope scope symbols)
          (ManySortedFC.evidenceKinds
            (PreparedSignature.entriesRelations entries))) } := by
  rw [openedCaptureIntervalsAt_openEntries]
  simp [sourceAt, renameCaptureInterval]

private theorem openTypeIntervals_preserves_tail
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (label : Nat)
    (name : ManySortedFC.BVar (ManySortedFC.SymbolScope scope symbols)
      (.symbol .type))
    (intervals : List (Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .type
        (ManySortedFC.SymbolScope scope symbols))))
    (tailRelations : List ManySortedFC.Relation)
    (tail : List (OpenedOccurrence scope symbols tailRelations))
    (occurrence : OpenedOccurrence scope symbols tailRelations)
    (membership : occurrence ∈ tail) :
    renameOpenedOccurrence
      (evidencePrefixRename scope symbols
        tailRelations (PreparedEntry.intervalRelations .type intervals))
      occurrence ∈
        openTypeIntervals label name intervals tailRelations tail := by
  induction intervals with
  | nil =>
      change renameOpenedOccurrence ManySortedFC.Rename.id occurrence ∈ tail
      rw [renameOpenedOccurrence_id]
      exact membership
  | cons current remaining induction =>
      simp only [openTypeIntervals]
      apply List.mem_cons.mpr
      right
      let older := renameOpenedOccurrence
        (evidencePrefixRename scope symbols tailRelations
          (PreparedEntry.intervalRelations .type remaining)) occurrence
      have mapped : older.weakenTwo (.inclusion .type) (.inclusion .type) ∈
          (openTypeIntervals label name remaining tailRelations tail).map
            (fun candidate => candidate.weakenTwo
              (.inclusion .type) (.inclusion .type)) :=
        List.mem_map.mpr ⟨older, induction, rfl⟩
      have shape : older.weakenTwo (.inclusion .type) (.inclusion .type) =
          renameOpenedOccurrence
            (evidencePrefixRename scope symbols tailRelations
              (PreparedEntry.intervalRelations .type
                (current :: remaining))) occurrence := by
        rw [weakenTwo_eq_renameOpenedOccurrence]
        rw [show older = renameOpenedOccurrence
          (evidencePrefixRename scope symbols tailRelations
            (PreparedEntry.intervalRelations .type remaining)) occurrence
          from rfl]
        rw [renameOpenedOccurrence_comp]
        apply congrArg (fun rho => renameOpenedOccurrence rho occurrence)
        apply ManySortedFC.Rename.ext
        intro kind index
        rfl
      exact shape ▸ mapped

private theorem openCaptureIntervals_preserves_tail
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (label : Nat)
    (name : ManySortedFC.BVar (ManySortedFC.SymbolScope scope symbols)
      (.symbol .capture))
    (intervals : List (Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .capture
        (ManySortedFC.SymbolScope scope symbols))))
    (tailRelations : List ManySortedFC.Relation)
    (tail : List (OpenedOccurrence scope symbols tailRelations))
    (occurrence : OpenedOccurrence scope symbols tailRelations)
    (membership : occurrence ∈ tail) :
    renameOpenedOccurrence
      (evidencePrefixRename scope symbols
        tailRelations (PreparedEntry.intervalRelations .capture intervals))
      occurrence ∈
        openCaptureIntervals label name intervals tailRelations tail := by
  induction intervals with
  | nil =>
      change renameOpenedOccurrence ManySortedFC.Rename.id occurrence ∈ tail
      rw [renameOpenedOccurrence_id]
      exact membership
  | cons current remaining induction =>
      simp only [openCaptureIntervals]
      apply List.mem_cons.mpr
      right
      let older := renameOpenedOccurrence
        (evidencePrefixRename scope symbols tailRelations
          (PreparedEntry.intervalRelations .capture remaining)) occurrence
      have mapped : older.weakenTwo (.inclusion .capture)
          (.inclusion .capture) ∈
          (openCaptureIntervals label name remaining tailRelations tail).map
            (fun candidate => candidate.weakenTwo
              (.inclusion .capture) (.inclusion .capture)) :=
        List.mem_map.mpr ⟨older, induction, rfl⟩
      have shape : older.weakenTwo (.inclusion .capture)
          (.inclusion .capture) =
          renameOpenedOccurrence
            (evidencePrefixRename scope symbols tailRelations
              (PreparedEntry.intervalRelations .capture
                (current :: remaining))) occurrence := by
        rw [weakenTwo_eq_renameOpenedOccurrence]
        rw [show older = renameOpenedOccurrence
          (evidencePrefixRename scope symbols tailRelations
            (PreparedEntry.intervalRelations .capture remaining)) occurrence
          from rfl]
        rw [renameOpenedOccurrence_comp]
        apply congrArg (fun rho => renameOpenedOccurrence rho occurrence)
        apply ManySortedFC.Rename.ext
        intro kind index
        rfl
      exact shape ▸ mapped

private theorem openClassifierIntervals_preserves_tail
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (label : Nat)
    (name : ManySortedFC.BVar (ManySortedFC.SymbolScope scope symbols)
      (.symbol .classifier))
    (intervals : List (Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .classifier
        (ManySortedFC.SymbolScope scope symbols))))
    (tailRelations : List ManySortedFC.Relation)
    (tail : List (OpenedOccurrence scope symbols tailRelations))
    (occurrence : OpenedOccurrence scope symbols tailRelations)
    (membership : occurrence ∈ tail) :
    renameOpenedOccurrence
      (evidencePrefixRename scope symbols tailRelations
        (PreparedEntry.intervalRelations .classifier intervals)) occurrence ∈
      openClassifierIntervals label name intervals tailRelations tail := by
  induction intervals with
  | nil =>
      change renameOpenedOccurrence ManySortedFC.Rename.id occurrence ∈ tail
      rw [renameOpenedOccurrence_id]
      exact membership
  | cons current remaining induction =>
      simp only [openClassifierIntervals]
      apply List.mem_cons.mpr
      right
      let older := renameOpenedOccurrence
        (evidencePrefixRename scope symbols tailRelations
          (PreparedEntry.intervalRelations .classifier remaining)) occurrence
      have mapped : older.weakenTwo (.inclusion .classifier)
          (.inclusion .classifier) ∈
          (openClassifierIntervals label name remaining tailRelations tail).map
            (fun candidate => candidate.weakenTwo
              (.inclusion .classifier) (.inclusion .classifier)) :=
        List.mem_map.mpr ⟨older, induction, rfl⟩
      have shape : older.weakenTwo (.inclusion .classifier)
          (.inclusion .classifier) =
          renameOpenedOccurrence
            (evidencePrefixRename scope symbols tailRelations
              (PreparedEntry.intervalRelations .classifier
                (current :: remaining))) occurrence := by
        rw [weakenTwo_eq_renameOpenedOccurrence]
        rw [show older = renameOpenedOccurrence
          (evidencePrefixRename scope symbols tailRelations
            (PreparedEntry.intervalRelations .classifier remaining)) occurrence
          from rfl]
        rw [renameOpenedOccurrence_comp]
        apply congrArg (fun rho => renameOpenedOccurrence rho occurrence)
        apply ManySortedFC.Rename.ext
        intro kind index
        rfl
      exact shape ▸ mapped

private theorem openEntries_contains_type
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope scope symbols)))
    (tailRelations : List ManySortedFC.Relation)
    (tail : List (OpenedOccurrence scope symbols tailRelations))
    {label : Nat}
    {name : ManySortedFC.BVar (ManySortedFC.SymbolScope scope symbols)
      (.symbol .type)}
    {intervals : List (Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .type
        (ManySortedFC.SymbolScope scope symbols)))}
    {interval : Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .type
        (ManySortedFC.SymbolScope scope symbols))}
    (entryMembership : PreparedEntry.type label name intervals ∈ entries)
    (intervalMembership : interval ∈ intervals) :
    ∃ lowerEvidence upperEvidence,
      OpenedOccurrence.type label
        ((ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope scope symbols)
          (ManySortedFC.evidenceKinds
            (PreparedSignature.entriesRelationsWithTail entries
              tailRelations))).var name)
        (interval.lower.rename
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedSignature.entriesRelationsWithTail entries
                tailRelations))))
        (interval.upper.rename
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedSignature.entriesRelationsWithTail entries
                tailRelations))))
        lowerEvidence upperEvidence ∈
          openEntriesWithTail entries tailRelations tail := by
  induction entries with
  | nil => cases entryMembership
  | cons current remaining induction =>
      rcases List.mem_cons.mp entryMembership with rfl | entryMembership
      · exact openTypeIntervals_contains label name intervals
          (PreparedSignature.entriesRelationsWithTail remaining tailRelations)
          (openEntriesWithTail remaining tailRelations tail)
          intervalMembership
      · obtain ⟨lowerEvidence, upperEvidence, retained⟩ :=
          induction entryMembership
        let tailRho := ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope scope symbols)
          (ManySortedFC.evidenceKinds
            (PreparedSignature.entriesRelationsWithTail remaining
              tailRelations))
        let older := OpenedOccurrence.type label (tailRho.var name)
          (interval.lower.rename tailRho) (interval.upper.rename tailRho)
          lowerEvidence upperEvidence
        cases current with
        | type currentLabel currentName currentIntervals =>
            let prefixRho := evidencePrefixRename scope symbols
              (PreparedSignature.entriesRelationsWithTail remaining
                tailRelations)
              (PreparedEntry.intervalRelations .type currentIntervals)
            have opened : renameOpenedOccurrence prefixRho older ∈
                openTypeIntervals currentLabel currentName currentIntervals
                  (PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations)
                  (openEntriesWithTail remaining tailRelations tail) :=
              openTypeIntervals_preserves_tail currentLabel currentName
                currentIntervals
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
                (openEntriesWithTail remaining tailRelations tail) older retained
            let fullRho := ManySortedFC.Rename.weakenMany
              (ManySortedFC.SymbolScope scope symbols)
              (ManySortedFC.evidenceKinds
                (PreparedEntry.intervalRelations .type currentIntervals ++
                  PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations))
            have rhoEq : tailRho.comp prefixRho = fullRho := by
              exact weakenMany_comp_evidencePrefix scope symbols
                (PreparedEntry.intervalRelations .type currentIntervals)
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
            refine ⟨(renameOpenedOccurrence prefixRho older).lowerEvidence,
              (renameOpenedOccurrence prefixRho older).upperEvidence, ?_⟩
            have shape : renameOpenedOccurrence prefixRho older =
                OpenedOccurrence.type label (fullRho.var name)
                  (interval.lower.rename fullRho)
                  (interval.upper.rename fullRho)
                  (renameOpenedOccurrence prefixRho older).lowerEvidence
                  (renameOpenedOccurrence prefixRho older).upperEvidence := by
              simp only [older, renameOpenedOccurrence,
                OpenedOccurrence.lowerEvidence,
                OpenedOccurrence.upperEvidence]
              rw [ManySortedFC.StaticExpr.rename_comp,
                ManySortedFC.StaticExpr.rename_comp, rhoEq]
              have nameEq : prefixRho.var (tailRho.var name) =
                  fullRho.var name := by
                exact congrArg (fun rho => rho.var name) rhoEq
              rw [nameEq]
            exact shape ▸ opened
        | capture currentLabel currentName currentIntervals =>
            let prefixRho := evidencePrefixRename scope symbols
              (PreparedSignature.entriesRelationsWithTail remaining
                tailRelations)
              (PreparedEntry.intervalRelations .capture currentIntervals)
            have opened : renameOpenedOccurrence prefixRho older ∈
                openCaptureIntervals currentLabel currentName currentIntervals
                  (PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations)
                  (openEntriesWithTail remaining tailRelations tail) :=
              openCaptureIntervals_preserves_tail currentLabel currentName
                currentIntervals
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
                (openEntriesWithTail remaining tailRelations tail) older retained
            let fullRho := ManySortedFC.Rename.weakenMany
              (ManySortedFC.SymbolScope scope symbols)
              (ManySortedFC.evidenceKinds
                (PreparedEntry.intervalRelations .capture currentIntervals ++
                  PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations))
            have rhoEq : tailRho.comp prefixRho = fullRho := by
              exact weakenMany_comp_evidencePrefix scope symbols
                (PreparedEntry.intervalRelations .capture currentIntervals)
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
            refine ⟨(renameOpenedOccurrence prefixRho older).lowerEvidence,
              (renameOpenedOccurrence prefixRho older).upperEvidence, ?_⟩
            have shape : renameOpenedOccurrence prefixRho older =
                OpenedOccurrence.type label (fullRho.var name)
                  (interval.lower.rename fullRho)
                  (interval.upper.rename fullRho)
                  (renameOpenedOccurrence prefixRho older).lowerEvidence
                  (renameOpenedOccurrence prefixRho older).upperEvidence := by
              simp only [older, renameOpenedOccurrence,
                OpenedOccurrence.lowerEvidence,
                OpenedOccurrence.upperEvidence]
              rw [ManySortedFC.StaticExpr.rename_comp,
                ManySortedFC.StaticExpr.rename_comp, rhoEq]
              have nameEq : prefixRho.var (tailRho.var name) =
                  fullRho.var name := by
                exact congrArg (fun rho => rho.var name) rhoEq
              rw [nameEq]
            exact shape ▸ opened
        | classifier currentLabel currentName currentIntervals =>
            let prefixRho := evidencePrefixRename scope symbols
              (PreparedSignature.entriesRelationsWithTail remaining
                tailRelations)
              (PreparedEntry.intervalRelations .classifier currentIntervals)
            have opened : renameOpenedOccurrence prefixRho older ∈
                openClassifierIntervals currentLabel currentName currentIntervals
                  (PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations)
                  (openEntriesWithTail remaining tailRelations tail) :=
              openClassifierIntervals_preserves_tail currentLabel currentName
                currentIntervals
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
                (openEntriesWithTail remaining tailRelations tail) older retained
            let fullRho := ManySortedFC.Rename.weakenMany
              (ManySortedFC.SymbolScope scope symbols)
              (ManySortedFC.evidenceKinds
                (PreparedEntry.intervalRelations .classifier currentIntervals ++
                  PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations))
            have rhoEq : tailRho.comp prefixRho = fullRho := by
              exact weakenMany_comp_evidencePrefix scope symbols
                (PreparedEntry.intervalRelations .classifier currentIntervals)
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
            refine ⟨(renameOpenedOccurrence prefixRho older).lowerEvidence,
              (renameOpenedOccurrence prefixRho older).upperEvidence, ?_⟩
            have shape : renameOpenedOccurrence prefixRho older =
                OpenedOccurrence.type label (fullRho.var name)
                  (interval.lower.rename fullRho)
                  (interval.upper.rename fullRho)
                  (renameOpenedOccurrence prefixRho older).lowerEvidence
                  (renameOpenedOccurrence prefixRho older).upperEvidence := by
              simp only [older, renameOpenedOccurrence,
                OpenedOccurrence.lowerEvidence,
                OpenedOccurrence.upperEvidence]
              rw [ManySortedFC.StaticExpr.rename_comp,
                ManySortedFC.StaticExpr.rename_comp, rhoEq]
              have nameEq : prefixRho.var (tailRho.var name) =
                  fullRho.var name := by
                exact congrArg (fun rho => rho.var name) rhoEq
              rw [nameEq]
            exact shape ▸ opened

private theorem openEntries_contains_capture
    {scope : ManySortedFC.Sig} {symbols : List ManySortedFC.StaticSort}
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope scope symbols)))
    (tailRelations : List ManySortedFC.Relation)
    (tail : List (OpenedOccurrence scope symbols tailRelations))
    {label : Nat}
    {name : ManySortedFC.BVar (ManySortedFC.SymbolScope scope symbols)
      (.symbol .capture)}
    {intervals : List (Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .capture
        (ManySortedFC.SymbolScope scope symbols)))}
    {interval : Preparation.Source.MemberInterval
      (ManySortedFC.StaticExpr .capture
        (ManySortedFC.SymbolScope scope symbols))}
    (entryMembership : PreparedEntry.capture label name intervals ∈ entries)
    (intervalMembership : interval ∈ intervals) :
    ∃ lowerEvidence upperEvidence,
      OpenedOccurrence.capture label
        ((ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope scope symbols)
          (ManySortedFC.evidenceKinds
            (PreparedSignature.entriesRelationsWithTail entries
              tailRelations))).var name)
        (interval.lower.rename
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedSignature.entriesRelationsWithTail entries
                tailRelations))))
        (interval.upper.rename
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope scope symbols)
            (ManySortedFC.evidenceKinds
              (PreparedSignature.entriesRelationsWithTail entries
                tailRelations))))
        lowerEvidence upperEvidence ∈
          openEntriesWithTail entries tailRelations tail := by
  induction entries with
  | nil => cases entryMembership
  | cons current remaining induction =>
      rcases List.mem_cons.mp entryMembership with rfl | entryMembership
      · exact openCaptureIntervals_contains label name intervals
          (PreparedSignature.entriesRelationsWithTail remaining tailRelations)
          (openEntriesWithTail remaining tailRelations tail)
          intervalMembership
      · obtain ⟨lowerEvidence, upperEvidence, retained⟩ :=
          induction entryMembership
        let tailRho := ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope scope symbols)
          (ManySortedFC.evidenceKinds
            (PreparedSignature.entriesRelationsWithTail remaining
              tailRelations))
        let older := OpenedOccurrence.capture label (tailRho.var name)
          (interval.lower.rename tailRho) (interval.upper.rename tailRho)
          lowerEvidence upperEvidence
        cases current with
        | type currentLabel currentName currentIntervals =>
            let prefixRho := evidencePrefixRename scope symbols
              (PreparedSignature.entriesRelationsWithTail remaining
                tailRelations)
              (PreparedEntry.intervalRelations .type currentIntervals)
            have opened : renameOpenedOccurrence prefixRho older ∈
                openTypeIntervals currentLabel currentName currentIntervals
                  (PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations)
                  (openEntriesWithTail remaining tailRelations tail) :=
              openTypeIntervals_preserves_tail currentLabel currentName
                currentIntervals
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
                (openEntriesWithTail remaining tailRelations tail) older retained
            let fullRho := ManySortedFC.Rename.weakenMany
              (ManySortedFC.SymbolScope scope symbols)
              (ManySortedFC.evidenceKinds
                (PreparedEntry.intervalRelations .type currentIntervals ++
                  PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations))
            have rhoEq : tailRho.comp prefixRho = fullRho := by
              exact weakenMany_comp_evidencePrefix scope symbols
                (PreparedEntry.intervalRelations .type currentIntervals)
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
            refine ⟨(renameOpenedOccurrence prefixRho older).lowerEvidence,
              (renameOpenedOccurrence prefixRho older).upperEvidence, ?_⟩
            have shape : renameOpenedOccurrence prefixRho older =
                OpenedOccurrence.capture label (fullRho.var name)
                  (interval.lower.rename fullRho)
                  (interval.upper.rename fullRho)
                  (renameOpenedOccurrence prefixRho older).lowerEvidence
                  (renameOpenedOccurrence prefixRho older).upperEvidence := by
              simp only [older, renameOpenedOccurrence,
                OpenedOccurrence.lowerEvidence,
                OpenedOccurrence.upperEvidence]
              rw [ManySortedFC.StaticExpr.rename_comp,
                ManySortedFC.StaticExpr.rename_comp, rhoEq]
              have nameEq : prefixRho.var (tailRho.var name) =
                  fullRho.var name := by
                exact congrArg (fun rho => rho.var name) rhoEq
              rw [nameEq]
            exact shape ▸ opened
        | capture currentLabel currentName currentIntervals =>
            let prefixRho := evidencePrefixRename scope symbols
              (PreparedSignature.entriesRelationsWithTail remaining
                tailRelations)
              (PreparedEntry.intervalRelations .capture currentIntervals)
            have opened : renameOpenedOccurrence prefixRho older ∈
                openCaptureIntervals currentLabel currentName currentIntervals
                  (PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations)
                  (openEntriesWithTail remaining tailRelations tail) :=
              openCaptureIntervals_preserves_tail currentLabel currentName
                currentIntervals
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
                (openEntriesWithTail remaining tailRelations tail) older retained
            let fullRho := ManySortedFC.Rename.weakenMany
              (ManySortedFC.SymbolScope scope symbols)
              (ManySortedFC.evidenceKinds
                (PreparedEntry.intervalRelations .capture currentIntervals ++
                  PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations))
            have rhoEq : tailRho.comp prefixRho = fullRho := by
              exact weakenMany_comp_evidencePrefix scope symbols
                (PreparedEntry.intervalRelations .capture currentIntervals)
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
            refine ⟨(renameOpenedOccurrence prefixRho older).lowerEvidence,
              (renameOpenedOccurrence prefixRho older).upperEvidence, ?_⟩
            have shape : renameOpenedOccurrence prefixRho older =
                OpenedOccurrence.capture label (fullRho.var name)
                  (interval.lower.rename fullRho)
                  (interval.upper.rename fullRho)
                  (renameOpenedOccurrence prefixRho older).lowerEvidence
                  (renameOpenedOccurrence prefixRho older).upperEvidence := by
              simp only [older, renameOpenedOccurrence,
                OpenedOccurrence.lowerEvidence,
                OpenedOccurrence.upperEvidence]
              rw [ManySortedFC.StaticExpr.rename_comp,
                ManySortedFC.StaticExpr.rename_comp, rhoEq]
              have nameEq : prefixRho.var (tailRho.var name) =
                  fullRho.var name := by
                exact congrArg (fun rho => rho.var name) rhoEq
              rw [nameEq]
            exact shape ▸ opened
        | classifier currentLabel currentName currentIntervals =>
            let prefixRho := evidencePrefixRename scope symbols
              (PreparedSignature.entriesRelationsWithTail remaining
                tailRelations)
              (PreparedEntry.intervalRelations .classifier currentIntervals)
            have opened : renameOpenedOccurrence prefixRho older ∈
                openClassifierIntervals currentLabel currentName currentIntervals
                  (PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations)
                  (openEntriesWithTail remaining tailRelations tail) :=
              openClassifierIntervals_preserves_tail currentLabel currentName
                currentIntervals
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
                (openEntriesWithTail remaining tailRelations tail) older retained
            let fullRho := ManySortedFC.Rename.weakenMany
              (ManySortedFC.SymbolScope scope symbols)
              (ManySortedFC.evidenceKinds
                (PreparedEntry.intervalRelations .classifier currentIntervals ++
                  PreparedSignature.entriesRelationsWithTail remaining
                    tailRelations))
            have rhoEq : tailRho.comp prefixRho = fullRho := by
              exact weakenMany_comp_evidencePrefix scope symbols
                (PreparedEntry.intervalRelations .classifier currentIntervals)
                (PreparedSignature.entriesRelationsWithTail remaining
                  tailRelations)
            refine ⟨(renameOpenedOccurrence prefixRho older).lowerEvidence,
              (renameOpenedOccurrence prefixRho older).upperEvidence, ?_⟩
            have shape : renameOpenedOccurrence prefixRho older =
                OpenedOccurrence.capture label (fullRho.var name)
                  (interval.lower.rename fullRho)
                  (interval.upper.rename fullRho)
                  (renameOpenedOccurrence prefixRho older).lowerEvidence
                  (renameOpenedOccurrence prefixRho older).upperEvidence := by
              simp only [older, renameOpenedOccurrence,
                OpenedOccurrence.lowerEvidence,
                OpenedOccurrence.upperEvidence]
              rw [ManySortedFC.StaticExpr.rename_comp,
                ManySortedFC.StaticExpr.rename_comp, rhoEq]
              have nameEq : prefixRho.var (tailRho.var name) =
                  fullRho.var name := by
                exact congrArg (fun rho => rho.var name) rhoEq
              rw [nameEq]
            exact shape ▸ opened
/-! These carriers are the executable boundary.  Unlike `TypeCoordinates`
and `CaptureCoordinates` below, they expose the concrete entries of
`Encoding.openedOccurrences`, so a compiler can search the finite list and
use retention only to prove that the search succeeds. -/

structure OpenedTypeCoordinates {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .type)) where
  name : ManySortedFC.BVar
    (ManySortedFC.SymbolScope targetScope prepared.symbols)
    (.symbol .type)
  intervals : List (Preparation.Source.MemberInterval
    (ManySortedFC.StaticExpr .type
      (ManySortedFC.SymbolScope targetScope prepared.symbols)))
  translated : Preparation.Source.MemberInterval
    (ManySortedFC.StaticExpr .type
      (ManySortedFC.SymbolScope targetScope prepared.symbols))
  entryMembership : PreparedEntry.type label name intervals ∈ prepared.entries
  intervalMembership : translated ∈ intervals
  translation : Preparation.Compile.translateMemberIntervals
    (layout.renameTarget
      (ManySortedFC.Rename.weakenSymbols prepared.symbols))
    prepared.members [sourceInterval] = .ok [translated]
  lowerEvidence : ManySortedFC.BVar
    (ManySortedFC.StaticScope targetScope prepared.symbols
      prepared.relations)
    (.evidence (.inclusion .type))
  upperEvidence : ManySortedFC.BVar
    (ManySortedFC.StaticScope targetScope prepared.symbols
      prepared.relations)
    (.evidence (.inclusion .type))
  occurrenceMembership :
    OpenedOccurrence.type label
      ((ManySortedFC.Rename.weakenMany
        (ManySortedFC.SymbolScope targetScope prepared.symbols)
        (ManySortedFC.evidenceKinds prepared.relations)).var name)
      (translated.lower.rename
        (ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope targetScope prepared.symbols)
          (ManySortedFC.evidenceKinds prepared.relations)))
      (translated.upper.rename
        (ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope targetScope prepared.symbols)
          (ManySortedFC.evidenceKinds prepared.relations)))
      lowerEvidence upperEvidence ∈ (encode prepared).openedOccurrences

structure OpenedCaptureCoordinates {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .capture)) where
  name : ManySortedFC.BVar
    (ManySortedFC.SymbolScope targetScope prepared.symbols)
    (.symbol .capture)
  intervals : List (Preparation.Source.MemberInterval
    (ManySortedFC.StaticExpr .capture
      (ManySortedFC.SymbolScope targetScope prepared.symbols)))
  translated : Preparation.Source.MemberInterval
    (ManySortedFC.StaticExpr .capture
      (ManySortedFC.SymbolScope targetScope prepared.symbols))
  entryMembership :
    PreparedEntry.capture label name intervals ∈ prepared.entries
  intervalMembership : translated ∈ intervals
  translation : Preparation.Compile.translateMemberIntervals
    (layout.renameTarget
      (ManySortedFC.Rename.weakenSymbols prepared.symbols))
    prepared.members [sourceInterval] = .ok [translated]
  lowerEvidence : ManySortedFC.BVar
    (ManySortedFC.StaticScope targetScope prepared.symbols
      prepared.relations)
    (.evidence (.inclusion .capture))
  upperEvidence : ManySortedFC.BVar
    (ManySortedFC.StaticScope targetScope prepared.symbols
      prepared.relations)
    (.evidence (.inclusion .capture))
  occurrenceMembership :
    OpenedOccurrence.capture label
      ((ManySortedFC.Rename.weakenMany
        (ManySortedFC.SymbolScope targetScope prepared.symbols)
        (ManySortedFC.evidenceKinds prepared.relations)).var name)
      (translated.lower.rename
        (ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope targetScope prepared.symbols)
          (ManySortedFC.evidenceKinds prepared.relations)))
      (translated.upper.rename
        (ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope targetScope prepared.symbols)
          (ManySortedFC.evidenceKinds prepared.relations)))
      lowerEvidence upperEvidence ∈ (encode prepared).openedOccurrences

theorem openedTypeCoordinates_nonempty_of_retained
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .type))
    (retained : Retained
      (layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols prepared.symbols))
      prepared.members (.type label sourceInterval) prepared.entries) :
    Nonempty (OpenedTypeCoordinates layout prepared label sourceInterval) := by
  obtain ⟨name, intervals, translated, entryMembership,
    intervalMembership, translation⟩ := retained
  obtain ⟨lowerEvidence, upperEvidence, occurrenceMembership⟩ :=
    openEntries_contains_type prepared.entries
      (prepared.constraints.map PreparedConstraint.relation) []
      entryMembership intervalMembership
  exact ⟨
    { name, intervals, translated, entryMembership, intervalMembership,
      translation, lowerEvidence, upperEvidence, occurrenceMembership }⟩

theorem openedCaptureCoordinates_nonempty_of_retained
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .capture))
    (retained : Retained
      (layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols prepared.symbols))
      prepared.members (.capture label sourceInterval) prepared.entries) :
    Nonempty
      (OpenedCaptureCoordinates layout prepared label sourceInterval) := by
  obtain ⟨name, intervals, translated, entryMembership,
    intervalMembership, translation⟩ := retained
  obtain ⟨lowerEvidence, upperEvidence, occurrenceMembership⟩ :=
    openEntries_contains_capture prepared.entries
      (prepared.constraints.map PreparedConstraint.relation) []
      entryMembership intervalMembership
  exact ⟨
    { name, intervals, translated, entryMembership, intervalMembership,
      translation, lowerEvidence, upperEvidence, occurrenceMembership }⟩

/-- Every proof-selected raw type occurrence appears in the executable
opened-occurrence enumeration. -/
theorem openedTypeCoordinates_nonempty_of_raw
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {label : Nat} {lower upper : Preparation.Source.Ty sourceScope}
    (occurrence : interface.HasTypeOccurrence label lower upper) :
    Nonempty (OpenedTypeCoordinates layout prepared label
      { lower := .type lower, upper := .type upper }) :=
  openedTypeCoordinates_nonempty_of_retained layout prepared label _
    (collectAndPrepare_retains_raw_occurrence layout interface success _
      (RawOccurrence.type_mem occurrence))

/-- Every proof-selected raw capture occurrence appears in the executable
opened-occurrence enumeration. -/
theorem openedCaptureCoordinates_nonempty_of_raw
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {label : Nat}
    {lower upper : Preparation.Source.Capture sourceScope}
    (occurrence : interface.HasCaptureOccurrence label lower upper) :
    Nonempty (OpenedCaptureCoordinates layout prepared label
      { lower := .capture lower, upper := .capture upper }) :=
  openedCaptureCoordinates_nonempty_of_retained layout prepared label _
    (collectAndPrepare_retains_raw_occurrence layout interface success _
      (RawOccurrence.capture_mem occurrence))

/-- Exact lower and upper coordinates for one retained type occurrence. -/
structure TypeCoordinates {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .type)) where
  name : ManySortedFC.BVar
    (ManySortedFC.SymbolScope targetScope prepared.symbols)
    (.symbol .type)
  intervals : List (Preparation.Source.MemberInterval
    (ManySortedFC.StaticExpr .type
      (ManySortedFC.SymbolScope targetScope prepared.symbols)))
  translated : Preparation.Source.MemberInterval
    (ManySortedFC.StaticExpr .type
      (ManySortedFC.SymbolScope targetScope prepared.symbols))
  entryMembership : PreparedEntry.type label name intervals ∈ prepared.entries
  intervalMembership : translated ∈ intervals
  translation : Preparation.Compile.translateMemberIntervals
    (layout.renameTarget
      (ManySortedFC.Rename.weakenSymbols prepared.symbols))
    prepared.members [sourceInterval] = .ok [translated]
  lower : ManySortedFC.ConstraintRef prepared.relations
    (.inclusion .type)
  upper : ManySortedFC.ConstraintRef prepared.relations
    (.inclusion .type)
  lowerProposition : (encode prepared).theory.propositionAt lower =
    .inclusion translated.lower (.type (.tvar name))
  upperProposition : (encode prepared).theory.propositionAt upper =
    .inclusion (.type (.tvar name)) translated.upper

/-- Capture-sorted counterpart of `TypeCoordinates`. -/
structure CaptureCoordinates {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .capture)) where
  name : ManySortedFC.BVar
    (ManySortedFC.SymbolScope targetScope prepared.symbols)
    (.symbol .capture)
  intervals : List (Preparation.Source.MemberInterval
    (ManySortedFC.StaticExpr .capture
      (ManySortedFC.SymbolScope targetScope prepared.symbols)))
  translated : Preparation.Source.MemberInterval
    (ManySortedFC.StaticExpr .capture
      (ManySortedFC.SymbolScope targetScope prepared.symbols))
  entryMembership :
    PreparedEntry.capture label name intervals ∈ prepared.entries
  intervalMembership : translated ∈ intervals
  translation : Preparation.Compile.translateMemberIntervals
    (layout.renameTarget
      (ManySortedFC.Rename.weakenSymbols prepared.symbols))
    prepared.members [sourceInterval] = .ok [translated]
  lower : ManySortedFC.ConstraintRef prepared.relations
    (.inclusion .capture)
  upper : ManySortedFC.ConstraintRef prepared.relations
    (.inclusion .capture)
  lowerProposition : (encode prepared).theory.propositionAt lower =
    .inclusion translated.lower (.capture (.cvar name))
  upperProposition : (encode prepared).theory.propositionAt upper =
    .inclusion (.capture (.cvar name)) translated.upper

/-- Classifier-sorted counterpart of `TypeCoordinates`. -/
structure ClassifierCoordinates {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .classifier)) where
  name : ManySortedFC.BVar
    (ManySortedFC.SymbolScope targetScope prepared.symbols)
    (.symbol .classifier)
  intervals : List (Preparation.Source.MemberInterval
    (ManySortedFC.StaticExpr .classifier
      (ManySortedFC.SymbolScope targetScope prepared.symbols)))
  translated : Preparation.Source.MemberInterval
    (ManySortedFC.StaticExpr .classifier
      (ManySortedFC.SymbolScope targetScope prepared.symbols))
  entryMembership :
    PreparedEntry.classifier label name intervals ∈ prepared.entries
  intervalMembership : translated ∈ intervals
  translation : Preparation.Compile.translateMemberIntervals
    (layout.renameTarget
      (ManySortedFC.Rename.weakenSymbols prepared.symbols))
    prepared.members [sourceInterval] = .ok [translated]
  lower : ManySortedFC.ConstraintRef prepared.relations
    (.inclusion .classifier)
  upper : ManySortedFC.ConstraintRef prepared.relations
    (.inclusion .classifier)
  lowerProposition : (encode prepared).theory.propositionAt lower =
    .inclusion translated.lower (.classifier (.var name))
  upperProposition : (encode prepared).theory.propositionAt upper =
    .inclusion (.classifier (.var name)) translated.upper

namespace ClassifierCoordinates

/-- Exact lookup for the lower classifier-inclusion evidence coordinate. -/
theorem lowerLookup
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    {layout : Layout sourceScope targetScope}
    {prepared : PreparedSignature targetScope}
    {label : Nat}
    {sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .classifier)}
    (coordinate : ClassifierCoordinates layout prepared label sourceInterval)
    (context : ManySortedFC.Ctx targetScope) :
    (context.extendTheory (encode prepared).theory).lookup
        (coordinate.lower.toEvidenceBVar
          (ManySortedFC.SymbolScope targetScope prepared.symbols)) =
      .evidence
        ((ManySortedFC.Proposition.inclusion coordinate.translated.lower
          (.classifier (.var coordinate.name))).rename
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope targetScope prepared.symbols)
            (ManySortedFC.evidenceKinds prepared.relations))) := by
  unfold ManySortedFC.Ctx.extendTheory
  change
    (ManySortedFC.Ctx.extendTheoryEvidence
      (context.extendSymbols prepared.symbols) (encode prepared).theory).lookup
        (coordinate.lower.toEvidenceBVar
          (ManySortedFC.SymbolScope targetScope prepared.symbols)) = _
  have found := ManySortedFC.Ctx.lookup_extendTheoryEvidence_constraint
    (context.extendSymbols prepared.symbols) (encode prepared).theory
      coordinate.lower
  have propositionAt := coordinate.lowerProposition
  simp only [encode] at propositionAt found ⊢
  rw [propositionAt] at found
  exact found

/-- Exact lookup for the upper classifier-inclusion evidence coordinate. -/
theorem upperLookup
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    {layout : Layout sourceScope targetScope}
    {prepared : PreparedSignature targetScope}
    {label : Nat}
    {sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .classifier)}
    (coordinate : ClassifierCoordinates layout prepared label sourceInterval)
    (context : ManySortedFC.Ctx targetScope) :
    (context.extendTheory (encode prepared).theory).lookup
        (coordinate.upper.toEvidenceBVar
          (ManySortedFC.SymbolScope targetScope prepared.symbols)) =
      .evidence
        ((ManySortedFC.Proposition.inclusion
          (.classifier (.var coordinate.name))
          coordinate.translated.upper).rename
          (ManySortedFC.Rename.weakenMany
            (ManySortedFC.SymbolScope targetScope prepared.symbols)
            (ManySortedFC.evidenceKinds prepared.relations))) := by
  unfold ManySortedFC.Ctx.extendTheory
  change
    (ManySortedFC.Ctx.extendTheoryEvidence
      (context.extendSymbols prepared.symbols) (encode prepared).theory).lookup
        (coordinate.upper.toEvidenceBVar
          (ManySortedFC.SymbolScope targetScope prepared.symbols)) = _
  have found := ManySortedFC.Ctx.lookup_extendTheoryEvidence_constraint
    (context.extendSymbols prepared.symbols) (encode prepared).theory
      coordinate.upper
  have propositionAt := coordinate.upperProposition
  simp only [encode] at propositionAt found ⊢
  rw [propositionAt] at found
  exact found

end ClassifierCoordinates

/-- A retained type occurrence has exact coordinates in the generated target
theory. -/
theorem typeCoordinates_nonempty_of_retained
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .type))
    (retained : Retained
      (layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols prepared.symbols))
      prepared.members (.type label sourceInterval) prepared.entries) :
    Nonempty (TypeCoordinates layout prepared label sourceInterval) := by
  obtain ⟨name, intervals, translated, entryMembership,
    intervalMembership, translation⟩ := retained
  have propositions := Encoding.contains_type_interval prepared
    entryMembership intervalMembership
  obtain ⟨lower, lowerProposition⟩ :=
    DOTCaptureToManySortedFC.Intersections.TheoryPermutationCoherence.PackedTheory.exists_matching_reference
      (encode prepared).theory _ propositions.1
  obtain ⟨upper, upperProposition⟩ :=
    DOTCaptureToManySortedFC.Intersections.TheoryPermutationCoherence.PackedTheory.exists_matching_reference
      (encode prepared).theory _ propositions.2
  exact ⟨
    { name, intervals, translated, entryMembership, intervalMembership,
      translation, lower, upper, lowerProposition, upperProposition }⟩

/-- Choose the exact coordinates established by the retention theorem. -/
noncomputable def typeCoordinatesOfRetained
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .type))
    (retained : Retained
      (layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols prepared.symbols))
      prepared.members (.type label sourceInterval) prepared.entries) :
    TypeCoordinates layout prepared label sourceInterval :=
  Classical.choice
    (typeCoordinates_nonempty_of_retained layout prepared label
      sourceInterval retained)

/-- A retained capture occurrence has exact coordinates in the generated
target theory. -/
theorem captureCoordinates_nonempty_of_retained
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .capture))
    (retained : Retained
      (layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols prepared.symbols))
      prepared.members (.capture label sourceInterval) prepared.entries) :
    Nonempty (CaptureCoordinates layout prepared label sourceInterval) := by
  obtain ⟨name, intervals, translated, entryMembership,
    intervalMembership, translation⟩ := retained
  have propositions := Encoding.contains_capture_interval prepared
    entryMembership intervalMembership
  obtain ⟨lower, lowerProposition⟩ :=
    DOTCaptureToManySortedFC.Intersections.TheoryPermutationCoherence.PackedTheory.exists_matching_reference
      (encode prepared).theory _ propositions.1
  obtain ⟨upper, upperProposition⟩ :=
    DOTCaptureToManySortedFC.Intersections.TheoryPermutationCoherence.PackedTheory.exists_matching_reference
      (encode prepared).theory _ propositions.2
  exact ⟨
    { name, intervals, translated, entryMembership, intervalMembership,
      translation, lower, upper, lowerProposition, upperProposition }⟩

/-- Choose the exact capture coordinates established by retention. -/
noncomputable def captureCoordinatesOfRetained
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .capture))
    (retained : Retained
      (layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols prepared.symbols))
      prepared.members (.capture label sourceInterval) prepared.entries) :
    CaptureCoordinates layout prepared label sourceInterval :=
  Classical.choice
    (captureCoordinates_nonempty_of_retained layout prepared label
      sourceInterval retained)

/-- A retained classifier occurrence has exact coordinates in the generated
target theory. -/
theorem classifierCoordinates_nonempty_of_retained
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .classifier))
    (retained : Retained
      (layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols prepared.symbols))
      prepared.members (.classifier label sourceInterval) prepared.entries) :
    Nonempty (ClassifierCoordinates layout prepared label sourceInterval) := by
  obtain ⟨name, intervals, translated, entryMembership,
    intervalMembership, translation⟩ := retained
  have propositions := Encoding.contains_classifier_interval prepared
    entryMembership intervalMembership
  obtain ⟨lower, lowerProposition⟩ :=
    DOTCaptureToManySortedFC.Intersections.TheoryPermutationCoherence.PackedTheory.exists_matching_reference
      (encode prepared).theory _ propositions.1
  obtain ⟨upper, upperProposition⟩ :=
    DOTCaptureToManySortedFC.Intersections.TheoryPermutationCoherence.PackedTheory.exists_matching_reference
      (encode prepared).theory _ propositions.2
  exact ⟨
    { name, intervals, translated, entryMembership, intervalMembership,
      translation, lower, upper, lowerProposition, upperProposition }⟩

/-- Choose the exact classifier coordinates established by retention. -/
noncomputable def classifierCoordinatesOfRetained
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (prepared : PreparedSignature targetScope)
    (label : Nat)
    (sourceInterval : Preparation.Source.MemberInterval
      (Preparation.Source.MemberExpr sourceScope .classifier))
    (retained : Retained
      (layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols prepared.symbols))
      prepared.members (.classifier label sourceInterval) prepared.entries) :
    ClassifierCoordinates layout prepared label sourceInterval :=
  Classical.choice
    (classifierCoordinates_nonempty_of_retained layout prepared label
      sourceInterval retained)

/-- Total raw type-occurrence to generated-constraint correspondence. -/
noncomputable def typeCoordinatesOfRaw
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {label : Nat} {lower upper : Preparation.Source.Ty sourceScope}
    (occurrence : interface.HasTypeOccurrence label lower upper) :
    TypeCoordinates layout prepared label
      { lower := .type lower, upper := .type upper } :=
  typeCoordinatesOfRetained layout prepared label _
    (collectAndPrepare_retains_raw_occurrence layout interface success _
      (RawOccurrence.type_mem occurrence))

/-- Total raw capture-occurrence to generated-constraint correspondence. -/
noncomputable def captureCoordinatesOfRaw
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {label : Nat}
    {lower upper : Preparation.Source.Capture sourceScope}
    (occurrence : interface.HasCaptureOccurrence label lower upper) :
    CaptureCoordinates layout prepared label
      { lower := .capture lower, upper := .capture upper } :=
  captureCoordinatesOfRetained layout prepared label _
    (collectAndPrepare_retains_raw_occurrence layout interface success _
      (RawOccurrence.capture_mem occurrence))

/-- Total raw classifier-occurrence to generated-constraint correspondence. -/
noncomputable def classifierCoordinatesOfRaw
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {label : Nat}
    {lower upper : Preparation.Source.ClassifierExpr sourceScope}
    (occurrence : interface.HasClassifierOccurrence label lower upper) :
    ClassifierCoordinates layout prepared label
      { lower := lower, upper := upper } :=
  classifierCoordinatesOfRetained layout prepared label _
    (collectAndPrepare_retains_raw_occurrence layout interface success _
      (RawOccurrence.classifier_mem occurrence))

/-! ## Prepared-object specialization -/

/-- Successful object preparation exposes the exact successful interface
preparation stored in its encoding. -/
theorem prepareObject_interface
    {sourceScope : Preparation.Source.Sig}
    {targetScope : Preparation.Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Preparation.Source.ObjectType sourceScope)
    {object : Preparation.PreparedObject targetScope}
    (success : Preparation.prepareObject layout source = .ok object) :
    Preparation.collectAndPrepare layout source.interface =
      .ok object.encoding.prepared := by
  simp only [Preparation.prepareObject] at success
  cases preparedResult : Preparation.collectAndPrepare layout source.interface with
  | error failure =>
      rw [preparedResult] at success
      nomatch success
  | ok prepared =>
      rw [preparedResult] at success
      simp only [
        DOTCaptureToManySortedFC.Intersections.Encoding.Encoding.symbols,
        DOTCaptureToManySortedFC.Intersections.Encoding.Encoding.relations,
        DOTCaptureToManySortedFC.Intersections.Encoding.encode] at success
      simp only [bind, Except.bind] at success
      cases representationResult : Preparation.Compile.translateType
          (layout.renameTarget
            (ManySortedFC.Rename.weakenSymbols prepared.symbols))
          prepared.members source.representation with
      | error failure =>
          rw [representationResult] at success
          nomatch success
      | ok targetRepresentation =>
          rw [representationResult] at success
          cases captureResult : Preparation.translateCapture layout
              source.packageCapture with
          | error failure =>
              simp only [Preparation.translateCapture] at captureResult
              rw [captureResult] at success
              nomatch success
          | ok targetCapture =>
              simp only [Preparation.translateCapture] at captureResult
              rw [captureResult] at success
              injection success with objectEq
              subst object
              rfl

end DOTCaptureToManySortedFC.ModalIntersections.ConstraintRetention
