import Coercions.Translation.ManySorted.Intersections.EncodingMetatheory
import Coercions.Translation.ManySorted.Intersections.PreparationMetatheory

/-!
# End-to-end retention of intersection constraints

This file connects the three representations used by M11:

* declaration occurrences in the raw intersection tree;
* interval occurrences in the normalized, one-entry-per-label signature;
* the exact lower/name and name/upper propositions emitted in ManySortedFC.

Mixed classifier constraints follow the parallel path from the raw tree to
the normalized constraint tail and then to an exact target proposition.

The result is per occurrence.  It does not infer satisfiability, combine
endpoints, or rely on a cardinality argument.
-/

namespace DOTCaptureToManySortedFC.Intersections.ConstraintRetention

open DOTCaptureToManySortedFC.Intersections
open Encoding
open Preparation

abbrev SourceOccurrence (scope : Preparation.Source.Scope) :=
  DOTCapture.Intersections.Occurrence (Preparation.Source.Expr scope)

/-! ## Raw declaration occurrences -/

/-- Flatten the raw interface tree without normalizing labels.  This is the
source-side list whose elements the final theorem quantifies over. -/
def rawOccurrences {scope : Preparation.Source.Scope} :
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
        { lower := .classifier lower
          upper := .classifier upper }]
  | .classifierDisjoint _ _ => []
  | .captureHasKind _ _ => []
  | .inter left right => rawOccurrences left ++ rawOccurrences right

/-- A mixed static constraint contributed by the raw interface.  These live
in the normalized signature's constraint tail, separately from member
interval occurrences. -/
abbrev SourceConstraint (scope : Preparation.Source.Scope) :=
  DOTCapture.Intersections.Constraint (Preparation.Source.Expr scope)

/-- Flatten mixed constraints in source order.  Collection neither sorts nor
combines this tail. -/
def rawConstraints {scope : Preparation.Source.Scope} :
    Preparation.Source.Interface scope -> List (SourceConstraint scope)
  | .empty => []
  | .typeMember _ _ _ => []
  | .captureMember _ _ _ => []
  | .classifierMember _ _ _ => []
  | .classifierDisjoint left right =>
      [.classifierDisjoint (.classifier left) (.classifier right)]
  | .captureHasKind capture classifier =>
      [.captureHasKind (.capture capture) (.classifier classifier)]
  | .inter left right => rawConstraints left ++ rawConstraints right

/-- Successful collection changes only canonical order and grouping.  Every
raw declaration occurrence is present in the normalized signature. -/
theorem collect_occurrences {scope : Preparation.Source.Scope}
    (interface : Preparation.Source.Interface scope)
    {signature : Preparation.Source.Signature
      (Preparation.Source.Expr scope)}
    (success : interface.collect = .ok signature) :
    signature.occurrences.Perm (rawOccurrences interface) := by
  cases interface with
  | empty =>
      simp only [DOTCapture.Intersections.Source.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | typeMember label lower upper =>
      simp only [DOTCapture.Intersections.Source.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | captureMember label lower upper =>
      simp only [DOTCapture.Intersections.Source.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | classifierMember label lower upper =>
      simp only [DOTCapture.Intersections.Source.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | classifierDisjoint left right =>
      simp only [DOTCapture.Intersections.Source.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | captureHasKind capture classifier =>
      simp only [DOTCapture.Intersections.Source.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | inter left right =>
      simp only [DOTCapture.Intersections.Source.Interface.collect] at success
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
source order. -/
theorem collect_constraints {scope : Preparation.Source.Scope}
    (interface : Preparation.Source.Interface scope)
    {signature : Preparation.Source.Signature
      (Preparation.Source.Expr scope)}
    (success : interface.collect = .ok signature) :
    signature.constraints = rawConstraints interface := by
  cases interface with
  | empty =>
      simp only [DOTCapture.Intersections.Source.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | typeMember label lower upper =>
      simp only [DOTCapture.Intersections.Source.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | captureMember label lower upper =>
      simp only [DOTCapture.Intersections.Source.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | classifierMember label lower upper =>
      simp only [DOTCapture.Intersections.Source.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | classifierDisjoint left right =>
      simp only [DOTCapture.Intersections.Source.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | captureHasKind capture classifier =>
      simp only [DOTCapture.Intersections.Source.Interface.collect,
        Except.ok.injEq] at success
      subst signature
      rfl
  | inter left right =>
      simp only [DOTCapture.Intersections.Source.Interface.collect] at success
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

/-! ## Preparation retains translated intervals -/

/-- One normalized source occurrence is represented by one target interval
under the allocated member for its label. -/
def Retained {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : SourceOccurrence sourceScope)
    (entries : List (PreparedEntry targetScope)) : Prop :=
  match source with
  | .type label interval =>
      ∃ name intervals translated,
        PreparedEntry.type label name intervals ∈ entries ∧
        translated ∈ intervals ∧
        Preparation.Compile.translateInterval layout members interval =
          .ok translated
  | .capture label interval =>
      ∃ name intervals translated,
        PreparedEntry.capture label name intervals ∈ entries ∧
        translated ∈ intervals ∧
        Preparation.Compile.translateInterval layout members interval =
          .ok translated
  | .classifier label interval =>
      ∃ name intervals translated,
        PreparedEntry.classifier label name intervals ∈ entries ∧
        translated ∈ intervals ∧
        Preparation.Compile.translateInterval layout members interval =
          .ok translated

/-- One normalized mixed constraint is translated and retained in the
prepared constraint tail. -/
def ConstraintRetained {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : SourceConstraint sourceScope)
    (constraints : List (PreparedConstraint targetScope)) : Prop :=
  ∃ translated, translated ∈ constraints ∧
    Preparation.Compile.translateConstraint layout members source =
      .ok translated

private theorem Retained.cons
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    {layout : Preparation.OuterLayout sourceScope targetScope}
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

private theorem translateIntervals_retains
    {sort : Preparation.Source.StaticSort}
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (sourceIntervals : List
      (Preparation.Source.Interval
        (Preparation.Source.Expr sourceScope sort)))
    {targetIntervals : List
      (Preparation.Source.Interval
        (ManySortedFC.StaticExpr (targetSort sort) targetScope))}
    (success : Preparation.Compile.translateIntervals layout members
      sourceIntervals = .ok targetIntervals)
    {sourceInterval : Preparation.Source.Interval
      (Preparation.Source.Expr sourceScope sort)}
    (membership : sourceInterval ∈ sourceIntervals) :
    ∃ targetInterval ∈ targetIntervals,
      Preparation.Compile.translateInterval layout members sourceInterval =
        .ok targetInterval := by
  induction sourceIntervals generalizing targetIntervals with
  | nil => cases membership
  | cons current remaining induction =>
      simp only [Preparation.Compile.translateIntervals] at success
      cases currentResult :
          Preparation.Compile.translateInterval layout members current with
      | error failure =>
          rw [currentResult] at success
          nomatch success
      | ok translatedCurrent =>
          cases remainingResult :
              Preparation.Compile.translateIntervals layout members remaining with
          | error failure =>
              rw [currentResult, remainingResult] at success
              nomatch success
          | ok translatedRemaining =>
              rw [currentResult, remainingResult] at success
              injection success with targetIntervalsEq
              subst targetIntervals
              rcases List.mem_cons.mp membership with rfl | tailMembership
              · exact ⟨translatedCurrent, .head _, currentResult⟩
              · obtain ⟨translated, translatedMember, translatedResult⟩ :=
                  induction remainingResult tailMembership
                exact ⟨translated, .tail _ translatedMember,
                  translatedResult⟩

/-- Successful entry translation retains every normalized occurrence and
records the translated interval under the entry's one allocated name. -/
theorem entries_retain_occurrence
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (allMembers : List (MemberName targetScope))
    (sourceEntries : List
      (Preparation.Source.Entry (Preparation.Source.Expr sourceScope)))
    (allocated : List (MemberName targetScope))
    {preparedEntries : List (PreparedEntry targetScope)}
    (success : Preparation.Compile.entries layout allMembers sourceEntries
      allocated = .ok preparedEntries)
    (source : SourceOccurrence sourceScope)
    (membership : source ∈
      ({ entries := sourceEntries } : Preparation.Source.Signature
        (Preparation.Source.Expr sourceScope)).occurrences) :
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
                      simp only [Preparation.Compile.entries]
                        at success
                      cases intervalResult :
                          Preparation.Compile.translateIntervals layout
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
                                  translatedResult⟩ :=
                                translateIntervals_retains layout allMembers
                                  sourceIntervals intervalResult
                                  sourceIntervalMember
                              exact ⟨name, translatedIntervals, translated,
                                .head _, translatedMember, translatedResult⟩
                    · simp [Preparation.Compile.entries, labelsMatch] at success
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
                      simp only [Preparation.Compile.entries]
                        at success
                      cases intervalResult :
                          Preparation.Compile.translateIntervals layout
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
                                  translatedResult⟩ :=
                                translateIntervals_retains layout allMembers
                                  sourceIntervals intervalResult
                                  sourceIntervalMember
                              exact ⟨name, translatedIntervals, translated,
                                .head _, translatedMember, translatedResult⟩
                    · simp [Preparation.Compile.entries, labelsMatch] at success
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
                          Preparation.Compile.translateIntervals layout
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
                                  translatedResult⟩ :=
                                translateIntervals_retains layout allMembers
                                  sourceIntervals intervalResult
                                  sourceIntervalMember
                              exact ⟨name, translatedIntervals, translated,
                                .head _, translatedMember, translatedResult⟩
                    · simp [Preparation.Compile.entries, labelsMatch] at success
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
                          Preparation.Compile.translateIntervals layout
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
                    · simp [Preparation.Compile.entries, labelsMatch] at success
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
                          Preparation.Compile.translateIntervals layout
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
                    · simp [Preparation.Compile.entries, labelsMatch] at success
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
                          Preparation.Compile.translateIntervals layout
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
                    · simp [Preparation.Compile.entries, labelsMatch] at success

/-- Entry preparation copies the allocated member coordinates exactly.  It
never allocates another name while translating constraints. -/
theorem entries_preserve_members
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (allMembers : List (MemberName targetScope))
    (sourceEntries : List
      (Preparation.Source.Entry (Preparation.Source.Expr sourceScope)))
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
      | nil => cases sourceEntry <;> simp [Preparation.Compile.entries] at success
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
                        Preparation.Compile.translateIntervals layout
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
                            simpa [PreparedEntry.member] using
                              congrArg
                                (fun tail => MemberName.type label name :: tail)
                                (induction allocatedRemaining remainingResult)
                  · simp [Preparation.Compile.entries, labelsMatch] at success

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
                        Preparation.Compile.translateIntervals layout
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
                            simpa [PreparedEntry.member] using
                              congrArg
                                (fun tail =>
                                  MemberName.capture label name :: tail)
                                (induction allocatedRemaining remainingResult)
                  · simp [Preparation.Compile.entries, labelsMatch] at success

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
                        Preparation.Compile.translateIntervals layout
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
                            simpa [PreparedEntry.member] using
                              congrArg
                                (fun tail =>
                                  MemberName.classifier label name :: tail)
                                (induction allocatedRemaining remainingResult)
                  · simp [Preparation.Compile.entries, labelsMatch] at success

private theorem translateConstraints_retains
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (sourceConstraints : List (SourceConstraint sourceScope))
    {targetConstraints : List (PreparedConstraint targetScope)}
    (success : Preparation.Compile.translateConstraints layout members
      sourceConstraints = .ok targetConstraints)
    {source : SourceConstraint sourceScope}
    (membership : source ∈ sourceConstraints) :
    ConstraintRetained layout members source targetConstraints := by
  induction sourceConstraints generalizing targetConstraints with
  | nil => cases membership
  | cons current remaining induction =>
      simp only [Preparation.Compile.translateConstraints] at success
      cases currentResult :
          Preparation.Compile.translateConstraint layout members current with
      | error failure =>
          rw [currentResult] at success
          nomatch success
      | ok translatedCurrent =>
          cases remainingResult :
              Preparation.Compile.translateConstraints layout members
                remaining with
          | error failure =>
              rw [currentResult, remainingResult] at success
              nomatch success
          | ok translatedRemaining =>
              rw [currentResult, remainingResult] at success
              injection success with targetConstraintsEq
              subst targetConstraints
              rcases List.mem_cons.mp membership with rfl | tailMembership
              · exact ⟨translatedCurrent, .head _, currentResult⟩
              · obtain ⟨translated, translatedMember, translatedResult⟩ :=
                  induction remainingResult tailMembership
                exact ⟨translated, .tail _ translatedMember,
                  translatedResult⟩

/-- The successful preparation of a normalized signature retains each of its
source occurrences under the complete, shared allocation it actually emits. -/
theorem prepare_retains_occurrence
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (signature : Preparation.Source.Signature
      (Preparation.Source.Expr sourceScope))
    {prepared : PreparedSignature targetScope}
    (success : Preparation.prepare layout signature = .ok prepared)
    (source : SourceOccurrence sourceScope)
    (membership : source ∈ signature.occurrences) :
    Retained
      (Preparation.Compile.weakenLayout layout prepared.symbols)
      prepared.members source prepared.entries := by
  unfold Preparation.prepare at success
  let symbols := Preparation.Allocation.symbols signature.entries
  let allocated := Preparation.Allocation.members targetScope signature.entries
  let namesLayout := Preparation.Compile.weakenLayout layout symbols
  cases entriesResult : Preparation.Compile.entries namesLayout allocated
      signature.entries allocated with
  | error failure =>
      simp only [symbols, allocated, namesLayout, entriesResult, bind,
        Except.bind] at success
      nomatch success
  | ok preparedEntries =>
      cases constraintsResult :
          Preparation.Compile.translateConstraints namesLayout allocated
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

/-- Successful preparation also retains each normalized mixed constraint;
success includes successful translation of the complete constraint tail. -/
theorem prepare_retains_constraint
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (signature : Preparation.Source.Signature
      (Preparation.Source.Expr sourceScope))
    {prepared : PreparedSignature targetScope}
    (success : Preparation.prepare layout signature = .ok prepared)
    (source : SourceConstraint sourceScope)
    (membership : source ∈ signature.constraints) :
    ConstraintRetained
      (Preparation.Compile.weakenLayout layout prepared.symbols)
      prepared.members source prepared.constraints := by
  unfold Preparation.prepare at success
  let symbols := Preparation.Allocation.symbols signature.entries
  let allocated := Preparation.Allocation.members targetScope signature.entries
  let namesLayout := Preparation.Compile.weakenLayout layout symbols
  cases entriesResult : Preparation.Compile.entries namesLayout allocated
      signature.entries allocated with
  | error failure =>
      simp only [symbols, allocated, namesLayout, entriesResult, bind,
        Except.bind] at success
      nomatch success
  | ok preparedEntries =>
      cases constraintsResult :
          Preparation.Compile.translateConstraints namesLayout allocated
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
          have retained := translateConstraints_retains namesLayout allocated
            signature.constraints constraintsResult membership
          have membersEq := entries_preserve_members namesLayout allocated
            signature.entries allocated entriesResult
          simpa [PreparedSignature.members, membersEq] using retained

/-- Successful collection followed by preparation retains every occurrence
from the raw interface tree. -/
theorem collectAndPrepare_retains_raw_occurrence
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    (source : SourceOccurrence sourceScope)
    (membership : source ∈ rawOccurrences interface) :
    Retained
      (Preparation.Compile.weakenLayout layout prepared.symbols)
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

/-- Collection followed by preparation retains every raw mixed constraint
and its exact translation result. -/
theorem collectAndPrepare_retains_raw_constraint
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    (source : SourceConstraint sourceScope)
    (membership : source ∈ rawConstraints interface) :
    ConstraintRetained
      (Preparation.Compile.weakenLayout layout prepared.symbols)
      prepared.members source prepared.constraints := by
  unfold Preparation.collectAndPrepare at success
  cases collected : interface.collect with
  | error conflict =>
      rw [collected] at success
      nomatch success
  | ok signature =>
      rw [collected] at success
      have normalizedMembership : source ∈ signature.constraints := by
        rw [collect_constraints interface collected]
        exact membership
      exact prepare_retains_constraint layout signature success source
        normalizedMembership

private theorem translateInterval_endpoints
    {sort : Preparation.Source.StaticSort}
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Preparation.Source.Interval
      (Preparation.Source.Expr sourceScope sort))
    (translated : Preparation.Source.Interval
      (ManySortedFC.StaticExpr (targetSort sort) targetScope))
    (success : Preparation.Compile.translateInterval layout members source =
      .ok translated) :
    Preparation.Compile.translateStaticExpr layout members source.lower =
        .ok translated.lower ∧
      Preparation.Compile.translateStaticExpr layout members source.upper =
        .ok translated.upper := by
  unfold Preparation.Compile.translateInterval at success
  unfold Preparation.Compile.translateStaticExpr
  cases lowerResult : Preparation.Compile.translateStaticExpr layout members
      source.lower with
  | error failure =>
      rw [lowerResult] at success
      nomatch success
  | ok lower =>
      cases upperResult : Preparation.Compile.translateStaticExpr layout members
          source.upper with
      | error failure =>
          rw [lowerResult, upperResult] at success
          nomatch success
      | ok upper =>
          rw [lowerResult, upperResult] at success
          injection success with translatedEq
          subst translated
          exact ⟨lowerResult, upperResult⟩

private theorem member_unique_by_label
    {scope : Encoding.Target.Sig}
    (members : List (MemberName scope))
    (labelsNodup : (members.map MemberName.label).Nodup)
    (member other : MemberName scope)
    (memberMembership : member ∈ members)
    (otherMembership : other ∈ members)
    (sameLabel : other.label = member.label) : other = member := by
  induction members with
  | nil => cases memberMembership
  | cons head tail induction =>
      have headNotIn : head.label ∉ tail.map MemberName.label :=
        (List.nodup_cons.mp labelsNodup).1
      have tailNodup : (tail.map MemberName.label).Nodup :=
        (List.nodup_cons.mp labelsNodup).2
      rcases List.mem_cons.mp memberMembership with rfl | memberTail
      · rcases List.mem_cons.mp otherMembership with rfl | otherTail
        · rfl
        · exfalso
          exact headNotIn
            (List.mem_map.mpr ⟨other, otherTail, sameLabel⟩)
      · rcases List.mem_cons.mp otherMembership with rfl | otherTail
        · exfalso
          exact headNotIn
            (List.mem_map.mpr ⟨member, memberTail, sameLabel.symm⟩)
        · exact induction tailNodup memberTail otherTail

/-! ## Exact emitted propositions -/

/-- The exact target claim for one raw declaration occurrence.  Besides the
two emitted propositions it records endpoint translation and says that the
member appearing in both propositions is the unique allocated member at the
source label. -/
def Emitted {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    (prepared : PreparedSignature targetScope)
    (layout : Preparation.OuterLayout sourceScope
      (Encoding.Target.SymbolScope targetScope prepared.symbols))
    (source : SourceOccurrence sourceScope) : Prop :=
  match source with
  | .type label interval =>
      ∃ name, ∃ translated : Preparation.Source.Interval
          (ManySortedFC.StaticExpr .type
            (Encoding.Target.SymbolScope targetScope prepared.symbols)),
        MemberName.type label name ∈ prepared.members ∧
        (∀ other ∈ prepared.members, other.label = label →
          other = MemberName.type label name) ∧
        Preparation.Compile.translateStaticExpr layout prepared.members
            interval.lower = .ok translated.lower ∧
        Preparation.Compile.translateStaticExpr layout prepared.members
            interval.upper = .ok translated.upper ∧
        Target.PackedProposition.pack
            (.inclusion translated.lower (.type (.tvar name))) ∈
          Target.Theory.propositions (encode prepared).theory ∧
        Target.PackedProposition.pack
            (.inclusion (.type (.tvar name)) translated.upper) ∈
          Target.Theory.propositions (encode prepared).theory
  | .capture label interval =>
      ∃ name, ∃ translated : Preparation.Source.Interval
          (ManySortedFC.StaticExpr .capture
            (Encoding.Target.SymbolScope targetScope prepared.symbols)),
        MemberName.capture label name ∈ prepared.members ∧
        (∀ other ∈ prepared.members, other.label = label →
          other = MemberName.capture label name) ∧
        Preparation.Compile.translateStaticExpr layout prepared.members
            interval.lower = .ok translated.lower ∧
        Preparation.Compile.translateStaticExpr layout prepared.members
            interval.upper = .ok translated.upper ∧
        Target.PackedProposition.pack
            (.inclusion translated.lower (.capture (.cvar name))) ∈
          Target.Theory.propositions (encode prepared).theory ∧
        Target.PackedProposition.pack
            (.inclusion (.capture (.cvar name)) translated.upper) ∈
          Target.Theory.propositions (encode prepared).theory
  | .classifier label interval =>
      ∃ name, ∃ translated : Preparation.Source.Interval
          (ManySortedFC.StaticExpr .classifier
            (Encoding.Target.SymbolScope targetScope prepared.symbols)),
        MemberName.classifier label name ∈ prepared.members ∧
        (∀ other ∈ prepared.members, other.label = label →
          other = MemberName.classifier label name) ∧
        Preparation.Compile.translateStaticExpr layout prepared.members
            interval.lower = .ok translated.lower ∧
        Preparation.Compile.translateStaticExpr layout prepared.members
            interval.upper = .ok translated.upper ∧
        Target.PackedProposition.pack
            (.inclusion translated.lower (.classifier (.var name))) ∈
          Target.Theory.propositions (encode prepared).theory ∧
        Target.PackedProposition.pack
            (.inclusion (.classifier (.var name)) translated.upper) ∈
          Target.Theory.propositions (encode prepared).theory

/-- The exact target claim for one raw mixed constraint. -/
def ConstraintEmitted {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    (prepared : PreparedSignature targetScope)
    (layout : Preparation.OuterLayout sourceScope
      (Encoding.Target.SymbolScope targetScope prepared.symbols))
    (source : SourceConstraint sourceScope) : Prop :=
  ∃ translated, Preparation.Compile.translateConstraint layout
      prepared.members source = .ok translated ∧
    translated.packed ∈
      Target.Theory.propositions (encode prepared).theory

/-- Every raw mixed constraint is translated exactly once and appears in the
emitted ManySortedFC theory. -/
theorem collectAndPrepare_emits_raw_constraint
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    (source : SourceConstraint sourceScope)
    (membership : source ∈ rawConstraints interface) :
    ConstraintEmitted prepared
      (Preparation.Compile.weakenLayout layout prepared.symbols) source := by
  obtain ⟨translated, translatedMember, translatedResult⟩ :=
    collectAndPrepare_retains_raw_constraint layout interface success source
      membership
  exact ⟨translated, translatedResult,
    Encoding.contains_constraint prepared translatedMember⟩

/-- Every raw occurrence reaches its two exact ManySortedFC propositions.
All occurrences at its label use the unique name allocated after label-first
normalization.  No consistency assumption is used. -/
theorem collectAndPrepare_emits_raw_occurrence
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Encoding.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (interface : Preparation.Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    (source : SourceOccurrence sourceScope)
    (membership : source ∈ rawOccurrences interface) :
    Emitted prepared
      (Preparation.Compile.weakenLayout layout prepared.symbols) source := by
  have retained := collectAndPrepare_retains_raw_occurrence layout interface
    success source membership
  unfold Preparation.collectAndPrepare at success
  cases collected : interface.collect with
  | error conflict =>
      rw [collected] at success
      nomatch success
  | ok signature =>
      rw [collected] at success
      have normalized :=
        DOTCapture.Intersections.Source.Interface.collect_normalized interface
          collected
      have labelsNodup := Preparation.prepare_member_labels_nodup layout
        signature normalized success
      cases source with
      | type label interval =>
          obtain ⟨name, intervals, translated, entryMember,
            intervalMember, translatedResult⟩ := retained
          have memberMembership : MemberName.type label name ∈
              prepared.members := by
            apply List.mem_map.mpr
            exact ⟨PreparedEntry.type label name intervals, entryMember, rfl⟩
          have endpoints := translateInterval_endpoints
            (Preparation.Compile.weakenLayout layout prepared.symbols)
            prepared.members interval translated translatedResult
          have propositions := Encoding.contains_type_interval prepared
            entryMember intervalMember
          exact ⟨name, translated, memberMembership,
            fun other otherMember sameLabel =>
              member_unique_by_label prepared.members labelsNodup
                (MemberName.type label name) other memberMembership otherMember
                sameLabel,
            endpoints.1, endpoints.2, propositions.1, propositions.2⟩
      | capture label interval =>
          obtain ⟨name, intervals, translated, entryMember,
            intervalMember, translatedResult⟩ := retained
          have memberMembership : MemberName.capture label name ∈
              prepared.members := by
            apply List.mem_map.mpr
            exact ⟨PreparedEntry.capture label name intervals, entryMember, rfl⟩
          have endpoints := translateInterval_endpoints
            (Preparation.Compile.weakenLayout layout prepared.symbols)
            prepared.members interval translated translatedResult
          have propositions := Encoding.contains_capture_interval prepared
            entryMember intervalMember
          exact ⟨name, translated, memberMembership,
            fun other otherMember sameLabel =>
              member_unique_by_label prepared.members labelsNodup
                (MemberName.capture label name) other memberMembership
                otherMember sameLabel,
            endpoints.1, endpoints.2, propositions.1, propositions.2⟩
      | classifier label interval =>
          obtain ⟨name, intervals, translated, entryMember,
            intervalMember, translatedResult⟩ := retained
          have memberMembership : MemberName.classifier label name ∈
              prepared.members := by
            apply List.mem_map.mpr
            exact ⟨PreparedEntry.classifier label name intervals, entryMember,
              rfl⟩
          have endpoints := translateInterval_endpoints
            (Preparation.Compile.weakenLayout layout prepared.symbols)
            prepared.members interval translated translatedResult
          have propositions := Encoding.contains_classifier_interval prepared
            entryMember intervalMember
          exact ⟨name, translated, memberMembership,
            fun other otherMember sameLabel =>
              member_unique_by_label prepared.members labelsNodup
                (MemberName.classifier label name) other memberMembership
                otherMember sameLabel,
            endpoints.1, endpoints.2, propositions.1, propositions.2⟩

end DOTCaptureToManySortedFC.Intersections.ConstraintRetention
