import Coercions.Translation.ManySorted.Intersections.ConstraintRetention
import Coercions.Translation.ManySorted.Intersections.ObjectPreparation

/-!
# M11 static resource metrics

These counters stop at object-signature preparation.  The repository's
existing term-node counters describe the single-sorted FCsub case study, not
ManySortedFC, so they are not reused under a misleading name here.  A later
compiled-program report can extend `StaticMetrics` with ManySortedFC term,
erasure, and checker fields while reusing this static resource block.
-/

namespace DOTCaptureToManySortedFC.Intersections.Metrics

open DOTCaptureToManySortedFC.Intersections
open Encoding Preparation ConstraintRetention ObjectPreparation

/-- Resources produced by the M11 interface pipeline. -/
structure StaticMetrics where
  /-- Leaves in the raw source intersection tree, before label grouping. -/
  rawDeclarationOccurrences : Nat
  /-- Shared static names after grouping by label and checking one sort. -/
  normalizedAllocatedNames : Nat
  /-- Source interval occurrences retained after normalization. -/
  retainedIntervals : Nat
  /-- Primitive lower/name and name/upper target propositions. -/
  emittedConstraints : Nat
  /-- Ordinary runtime representations carried by one object package. -/
  runtimePayloads : Nat
deriving DecidableEq, Repr

/-- Measure a successfully prepared object without inspecting or attempting
to solve its static theory. -/
def ofPreparedObject {sourceScope : Preparation.Source.Scope}
    {targetScope : ManySortedFC.Sig}
    (interface : Preparation.Source.Interface sourceScope)
    (object : PreparedObject targetScope) : StaticMetrics :=
  { rawDeclarationOccurrences := (rawOccurrences interface).length
    normalizedAllocatedNames := object.encoding.prepared.members.length
    retainedIntervals := object.encoding.prepared.occurrenceCount
    emittedConstraints := object.encoding.relations.length
    runtimePayloads := 1 }

/-- Run object preparation and report its static resources.  Preparation
errors, including a same-label sort conflict, remain visible to the caller. -/
def prepareObject {sourceScope : Preparation.Source.Scope}
    {targetScope : ManySortedFC.Sig}
    (layout : StableLayout.Layout sourceScope targetScope)
    (source : DOTCapture.Intersections.Source.ObjectType sourceScope) :
    Except Preparation.Error StaticMetrics := do
  let object ← ObjectPreparation.prepareObject layout source
  pure (ofPreparedObject source.interface object)

@[simp]
theorem ofPreparedObject_runtimePayloads
    {sourceScope : Preparation.Source.Scope}
    {targetScope : ManySortedFC.Sig}
    (interface : Preparation.Source.Interface sourceScope)
    (object : PreparedObject targetScope) :
    (ofPreparedObject interface object).runtimePayloads = 1 := rfl

/-- The reported payload count is the actual increase in ordinary term
binders when the prepared object is opened. -/
theorem payload_scope_matches_report
    {sourceScope : Preparation.Source.Scope}
    {targetScope : ManySortedFC.Sig}
    (interface : Preparation.Source.Interface sourceScope)
    (object : PreparedObject targetScope) :
    (ManySortedFC.PayloadScope targetScope object.encoding.symbols
      object.encoding.relations).termCount =
        targetScope.termCount +
          (ofPreparedObject interface object).runtimePayloads := by
  simp [ofPreparedObject, object.one_payload]

/-- Every retained interval emits exactly its lower and upper inclusion.
This is resource accounting only; no interval-consistency premise appears. -/
theorem emitted_constraints_eq_twice_retained
    {sourceScope : Preparation.Source.Scope}
    {targetScope : ManySortedFC.Sig}
    (interface : Preparation.Source.Interface sourceScope)
    (object : PreparedObject targetScope) :
    (ofPreparedObject interface object).emittedConstraints =
      2 * (ofPreparedObject interface object).retainedIntervals := by
  exact Encoding.relations_length object.encoding

end DOTCaptureToManySortedFC.Intersections.Metrics
