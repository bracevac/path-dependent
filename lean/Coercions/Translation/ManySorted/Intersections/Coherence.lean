import Coercions.Translation.ManySorted.Intersections.Preparation

/-!
# Coherence of canonical intersection preparation

Preparation depends only on the collected normalized signature. Therefore
alternative source intersection trees that collect to the same signature
allocate exactly the same target symbols, members, bounds, and theory.
Evidence terms supplied later are intentionally outside this equality.
-/

namespace DOTCaptureToManySortedFC.Intersections.Preparation

/-- Equal normalized collection results give literally equal prepared target
signatures. This covers association and any other derivation choice that does
not reorder retained constraint occurrences. -/
theorem collectAndPrepare_eq_of_collect_eq
    {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (first second : Source.Interface sourceScope)
    (collected : first.collect = second.collect) :
    collectAndPrepare layout first = collectAndPrepare layout second := by
  unfold collectAndPrepare
  rw [collected]

/-- Successful preparations of collection-equivalent source trees return the
same complete prepared signature, not merely the same number of members. -/
theorem prepared_eq_of_collect_eq
    {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (first second : Source.Interface sourceScope)
    (collected : first.collect = second.collect)
    {firstPrepared secondPrepared : Encoding.PreparedSignature targetScope}
    (firstSuccess : collectAndPrepare layout first = .ok firstPrepared)
    (secondSuccess : collectAndPrepare layout second = .ok secondPrepared) :
    firstPrepared = secondPrepared := by
  have samePreparation := collectAndPrepare_eq_of_collect_eq layout first second
    collected
  rw [firstSuccess, secondSuccess] at samePreparation
  exact Except.ok.inj samePreparation

end DOTCaptureToManySortedFC.Intersections.Preparation
