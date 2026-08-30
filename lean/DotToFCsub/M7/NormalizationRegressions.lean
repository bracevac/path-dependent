import FCsub.Normalization
import DotToFCsub.M6.Examples

/-!
# M7 normalization regressions

These checks specialize the standalone FCsub normalizer to the concrete
singleton-member equality emitted by the M6 nested-path example.  The source
paths remain separately allocated; normalization only removes the explicit
reflexive anchor link from their equality certificate.
-/

namespace DotToFCsub.M7.NormalizationRegressions

open DotToFCsub.M6
open DotToFCsub.M6.Examples

/-- The concrete M6 alias-to-alias certificate contains six equality nodes:
two variables, symmetry, two transitivity nodes, and anchor reflexivity. -/
theorem singleton_equality_raw_nodes :
    singletonMemberEquality.evidence.nodeCount = 6 := rfl

/-- Normalization deletes the reflexive anchor link and its adjacent
transitivity node. -/
theorem singleton_equality_normalized_nodes :
    singletonMemberEquality.evidence.normalize.nodeCount = 4 := rfl

/-- The normalized concrete certificate satisfies the executable FCsub
normal-form predicate. -/
theorem singleton_equality_normalized_reduced :
    singletonMemberEquality.evidence.normalize.reduced = true :=
  FCsub.EqCo.reduced_normalize singletonMemberEquality.evidence

/-- Re-normalizing the concrete M6 certificate is a fixed point. -/
theorem singleton_equality_normalization_idempotent :
    singletonMemberEquality.evidence.normalize.normalize =
      singletonMemberEquality.evidence.normalize :=
  FCsub.EqCo.normalize_idempotent singletonMemberEquality.evidence

/-- The proof-producing structural checker synthesizes the same two concrete
fresh alias endpoints after normalization. -/
theorem singleton_equality_normalized_synths :
    FCsub.synthEq TargetContext singletonMemberEquality.evidence.normalize =
      some ((layout.ownedImage rabASlot).aliasType,
        (layout.ownedImage qASlot).aliasType) :=
  FCsub.EqCo.synthEq_normalize
    (singletonMemberEquality.evidence_hasType
      (.nil : FCsub.Ctx []))

/-- The public expected-endpoint equality checker accepts the normalized
certificate at exactly the endpoints used by the original M6 regression. -/
theorem singleton_equality_normalized_checks :
    FCsub.checkEquality TargetContext
      singletonMemberEquality.evidence.normalize
      (layout.ownedImage rabASlot).aliasType
      (layout.ownedImage qASlot).aliasType = true := by
  simp [FCsub.checkEquality, singleton_equality_normalized_synths]

/-- Alternative source co-resolution proof trees still produce identical
normalized target syntax. -/
theorem singleton_equality_alternative_normalized_coherent :
    singletonMemberEquality.evidence.normalize =
      singletonMemberEqualityAlternative.evidence.normalize :=
  congrArg FCsub.EqCo.normalize singleton_evidence_coherent

end DotToFCsub.M7.NormalizationRegressions
