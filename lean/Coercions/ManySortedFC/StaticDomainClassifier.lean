import Coercions.ManySortedFC.StaticDomain
import Coercions.ManySortedFC.Classifier

/-!
# The standalone classifier-kind ground domain

This instantiates `GroundStaticDomain` with the existing executable
classifier-kind algebra. Ground expressions are `Classifier.Kind` values,
semantic observations are classifier tree nodes, and interpretation is
`Classifier.Kind.Contains`.

This instance packages the closed classifier algebra used by ground capture
projection. It does not add a classifier static sort, classifier variables,
target propositions, or target evidence constructors.
-/

namespace ManySortedFC

/-- The existing closed classifier-kind algebra as a ground static domain. -/
def classifierKindGroundDomain : GroundStaticDomain where
  Ground := Classifier.Kind
  Point := Classifier
  Contains := Classifier.Kind.Contains
  Equivalent := Classifier.Kind.Equivalent
  Includes := Classifier.Kind.Subkind
  Disjoint := Classifier.Kind.Disjoint
  groundDecidableEq := inferInstance
  containsDecision := Classifier.Kind.Contains.decision
  equivalentDecision := Classifier.Kind.Equivalent.decision
  includesDecision := Classifier.Kind.Subkind.decision
  disjointDecision := Classifier.Kind.Disjoint.decision
  equivalent_semantics := by
    intro left right
    constructor
    · intro equivalent point
      exact equivalent.contains
    · intro same
      exact Classifier.Kind.Equivalent.of_contains same
  includes_semantics := by
    intro source target
    exact Classifier.Kind.Subkind.semantics
  disjoint_semantics := by
    intro left right
    exact Classifier.Kind.Disjoint.semantics

end ManySortedFC
