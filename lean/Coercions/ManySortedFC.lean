import Coercions.ManySortedFC.Classifier
import Coercions.ManySortedFC.StaticDomain
import Coercions.ManySortedFC.StaticDomainClassifier
import Coercions.ManySortedFC.Scope
import Coercions.ManySortedFC.Syntax
import Coercions.ManySortedFC.Context
import Coercions.ManySortedFC.Substitution
import Coercions.ManySortedFC.Recursion
import Coercions.ManySortedFC.Intervals
import Coercions.ManySortedFC.IntervalElaboration
import Coercions.ManySortedFC.Evidence
import Coercions.ManySortedFC.EvidenceChecker
import Coercions.ManySortedFC.EvidenceCheckerCompleteness
import Coercions.ManySortedFC.EvidenceNormalization
import Coercions.ManySortedFC.TheoryModel
import Coercions.ManySortedFC.ModalContext
import Coercions.ManySortedFC.TheoryModelChecker
import Coercions.ManySortedFC.TheoryMorphism
import Coercions.ManySortedFC.TheoryMorphismChecker
import Coercions.ManySortedFC.TheoryMap
import Coercions.ManySortedFC.TheoryMapChecker
import Coercions.ManySortedFC.TheoryMapCheckerCompleteness
import Coercions.ManySortedFC.TheoryMapComposition
import Coercions.ManySortedFC.TheoryMapMetatheory
import Coercions.ManySortedFC.ModalTheoryMap
import Coercions.ManySortedFC.Adapter
import Coercions.ManySortedFC.Term
import Coercions.ManySortedFC.StaticInstantiation
import Coercions.ManySortedFC.TermTyping
import Coercions.ManySortedFC.TermChecker
import Coercions.ManySortedFC.TermCheckerCompleteness
import Coercions.ManySortedFC.Runtime
import Coercions.ManySortedFC.TermProjection
import Coercions.ManySortedFC.Erasure
import Coercions.ManySortedFC.Consistency
import Coercions.ManySortedFC.SeparationConsistency
import Coercions.ManySortedFC.ModalConfinement
import Coercions.ManySortedFC.DisjointCaptureTheory
import Coercions.ManySortedFC.StaticExamples
import Coercions.ManySortedFC.RecursiveExamples
import Coercions.ManySortedFC.SeparationExamples
import Coercions.ManySortedFC.ModelConsistency
import Coercions.ManySortedFC.TermExamples
import Coercions.ManySortedFC.ModalExamples
import Coercions.ManySortedFC.DisjointCaptureTheoryExamples
import Coercions.ManySortedFC.ClassifierProjectionExamples
import Coercions.ManySortedFC.StaticDomainExamples
import Coercions.ManySortedFC.EvidenceNormalizationExamples

/-!
Import root for the static layer of the many-sorted FC target: two-sorted
(type and capture) syntax, constraint telescopes, checked evidence with a
sound and complete checker, structural adapters, term typing with a checker,
theory models and maps, the closed and separation consistency models, and the
ground classifier kind algebra.  The operational semantics, erasure dynamics,
and modal preservation layer were removed in the September 2026 cut; a typed
dynamics with full static substitution is future work.
-/
