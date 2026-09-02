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
import Coercions.ManySortedFC.TheoryMapLaws
import Coercions.ManySortedFC.TheoryMapMorphism
import Coercions.ManySortedFC.ModalTheoryMap
import Coercions.ManySortedFC.Adapter
import Coercions.ManySortedFC.Term
import Coercions.ManySortedFC.StaticInstantiation
import Coercions.ManySortedFC.TermTyping
import Coercions.ManySortedFC.TermChecker
import Coercions.ManySortedFC.TermCheckerCompleteness
import Coercions.ManySortedFC.Runtime
import Coercions.ManySortedFC.RuntimeDeterminism
import Coercions.ManySortedFC.TermProjection
import Coercions.ManySortedFC.Erasure
import Coercions.ManySortedFC.Dynamics
import Coercions.ManySortedFC.ModalOperational
import Coercions.ManySortedFC.ModalPreservation
import Coercions.ManySortedFC.Administrative
import Coercions.ManySortedFC.Consistency
import Coercions.ManySortedFC.SeparationConsistency
import Coercions.ManySortedFC.ModalConfinement
import Coercions.ManySortedFC.DisjointCaptureTheory
import Coercions.ManySortedFC.StaticExamples
import Coercions.ManySortedFC.RecursiveExamples
import Coercions.ManySortedFC.SeparationExamples
import Coercions.ManySortedFC.ModelConsistency
import Coercions.ManySortedFC.TermExamples
import Coercions.ManySortedFC.StaticApplicationExamples
import Coercions.ManySortedFC.TheoryMorphismExamples
import Coercions.ManySortedFC.TheoryMapExamples
import Coercions.ManySortedFC.TheoryMapCompositionExamples
import Coercions.ManySortedFC.TheoryMapMorphismExamples
import Coercions.ManySortedFC.ModalExamples
import Coercions.ManySortedFC.ModalAdapterExamples
import Coercions.ManySortedFC.ModalPreservationExamples
import Coercions.ManySortedFC.DisjointCaptureTheoryExamples
import Coercions.ManySortedFC.ClassifierProjectionExamples
import Coercions.ManySortedFC.StaticDomainExamples
import Coercions.ManySortedFC.EvidenceNormalizationExamples

/-!
Independent import root for the many-sorted FC target. This development is a
sibling of the type-only `FCsub` kernel and has no DOT dependency. Ordinary
application, static elimination, and existential opening accept typed
computations, while static abstraction, package payloads, and structural
adaptation retain their explicit value boundaries. Primitive modal locks
suspend arbitrary typed computations under explicit `Mode` and `Separate`
assumptions; unlocking requires evidence checked in the unchanged outer
context and erases to runtime `force`. Head-guarded simultaneous recursive
type projections have checked unfold equality. Capture terms remain acyclic,
and this syntactic facility does not claim a global semantic consistency
theorem for arbitrary recursive type equations.

Classifier projection is a ground extension: classifier nodes and kind
filters are closed data inside capture syntax, not a third bindable static
sort. `captureHasKind(C, K)` constrains an ordinary capture symbol by a ground
kind, and projection completeness certifies `C.project(K) = C`. The target
checker recomputes ground subkind, equivalence, emptiness, and disjointness
side conditions. This is the capture-kinding and projection interface needed
by the classifier case study; it is not the full Capless(K) source calculus,
handler semantics, or safety proof.
-/
