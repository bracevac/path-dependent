import Coercions.ManySortedFC.Scope
import Coercions.ManySortedFC.Syntax
import Coercions.ManySortedFC.Context
import Coercions.ManySortedFC.Substitution
import Coercions.ManySortedFC.Intervals
import Coercions.ManySortedFC.IntervalElaboration
import Coercions.ManySortedFC.Evidence
import Coercions.ManySortedFC.EvidenceChecker
import Coercions.ManySortedFC.TheoryModel
import Coercions.ManySortedFC.TheoryModelChecker
import Coercions.ManySortedFC.TheoryMorphism
import Coercions.ManySortedFC.TheoryMorphismChecker
import Coercions.ManySortedFC.Adapter
import Coercions.ManySortedFC.Term
import Coercions.ManySortedFC.TermTyping
import Coercions.ManySortedFC.TermChecker
import Coercions.ManySortedFC.TermCheckerCompleteness
import Coercions.ManySortedFC.Runtime
import Coercions.ManySortedFC.TermProjection
import Coercions.ManySortedFC.Erasure
import Coercions.ManySortedFC.Administrative
import Coercions.ManySortedFC.Consistency
import Coercions.ManySortedFC.StaticExamples
import Coercions.ManySortedFC.ModelConsistency
import Coercions.ManySortedFC.TermExamples
import Coercions.ManySortedFC.TheoryMorphismExamples

/-!
Independent import root for the many-sorted FC target. This development is a
sibling of the type-only `FCsub` kernel and has no DOT dependency. Ordinary
application and existential opening accept typed computations, while static
elimination, package payloads, and structural adaptation retain their explicit
value boundaries.
-/
