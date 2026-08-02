import LambdaP.Repaired.FinFun
import LambdaP.Repaired.Syntax
import LambdaP.Repaired.Context
import LambdaP.Repaired.Typing
import LambdaP.Repaired.Renaming
import LambdaP.Repaired.Opening
import LambdaP.Repaired.Store
import LambdaP.Repaired.PathReduction
import LambdaP.Repaired.Lookup
import LambdaP.Repaired.Cont
import LambdaP.Repaired.State
import LambdaP.Repaired.Machine
import LambdaP.Repaired.PathFunctionality
import LambdaP.Repaired.TypingInversion
import LambdaP.Repaired.PreciseStore
import LambdaP.Repaired.ValueInversion
import LambdaP.Repaired.Canonical
import LambdaP.Repaired.PathPreservation
import LambdaP.Repaired.PathProgress
import LambdaP.Repaired.Progress
import LambdaP.Repaired.PreciseProgress
import LambdaP.Repaired.AdministrativePreservation
import LambdaP.Repaired.SourceCounterexampleBlocked
import LambdaP.Repaired.RuntimeConversion
import LambdaP.Repaired.ScopedRuntimeEq
import LambdaP.Repaired.StructuralRuntimeTyping
import LambdaP.Repaired.StructuralTermTyping
import LambdaP.Repaired.StructuralRuntimeLemmas
import LambdaP.Repaired.StructuralMachineInvariant
import LambdaP.Repaired.StructuralValueInversion
import LambdaP.Repaired.StructuralPathSubstitution
import LambdaP.Repaired.StructuralNarrowing
import LambdaP.Repaired.StructuralPreciseStore
import LambdaP.Repaired.StructuralResolution
import LambdaP.Repaired.StructuralApplicationBoundary
import LambdaP.Repaired.PairRuleExamples
import LambdaP.Repaired.StructuralClosedSafety

/-!
The repaired intrinsically scoped calculus.

`Ty.Single p` is a term singleton and `Ty.TSel p A` is an abstract type
selection.  The final imports expose the checked dependent-pair regression
examples, proof-relevant realization theorem, exact-store canonical forms,
progress, preservation, and closed finite-run type safety.
-/
