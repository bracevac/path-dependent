import LambdaP.FinFun
import LambdaP.Syntax
import LambdaP.Context
import LambdaP.Typing
import LambdaP.Renaming
import LambdaP.Opening
import LambdaP.Store
import LambdaP.PathReduction
import LambdaP.Lookup
import LambdaP.Cont
import LambdaP.State
import LambdaP.Machine
import LambdaP.PathFunctionality
import LambdaP.TypingInversion
import LambdaP.PreciseStore
import LambdaP.ValueInversion
import LambdaP.Canonical
import LambdaP.PathPreservation
import LambdaP.PathProgress
import LambdaP.Progress
import LambdaP.PreciseProgress
import LambdaP.AdministrativePreservation
import LambdaP.CounterexampleRegression
import LambdaP.RuntimeConversion
import LambdaP.ScopedRuntimeEq
import LambdaP.StructuralRuntimeTyping
import LambdaP.StructuralTermTyping
import LambdaP.StructuralRuntimeLemmas
import LambdaP.StructuralMachineInvariant
import LambdaP.StructuralValueInversion
import LambdaP.StructuralPathSubstitution
import LambdaP.StructuralNarrowing
import LambdaP.StructuralPreciseStore
import LambdaP.StructuralResolution
import LambdaP.StructuralApplicationBoundary
import LambdaP.Examples
import LambdaP.Safety

/-!
The intrinsically scoped `lambda_p` calculus and its metatheory.

`Ty.Single p` is a term singleton and `Ty.TSel p A` is an abstract type
selection.  This aggregate includes the source calculus, CK machine,
proof-relevant realization, exact-store canonical forms, progress,
preservation, closed finite-run type safety, and checked examples.
-/
