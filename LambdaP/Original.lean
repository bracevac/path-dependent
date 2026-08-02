import LambdaP.Original.FinFun
import LambdaP.Original.Syntax
import LambdaP.Original.Context
import LambdaP.Original.Typing
import LambdaP.Original.Renaming
import LambdaP.Original.Opening
import LambdaP.Original.Store
import LambdaP.Original.PathReduction
import LambdaP.Original.Lookup
import LambdaP.Original.PreciseStore
import LambdaP.Original.PathFunctionality
import LambdaP.Original.PathPreservation
import LambdaP.Original.PathProgress
import LambdaP.Original.RuntimeConversion
import LambdaP.Original.ScopedRuntimeEq
import LambdaP.Original.ScopedTypeConversion
import LambdaP.Original.StructuralRuntimeTyping
import LambdaP.Original.StructuralTermTyping
import LambdaP.Original.StructuralRuntimeLemmas
import LambdaP.Original.StructuralMachineInvariant
import LambdaP.Original.StructuralValueInversion
import LambdaP.Original.StructuralApplicationBoundary
import LambdaP.Original.StructuralRefinedProgress
import LambdaP.Original.StructuralRuntimePathValidity
import LambdaP.Original.StructuralResolution
import LambdaP.Original.StructuralPathSubstitution
import LambdaP.Original.StructuralNarrowing
import LambdaP.Original.StructuralApplicationCompatibility
import LambdaP.Original.StructuralPreservation
import LambdaP.Original.StructuralProgress
import LambdaP.Original.StructuralHeadReflection
import LambdaP.Original.StructuralSafetyBoundary
import LambdaP.Original.StructuralPreciseStore
import LambdaP.Original.StructuralPreciseCanonical
import LambdaP.Original.StructuralPreciseProgress
import LambdaP.Original.StructuralPrecisePreservation
import LambdaP.Original.StructuralPrecisePushbackCounterexample
import LambdaP.Original.StructuralPreciseFunctionPushbackCounterexample
import LambdaP.Original.RuntimeTyping
import LambdaP.Original.RuntimePathPreservation
import LambdaP.Original.RuntimeOpeningProbe
import LambdaP.Original.RuntimeChecking
import LambdaP.Original.DeepRuntimeTyping
import LambdaP.Original.DeepRenaming
import LambdaP.Original.PromotedPathChecking
import LambdaP.Original.DeepPathPreservation
import LambdaP.Original.DeepMachineInvariant
import LambdaP.Original.DeepValueInversion
import LambdaP.Original.DeepApplicationBoundary
import LambdaP.Original.ValueInversion
import LambdaP.Original.StoreRefinement
import LambdaP.Original.Canonical
import LambdaP.Original.TypingInversion
import LambdaP.Original.Cont
import LambdaP.Original.State
import LambdaP.Original.Machine
import LambdaP.Original.Progress
import LambdaP.Original.PreciseProgress
import LambdaP.Original.RefinedPathProgress
import LambdaP.Original.AdministrativePreservation
import LambdaP.Original.LookupCounterexample
import LambdaP.Original.RuntimeCounterexampleRepair
import LambdaP.Original.ClosedCounterexample
import LambdaP.Original.SourceUnsoundnessCounterexample

/-!
The original precise-path-typing presentation of `lambda_p`, reconstructed
from the final pre-restart development and completed with capture-avoiding
binding operations.

Soundness modules are imported here only once their statements and proofs are
checked; this keeps the root an honest account of the completed development.
-/
