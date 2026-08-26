import LambdaPToFCo.Full.TypingViews
import LambdaPToFCo.Full.ValueTypingViews
import LambdaPToFCo.Full.ContextWellFormed
import LambdaPToFCo.Full.IdentityRegression
import LambdaPToFCo.Full.IllWfSubtypingRegression
import LambdaPToFCo.Full.PathTypingUniqueness
import LambdaPToFCo.Full.TranslationOrigins
import LambdaPToFCo.Full.OriginConstruction
import LambdaPToFCo.Full.ValueModel
import LambdaPToFCo.Full.AtomicModels
import LambdaPToFCo.Full.FunctionModel
import LambdaPToFCo.Full.PairModel
import LambdaPToFCo.Full.ValueInterface
import LambdaPToFCo.Full.PlanScope
import LambdaPToFCo.Full.ScopeView
import LambdaPToFCo.Full.InterfaceSubstitution
import LambdaPToFCo.Full.InterfacePackageBridge
import LambdaPToFCo.Full.FunctionInterface
import LambdaPToFCo.Full.PairInterface
import LambdaPToFCo.Full.PathPackageZipper
import LambdaPToFCo.Full.PathPackageClosure
import LambdaPToFCo.Full.StableIdentity
import LambdaPToFCo.Full.StableIdentitySubstitution
import LambdaPToFCo.Full.FunctionStableAdapter
import LambdaPToFCo.Full.PairStableAdapter
import LambdaPToFCo.Full.StableIdentityReduction
import LambdaPToFCo.Full.TranslationModelCore
import LambdaPToFCo.Full.TranslationInterfaces
import LambdaPToFCo.Full.PairedInstantiation
import LambdaPToFCo.Full.WfPlan
import LambdaPToFCo.Full.SubtypingCompilerCore
import LambdaPToFCo.Full.IntervalSubtypingCompilerCore
import LambdaPToFCo.Full.AtomicSubtypingCompiler
import LambdaPToFCo.Full.TranslationModelRebase
import LambdaPToFCo.Full.DemandDirectedSubtyping

/-!
# Full LambdaPFC compilation track

This aggregate exposes the constructor-complete compiler development that
targets the separate `SystemFCoExt` calculus.  It is intentionally distinct
from the existing restricted `LambdaPToFCo` aggregate and will become the
public full compiler entry point as the remaining path, subtyping, term, and
operational layers land.

No module imported here changes or extends the original `SystemFCo` library.
-/
