import DotToFCsub.M7.Surface
import DotToFCsub.M7.Elaboration
import DotToFCsub.M7.Compiler
import DotToFCsub.M7.Soundness
import DotToFCsub.M7.Metrics
import DotToFCsub.M7.ArtifactRegressions
import DotToFCsub.M7.NormalizationRegressions
import DotToFCsub.M7.Examples

/-!
Milestone 7: a derivation-directed Scala-like case study emits a proof-free
closed FCsub artifact, which is accepted by the standalone checker.  The
scope is intentionally narrower than a total `DotFCRP.HasTy` compiler: M5
supplies recursive-object preservation, M6 supplies finite traceable path
certificates, and the generated target client uses normalized explicit
equality evidence.
-/
