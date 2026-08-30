import Coercions.Translation.CompilerCaseStudy.Surface
import Coercions.Translation.CompilerCaseStudy.Certificate
import Coercions.Translation.CompilerCaseStudy.Compiler
import Coercions.Translation.CompilerCaseStudy.Correctness
import Coercions.Translation.CompilerCaseStudy.Metrics
import Coercions.Translation.CompilerCaseStudy.ArtifactRegressions
import Coercions.Translation.CompilerCaseStudy.NormalizationRegressions
import Coercions.Translation.CompilerCaseStudy.Examples

/-!
A derivation-directed Scala-like case study emits a proof-free
closed FCsub artifact, which is accepted by the standalone checker.  The
scope is intentionally narrower than a total `DotFCRP.HasTy` compiler: the
recursive-object layer supplies preservation, the path-alias layer supplies finite traceable path
certificates, and the generated target client uses normalized explicit
equality evidence.
-/
