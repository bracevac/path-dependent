import Coercions.Translation.ManySorted.RecursiveObjects.Source
import Coercions.Translation.ManySorted.RecursiveObjects.SourceExamples
import Coercions.Translation.ManySorted.RecursiveObjects.SourceErasure
import Coercions.Translation.ManySorted.RecursiveObjects.Encoding
import Coercions.Translation.ManySorted.RecursiveObjects.EncodingExamples
import Coercions.Translation.ManySorted.RecursiveObjects.Model
import Coercions.Translation.ManySorted.RecursiveObjects.ModelExamples
import Coercions.Translation.ManySorted.RecursiveObjects.PositiveObjectCompilation
import Coercions.Translation.ManySorted.RecursiveObjects.Inertness
import Coercions.Translation.ManySorted.RecursiveObjects.InertnessExamples
import Coercions.Translation.ManySorted.RecursiveObjects.CompilerExamples
import Coercions.Translation.ManySorted.RecursiveObjects.ExactErasure
import Coercions.Translation.ManySorted.RecursiveObjects.ExactErasureExamples
import Coercions.Translation.ManySorted.RecursiveObjects.CompilerMetrics
import Coercions.Translation.ManySorted.RecursiveObjects.CompilerMetricsExamples
import Coercions.Translation.ManySorted.RecursiveObjects.CompletionExamples
import Coercions.Translation.ManySorted.RecursiveObjects.Conservativity
import Coercions.Translation.ManySorted.RecursiveObjects.ConservativityExamples

/-!
# Cumulative recursive captured objects

Guarded type definitions and capture-member equations are realized
simultaneously inside the cumulative object theory. Type members use checked
recursive projections. Capture members use finite ambient witnesses supplied
as one existential model; no target capture fixed point is generated.
Classifier members remain nonrecursive: recursive classifier witnesses and
equations are outside this case-study layer.

A tagged recursive literal compiles positively to one checked model and one
ordinary value payload with explicit `C_rep` evidence. Its object theory checks
`C_rep` against the advertised capture; positive packaging separately checks
it against an ambient package envelope. This permits the advertised capture to
refer to a recursive member without placing that local name in the package's
outer type. The literal must be opened by a source `objectLet` before
path-dependent or negative use. The open establishes one stable identity for
repeated member selections. Recursive finalization erases literally to the
compiled payload. `ExactErasure` makes the inherited boundary explicit:
recursive packaging and opening preserve literal erasure exactly when their
compiled subterms do. The unrestricted cumulative compiler continues to use
administrative equivalence because function and modal adapters eta-expand;
a checked counterexample records why unconditional literal equality would be
false. The representative exact programs execute by ordinary zeta and beta
reduction. Conservativity theorems compare independently accepted M10, M11,
and exact cumulative artifacts by literal runtime erasure.

The compiler remains a checked partial function: every successful result
carries standalone term and value-checker certificates, but this module does
not claim a completeness theorem for every source typing derivation.
-/
