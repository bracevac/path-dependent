import Coercions.Translation
import Coercions.DOT.Captures
import Coercions.ManySortedFC
import Coercions.Translation.ManySorted

/-!
Umbrella for the complete coercion development. `Coercions.Translation`
transitively exposes the independently buildable DOT and FCsub roots, while
`Coercions.ManySortedFC` exposes the separate many-sorted target foundation.
`Coercions.DOT.Captures` and `Coercions.Translation.ManySorted` expose the
captured-DOT source layers, their cumulative compiler bridges, and the bounded
guarded recursive type-member case study.
The classifier case study keeps classifier nodes and kinds ground. Surface
`.only`/`.except` chains lower to capture filters, while a kind-bounded capture
variable lowers to a capture symbol plus checked ground-kind evidence. It does
not add a third classifier/kind sort.
-/
