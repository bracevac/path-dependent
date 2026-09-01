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
Closed classifier projections provide a separate source-facing litmus test:
surface `.only`/`.except` chains lower to checked ground capture filters and
erase without runtime code.
-/
