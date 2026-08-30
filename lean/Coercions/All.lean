import Coercions.Translation
import Coercions.DOT.Captures
import Coercions.ManySortedFC
import Coercions.Translation.ManySorted

/-!
Umbrella for the complete coercion development. `Coercions.Translation`
transitively exposes the independently buildable DOT and FCsub roots, while
`Coercions.ManySortedFC` exposes the separate many-sorted target foundation.
`Coercions.DOT.Captures` and `Coercions.Translation.ManySorted` expose the
independent binder-only DOT/capture-interval source scaffold and its bridge
to that target.
-/
