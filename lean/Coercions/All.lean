import Coercions.Translation
import Coercions.ManySortedFC

/-!
Umbrella for the coercion development. `Coercions.Translation` transitively
exposes the independently buildable acyclic DOT and FCsub roots and the
stable-root DOT-to-FCsub compiler. `Coercions.ManySortedFC` exposes the static
layer of the many-sorted target: syntax, evidence, checkers, consistency
models, and the ground classifier algebra.
-/
