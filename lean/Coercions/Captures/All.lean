import Coercions.Captures.DotMNF
import Coercions.Captures.FCdot
import Coercions.Captures.DotToFCdot
import Coercions.Captures.Runtime

/-!
This extension adds capture checking the DOT way on top of the vanilla
development (`Coercions.DotMNF`, `Coercions.FCdot`, `Coercions.DotToFCdot`,
`Coercions.Runtime`, at the commit recorded in `BASE`). Capture checking
tracks, for each type, the set of variables a value of that type may capture,
and checks that this set is respected throughout typing and evaluation.
-/
