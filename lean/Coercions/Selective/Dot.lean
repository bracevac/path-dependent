import Coercions.Selective.Dot.Syntax
import Coercions.Selective.Dot.Typing
import Coercions.Selective.Dot.Machine
import Coercions.Selective.Dot.Probes

/-!
# Selective DOT

The root of the `SelectiveDot` library: the coercive calculus for WadlerFest DOT
in monadic normal form whose only coercions are `step[S,T]` and `c ; d`.
-/
