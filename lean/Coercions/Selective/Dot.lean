import Coercions.Selective.Dot.Syntax
import Coercions.Selective.Dot.Typing
import Coercions.Selective.Dot.Machine
import Coercions.Selective.Dot.RenameTy
import Coercions.Selective.Dot.Rename
import Coercions.Selective.Dot.Subst
import Coercions.Selective.Dot.State
import Coercions.Selective.Dot.Tight
import Coercions.Selective.Dot.Lift
import Coercions.Selective.Dot.Canonical
import Coercions.Selective.Dot.Safety
import Coercions.Selective.Dot.Examples

/-!
# Selective DOT

The root of the `SelectiveDot` library: the coercive calculus for WadlerFest DOT
in monadic normal form whose only coercions are `step[S,T]` and `c ; d`, with its
machine and its type safety proof (`Safety.lean`). Nothing here imports the
vanilla calculus; the correspondence with it is the library `SelectiveDotVanilla`
under `Dot/Vanilla`. The axiom audit is `Dot/Axioms.lean`.
-/
