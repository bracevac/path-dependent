import Coercions.Selective.Dot.Vanilla.Translate
import Coercions.Selective.Dot.Vanilla.Sound
import Coercions.Selective.Dot.Vanilla.Elab
import Coercions.Selective.Dot.Vanilla.Exact

/-!
# Selective DOT and DOT-MNF

The correspondence between the coercive calculus `SelDot` and its source
DOT-MNF. `Translate` relates the two syntaxes; `Sound` shows that the erasure
of a typed term is typed in the source; `Elab` elaborates a source derivation
into a typed term, a certificate for every subtyping derivation and a cast
path for every typing of a variable; `Exact` states the two equivalences.
-/
