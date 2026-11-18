import Coercions.CoDot.Core
import Coercions.CoDot.Subst
import Coercions.CoDot.Eval
import Coercions.CoDot.Elimination
import Coercions.CoDot.Term
import Coercions.CoDot.Machine
import Coercions.CoDot.Admin
import Coercions.CoDot.Elab
import Coercions.CoDot.Bridge
import Coercions.CoDot.WadlerFest
import Coercions.CoDot.Examples

/-!
# CoDot

The root of the `CoDot` library: DOT in monadic normal form with explicit
coercions and a direct safety proof (`Core` to `Machine`), and its
correspondence with DOT-MNF and the WadlerFest presentations (`Admin`,
`Elab`, `Bridge`, `WadlerFest`, `Examples`). `README.md` in `CoDot/` is the
introduction.

The axiom audit, `CoDot/Axioms.lean`, is not imported here.
-/
