import Coercions.Selective
import Coercions.Selective.Fsub
import Coercions.Selective.FsubDeclarative
import Coercions.Selective.FsubCompare
import Coercions.Selective.Bridge
import Coercions.Selective.Dot
import Coercions.Selective.Dot.Vanilla

/-!
# All selective-subtyping libraries in one environment

This module imports the roots of every library under `Coercions/Selective`. It
has no declarations. Building it checks that the libraries can be loaded
together, that is, that no two of them declare the same name.
-/
