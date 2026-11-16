import Coercions.Selective.Prim
import Coercions.Selective.Syntax
import Coercions.Selective.Typing
import Coercions.Selective.Check
import Coercions.Selective.Sound
import Coercions.Selective.Lift
import Coercions.Selective.Complete
import Coercions.Selective.Annotate
import Coercions.Selective.Rename
import Coercions.Selective.Typer
import Coercions.Selective.Witness
import Coercions.Selective.Matrix
import Coercions.Selective.Negative
import Coercions.Selective.Subst
import Coercions.Selective.Hybrid

/-!
# Selective subtyping for DOT-MNF

The root of the `Selective` library. It imports the modules of
`lean/Coercions/Selective/`: implicit primitive subtyping without transitivity,
written certificates for every further step, and the correspondence with
DOT-MNF. `Hybrid` collects the main statements and two worked examples;
`README.md` in that directory is the introduction.

The axiom audit `Selective/Axioms.lean` is not imported here; replay it with
`lake env lean lean/Coercions/Selective/Axioms.lean`. The companions under
`Selective/Fsub`, `Selective/FsubDeclarative`, `Selective/FsubCompare` and
`Selective/Bridge` have their own import roots and Lake targets.
-/
