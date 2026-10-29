import Coercions.PDot.Frontend.Surface
import Coercions.PDot.Frontend.Notation
import Coercions.PDot.Frontend.Ann
import Coercions.PDot.Frontend.Resolve
import Coercions.PDot.Frontend.Sources
import Coercions.PDot.Frontend.Decide
import Coercions.PDot.Frontend.Look
import Coercions.PDot.Frontend.Sub
import Coercions.PDot.Frontend.Judgment
import Coercions.PDot.Frontend.Avoid
import Coercions.PDot.Frontend.Typer
import Coercions.PDot.Frontend.Elab
import Coercions.PDot.Frontend.Pipeline
import Coercions.PDot.Frontend.Pretty
import Coercions.PDot.Frontend.Examples

/-!
# The pDOT front end

The library `PDotFrontend` reads programs of pDOT written by hand and turns them
into the terms of `PDot.Source`.  It is plan XI (`plan-11-pdot-frontends.md`).

`Surface.lean` holds the surface tree, the label tables and the four side
conditions `Scoped`, `LabelsIn`, `FieldsOk` and `PathOperands`.
`Notation.lean` holds the notation `pdtTy%`, `pdt%` and `pdtDefs%`.
`Ann.lean` holds the annotated terms `ATm` and the partial terms `PTm`.
`Resolve.lean` holds resolution, from the surface tree to the partial terms,
with its totality and the no insertion property.  `Sources.lean` holds the
programs of `PDot.Source` written in the notation, each with its label table
and the theorem that it resolves to its hand term.

Every recursive definition of the library is structural.  The last line fails
the build when one of them is compiled by well-founded recursion.
-/

#assert_no_wf PDotFrontend
