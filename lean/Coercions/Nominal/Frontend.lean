import Coercions.Nominal.Frontend.Surface
import Coercions.Nominal.Frontend.Notation
import Coercions.Nominal.Frontend.Ann
import Coercions.Nominal.Frontend.Resolve
import Coercions.Nominal.Frontend.Sources
import Coercions.Nominal.Frontend.Decide
import Coercions.Nominal.Frontend.Look
import Coercions.Nominal.Frontend.Sub
import Coercions.Nominal.Frontend.Judgment
import Coercions.Nominal.Frontend.Avoid
import Coercions.Nominal.Frontend.Typer
import Coercions.Nominal.Frontend.Elab
import Coercions.Nominal.Frontend.Pipeline
import Coercions.Nominal.Frontend.Pretty
import Coercions.Nominal.Frontend.Examples

/-!
# The pDOT front end

The library `NominalFrontend` reads programs of pDOT written by hand and turns them
into the terms of `Nominal.Source`.  It is plan XI (`plan-11-pdot-frontends.md`).

`Surface.lean` holds the surface tree, the label tables and the four side
conditions `Scoped`, `LabelsIn`, `FieldsOk` and `PathOperands`.
`Notation.lean` holds the notation `pdcTy%`, `pdc%` and `pdcDefs%`.
`Ann.lean` holds the annotated terms `ATm` and the partial terms `PTm`.
`Resolve.lean` holds resolution, from the surface tree to the partial terms,
with its totality and the no insertion property.  `Sources.lean` holds the
programs of `Nominal.Source` written in the notation, each with its label table
and the theorem that it resolves to its hand term.

Every recursive definition of the library is structural.  The last line fails
the build when one of them is compiled by well-founded recursion.
-/

#assert_no_wf NominalFrontend
