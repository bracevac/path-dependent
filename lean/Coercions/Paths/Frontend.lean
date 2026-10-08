import Coercions.Paths.Frontend.Surface
import Coercions.Paths.Frontend.Notation
import Coercions.Paths.Frontend.Ann
import Coercions.Paths.Frontend.Resolve
import Coercions.Paths.Frontend.Decide
import Coercions.Paths.Frontend.Table
import Coercions.Paths.Frontend.Search
import Coercions.Paths.Frontend.Typer
import Coercions.Paths.Frontend.Step
import Coercions.Paths.Frontend.StepFC
import Coercions.Paths.Frontend.Pipeline
import Coercions.Paths.Frontend.Pretty
import Coercions.Paths.Frontend.Examples

/-!
# The front end of `Paths`

The root of the `PathsFrontend` library.  It lets you write, type and run
programs of the `Paths` version (paths and singleton types) without building
derivations by hand.  A program is resolved, typed by a search that returns
the version's derivation, translated to FCdot, checked and run.

The library imports the version and changes nothing in it.  It is not a
default build target.
-/

#assert_no_wf PathsFrontend
