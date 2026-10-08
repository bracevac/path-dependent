import Coercions.Captures.Frontend.Surface
import Coercions.Captures.Frontend.Notation
import Coercions.Captures.Frontend.Ann
import Coercions.Captures.Frontend.Resolve
import Coercions.Captures.Frontend.Decide
import Coercions.Captures.Frontend.Search
import Coercions.Captures.Frontend.Adapt
import Coercions.Captures.Frontend.Typer
import Coercions.Captures.Frontend.Step
import Coercions.Captures.Frontend.StepFC
import Coercions.Captures.Frontend.Pipeline
import Coercions.Captures.Frontend.Pretty
import Coercions.Captures.Frontend.Examples

/-!
# The front end of `Captures`

The root of the `CapturesFrontend` library.  A program in the version's
notation (capture checking the DOT way) is resolved, typed by a search that
returns the version's derivation, translated to FCdot, checked and run.  The
source is DOT-MNF with capture sets.

The library imports the version and changes nothing in it.  It is not a
default target.
-/

/-! Every definition of the front end is structural, so the kernel can reduce it. -/
#assert_no_wf CapturesFrontend
