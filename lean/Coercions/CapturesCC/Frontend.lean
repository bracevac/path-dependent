import Coercions.CapturesCC.Frontend.Surface
import Coercions.CapturesCC.Frontend.Notation
import Coercions.CapturesCC.Frontend.Ann
import Coercions.CapturesCC.Frontend.Resolve
import Coercions.CapturesCC.Frontend.Decide
import Coercions.CapturesCC.Frontend.Search
import Coercions.CapturesCC.Frontend.Look
import Coercions.CapturesCC.Frontend.Adapt
import Coercions.CapturesCC.Frontend.Typer
import Coercions.CapturesCC.Frontend.Step
import Coercions.CapturesCC.Frontend.StepFC
import Coercions.CapturesCC.Frontend.Pipeline
import Coercions.CapturesCC.Frontend.Pretty
import Coercions.CapturesCC.Frontend.Examples

/-!
# The front end of `CapturesCC`

The root of the `CapturesCCFrontend` library.  It lets one write, type and run
programs of the `CapturesCC` version, which checks captures the way the Scala 3
compiler does, without assembling derivations by hand.  A program in the
version's notation is resolved, typed by a search that returns the version's
derivation, translated, checked and run.  The source is DOT-MNF with scopes and
levels, translated to FCdot.

The library imports the version and changes nothing in it.  It is not a
default target.
-/

/-! Every definition of the front end is structural, so the kernel reduces it. -/
#assert_no_wf CapturesCCFrontend
