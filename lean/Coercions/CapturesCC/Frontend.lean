import Coercions.CapturesCC.Frontend.Surface
import Coercions.CapturesCC.Frontend.Notation
import Coercions.CapturesCC.Frontend.Ann
import Coercions.CapturesCC.Frontend.Resolve
import Coercions.CapturesCC.Frontend.Decide
import Coercions.CapturesCC.Frontend.Search
import Coercions.CapturesCC.Frontend.Look
import Coercions.CapturesCC.Frontend.Sub
import Coercions.CapturesCC.Frontend.Alg
import Coercions.CapturesCC.Frontend.Avoid
import Coercions.CapturesCC.Frontend.Adapt
import Coercions.CapturesCC.Frontend.Typer
import Coercions.CapturesCC.Frontend.Elab
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
version's notation is resolved, typed by a typer that returns the version's
derivation, translated, checked and run.  The typer follows the compiler's
algorithm on one tank of fuel.  The source is DOT-MNF with scopes and levels,
translated to FCdot.

The elaborator (`Elab.lean`) fills the annotations a program leaves out and
types the result with the typer.  It rejects a program with a `Reason`, the
type that `Coercions.Frontend.Reason` shares among the front ends, at the
labels of this version and with the typer's own reasons.  `formSelfF` forms
the self shape of a literal that has none from its definitions, in rounds, as
the completers of `Namer` type the members of a class.  The literal is then
filled at the formed shape and typed by the typer, so its derivation is the
version's object rule.

The library imports the version and changes nothing in it.  It is not a
default target.
-/

/-! Every definition of the front end is structural, so the kernel reduces it. -/
#assert_no_wf CapturesCCFrontend
