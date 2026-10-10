import Coercions.Captures.Frontend.Surface
import Coercions.Captures.Frontend.Notation
import Coercions.Captures.Frontend.Ann
import Coercions.Captures.Frontend.Resolve
import Coercions.Captures.Frontend.Decide
import Coercions.Captures.Frontend.Search
import Coercions.Captures.Frontend.Look
import Coercions.Captures.Frontend.Sub
import Coercions.Captures.Frontend.Alg
import Coercions.Captures.Frontend.Avoid
import Coercions.Captures.Frontend.Adapt
import Coercions.Captures.Frontend.Typer
import Coercions.Captures.Frontend.Elab
import Coercions.Captures.Frontend.Step
import Coercions.Captures.Frontend.StepFC
import Coercions.Captures.Frontend.Pipeline
import Coercions.Captures.Frontend.Pretty
import Coercions.Captures.Frontend.Examples

/-!
# The front end of `Captures`

The root of the `CapturesFrontend` library.  A program in the version's
notation (DOT-MNF with capture sets) is resolved, typed by a typer that
returns the version's derivation, translated to FCdot, checked and run.  The
typer follows the compiler's subtyping and subcapturing (`TypeComparer`),
member lookup (`Types.findMember`) and avoidance (`TypeOps.avoid`), on one fuel
tank.

The elaborator (`Elab.lean`) fills the annotations a program leaves out and
types the result with the typer.  It rejects a program with a `Reason`, the
type that `Coercions.Frontend.Reason` shares among the front ends, at the
labels of this version.

The library imports the version and changes nothing in it.  It is not a
default target.
-/

/-! Every definition of the front end is structural, so the kernel can reduce it. -/
#assert_no_wf CapturesFrontend
