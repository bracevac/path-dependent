import Coercions.Paths.Frontend.Surface
import Coercions.Paths.Frontend.Notation
import Coercions.Paths.Frontend.Ann
import Coercions.Paths.Frontend.Resolve
import Coercions.Paths.Frontend.Decide
import Coercions.Paths.Frontend.Look
import Coercions.Paths.Frontend.Sub
import Coercions.Paths.Frontend.Alg
import Coercions.Paths.Frontend.Avoid
import Coercions.Paths.Frontend.Typer
import Coercions.Paths.Frontend.Elab
import Coercions.Paths.Frontend.Step
import Coercions.Paths.Frontend.StepFC
import Coercions.Paths.Frontend.Pipeline
import Coercions.Paths.Frontend.Pretty
import Coercions.Paths.Frontend.Examples

/-!
# The front end of `Paths`

The root of the `PathsFrontend` library.  It lets you write, type and run
programs of the `Paths` version (paths and singleton types) without building
derivations by hand.  A program is resolved, typed, translated to FCdot,
checked and run.

The typer follows the subtype checker of the Scala 3 compiler in its case
order and returns the version's own derivation, so it is sound by
construction.  It runs on one fuel tank and reports a recursion limit when the
tank runs short.  It is complete up to that limit with respect to its
algorithmic judgment `Alg` (`Alg.lean`).  It rejects E1p, E3p, E4p and R1 as
scalac does, and their variants that write the middle type compile.  It
rejects R2 and PQ, which scalac accepts, since the version has no rule for
them.  Every definition is structural, so each verdict of `Examples.lean` is
a theorem the kernel checks.

The elaborator (`Elab.lean`) fills the annotations a program leaves out and
types the result with the typer.  It rejects a program with a `Reason`, the
type that `Coercions.Frontend.Reason` shares among the front ends, at the
labels of this version.  `formSelfF` forms a literal's self type from its
definitions, in rounds that type each field without a written type at its
least candidate, after the fields it reads off the self, and names the cyclic
reference when a round types nothing.  A literal without a self type and
without a `μ` goal is filled at the formed self type and typed by the object
clause of the typer (`obj_none_landed`).

`compileE` (`Pipeline.lean`) resolves a program to a partial term and
elaborates it.  It returns the fill with its derivation, or the reason the
program is rejected, which `ppReason` (`Pretty.lean`) prints.  `compile` is
the same without the reason.  A program with every slot written compiles as
the typer's synthesis (`compile_full`).  A program whose empty slots are
lambda domains at the direct sites compiles to the fill the typer accepts,
from some fuel on (`compile_complete_direct`).  `Examples.lean` states the
verdict on each example with its annotations erased in five ways, one row of
`decide +kernel` facts per program.  It applies `compile_complete_direct` to
programs whose domains are erased at those sites.

The library imports the version and changes nothing in it.  It is not a
default build target.
-/

#assert_no_wf PathsFrontend
