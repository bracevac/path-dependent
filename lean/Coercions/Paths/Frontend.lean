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

The library imports the version and changes nothing in it.  It is not a
default build target.
-/

#assert_no_wf PathsFrontend
