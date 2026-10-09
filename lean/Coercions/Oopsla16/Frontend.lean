import Coercions.Oopsla16.Frontend.Surface
import Coercions.Oopsla16.Frontend.Notation
import Coercions.Oopsla16.Frontend.Ann
import Coercions.Oopsla16.Frontend.Resolve
import Coercions.Oopsla16.Frontend.Decide
import Coercions.Oopsla16.Frontend.Look
import Coercions.Oopsla16.Frontend.Sub
import Coercions.Oopsla16.Frontend.Alg
import Coercions.Oopsla16.Frontend.Avoid
import Coercions.Oopsla16.Frontend.Typer
import Coercions.Oopsla16.Frontend.Step
import Coercions.Oopsla16.Frontend.StepFC
import Coercions.Oopsla16.Frontend.Pipeline
import Coercions.Oopsla16.Frontend.Pretty
import Coercions.Oopsla16.Frontend.Examples

/-!
# The front end of `Oopsla16`

The root of the `Oopsla16Frontend` library.  It lets one write, type and run
programs of `Oopsla16` (the OOPSLA 2016 DOT calculus with recursive subtyping)
without building derivations by hand.  A program is resolved, typed,
elaborated into FCdotR, checked and run.

The typer follows the case order of the Scala 3 subtype checker
(`TypeComparer`) and returns the derivation of the calculus, so it is sound by
construction.  It runs on one fuel tank and reports a recursion limit when the
tank runs out.  It is complete up to that limit with respect to its
algorithmic judgment `Alg` (`Alg.lean`).  As in the compiler, it rejects a call on a
receiver at a union or at `⊥`.  Every definition is structural, so each verdict
of `Examples.lean` is a theorem the kernel checks.
-/

#assert_no_wf Oopsla16Frontend
