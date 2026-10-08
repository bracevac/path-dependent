import Coercions.Oopsla16.Frontend.Surface
import Coercions.Oopsla16.Frontend.Notation
import Coercions.Oopsla16.Frontend.Ann
import Coercions.Oopsla16.Frontend.Resolve
import Coercions.Oopsla16.Frontend.Decide
import Coercions.Oopsla16.Frontend.Look
import Coercions.Oopsla16.Frontend.Sub
import Coercions.Oopsla16.Frontend.Alg
import Coercions.Oopsla16.Frontend.Search
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
without assembling derivations by hand.  A program is resolved, typed by a
search that returns the calculus's own derivation, elaborated into FCdotR,
checked and run.
-/

#assert_no_wf Oopsla16Frontend
