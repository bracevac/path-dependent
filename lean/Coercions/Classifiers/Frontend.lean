import Coercions.Classifiers.Frontend.Surface
import Coercions.Classifiers.Frontend.Notation
import Coercions.Classifiers.Frontend.Ann
import Coercions.Classifiers.Frontend.Resolve
import Coercions.Classifiers.Frontend.Decide
import Coercions.Classifiers.Frontend.Kind
import Coercions.Classifiers.Frontend.Search
import Coercions.Classifiers.Frontend.Look
import Coercions.Classifiers.Frontend.Sub
import Coercions.Classifiers.Frontend.Alg
import Coercions.Classifiers.Frontend.Avoid
import Coercions.Classifiers.Frontend.Adapt
import Coercions.Classifiers.Frontend.Typer
import Coercions.Classifiers.Frontend.Elab
import Coercions.Classifiers.Frontend.Step
import Coercions.Classifiers.Frontend.StepFC
import Coercions.Classifiers.Frontend.Pipeline
import Coercions.Classifiers.Frontend.Pretty
import Coercions.Classifiers.Frontend.Examples

/-!
# The front end of `Classifiers`

The root of the `ClassifiersFrontend` library.  It lets one write, type and run
programs of the `Classifiers` version (capability classifiers) without
assembling derivations by hand.  A program in the version's notation is
resolved, typed by a typer that returns the version's derivation, translated
to FCdot, checked and run.  The typer follows the compiler's algorithm on one
tank of fuel.

The elaborator (`Elab.lean`) fills the annotations a program leaves out and
types the result with the typer.  It rejects a program with a `Reason`, the
type that `Coercions.Frontend.Reason` shares among the front ends, at the
labels of this version and with the typer's own reasons.  `formSelfF` forms
the self shape of a literal that has none from its definitions, in rounds, as
the completers of `Namer` type the members of a class.  The literal is then
filled at the formed shape and typed by the typer, so its derivation is the
version's object rule.  `compile` (`Pipeline.lean`) runs the elaborator on the
body of a whole program and returns the fill, the body with its empty slots
filled, with the typer's derivation.  `compileE` returns the reason a program
is rejected as well, and `Pretty.lean` prints partial terms and reasons.
`Examples.lean` takes every program through the front end, written and with
the annotations of its body erased.  At the direct sites a program with its
body erased compiles as its written form does, from some fuel on
(`compile_complete_canonAt`).

The library only imports the version.  It is not a default build target.
-/

/-! Every definition is structural, so the kernel reduces it. -/
#assert_no_wf ClassifiersFrontend
