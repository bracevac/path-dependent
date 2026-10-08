import Coercions.Classifiers.Frontend.Surface
import Coercions.Classifiers.Frontend.Notation
import Coercions.Classifiers.Frontend.Ann
import Coercions.Classifiers.Frontend.Resolve
import Coercions.Classifiers.Frontend.Decide
import Coercions.Classifiers.Frontend.Kind
import Coercions.Classifiers.Frontend.Search
import Coercions.Classifiers.Frontend.Look
import Coercions.Classifiers.Frontend.Adapt
import Coercions.Classifiers.Frontend.Typer
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
resolved, typed by a search that returns the version's derivation, translated
to FCdot, checked and run.  The library only imports the version.  It is not a
default build target.
-/

/-! Every definition is structural, so the kernel reduces it. -/
#assert_no_wf ClassifiersFrontend
