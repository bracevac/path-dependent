import Coercions.Classifiers.Frontend.Surface
import Coercions.Classifiers.Frontend.Notation
import Coercions.Classifiers.Frontend.Ann
import Coercions.Classifiers.Frontend.Resolve
import Coercions.Classifiers.Frontend.Step
import Coercions.Classifiers.Frontend.StepFC

/-!
# The front end of `Classifiers`

The root of the `ClassifiersFrontend` library: a way to write, type and run
programs of the `Classifiers` version (capability classifiers) without assembling
derivations by hand.  A program in the version's notation is resolved, typed
by a search that returns the version's derivation, translated, checked and
run.  The source is DOT-MNF with classifiers, translated to FCdot.

The library imports the version and changes nothing in it.  It is not a
default target.
-/

/-! Every definition of the front end is structural, so the kernel reduces it. -/
#assert_no_wf ClassifiersFrontend
