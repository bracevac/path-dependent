import Coercions.CapturesCC.Frontend.Surface
import Coercions.CapturesCC.Frontend.Notation
import Coercions.CapturesCC.Frontend.Ann
import Coercions.CapturesCC.Frontend.Resolve

/-!
# The front end of `CapturesCC`

The root of the `CapturesCCFrontend` library: a way to write, type and run
programs of the `CapturesCC` version (capture checking the way the Scala 3 compiler does it) without assembling
derivations by hand.  A program in the version's notation is resolved, typed
by a search that returns the version's derivation, translated, checked and
run.  The source is DOT-MNF with scopes and levels, translated to FCdot.

The library imports the version and changes nothing in it.  It is not a
default target.
-/

/-! Every definition of the front end is structural, so the kernel reduces it. -/
#assert_no_wf CapturesCCFrontend
