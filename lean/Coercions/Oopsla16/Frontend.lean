import Coercions.Oopsla16.Frontend.Surface
import Coercions.Oopsla16.Frontend.Notation
import Coercions.Oopsla16.Frontend.Ann
import Coercions.Oopsla16.Frontend.Resolve

/-!
# The front end of `Oopsla16`

The root of the `Oopsla16Frontend` library: a way to write, type and run
programs of the `Oopsla16` version (the OOPSLA 2016 DOT calculus with recursive subtyping) without assembling
derivations by hand.  A program in the version's notation is resolved, typed
by a search that returns the version's derivation, translated, checked and
run.  The source is `Oopsla16`, elaborated into FCdotR.

The library imports the version and changes nothing in it.  It is not a
default target.
-/
