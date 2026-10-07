/-!
# The front end of `Captures`

The root of the `CapturesFrontend` library: a way to write, type and run
programs of the `Captures` version (capture checking the DOT way) without assembling
derivations by hand.  A program in the version's notation is resolved, typed
by a search that returns the version's derivation, translated, checked and
run.  The source is DOT-MNF with capture sets, translated to FCdot.

The library imports the version and changes nothing in it.  It is not a
default target.
-/
