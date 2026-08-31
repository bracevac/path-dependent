import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.SourceErasure
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.Compiler
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.CompilerConservativity
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.CompilerChecker
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.BoundaryRegressions
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.CompilerErasure
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.ComputationalExample
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.ObjectConsumerCompilation

/-!
# General captured-DOT expressions to many-sorted FC

This root collects the direct compiler from the general-expression captured-
DOT surface into computation-accepting many-sorted FC.  The value-MNF source
and its compiler remain a separate, stable core and regression suite.

General applications compile homomorphically to target applications, and a
computation producing an object package compiles directly as the scrutinee of
existential opening.  Selection remains restricted to stable paths.  The
compiler preserves the independently defined source runtime term by literal
equality after erasure; it does not insert an ANF normalization pass.

Object consumers use a polarized boundary: positive objects remain packages,
while a negative object parameter becomes static model abstraction followed
by a runtime payload function.  Only canonical literals and already-open
stable roots can be supplied directly.  Other object-producing computations
must first cross an explicit source object let/open.

The compiler is derivation-directed for this acyclic fixed-member surface. It
is not presented as a compiler for full DOT.
-/
