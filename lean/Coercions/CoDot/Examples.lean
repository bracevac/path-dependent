import Coercions.CoDot.Elab
import Coercions.DotMNF.Examples

/-!
# The source examples E9 to E12

The closed DOT-MNF derivations E9 to E12 of `DotMNF/Examples.lean`, through
the elaboration theorem: each has a CoDot annotation at the same type that
erases to the same term. E9 passes a function through a recursive type, E10
is a self-dependent intersection under recursion, E11 nests recursion, and
E12 selects on a bare self variable.
-/

namespace CoDot

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ty Path)

open DotMNF.Examples in
theorem E9_elab : ∃ t', Typed (ofDot .nil) (.tm t' .top) ∧ t'.erase = E9Term :=
  elaboration E9

open DotMNF.Examples in
theorem E10_elab : ∃ t', Typed (ofDot .nil) (.tm t' (.all E10Rec (.sel (.var .here) lB))) ∧
    t'.erase = E10Term :=
  elaboration E10

open DotMNF.Examples in
theorem E11_elab : ∃ t', Typed (ofDot .nil) (.tm t' (.all E11Rec (.sel (.var .here) lA))) ∧
    t'.erase = E11Term :=
  elaboration E11

open DotMNF.Examples in
theorem E12_elab : ∃ t', Typed (ofDot .nil) (.tm t' (.all E12Rec (.sel (.var .here) lA))) ∧
    t'.erase = E12Term :=
  elaboration E12

end CoDot
