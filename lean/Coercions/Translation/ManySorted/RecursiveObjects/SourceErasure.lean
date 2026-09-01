import Coercions.Translation.ManySorted.RecursiveObjects.Source
import Coercions.ManySortedFC.Runtime

/-!
# Independent erasure for the Stage 6A recursive object literal

The case-study representation is `Unit`, so a recursive object literal has
one runtime payload and all type names, capture names, bounds, recursive
equations, and package evidence disappear.  This definition mentions no
target encoding or compiler.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.Source

/-- Independent shared-runtime meaning of one closed Stage 6A object literal. -/
def eraseObject {scope : Sig} {runtimeScope : Nat}
    (_signature : Signature scope) : ManySortedFC.Runtime.Tm runtimeScope :=
  .unit

@[simp]
theorem eraseObject_eq_unit {scope : Sig} {runtimeScope : Nat}
    (signature : Signature scope) :
    eraseObject (runtimeScope := runtimeScope) signature =
      (.unit : ManySortedFC.Runtime.Tm runtimeScope) := rfl

end DOTCaptureToManySortedFC.RecursiveObjects.Source
