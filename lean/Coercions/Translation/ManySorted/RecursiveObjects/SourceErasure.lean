import Coercions.Translation.ManySorted.RecursiveObjects.Source
import Coercions.ManySortedFC.Runtime

/-!
# Compatibility erasure for the original unit recursive-object example

The cumulative compiler uses the independently defined source erasure from
`DOT.Captures.ModalIntersections`. This older helper remains for the original
closed `Unit` example: all static names, equations, bounds, and evidence erase,
leaving its single runtime payload. It mentions no target encoding or compiler.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.Source

/-- Independent shared-runtime meaning of the original closed unit literal. -/
def eraseObject {scope : Sig} {runtimeScope : Nat}
    (_signature : Signature scope) : ManySortedFC.Runtime.Tm runtimeScope :=
  .unit

@[simp]
theorem eraseObject_eq_unit {scope : Sig} {runtimeScope : Nat}
    (signature : Signature scope) :
    eraseObject (runtimeScope := runtimeScope) signature =
      (.unit : ManySortedFC.Runtime.Tm runtimeScope) := rfl

end DOTCaptureToManySortedFC.RecursiveObjects.Source
