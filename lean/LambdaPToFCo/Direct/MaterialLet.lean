import LambdaPToFCo.Direct.Introduction
import LambdaPToFCo.Direct.MaterialTermPath

/-!
# Material raw let binding

This leaf closes one already checked let body.  It eliminates the bound's
actual package exactly once, seals the emitted package with the original
outer result representation, and optionally recloses that material Slot
through an existing package-aware focus.

Body compilation and source dispatch remain outside this target-only seam.
-/

namespace LambdaPToFCo.Direct.Internal.MaterialLet

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.Wf
open LambdaPToFCo.Direct.Internal.Introduction
open LambdaPToFCo.Direct.Internal.MaterialTermPath

/-- Bind an arbitrary raw material value around one exact checked body
interface.

The body interface has the outer result Shape renamed beneath every binder
of the bound Shape.  Eliminating the actual bound package returns an ordinary
package at the original result Shape; sealing pairs it with `result.rep`
itself, whose source index is `resultSource`, never `resultSource.weaken`. -/
noncomputable def bindExact
    {base : Ctx sig}
    {boundSource resultSource : LambdaPFC.Ty n}
    (bound : Slot base boundSource)
    (result : Proper base resultSource)
    (bodyInterface : Shape.Interface (bound.shape.context base)
      (result.shape.rename bound.shape.binders.weaken)) :
    Slot base resultSource := by
  let package := Introduction.bind bound.shape bound.interface.package
    result.shape.inputTy bodyInterface.package
  have packageTyping : Exp.HasType base package result.shape.inputTy := by
    apply Introduction.bind_hasType bound.interface.package_hasType
    simpa only [Shape.inputTy_rename] using
      bodyInterface.package_hasType
  exact Slot.sealPackage result.rep package packageTyping

/-- Bind in a current target scope and reclose the material result through
one already retained outer actual-package focus. -/
noncomputable def bindFocused
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    {boundSource resultSource : LambdaPFC.Ty n}
    (focus : Focus rootContext currentContext)
    (bound : Slot currentContext boundSource)
    (result : Proper currentContext resultSource)
    (bodyInterface : Shape.Interface
      (bound.shape.context currentContext)
      (result.shape.rename bound.shape.binders.weaken)) :
    Slot rootContext resultSource :=
  focus.closeSlot (bindExact bound result bodyInterface)

end LambdaPToFCo.Direct.Internal.MaterialLet
