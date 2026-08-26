import LambdaPToFCo.Direct.RepresentationClosure

/-! A nonempty target focus closes a raw representation to an opaque root
carrier without source-side formation evidence. -/

namespace LambdaPToFCo.Direct.Internal.RepresentationClosureRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation

abbrev RootContext : Ctx [] := Ctx.empty

abbrev Focus : Telescope [] := .var .top .nil

abbrev FocusedContext : Ctx Focus.scope := Focus.context RootContext

abbrev FocusedShape : Shape Focus.scope := .stable (Top.plan Focus.scope)

def focused : Rep FocusedContext (.Top : LambdaPFC.Ty 0) FocusedShape :=
  .top FocusedContext

noncomputable def closed : Rep RootContext (.Top : LambdaPFC.Ty 0)
    (Reclosure.outerShape Focus FocusedShape) :=
  focused.close Focus

/-- The adapter creates the literal faithful closure constructor. -/
theorem closed_shape :
    Reclosure.outerShape Focus FocusedShape =
      .opaque (Focus.append (.var FocusedShape.inputTy .nil)).existsTy := by
  rfl

def topPayload {sig : Sig} : Exp sig :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

noncomputable def topPayload_hasType (base : Ctx sig) :
    Exp.HasType base (topPayload : Exp sig) .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

noncomputable def topInterface (base : Ctx sig) :
    Shape.Interface base (.stable (Top.plan sig)) where
  arguments := Top.arguments .top topPayload (topPayload_hasType base)

/-- A genuinely non-renaming opening instantiates the focus prefix. -/
noncomputable def opening : Subst Focus.scope [] :=
  Subst.openVar topPayload

noncomputable def opening_typed :
    Subst.Typed FocusedContext RootContext opening :=
  Subst.Typed.openVar (topPayload_hasType RootContext)

/-- Raw representation closure and value reclosure share one exact Shape. -/
noncomputable def reclosedSlot :
    Slot RootContext (.Top : LambdaPFC.Ty 0) :=
  Slot.reclose Focus focused opening opening_typed (by
    simpa only [FocusedShape, Shape.subst, Top.plan_subst] using
      topInterface RootContext)

noncomputable def reclosedSlot_package_hasType :
    Exp.HasType RootContext reclosedSlot.interface.package
      reclosedSlot.shape.inputTy :=
  reclosedSlot.interface.package_hasType

end LambdaPToFCo.Direct.Internal.RepresentationClosureRegression
