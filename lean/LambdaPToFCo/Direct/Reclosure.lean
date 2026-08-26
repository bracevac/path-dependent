import LambdaPToFCo.Direct.Shape

/-!
# Scope-natural target closure

`Reclosure` is the target-only executable operation determined by an opened
telescope and focused Shape.  It is not a source derivation plan.  It works
after every later typed target substitution, extracts the exact opened
telescope arguments, and appends the focused value package to reconstruct the
opaque carrier.
-/

namespace LambdaPToFCo.Direct.Internal

open SystemFCo

namespace Reclosure

/-- Public opaque carrier Shape produced by closing `inner` through `focus`. -/
def outerShape (focus : Telescope sig) (inner : Shape focus.scope) :
    Shape sig :=
  .opaque (focus.append (.var inner.inputTy .nil)).existsTy

/-- Reclose an exact focused interface after an arbitrary later target
substitution.  `fromOpenedSubst` recovers all prefix fields from that
substitution; its cancellation law aligns the dependent final value field.
-/
noncomputable def reclose
    {root : Sig} (rootContext : Ctx root)
    (focus : Telescope root) (inner : Shape focus.scope)
    {final : Sig} {finalContext : Ctx final}
    (opening : Subst focus.scope final)
    (typed : Subst.Typed (focus.context rootContext) finalContext opening)
    (interface : Shape.Interface finalContext (inner.subst opening)) :
    Shape.Interface finalContext
      ((outerShape focus inner).subst
        (focus.weaken.asSubst.comp opening)) := by
  let total := focus.weaken.asSubst.comp opening
  let opened := Telescope.Args.fromOpenedSubst focus rootContext opening typed
  let valueField : Telescope focus.scope := .var inner.inputTy .nil
  have valueType :
      ((inner.inputTy.subst (focus.liftSubst
          (focus.weaken.asSubst.comp opening))).subst
          opened.arguments.substitution) =
        (inner.subst opening).inputTy := by
    rw [Ty.subst_comp, opened.cancel, Shape.inputTy_subst]
  let finalValue : Telescope.Args finalContext
      ((valueField.subst (focus.liftSubst
          (focus.weaken.asSubst.comp opening))).subst
        opened.arguments.substitution) := by
    refine .var interface.package ?_ .nil
    exact valueType.symm ▸ interface.package_hasType
  let combined := opened.arguments.append
    (valueField.subst (focus.liftSubst
      (focus.weaken.asSubst.comp opening))) finalValue
  let carrier := Telescope.pack combined
  have carrierTyping : Exp.HasType finalContext carrier
      ((focus.subst (focus.weaken.asSubst.comp opening)).append
        (valueField.subst (focus.liftSubst
          (focus.weaken.asSubst.comp opening)))).existsTy :=
    Telescope.pack_hasType combined
  refine { arguments := .var carrier ?_ .nil }
  simpa only [outerShape, Shape.subst, Package.existsTy_subst,
    Telescope.append_subst, total] using carrierTyping

end Reclosure

end LambdaPToFCo.Direct.Internal
