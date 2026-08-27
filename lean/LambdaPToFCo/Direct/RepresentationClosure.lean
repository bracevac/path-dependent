import LambdaPToFCo.Direct.Reclosure
import LambdaPToFCo.Direct.Representation

/-!
# Faithful closure of raw representations

This target-only leaf materializes a focused `Representation.Rep` at its root
scope.  The public Shape is the same opaque carrier used by `Reclosure`; the
private payload is ordinary System FCo syntax derived canonically from the
focus and focused Shape.
-/

namespace LambdaPToFCo.Direct.Internal

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation

namespace RepresentationClosure

/-! ## Exact interfaces under arbitrary target substitution -/

private theorem openVarSubstComm (argument : Exp source)
    (substitution : Subst source target) :
    (Subst.openVar argument).comp substitution =
      (substitution.lift .var).comp
        (Subst.openVar (argument.subst substitution)) := by
  apply Subst.funext
  · intro index
    cases index with
    | here => rfl
    | there index =>
        exact (Exp.weaken_subst_cancel (substitution.var index)
          (Subst.openVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openVar _)).symm
  · intro index
    cases index with
    | there index =>
        exact (Ty.weaken_subst_cancel (substitution.tvar index)
          (Subst.openVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openVar _)).symm
  · intro index
    cases index with
    | there index =>
        exact (Co.weaken_subst_cancel (substitution.cvar index)
          (Subst.openVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openVar _)).symm

private theorem openTVarSubstComm (argument : Ty source)
    (substitution : Subst source target) :
    (Subst.openTVar argument).comp substitution =
      (substitution.lift .tvar).comp
        (Subst.openTVar (argument.subst substitution)) := by
  apply Subst.funext
  · intro index
    cases index with
    | there index =>
        exact (Exp.weaken_subst_cancel (substitution.var index)
          (Subst.openTVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openTVar _)).symm
  · intro index
    cases index with
    | here => rfl
    | there index =>
        exact (Ty.weaken_subst_cancel (substitution.tvar index)
          (Subst.openTVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openTVar _)).symm
  · intro index
    cases index with
    | there index =>
        exact (Co.weaken_subst_cancel (substitution.cvar index)
          (Subst.openTVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openTVar _)).symm

private theorem openCVarSubstComm (argument : Co source)
    (substitution : Subst source target) :
    (Subst.openCVar argument).comp substitution =
      (substitution.lift .cvar).comp
        (Subst.openCVar (argument.subst substitution)) := by
  apply Subst.funext
  · intro index
    cases index with
    | there index =>
        exact (Exp.weaken_subst_cancel (substitution.var index)
          (Subst.openCVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openCVar _)).symm
  · intro index
    cases index with
    | there index =>
        exact (Ty.weaken_subst_cancel (substitution.tvar index)
          (Subst.openCVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openCVar _)).symm
  · intro index
    cases index with
    | here => rfl
    | there index =>
        exact (Co.weaken_subst_cancel (substitution.cvar index)
          (Subst.openCVar (argument.subst substitution))
          (Subst.weakenAsSubst_comp_openCVar _)).symm

private noncomputable def argumentsTargetSubst
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target} {tele : Telescope source}
    (arguments : Telescope.Args sourceContext tele)
    (substitution : Subst source target)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    Telescope.Args targetContext (tele.subst substitution) := by
  induction arguments generalizing target targetContext with
  | nil => exact .nil
  | @var type tail argument argumentTyping rest ih =>
      refine .var (argument.subst substitution)
        (argumentTyping.subst typed) ?_
      have equal :
          (tail.subst (Subst.openVar argument)).subst substitution =
            (tail.subst (substitution.lift .var)).subst
              (Subst.openVar (argument.subst substitution)) := by
        rw [tail.subst_comp, tail.subst_comp, openVarSubstComm]
      exact equal ▸ ih substitution typed
  | @tvar tail argument rest ih =>
      refine .tvar (argument.subst substitution) ?_
      have equal :
          (tail.subst (Subst.openTVar argument)).subst substitution =
            (tail.subst (substitution.lift .tvar)).subst
              (Subst.openTVar (argument.subst substitution)) := by
        rw [tail.subst_comp, tail.subst_comp, openTVarSubstComm]
      exact equal ▸ ih substitution typed
  | @cvar sourceType targetType tail argument argumentTyping rest ih =>
      refine .cvar (argument.subst substitution)
        (argumentTyping.subst typed) ?_
      have equal :
          (tail.subst (Subst.openCVar argument)).subst substitution =
            (tail.subst (substitution.lift .cvar)).subst
              (Subst.openCVar (argument.subst substitution)) := by
        rw [tail.subst_comp, tail.subst_comp, openCVarSubstComm]
      exact equal ▸ ih substitution typed

private noncomputable def renameTypedAsSubst
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {mapping : Rename source target}
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Subst.Typed sourceContext targetContext mapping.asSubst where
  lookup := by
    intro kind index binding lookup
    have renamed := typed.lookup lookup
    cases binding with
    | var type =>
        simpa only [Subst.Realizes, Ty.subst_asSubst] using
          (Exp.HasType.var renamed)
    | tvar => exact PUnit.unit
    | cvar source result =>
        simpa only [Subst.Realizes, Ty.subst_asSubst] using
          (Co.HasType.cvar renamed)

end RepresentationClosure

end LambdaPToFCo.Direct.Internal

namespace LambdaPToFCo.Direct.Shape.Interface

open SystemFCo

/-- Reindex an exact open interface through any typed target substitution. -/
noncomputable def targetSubst
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target} {shape : Shape source}
    (interface : Shape.Interface sourceContext shape)
    (substitution : Subst source target)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    Shape.Interface targetContext (shape.subst substitution) where
  arguments := by
    rw [← Shape.binders_subst]
    exact Internal.RepresentationClosure.argumentsTargetSubst
      interface.arguments substitution typed

end LambdaPToFCo.Direct.Shape.Interface

namespace LambdaPToFCo.Direct.Internal

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation

namespace RepresentationClosure

/-- Canonical target representation data for one focused Shape. -/
private structure Payload
    {sig : Sig} (base : Ctx sig)
    (focus : Telescope sig) (shape : Shape focus.scope) where
  storedShape : Shape
    (focus.append (.var shape.inputTy .nil)).scope
  storedPackage : Exp
    (focus.append (.var shape.inputTy .nil)).scope
  storedTyping : Exp.HasType
    ((focus.append (.var shape.inputTy .nil)).context base)
    storedPackage storedShape.inputTy
  opening : Rename focus.scope storedShape.scope
  openingTyped : Rename.Typed (focus.context base)
    (storedShape.context
      ((focus.append (.var shape.inputTy .nil)).context base))
    opening

/-- Compute the unique representation payload of `Reclosure.outerShape`. -/
private noncomputable def payload
    (base : Ctx sig)
    (focus : Telescope sig) (shape : Shape focus.scope) :
    Payload base focus shape := by
  induction focus with
  | nil =>
      let valueField := Telescope.var shape.inputTy Telescope.nil
      let storedShape := shape.rename valueField.weaken
      let storedPackage : Exp valueField.scope := .var .here
      have storedTyping : Exp.HasType (valueField.context base)
          storedPackage storedShape.inputTy := by
        simpa only [storedPackage, storedShape, Shape.inputTy_rename,
          valueField, Telescope.context, Telescope.weaken, Ty.weaken,
          Ty.rename_id] using
          (Exp.HasType.var (Ctx.Lookup.here :
            Ctx.VarLookup (valueField.context base) .here _))
      exact {
        storedShape := storedShape
        storedPackage := storedPackage
        storedTyping := storedTyping
        opening := valueField.weaken.comp storedShape.binders.weaken
        openingTyped := TypedRename.comp
          (valueField.weaken_typed base)
          (storedShape.binders.weaken_typed (valueField.context base))
      }
  | var type tail ih =>
      let result := ih (base := base.bindVar type) shape
      exact {
        storedShape := result.storedShape
        storedPackage := result.storedPackage
        storedTyping := result.storedTyping
        opening := result.opening
        openingTyped := result.openingTyped
      }
  | tvar tail ih =>
      let result := ih (base := base.bindTVar) shape
      exact {
        storedShape := result.storedShape
        storedPackage := result.storedPackage
        storedTyping := result.storedTyping
        opening := result.opening
        openingTyped := result.openingTyped
      }
  | cvar source target tail ih =>
      let result := ih (base := base.bindCVar source target) shape
      exact {
        storedShape := result.storedShape
        storedPackage := result.storedPackage
        storedTyping := result.storedTyping
        opening := result.opening
        openingTyped := result.openingTyped
      }

private theorem payload_openedShape
    (base : Ctx sig)
    (focus : Telescope sig) (shape : Shape focus.scope) :
    shape.rename (payload base focus shape).opening =
      (payload base focus shape).storedShape.rename
        (payload base focus shape).storedShape.binders.weaken := by
  induction focus with
  | nil => exact (Shape.rename_comp shape _ _).symm
  | var type tail ih =>
      simpa only [payload] using ih (base.bindVar type) shape
  | tvar tail ih =>
      simpa only [payload] using ih base.bindTVar shape
  | cvar source target tail ih =>
      simpa only [payload] using
        ih (base.bindCVar source target) shape

end RepresentationClosure

namespace Representation

namespace Rep

open SystemFCo

/-- Close a focused raw representation without assuming an inhabitant. -/
noncomputable def close
    {base : Ctx sig} {sourceType : LambdaPFC.Ty n}
    (focus : Telescope sig) {shape : Shape focus.scope}
    (focused : Rep (focus.context base) sourceType shape) :
    Rep base sourceType (Reclosure.outerShape focus shape) := by
  let fields := focus.append (.var shape.inputTy .nil)
  let data := RepresentationClosure.payload base focus shape
  let opened :=
    (RepresentationClosure.payload_openedShape base focus shape) ▸
    focused.targetRename data.opening data.openingTyped
  exact .closed fields data.storedShape data.storedPackage
    data.storedTyping opened

end Rep

namespace Slot

/-- Seal any exact typed representation package as a material raw Slot.
This works for source results which have no `Tau.Wf` derivation. -/
noncomputable def sealPackage
    {base : Ctx sig} {sourceType : LambdaPFC.Ty n}
    {shape : Shape sig}
    (rep : Rep base sourceType shape)
    (package : Exp sig)
    (typing : Exp.HasType base package shape.inputTy) :
    Slot base sourceType := by
  let focus : Telescope sig := .nil
  let fields : Telescope sig := .var shape.inputTy .nil
  let arguments : Telescope.Args base fields :=
    .var package typing .nil
  let carrier := Telescope.pack arguments
  have carrierTyping : Exp.HasType base carrier fields.existsTy :=
    Telescope.pack_hasType arguments
  exact {
    shape := Reclosure.outerShape focus shape
    interface := { arguments := .var carrier carrierTyping .nil }
    rep := Rep.close (base := base) focus rep
  }

/-- Reindex a raw exact slot through any typed target substitution. -/
noncomputable def targetSubst
    {source target : Sig} {sourceType : LambdaPFC.Ty n}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    (slot : Slot sourceContext sourceType)
    (substitution : Subst source target)
    (typed : Subst.Typed sourceContext targetContext substitution) :
    Slot targetContext sourceType where
  shape := slot.shape.subst substitution
  interface := slot.interface.targetSubst substitution typed
  rep := slot.rep.targetSubst substitution typed

/-- Reclose one exact focused value after an arbitrary later target
substitution.  The interface and representation share the same substituted
opaque carrier Shape definitionally. -/
noncomputable def reclose
    {root : Sig} {rootContext : Ctx root}
    {sourceType : LambdaPFC.Ty n}
    (focus : Telescope root) {inner : Shape focus.scope}
    (focusedRep : Rep (focus.context rootContext) sourceType inner)
    {final : Sig} {finalContext : Ctx final}
    (opening : Subst focus.scope final)
    (typed : Subst.Typed (focus.context rootContext) finalContext opening)
    (interface : Shape.Interface finalContext (inner.subst opening)) :
    Slot finalContext sourceType := by
  let total := focus.weaken.asSubst.comp opening
  let weakenTyped := RepresentationClosure.renameTypedAsSubst
    (focus.weaken_typed rootContext)
  let totalTyped := TypedSubst.comp weakenTyped typed
  exact {
    shape := (Reclosure.outerShape focus inner).subst total
    interface := Reclosure.reclose rootContext focus inner opening typed
      interface
    rep := (focusedRep.close focus).targetSubst total totalTyped
  }

end Slot

namespace Env

/-- Reindex every raw source slot through an arbitrary typed target
substitution. -/
noncomputable def targetSubst
    {source target : Sig} {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : Ctx source}
    {targetTargetContext : Ctx target}
    (environment : Env sourceContext sourceTargetContext)
    (substitution : Subst source target)
    (typed : Subst.Typed sourceTargetContext targetTargetContext
      substitution) :
    Env sourceContext targetTargetContext where
  lookup index :=
    (environment.lookup index).targetSubst substitution typed

end Env

end Representation

end LambdaPToFCo.Direct.Internal
