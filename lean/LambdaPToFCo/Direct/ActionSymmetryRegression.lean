import LambdaPToFCo.Direct.Action

/-!
# Singleton-symmetry Action regression

The symmetry leaf consumes the exact retained singleton Slot. Its target is
definitionally the singleton package for the proof path, and its Relation is
one value-specific constant conversion into that package.
-/

namespace LambdaPToFCo.Direct.Internal.ActionSymmetryRegression

open SystemFCo
open Representation

private noncomputable def retainedConstant
    {base : Ctx sig} {source : Ty sig} {target : Shape sig}
    (targetInterface : Shape.Interface base target) :
    Conversion base source target.inputTy :=
  Conversion.ofFunction
    (Adapter.ofBody source
      (targetInterface.package.rename (Rename.weaken .var)))
    (Adapter.ofBody_hasType (by
      simpa only [Ty.weaken, Shape.inputTy_rename] using
        targetInterface.package_hasType.rename
          (Rename.Typed.weaken base (.var source))))

private noncomputable def symmetryRelation
    {base : Ctx sig} {path referent : LambdaPFC.Path n}
    (source : Slot base (.Single referent)) :
    let target := TermIntroduction.singletonSlot path source
    Relation base (.Single referent) (.Single path)
      source.shape target.shape := by
  let target := TermIntroduction.singletonSlot path source
  exact Relation.ofConversion source.rep target.rep
    (retainedConstant target.interface)

/-- The Action index exposes the exact source Slot and singleton target; no
shape equality or generic atomic result is accepted. -/
private noncomputable def symmetryGate
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig} {side : ProofSide}
    (scope : ContextRelation.Scope sourceContext targetContext side base)
    {path referent : LambdaPFC.Path n}
    (typing : LambdaPFC.Path.Ty
      (side.choose sourceContext targetContext) path
      (.ty (.Single referent)))
    (source : Slot base (.Single referent)) :
    Action scope (.symm typing)
      (.proper (symmetryRelation (path := path) source)) := by
  exact Action.symmAt scope typing source

private theorem symmetryGate_treeSize
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig} {side : ProofSide}
    (scope : ContextRelation.Scope sourceContext targetContext side base)
    {path referent : LambdaPFC.Path n}
    (typing : LambdaPFC.Path.Ty
      (side.choose sourceContext targetContext) path
      (.ty (.Single referent)))
    (source : Slot base (.Single referent)) :
    (symmetryGate scope typing source).treeSize = 1 := by
  rfl

end LambdaPToFCo.Direct.Internal.ActionSymmetryRegression
