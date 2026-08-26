import LambdaPFC.Typing
import LambdaPToFCo.Direct.Shape

/-!
# Direct source-facing compiler core

This leaf connects source variables to raw target value expressions.  It
does not store target typing derivations in generated syntax, and it opens no
value shape eagerly.  The later path compiler is responsible for focused
elimination.  Stable values carry Church-package plans; abstract selections
may instead carry only an opaque target type.

The only public compiler result below is target syntax.  Its typing statement
is separate.  Source provenance is supplied by the source derivation consumed
by the eventual compiler, rather than duplicated in another public hierarchy.
-/

namespace LambdaPToFCo.Direct

open LambdaPFC
open SystemFCo

namespace Internal

/-- Raw target syntax stored for one source variable. -/
structure Slot (sig : Sig) where
  shape : Shape sig
  expression : Exp sig

namespace Slot

/-- Reindex both pieces of a raw slot. -/
def rename (slot : Slot source) (mapping : Rename source target) :
    Slot target where
  shape := slot.shape.rename mapping
  expression := slot.expression.rename mapping

/-- Extrinsic target typing for a raw slot. -/
def WellTyped (targetContext : SystemFCo.Ctx sig)
    (slot : Slot sig) : Type :=
  Exp.HasType targetContext slot.expression slot.shape.inputTy

/-- Slot typing is natural under a typed target renaming. -/
noncomputable def WellTyped.rename
    {sourceContext : SystemFCo.Ctx source}
    {targetContext : SystemFCo.Ctx target}
    {slot : Slot source}
    (typedSlot : WellTyped sourceContext slot)
    (mapping : Rename source target)
    (typedMapping : Rename.Typed sourceContext targetContext mapping) :
    WellTyped targetContext (slot.rename mapping) := by
  change Exp.HasType targetContext (slot.expression.rename mapping)
    (slot.shape.rename mapping).inputTy
  rw [← Shape.inputTy_rename]
  exact SystemFCo.Exp.HasType.rename typedSlot typedMapping

end Slot

/-- A syntax-only correspondence from source variables to target value
expressions.  The source context fixes the source indices and their types;
the environment adds no second provenance tree. -/
structure Env {n : Nat} (sourceContext : LambdaPFC.Ctx n) (sig : Sig) where
  lookup : Fin n -> Slot sig

namespace Env

/-- The unique environment for an empty source scope. -/
def empty : Env LambdaPFC.Ctx.nil sig where
  lookup index := Fin.elim0 index

/-- Reindex every target value in an environment. -/
def rename {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    (environment : Env sourceContext source)
    (mapping : Rename source target) : Env sourceContext target where
  lookup index := (environment.lookup index).rename mapping

/-- Add one raw target value variable.  Opening its available interface is a
later focused/CPS operation, not part of environment extension. -/
def bind {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    (environment : Env sourceContext sig)
    (sourceType : LambdaPFC.Ty n) (shape : Shape sig) :
    Env (sourceContext.snoc sourceType) (sig ,, .var) where
  lookup := Fin.cases
    { shape := shape.rename (Rename.weaken .var)
      expression := .var .here }
    (fun older => (environment.lookup older).rename (Rename.weaken .var))

@[simp] theorem bind_here
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    (environment : Env sourceContext sig)
    (sourceType : LambdaPFC.Ty n) (shape : Shape sig) :
    (environment.bind sourceType shape).lookup 0 =
      { shape := shape.rename (Rename.weaken .var)
        expression := .var .here } := by
  rfl

@[simp] theorem bind_there
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    (environment : Env sourceContext sig)
    (sourceType : LambdaPFC.Ty n) (shape : Shape sig)
    (index : Fin n) :
    (environment.bind sourceType shape).lookup index.succ =
      (environment.lookup index).rename (Rename.weaken .var) := by
  rfl

/-- Every raw environment slot is checked at its shape's input type. -/
structure WellTyped {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    (targetContext : SystemFCo.Ctx sig)
    (environment : Env sourceContext sig) : Type where
  lookup : (index : Fin n) ->
    Slot.WellTyped targetContext (environment.lookup index)

def WellTyped.empty (targetContext : SystemFCo.Ctx sig) :
    WellTyped targetContext empty where
  lookup index := Fin.elim0 index

/-- Environment typing is natural under a typed target renaming. -/
noncomputable def WellTyped.rename
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceTargetContext : SystemFCo.Ctx source}
    {targetTargetContext : SystemFCo.Ctx target}
    {environment : Env sourceContext source}
    (typedEnvironment : WellTyped sourceTargetContext environment)
    (mapping : Rename source target)
    (typedMapping : Rename.Typed sourceTargetContext targetTargetContext
      mapping) :
    WellTyped targetTargetContext (environment.rename mapping) where
  lookup index :=
    (typedEnvironment.lookup index).rename mapping typedMapping

/-- Binding a value shape preserves extrinsic environment typing. -/
noncomputable def WellTyped.bind
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    {environment : Env sourceContext sig}
    (typedEnvironment : WellTyped targetContext environment)
    (sourceType : LambdaPFC.Ty n) (shape : Shape sig) :
    WellTyped (targetContext.bindVar shape.inputTy)
      (environment.bind sourceType shape) where
  lookup index := by
    refine Fin.cases ?_ (fun older => ?_) index
    · change Exp.HasType (targetContext.bindVar shape.inputTy) (.var .here)
        (shape.rename (Rename.weaken .var)).inputTy
      rw [← Shape.inputTy_rename]
      exact .var Ctx.Lookup.here
    · exact (typedEnvironment.lookup older).rename
        (Rename.weaken .var)
        (Rename.Typed.weaken targetContext (.var shape.inputTy))

end Env

end Internal

/-- Generated target syntax.  No target derivation or compiler certificate
is stored in the public result. -/
structure Compiled (sig : Sig) where
  targetType : SystemFCo.Ty sig
  expression : SystemFCo.Exp sig

namespace Compiled

/-- The separate target-typing statement for generated syntax. -/
def WellTyped (targetContext : SystemFCo.Ctx sig)
    (compiled : Compiled sig) : Type :=
  SystemFCo.Exp.HasType targetContext compiled.expression compiled.targetType

end Compiled

end LambdaPToFCo.Direct
