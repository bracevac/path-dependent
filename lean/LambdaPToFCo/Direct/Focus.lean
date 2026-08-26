import LambdaPToFCo.Direct.Core

/-!
# Focused value opening for the direct compiler

Shape elimination exposes a stable plan's mixed telescope, or one raw binder
for an opaque value, only inside its consumer body.  This module reindexes a
source environment into that opened target scope and installs the canonical
reclosed value as its newest slot.

No source type representation is inferred here.  The later path compiler
decides when to enter a value and what its source typing derivation permits
it to observe.
-/

namespace LambdaPToFCo.Direct

open LambdaPFC
open SystemFCo

namespace Internal

namespace Focus

/-- Close a body authored at a stable or opaque value focus. -/
def eliminate (shape : Shape sig) (value : Exp sig)
    (answer : Ty sig) (body : Exp shape.scope) : Compiled sig where
  targetType := answer
  expression := shape.eliminate value answer body

/-- Extrinsic typing for focused elimination. -/
noncomputable def eliminate_wellTyped
    (shape : Shape sig) {targetContext : SystemFCo.Ctx sig}
    {value : Exp sig} {answer : Ty sig} {body : Exp shape.scope}
    (valueTyping : Exp.HasType targetContext value shape.inputTy)
    (bodyTyping : Exp.HasType (shape.context targetContext) body
      (answer.rename shape.binders.weaken)) :
    (eliminate shape value answer body).WellTyped targetContext :=
  shape.eliminate_hasType valueTyping bodyTyping

end Focus

namespace Env

/-- Open one shape and install its canonical reclosed value as the newest
source slot. Older values are weakened through the complete target binder
telescope. -/
noncomputable def enter
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    (targetContext : SystemFCo.Ctx sig)
    (environment : Env sourceContext sig)
    (sourceType : LambdaPFC.Ty n) (shape : Shape sig) :
    Env (sourceContext.snoc sourceType) shape.scope where
  lookup := Fin.cases
    { shape := shape.rename shape.binders.weaken
      expression := (Shape.Interface.canonical targetContext shape).package }
    (fun older =>
      (environment.lookup older).rename shape.binders.weaken)

@[simp] theorem enter_here
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    (targetContext : SystemFCo.Ctx sig)
    (environment : Env sourceContext sig)
    (sourceType : LambdaPFC.Ty n) (shape : Shape sig) :
    (environment.enter targetContext sourceType shape).lookup 0 =
      { shape := shape.rename shape.binders.weaken
        expression :=
          (Shape.Interface.canonical targetContext shape).package } := by
  rfl

@[simp] theorem enter_there
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    (targetContext : SystemFCo.Ctx sig)
    (environment : Env sourceContext sig)
    (sourceType : LambdaPFC.Ty n) (shape : Shape sig)
    (index : Fin n) :
    (environment.enter targetContext sourceType shape).lookup index.succ =
      (environment.lookup index).rename shape.binders.weaken := by
  rfl

end Env

namespace Env.WellTyped

/-- Opening a shape preserves every old slot and types the canonical new
slot. -/
noncomputable def enter
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    {environment : Env sourceContext sig}
    (typedEnvironment : Env.WellTyped targetContext environment)
    (sourceType : LambdaPFC.Ty n) (shape : Shape sig) :
    Env.WellTyped (shape.context targetContext)
      (environment.enter targetContext sourceType shape) where
  lookup index := by
    refine Fin.cases ?_ (fun older => ?_) index
    · exact (Shape.Interface.canonical targetContext shape).package_hasType
    · exact (typedEnvironment.lookup older).rename shape.binders.weaken
        (shape.binders.weaken_typed targetContext)

end Env.WellTyped

end Internal

end LambdaPToFCo.Direct
