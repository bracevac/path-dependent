import LambdaPToFCo.Direct.Core
import LambdaPToFCo.Direct.Shape

/-!
# Focused value elimination for the direct compiler

A focus closes a body authored inside the interface exposed by one stable or
opaque `Shape`. Source-environment extension belongs to the single
representation-indexed environment in `Direct.Representation`.
-/

namespace LambdaPToFCo.Direct.Internal.Focus

open SystemFCo

/-- Close a body authored at a stable or opaque value focus. -/
def eliminate (shape : Shape sig) (value : Exp sig)
    (answer : Ty sig) (body : Exp shape.scope) : Compiled sig where
  targetType := answer
  expression := shape.eliminate value answer body

/-- Extrinsic typing for focused elimination. -/
noncomputable def eliminate_wellTyped
    (shape : Shape sig) {targetContext : Ctx sig}
    {value : Exp sig} {answer : Ty sig} {body : Exp shape.scope}
    (valueTyping : Exp.HasType targetContext value shape.inputTy)
    (bodyTyping : Exp.HasType (shape.context targetContext) body
      (answer.rename shape.binders.weaken)) :
    (eliminate shape value answer body).WellTyped targetContext :=
  shape.eliminate_hasType valueTyping bodyTyping

end LambdaPToFCo.Direct.Internal.Focus
