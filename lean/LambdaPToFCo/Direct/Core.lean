import SystemFCo.Typing

/-!
# Public result of direct compilation

The direct compiler returns target syntax only. Its target-typing statement
is separate, so no derivation or compiler-internal representation is stored
in the generated term.
-/

namespace LambdaPToFCo.Direct

open SystemFCo

/-- Generated target syntax. -/
structure Compiled (sig : Sig) where
  targetType : Ty sig
  expression : Exp sig

namespace Compiled

/-- The separate target-typing statement for generated syntax. -/
def WellTyped (targetContext : Ctx sig)
    (compiled : Compiled sig) : Type :=
  Exp.HasType targetContext compiled.expression compiled.targetType

end Compiled

end LambdaPToFCo.Direct
