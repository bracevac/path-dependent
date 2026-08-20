import LambdaPFCI.Syntax

/-! Intrinsically scoped typing contexts for the calculus. -/

namespace LambdaPFCI

/-- A context stores each type in the scope preceding its binder. -/
inductive Ctx : Nat -> Type where
| nil : Ctx 0
| snoc : Ctx n -> Ty n -> Ctx (n + 1)

namespace Ctx

/-- The type stored at a context index, weakened through every newer binder. -/
def lookup : (Γ : Ctx n) -> Fin n -> Ty n
| .nil, x => Fin.elim0 x
| .snoc Γ T, x =>
    Fin.cases T.weaken (fun i => (lookup Γ i).weaken) x

end Ctx

end LambdaPFCI
