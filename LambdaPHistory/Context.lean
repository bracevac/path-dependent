import LambdaPHistory.Syntax

/-! Intrinsically scoped typing contexts for the restored calculus. -/

namespace LambdaPHistory

/-- A context stores each type in the scope preceding its binder. -/
inductive Ctx : Nat -> Type where
| nil : Ctx 0
| snoc : Ctx n -> Ty n -> Ctx (n + 1)

namespace Ctx

/-- Lookup in a context, with the stored type weakened to the full scope. -/
inductive Binds : Ctx n -> Fin n -> Ty n -> Prop where
| here : Binds (.snoc Γ T) 0 T.weaken
| there : Binds Γ x T -> Binds (.snoc Γ S) x.succ T.weaken

end Ctx

end LambdaPHistory
