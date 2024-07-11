import PathDependent.LambdaP.Syntax

namespace LambdaP.Context

  open Syntax

  inductive Ctx: Nat -> Type
  | nil  : Ctx 0
  | snoc : Ctx n -> Ty n -> Ctx (n + 1)

  open Ctx

  inductive Ctx.Binds: Ctx n -> Fin n -> Ty n -> Prop
  | here:  Binds (snoc Γ T) 0 T.weaken
  | there: Binds Γ x T -> Binds (Γ.snoc S) (Fin.succ x) T.weaken

end LambdaP.Context
