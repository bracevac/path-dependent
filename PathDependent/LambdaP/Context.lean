import PathDependent.LambdaP.Syntax

namespace LambdaP.Context

  open Syntax

  inductive Ctx: Nat -> Type
  | nil  : Ctx 0
  | snoc : Ctx n -> Ty n -> Ctx (n + 1)

  inductive Ctx.Binds: Ctx n -> Fin n -> Ty n -> Prop -- TODO

end LambdaP.Context
