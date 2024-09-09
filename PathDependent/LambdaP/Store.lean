import PathDependent.LambdaP.Syntax
import PathDependent.LambdaP.Context
import PathDependent.LambdaP.Typing

namespace LambdaP.Store
  open LambdaP.Syntax
  open LambdaP.Context
  open LambdaP.Typing

  inductive Store: Nat -> Type
  | empty : Store n
  | val : Store n -> (t: Tm n) -> t.IsValue -> Store (n + 1)

  inductive Store.Binds: Store n -> Fin n -> Tm n -> Prop
  | here:  Binds (val σ v vv) 0 v.weaken
  | there: Binds σ x v -> Binds (σ.val u uv) (Fin.succ x) v.weaken

  lemma Store.Binds.IsValue: Store.Binds σ x v -> v.IsValue := by
    sorry

  inductive Store.Ty: Ctx n -> Store n -> Prop
  | empty : Ty Ctx.nil Store.empty
  | val: Ty Γ σ ->
         Tm.Ty Γ t T ->
         Ty (Γ.snoc T) (σ.val t vt)

end LambdaP.Store
