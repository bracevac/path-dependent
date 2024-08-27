import PathDependent.LambdaP.Syntax

namespace LambdaP.Store
  open LambdaP.Syntax

  inductive Store: Nat -> Type
  | empty : Store n
  | val : Store n -> (t: Tm n) -> t.IsValue -> Store (n + 1)

  inductive Store.Binds: Store n -> Fin n -> Tm n -> Prop
  | here:  Binds (val σ v vv) 0 v.weaken
  | there: Binds σ x v -> Binds (σ.val u uv) (Fin.succ x) v.weaken

  lemma Store.Binds.IsValue: Store.Binds σ x v -> v.IsValue := by
    sorry

end LambdaP.Store
