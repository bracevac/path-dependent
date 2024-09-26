import PathDependent.LambdaP.Syntax
import PathDependent.LambdaP.Context
import PathDependent.LambdaP.Typing
import PathDependent.LambdaP.Cont
import PathDependent.LambdaP.Store

namespace LambdaP.State

  open LambdaP.Store
  open LambdaP.Syntax
  open LambdaP.Cont
  open LambdaP.Context
  open LambdaP.Typing

  structure State (n: Nat) where
      σ    : Store n
      cont : Tm.Cont n
      term : Tm n

  inductive State.Ty: Ctx n -> State n -> Ty n -> Prop
  | ok: {σ : Store n} ->
        Store.Ty Γ σ ->
        Tm.Cont.Ty Γ S k T ->
        Tm.Ty Γ t S ->
        State.Ty Γ ⟨σ, k, t⟩ T

  inductive State.IsFinal: State n -> Prop
  | is_var : {σ : Store n} ->
        σ.Binds x v ->
        State.IsFinal ⟨σ, [], (Tm.path (Path.var x))⟩
  | is_val : {σ : Store n} ->
        v.IsValue ->
        State.IsFinal ⟨σ, [], v⟩

end LambdaP.State
