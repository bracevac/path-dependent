import PathDependent.LambdaP.Syntax
import PathDependent.LambdaP.Cont
import PathDependent.LambdaP.Store

namespace LambdaP.Reduction

  open LambdaP.Syntax
  open LambdaP.Cont
  open LambdaP.Store

  structure State (n: Nat) where
    σ    : Store n
    cont_tm : Tm.Cont n
    cont_path : Path.Cont
    term : Tm n

  inductive State.Step : State n -> State m -> Prop
  | app_push_l {σ : Store n} :
        Step ⟨σ, k, [], Tm.app p q⟩ ⟨σ, Tm.Frame.app_l q :: k, [], Tm.path p⟩

  | app_push_r {σ : Store n} :
        Step ⟨σ, Tm.Frame.app_l q :: k, [], Tm.path (Path.var x) ⟩ ⟨σ, Tm.Frame.app_r x :: k, [], Tm.path q⟩

  | app {σ : Store n} :
        σ.Binds x (Tm.abs T t) ->
        Step ⟨σ, Tm.Frame.app_r x :: k, [], Tm.path (Path.var y)⟩ ⟨σ, k, [], t.open y⟩

  | let_push {σ : Store n} :
        Step ⟨σ, k, [], Tm.let s t⟩ ⟨σ, Tm.Frame.let t :: k, [], s⟩

  | rename {σ : Store n} :
        Step ⟨σ, Tm.Frame.let t :: k, [], Tm.path (Path.var x)⟩ ⟨σ, k, [], t.open x ⟩

  | lift {σ : Store n} :
        (vv : Tm.IsValue v) ->
        Step ⟨σ, Tm.Frame.let t :: k, [], v⟩ ⟨σ.val v vv, Tm.Cont.weaken k, [], t ⟩

  | ascribe {σ : Store n} :
        Step ⟨σ, k, [], Tm.typed t T⟩ ⟨σ, k, [], t⟩

  | fst_push {σ : Store n} :
        Step ⟨σ, k, p, Tm.path (Path.fst q)⟩ ⟨σ, k, Path.Frame.fst :: p, q⟩

  | fst {σ : Store n} :
        σ.Binds x (Tm.pair y α δ) ->
        Step ⟨σ, k, Path.Frame.fst :: p, Tm.path (Path.var x)⟩ ⟨σ, k, p, Tm.path (Path.var y) ⟩

  | sel_push {σ : Store n} :
        Step ⟨σ, k, p, Tm.path (Path.sel q a)⟩ ⟨σ, k, Path.Frame.sel a :: p, q⟩

  | sel {σ : Store n} :
        σ.Binds x (Tm.pair y a (Def.val z)) ->
        Step ⟨σ, k, Path.Frame.sel a :: p, Tm.path (Path.var x)⟩ ⟨σ, k, p, Tm.path (Path.var z) ⟩


end LambdaP.Reduction
