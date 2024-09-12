import PathDependent.LambdaP.Syntax
import PathDependent.LambdaP.Context
import PathDependent.LambdaP.Cont
import PathDependent.LambdaP.Store
import PathDependent.LambdaP.State

namespace LambdaP.Reduction

  open LambdaP.Syntax
  open LambdaP.Cont
  open LambdaP.Store
  open LambdaP.Context
  open LambdaP.State

  -- We reduce a path big-step until it is an atomic variable. pDOT would yield the *value* at the path, we opt to return the *location* instead.
  -- TODO: should we generalize this to permit type member lookup? is that needed?
  inductive Path.reduce: Path n -> Store n -> Fin n -> Prop
  | var : Path.reduce (Path.var x) σ x

  | fst : Path.reduce p σ x ->
          σ.Binds x (Tm.pair y α δ) ->
          Path.reduce p.fst σ y

  | sel_hit :
          Path.reduce p σ x ->
          σ.Binds x (Tm.pair y a (Def.val z)) ->
          Path.reduce (p.sel a) σ z

  | sel_miss :
          Path.reduce p σ x ->
          σ.Binds x (Tm.pair y b δ) ->
          a ≠ b ->
          Path.reduce ((Path.var y).sel a) σ z ->
          Path.reduce (p.sel a) σ z

  -- TODO: prove that Path.reduce is the graph of a partial function

  inductive State.Step : State n -> State m -> Prop
  | app {σ : Store n} :
        Path.reduce p σ x ->
        Path.reduce q σ y -> -- TODO: do we want to do it like pDOT and be lazy in the argument path q?
        σ.Binds x (Tm.abs T t) ->
        Step ⟨σ, k, Tm.app p q⟩ ⟨σ, k, t.open y⟩

  | let_push {σ : Store n} :
        Step ⟨σ, k, Tm.let s t⟩ ⟨σ, Tm.Frame.let t :: k, s⟩

  | rename {σ : Store n} :
        Step ⟨σ, Tm.Frame.let t :: k, Tm.path (Path.var x)⟩ ⟨σ, k, t.open x ⟩

  | lift {σ : Store n} :
        (vv : Tm.IsValue v) ->
        Step ⟨σ, Tm.Frame.let t :: k, v⟩ ⟨σ.val v vv, Tm.Cont.weaken k, t ⟩

  | ascribe {σ : Store n} :
        Step ⟨σ, k, Tm.typed t T⟩ ⟨σ, k, t⟩

end LambdaP.Reduction
