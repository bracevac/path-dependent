import LambdaP.PathReduction
import LambdaP.State

/-!
The small-step CK machine. Paths are resolved by the source `Path.reduce`
relation; the machine itself retains only term-level `let` frames.
-/

namespace LambdaP

/-- One transition of the indexed machine. -/
inductive State.Step : State n -> State m -> Prop where
| app {σ : Store n} :
    Path.reduce p σ x ->
    Path.reduce q σ y ->
    Store.Binds σ x (Tm.abs T t) ->
    State.Step ⟨σ, k, Tm.app p q⟩ ⟨σ, k, t.open y⟩
| path {σ : Store n} :
    Path.reduce p σ x ->
    ¬ p.IsVar ->
    State.Step
      ⟨σ, k, Tm.path p⟩
      ⟨σ, k, Tm.path (Path.var x)⟩
| let_push {σ : Store n} :
    State.Step
      ⟨σ, k, Tm.let s t⟩
      ⟨σ, Tm.Frame.let t :: k, s⟩
| rename {σ : Store n} :
    State.Step
      ⟨σ, Tm.Frame.let t :: k, Tm.path (Path.var x)⟩
      ⟨σ, k, t.open x⟩
| lift {σ : Store n} :
    (vv : Tm.IsValue v) ->
    State.Step
      ⟨σ, Tm.Frame.let t :: k, v⟩
      ⟨Store.val σ v vv, Tm.Cont.weaken k, t⟩
| ascribe {σ : Store n} :
    State.Step
      ⟨σ, k, Tm.typed t T⟩
      ⟨σ, k, t⟩

end LambdaP
