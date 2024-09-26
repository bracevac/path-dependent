import PathDependent.LambdaP.Syntax
import PathDependent.LambdaP.Context
import PathDependent.LambdaP.Cont
import PathDependent.LambdaP.Store
import PathDependent.LambdaP.State
import PathDependent.LambdaP.Reduction

open LambdaP.Syntax
open LambdaP.Typing
open LambdaP.Context
open LambdaP.Store
open LambdaP.State
open LambdaP.Reduction

namespace LambdaP.Soundness.Progress

  inductive Progress: State n -> Prop
  | is_final : s.IsFinal -> Progress s
  | can_step : State.Step s s' -> Progress s

  theorem progress (ht: State.Ty Γ s T): Progress s := by
    cases ht
    case ok σ st tt kt =>
      induction tt
      case path   => sorry
      case abs    => sorry
      case app    => sorry
      case pair   => sorry
      case tpair  => sorry
      case typed  => sorry
      case sub    => sorry
      case _      => sorry


end LambdaP.Soundness.Progress
