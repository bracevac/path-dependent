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

namespace LambdaP.Soundness.Preservation

  inductive Preserve: Ctx n -> State m -> Ty n -> Prop
  | same:
    State.Ty Γ σ T ->
    Preserve Γ σ T

  | extend:
    State.Ty (Γ.snoc S) σ T.weaken ->
    Preserve Γ σ T

  theorem preservation (hstep: State.Step s s') (hty: State.Ty Γ s T): Preserve Γ s' T := by
    cases hstep

    case app p_red_x q_red_y hl =>
      cases hty
      case ok S htys htyt htyk =>
      sorry

    case let_push =>
      cases hty
      case ok S htys htyt htyk =>
      sorry

    case rename =>
      cases hty
      case ok S htys htyt htyk =>
      sorry

    case lift =>
      cases hty
      case ok S htys htyt htyk =>
      sorry

    case ascribe =>
      cases hty
      case ok S htys htyt htyk =>
      sorry

end LambdaP.Soundness.Preservation
