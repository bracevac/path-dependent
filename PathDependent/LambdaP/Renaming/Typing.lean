import PathDependent.FinFun.Basic
import PathDependent.LambdaP.Context
import PathDependent.LambdaP.Syntax
import PathDependent.LambdaP.Typing
import PathDependent.LambdaP.Renaming.Basic

namespace LambdaP.Renaming.Typing

  open LambdaP.Context
  open LambdaP.Syntax
  open LambdaP.Typing

  theorem Path.Ty.rename: Path.Ty Γ p T -> Renaming Γ f Δ -> Path.Ty Δ (p.rename f) (T.rename f) := sorry

  theorem Tau.Sub.rename: Tau.Sub Γ τ1 τ2 -> Renaming Γ f Δ -> Tau.Sub Δ (τ1.rename f) (τ2.rename f) := sorry

  theorem Tau.Wf.rename: Tau.Wf Γ τ -> Renaming Γ f Δ -> Tau.Wf Δ (τ.rename f) := sorry

  theorem Tm.Ty.rename: Tm.Ty Γ t T -> Renaming Γ f Δ -> Tm.Ty Δ (t.rename f) (T.rename f) := sorry

end LambdaP.Renaming.Typing
