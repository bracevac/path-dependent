import PathDependent.FinFun.Basic
import PathDependent.LambdaP.Context
import PathDependent.LambdaP.Syntax

namespace LambdaP.Renaming

  open Context
  open FinFun
  open Syntax

  abbrev Renaming (Γ : Ctx n) (f : FinFun n m) (Δ : Ctx m) := ∀ {x T}, Γ.Binds x T -> Δ.Binds (f x) (T.rename f)

  open Ctx

  def ext (ρ: Renaming Γ f Δ): Renaming (Γ.snoc T) f.ext (Δ.snoc (T.rename f)) := by
    intros x T bnd
    cases bnd
    case here =>
      rw [<- Ty.weaken_rename]
      constructor
    case there bnd' =>
      rw [<- Ty.weaken_rename]
      simp [FinFun.ext]
      constructor
      apply ρ
      assumption

end LambdaP.Renaming
