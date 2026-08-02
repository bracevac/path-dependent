import LambdaP.Repaired.PreciseStore

/-! Value inversion for the repaired calculus. -/

namespace LambdaP.Repaired

/-- An ordinary typing of a value factors through its introduction type. -/
theorem Tm.Ty.value_inversion
    (h : Tm.Ty Gamma v T) (hv : v.IsValue) :
    exists P, Tm.PreciseTy Gamma v P /\
      Tau.Sub Gamma (Tau.ty P) (Tau.ty T) := by
  induction h with
  | path _ => cases hv
  | abs ht hwf _ =>
      exact ⟨_, Tm.PreciseTy.abs ht hwf, Tau.Sub.refl⟩
  | app _ _ _ _ => cases hv
  | pair hy hz =>
      exact ⟨_, Tm.PreciseTy.pair hy hz, Tau.Sub.refl⟩
  | tpair hy hwf =>
      exact ⟨_, Tm.PreciseTy.tpair hy hwf, Tau.Sub.refl⟩
  | «let» _ _ _ _ _ => cases hv
  | typed _ _ _ => cases hv
  | sub _ hsub _ ih =>
      obtain ⟨P, hp, hPT⟩ := ih hv
      exact ⟨P, hp, Tau.Sub.trans hPT hsub⟩

end LambdaP.Repaired
