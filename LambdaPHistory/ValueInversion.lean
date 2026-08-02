import LambdaPHistory.PreciseStore

/-!
Value inversion for the restored calculus.

Because ordinary term typing contains subsumption, the type appearing at the
root of a derivation need not reveal the value constructor.  The theorem
below peels off top-level subsumption and recovers the syntax-directed type
assigned by the corresponding value-introduction rule.
-/

namespace LambdaPHistory

/-- An ordinary typing of a value factors through its precise type. -/
theorem Tm.Ty.value_inversion
    (h : Tm.Ty Γ v T) (hv : v.IsValue) :
    ∃ P, Tm.PreciseTy Γ v P ∧
      Tau.Sub Γ (Tau.ty P) (Tau.ty T) := by
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

end LambdaPHistory
