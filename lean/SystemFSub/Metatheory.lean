import SystemFSub.Reduction

/-!
# Operational facts for System F<:

Source safety will ultimately be obtained from elaboration into the coercion
calculus.  These lemmas provide the small, syntax-directed interface needed by
that argument without duplicating a direct preservation proof for F<:.
-/

namespace SystemFSub
namespace Tm

/-- Weak left-to-right call-by-value evaluation has at most one next state. -/
theorem Step.deterministic {t t1 t2 : Tm s}
    (h1 : Step t t1) (h2 : Step t t2) : t1 = t2 := by
  induction h1 generalizing t2 with
  | app_left h ih =>
      cases h2 with
      | app_left h2 => exact congrArg (fun q => Tm.app q _) (ih h2)
      | app_right hv _ => exact False.elim (hv.not_step h)
      | beta _ => exact False.elim (IsValue.abs.not_step h)
  | app_right hv h ih =>
      cases h2 with
      | app_left h2 => exact False.elim (hv.not_step h2)
      | app_right _ h2 => exact congrArg (fun q => Tm.app _ q) (ih h2)
      | beta hv2 => exact False.elim (hv2.not_step h)
  | beta hv =>
      cases h2 with
      | app_left h2 => exact False.elim (IsValue.abs.not_step h2)
      | app_right _ h2 => exact False.elim (hv.not_step h2)
      | beta _ => rfl
  | tapp_fun h ih =>
      cases h2 with
      | tapp_fun h2 => exact congrArg (fun q => Tm.tapp q _) (ih h2)
      | type_beta => exact False.elim (IsValue.tabs.not_step h)
  | type_beta =>
      cases h2 with
      | tapp_fun h2 => exact False.elim (IsValue.tabs.not_step h2)
      | type_beta => rfl

/-- A value can only reduce to itself by zero steps. -/
theorem IsValue.steps_eq {v u : Tm s} (hv : IsValue v)
    (hsteps : Steps v u) : v = u := by
  cases hsteps with
  | refl => rfl
  | tail h _ => exact False.elim (hv.not_step h)

/-- Stuckness is exactly incompatible with the progress alternative. -/
theorem IsStuck.not_progress {t : Tm s} (hstuck : IsStuck t) :
    Not (HasProgress t) := by
  intro hprogress
  cases hprogress with
  | inl hv => exact hstuck.2 hv
  | inr hstep =>
      cases hstep with
      | intro u h => exact hstuck.1 u h

/--
To establish safety of a closed source program, it suffices to obtain progress
for every state reachable from it.  The elaboration proof will discharge that
premise using target preservation and progress.
-/
theorem not_goesWrong_of_reachable_progress {t : ClosedTerm}
    (hprogress : forall u, Steps t u -> HasProgress u) :
    Not (GoesWrong t) := by
  intro hwrong
  cases hwrong with
  | intro u hu =>
      exact hu.2.not_progress (hprogress u hu.1)

end Tm
end SystemFSub
