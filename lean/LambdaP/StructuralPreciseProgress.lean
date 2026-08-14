import LambdaP.StructuralPreciseCanonical
import LambdaP.StructuralProgress

/-!
Conditional progress for the exact structural-store invariant.

Exact lookup discharges operational path conversion.  The only remaining
canonical-forms premise is the proper-singleton concrete-head pushback
isolated in `StructuralPreciseCanonical`; abstract selection is represented
separately by `Ty.TSel`.
-/

namespace LambdaP

/-- Binding-oriented function reflection follows from the corresponding
store-binding conclusion once the occupant is supplied. -/
theorem Store.FunctionCheckReflection.to_funCheckReflection
    (h : Store.FunctionCheckReflection Gamma sigma) :
    Store.FunCheckReflection Gamma sigma := by
  intro x S U v hbind hfun
  obtain ⟨A, body, habs⟩ := h hfun
  have heq := Store.Binds.unique hbind habs
  cases heq
  exact ⟨A, body, rfl⟩

/-- The two exact concrete-head facts form the operational package used by
structural progress. -/
theorem Store.HeadCheckReflection.to_structOperational
    (h : Store.HeadCheckReflection Gamma sigma) :
    Store.StructOperational Gamma sigma :=
  ⟨h.pair,
    Store.FunctionCheckReflection.to_funCheckReflection h.function⟩

/-- Exact-state progress factored through its sole concrete-head input. -/
theorem State.PreciseStructTy.progress_of_headCheckReflection
    (hhead : Store.HeadCheckReflection Gamma sigma)
    (h : State.PreciseStructTy Gamma ⟨sigma, k, t⟩ T) :
    State.Progress ⟨sigma, k, t⟩ :=
  State.StructTy.progress hhead.to_structOperational h.toStructTy

/-- Exact store typing plus singleton-head pushback discharges both
reflection clauses used by structural progress. -/
theorem Store.StructPreciseTy.structOperational_of_singletonHeadPushback
    (hstore : Store.StructPreciseTy Gamma sigma)
    (hpush : Store.StructPreciseSingletonHeadPushback Gamma sigma) :
    Store.StructOperational Gamma sigma :=
  (hstore.headCheckReflection_of_singletonPushback hpush).to_structOperational

/-- Full progress for a precise structural state, conditional on exact
head inversion for proper singleton subtyping. -/
theorem State.PreciseStructTy.progress
    (hpush : Store.StructPreciseSingletonHeadPushback Gamma sigma)
    (h : State.PreciseStructTy Gamma ⟨sigma, k, t⟩ T) :
    State.Progress ⟨sigma, k, t⟩ := by
  cases h with
  | ok hstore hcont hterm =>
      exact State.StructTy.progress
        (hstore.structOperational_of_singletonHeadPushback hpush)
        (.ok hstore.toStructTy hcont hterm)

end LambdaP
