import LambdaPHistory.StructuralPreciseCanonical
import LambdaPHistory.StructuralProgress

/-!
Progress for the exact structural-store invariant.

`State.PreciseStructTy` keeps each store location at the introduction type
of its value.  The local bridge below turns concrete-head reflection into
the operational package consumed by the already checked structural progress
proof.  Exact lookup discharges all operational path-conversion issues; the
remaining parameter is the head-only singleton-subtyping pushback isolated
in `StructuralPreciseCanonical`.
-/

namespace LambdaPHistory

/-- The binding-oriented function reflection used by `StructuralProgress`
is equivalent to the store-binding conclusion of head reflection once a
particular occupant is supplied. -/
theorem Store.FunctionCheckReflection.to_funCheckReflection
    (h : Store.FunctionCheckReflection Gamma sigma) :
    Store.FunCheckReflection Gamma sigma := by
  intro x S U v hbind hfun
  obtain ⟨A, body, habs⟩ := h hfun
  have heq := Store.Binds.unique hbind habs
  cases heq
  exact ⟨A, body, rfl⟩

/-- The two concrete-head facts are exactly the operational assumptions
used by path and machine progress. -/
theorem Store.HeadCheckReflection.to_structOperational
    (h : Store.HeadCheckReflection Gamma sigma) :
    Store.StructOperational Gamma sigma :=
  ⟨h.pair,
    Store.FunctionCheckReflection.to_funCheckReflection h.function⟩

/-- Exact-state progress factored through its sole canonical-forms input.
This theorem remains useful as the interface between the exact-store and
machine developments. -/
theorem State.PreciseStructTy.progress_of_headCheckReflection
    (hhead : Store.HeadCheckReflection Gamma sigma)
    (h : State.PreciseStructTy Gamma ⟨sigma, k, t⟩ T) :
    State.Progress ⟨sigma, k, t⟩ :=
  State.StructTy.progress hhead.to_structOperational h.toStructTy

/-! ## Exact-store specialization -/

/-- Exact store typing plus the minimal singleton-head pushback property
discharges both reflection clauses used by structural progress. -/
theorem Store.StructPreciseTy.structOperational_of_singletonHeadPushback
    (hstore : Store.StructPreciseTy Gamma sigma)
    (hpush : Store.StructPreciseSingletonHeadPushback Gamma sigma) :
    Store.StructOperational Gamma sigma :=
  (hstore.headCheckReflection_of_singletonPushback hpush).to_structOperational

/-- Full progress for a precise structural state, conditional only on the
exact head-inversion residual for singleton subtyping. -/
theorem State.PreciseStructTy.progress
    (hpush : Store.StructPreciseSingletonHeadPushback Gamma sigma)
    (h : State.PreciseStructTy Gamma ⟨sigma, k, t⟩ T) :
    State.Progress ⟨sigma, k, t⟩ := by
  cases h with
  | ok hstore hcont hterm =>
      exact State.StructTy.progress
        (hstore.structOperational_of_singletonHeadPushback hpush)
        (.ok hstore.toStructTy hcont hterm)

end LambdaPHistory
