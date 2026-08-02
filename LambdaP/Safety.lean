import LambdaP.CanonicalForms

/-!
Unconditional safety for closed source programs.

The machine allocates values, so executions are heterogeneous in their scope
index.  Preservation therefore returns the exact context at the endpoint and
an explicit witness that it extends the empty initial context.  Non-stuckness
itself has the usual statement: every endpoint of a finite execution is final
or can take another step.
-/

namespace LambdaP

/-! ## Initial configurations -/

/-- The initial machine configuration for a closed term. -/
def State.initial (t : Tm 0) : State 0 :=
  ⟨Store.empty, [], t⟩

/-- Source typing embeds into the exact structural invariant at the empty
store and empty continuation. -/
theorem Tm.Ty.initial_preciseStructTy
    (ht : Tm.Ty Ctx.nil t T) :
    State.PreciseStructTy Ctx.nil (State.initial t) T := by
  exact .ok Store.StructPreciseTy.empty
    (Tm.Cont.StructTy.hole Tau.StructSub.refl)
    (Tm.StructCheck.of_source ht (Path.RuntimeEq Store.empty))

/-! ## One-step soundness -/

/-- A closed, well-typed source program is final or takes a step which
preserves the exact structural invariant. -/
theorem Tm.Ty.closed_one_step_safety
    (ht : Tm.Ty Ctx.nil t T) :
    State.PreciseStructSafetyOutcome Ctx.nil (State.initial t) T :=
  State.PreciseStructTy.one_step_safety_of_laws
    Store.mappedPreciseStructSafetyLaws ht.initial_preciseStructTy

/-- The usual initial-state progress corollary. -/
theorem Tm.Ty.closed_progress
    (ht : Tm.Ty Ctx.nil t T) :
    State.Progress (State.initial t) :=
  ht.closed_one_step_safety.progress

/-- A transition from a closed well-typed program has a precisely typed
target at either the same scope or one allocation extension. -/
theorem Tm.Ty.closed_step_preservation
    (ht : Tm.Ty Ctx.nil t T)
    (hstep : State.Step (State.initial t) target) :
    exists Delta U,
      State.PreciseStructExtension Ctx.nil T Delta U /\
      State.PreciseStructTy Delta target U := by
  exact State.PreciseSteps.preservation_of_laws
    Store.mappedPreciseStructSafetyLaws
    (.tail hstep .refl) ht.initial_preciseStructTy

/-! ## Finite-run soundness -/

/-- Every finite execution from a closed source term preserves exact
structural typing, with allocation-induced context growth made explicit. -/
theorem Tm.Ty.closed_finite_preservation
    (ht : Tm.Ty Ctx.nil t T)
    (hsteps : State.PreciseSteps (State.initial t) target) :
    exists Delta U,
      State.PreciseStructExtension Ctx.nil T Delta U /\
      State.PreciseStructTy Delta target U :=
  State.PreciseSteps.preservation_of_laws
    Store.mappedPreciseStructSafetyLaws hsteps
    ht.initial_preciseStructTy

/-- Preservation and progress at every finite execution endpoint. -/
theorem Tm.Ty.closed_finite_safety
    (ht : Tm.Ty Ctx.nil t T)
    (hsteps : State.PreciseSteps (State.initial t) target) :
    exists Delta U,
      State.PreciseStructExtension Ctx.nil T Delta U /\
      State.PreciseStructTy Delta target U /\
      State.PreciseStructSafetyOutcome Delta target U :=
  State.PreciseSteps.safety_of_laws
    Store.mappedPreciseStructSafetyLaws hsteps
    ht.initial_preciseStructTy

/-- Type safety: no finite execution of a closed, well-typed source term
ends in a stuck configuration. -/
theorem Tm.Ty.closed_type_safety
    (ht : Tm.Ty Ctx.nil t T)
    (hsteps : State.PreciseSteps (State.initial t) target) :
    State.Progress target :=
  State.PreciseSteps.nonstuck_of_laws
    Store.mappedPreciseStructSafetyLaws hsteps
    ht.initial_preciseStructTy

end LambdaP
