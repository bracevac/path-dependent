import LambdaPCC.CapturePreservation

/-!
Finite preservation and closed type safety for the capture-aware machine
invariant.  Store allocation may weaken both the result type and
the source use set.
-/

namespace LambdaPCC

noncomputable section

/-- Initial joint type-and-use evidence obtained from a closed source typing
derivation. -/
noncomputable def Tm.Ty.initialEvidence
    {term : Tm 0} {T : LambdaPCC.Ty 0} {C : CaptureSet 0}
    (code : Tm.Ty Ctx.nil term T C) :
    Cap.StateEvidence Cap.World.Valid.empty (State.initial term) T C := by
  let rho : Valuation 0 0 := Valuation.id
  have environment :
      Cap.Environment Cap.World.empty Ctx.nil rho :=
    Cap.Environment.empty
  have interpreted := Cap.Tm.Ty.interpret code environment
    Cap.World.Valid.empty
  have stateEvidence :
      Cap.StateEvidence Cap.World.Valid.empty
        (State.mk Store.empty [] (term.rename rho))
        (T.rename rho) (C.rename rho) :=
    .ok (.hole .refl .refl) interpreted
  simpa only [State.initial, rho, Valuation.id, Tm.rename_id,
    Ty.rename_id, CaptureSet.rename_id] using stateEvidence

/-- Joint semantic preservation iterated over a heterogeneous finite
execution. -/
theorem State.Steps.preservation
    {n m : Nat} {source : State n} {target : State m}
    {world : Cap.World source.store} {valid : Cap.World.Valid world}
    {T : LambdaPCC.Ty n} {C : CaptureSet n}
    (steps : State.Steps source target)
    (evidence : Cap.StateEvidence valid source T C) :
    exists (targetWorld : Cap.World target.store)
      (targetValid : Cap.World.Valid targetWorld)
      (U : LambdaPCC.Ty m) (D : CaptureSet m),
      Cap.Ty.Extends T U /\ Cap.CaptureSet.Extends C D /\
        Nonempty (Cap.StateEvidence targetValid target U D) := by
  induction steps with
  | refl =>
      exact ⟨world, valid, T, C, .refl, .refl, ⟨evidence⟩⟩
  | tail step rest ih =>
      obtain ⟨middleWorld, middleValid, U, D,
          typeExtension, captureExtension, ⟨middleEvidence⟩⟩ :=
        Cap.StateEvidence.preservation evidence step
      obtain ⟨targetWorld, targetValid, V, E,
          restTypeExtension, restCaptureExtension, finalEvidence⟩ :=
        ih middleEvidence
      exact ⟨targetWorld, targetValid, V, E,
        typeExtension.trans restTypeExtension,
        captureExtension.trans restCaptureExtension,
        finalEvidence⟩

/-- Initial progress for a closed, well-typed term under the joint invariant. -/
theorem Tm.Ty.closed_progress
    {term : Tm 0} {T : LambdaPCC.Ty 0} {C : CaptureSet 0}
    (typing : Tm.Ty Ctx.nil term T C) :
    State.Progress (State.initial term) :=
  typing.initialEvidence.progress

/-- Every state reached by a finite execution retains joint type-and-use
evidence, modulo allocation weakening. -/
theorem Tm.Ty.closed_finite_preservation
    {term : Tm 0} {T : LambdaPCC.Ty 0} {C : CaptureSet 0}
    (typing : Tm.Ty Ctx.nil term T C)
    (steps : State.Steps (State.initial term) target) :
    exists (targetWorld : Cap.World target.store)
      (targetValid : Cap.World.Valid targetWorld)
      (U : LambdaPCC.Ty _) (D : CaptureSet _),
      Cap.Ty.Extends T U /\ Cap.CaptureSet.Extends C D /\
        Nonempty (Cap.StateEvidence targetValid target U D) :=
  steps.preservation typing.initialEvidence

/-- A finite execution of a closed, well-typed term cannot end in a stuck
state. -/
theorem Tm.Ty.closed_type_safety
    {term : Tm 0} {T : LambdaPCC.Ty 0} {C : CaptureSet 0}
    (typing : Tm.Ty Ctx.nil term T C)
    (steps : State.Steps (State.initial term) target) :
    State.Progress target := by
  obtain ⟨targetWorld, targetValid, U, D, typeExtension,
      captureExtension, ⟨evidence⟩⟩ :=
    typing.closed_finite_preservation steps
  exact evidence.progress

end
end LambdaPCC
