import LambdaPFC.SemanticFundamental
import LambdaPFC.SemanticPreservation

/-!
Closed type safety for the native `LambdaPFC` development.

The source typing derivation is interpreted at the initial state. One step
preserves semantic evidence, allowing the advertised result type to be
weakened when the machine allocates.  Iteration yields progress at every
state reached by a finite execution.
-/

namespace LambdaPFC

noncomputable section

/-- Initial-state evidence obtained from a source typing derivation. -/
noncomputable def Tm.Ty.initialEvidence
    {term : Tm 0} {T : LambdaPFC.Ty 0}
    (code : Tm.Ty Ctx.nil term T) :
    State.Evidence (State.initial term) T := by
  simpa only [State.initial, FinFun.id, Tm.rename_id,
    Ty.rename_id] using
    State.Evidence.ok .hole (code.interpret Environment.empty)

/-- Semantic preservation iterated over a finite execution. -/
theorem State.Steps.preservation
    {n m : Nat} {source : State n} {target : State m}
    {T : LambdaPFC.Ty n}
    (steps : State.Steps source target)
    (evidence : State.Evidence source T) :
    exists U : LambdaPFC.Ty m,
      T.Extends U /\ Nonempty (State.Evidence target U) := by
  induction steps with
  | refl =>
      exact ⟨T, .refl, ⟨evidence⟩⟩
  | tail step rest ih =>
      obtain ⟨U, extension, ⟨middleEvidence⟩⟩ :=
        evidence.preservation step
      obtain ⟨V, restExtension, finalEvidence⟩ :=
        ih middleEvidence
      exact ⟨V, extension.trans restExtension, finalEvidence⟩

/-- Initial progress for a closed, well-typed term. -/
theorem Tm.Ty.closed_progress
    {term : Tm 0} {T : LambdaPFC.Ty 0}
    (typing : Tm.Ty Ctx.nil term T) :
    State.Progress (State.initial term) := by
  exact typing.initialEvidence.progress

/-- Every state reached by a finite execution retains semantic typing, modulo the
weakening induced by allocation. -/
theorem Tm.Ty.closed_finite_preservation
    {term : Tm 0} {T : LambdaPFC.Ty 0}
    (typing : Tm.Ty Ctx.nil term T)
    (steps : State.Steps (State.initial term) target) :
    exists U, T.Extends U /\ Nonempty (State.Evidence target U) := by
  exact steps.preservation typing.initialEvidence

/-- A finite execution of a closed, well-typed term cannot end in a stuck
state. -/
theorem Tm.Ty.closed_type_safety
    {term : Tm 0} {T : LambdaPFC.Ty 0}
    (typing : Tm.Ty Ctx.nil term T)
    (steps : State.Steps (State.initial term) target) :
    State.Progress target := by
  obtain ⟨U, extension, ⟨evidence⟩⟩ :=
    typing.closed_finite_preservation steps
  exact evidence.progress

end

end LambdaPFC
