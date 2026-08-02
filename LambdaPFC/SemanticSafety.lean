import LambdaPFC.SemanticFundamental
import LambdaPFC.SemanticPreservation

/-!
Closed type safety for the native `LambdaPFC` development.

The source typing derivation is elaborated once, at the initial state.  One
step preserves semantic evidence, allowing the advertised result type to be
weakened when the machine allocates.  Iteration yields progress at every
finite execution endpoint.
-/

namespace LambdaPFC

noncomputable section

/-- Proof-relevant initial-state evidence from a proof-relevant source typing
derivation. -/
noncomputable def TermCode.initialEvidence
    {term : Tm 0} {T : Ty 0} (code : TermCode Ctx.nil term T) :
    State.Evidence (State.initial term) T := by
  let rho : Valuation 0 0 := Valuation.id
  have environment : Environment Ctx.nil rho Store.empty :=
    .intro (fun x => Fin.elim0 x)
  have interpreted := code.interpret environment
  have stateEvidence :
      State.Evidence
        (State.mk Store.empty [] (term.rename rho)) (T.rename rho) :=
    .ok (.hole .refl) interpreted
  simpa only [State.initial, rho, Valuation.id, Tm.rename_id,
    Ty.rename_id] using stateEvidence

/-- Every closed declaratively typed term has initial semantic evidence. -/
theorem Tm.Ty.nonempty_initialEvidence
    {term : Tm 0} {T : LambdaPFC.Ty 0}
    (typing : Tm.Ty Ctx.nil term T) :
    Nonempty (State.Evidence (State.initial term) T) := by
  obtain ⟨code⟩ := TermCode.nonempty_of_ty typing
  exact ⟨code.initialEvidence⟩

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
  obtain ⟨evidence⟩ := typing.nonempty_initialEvidence
  exact evidence.progress

/-- Every finite execution endpoint retains semantic typing, modulo the
weakening induced by allocation. -/
theorem Tm.Ty.closed_finite_preservation
    {term : Tm 0} {T : LambdaPFC.Ty 0}
    (typing : Tm.Ty Ctx.nil term T)
    (steps : State.Steps (State.initial term) target) :
    exists U, T.Extends U /\ Nonempty (State.Evidence target U) := by
  obtain ⟨initialEvidence⟩ := typing.nonempty_initialEvidence
  exact steps.preservation initialEvidence

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

/-- Finite preservation and progress packaged together. -/
theorem Tm.Ty.closed_finite_safety
    {term : Tm 0} {T : LambdaPFC.Ty 0}
    (typing : Tm.Ty Ctx.nil term T)
    (steps : State.Steps (State.initial term) target) :
    exists U, T.Extends U /\
      Nonempty (State.Evidence target U) /\ State.Progress target := by
  obtain ⟨U, extension, evidence⟩ :=
    typing.closed_finite_preservation steps
  obtain ⟨targetEvidence⟩ := evidence
  exact ⟨U, extension, ⟨targetEvidence⟩, targetEvidence.progress⟩

end

end LambdaPFC
