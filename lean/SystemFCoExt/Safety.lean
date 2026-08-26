import SystemFCoExt.Preservation
import SystemFCoExt.Progress

/-! Finite type safety for the explicit-coercion target. -/

namespace SystemFCoExt.Exp

theorem preservation_steps
    (typing : context |-e expression : ty)
    (reductions : Steps expression expression') :
    Nonempty (context |-e expression' : ty) := by
  induction reductions with
  | refl => exact ⟨typing⟩
  | tail reduction reductions ih =>
      rcases preservation typing reduction with ⟨middleTyping⟩
      exact ih middleTyping

theorem reachable_progress
    (typing : Ctx.empty |-e expression : ty)
    (reductions : Steps expression expression') :
    IsValue expression' \/ Exists fun next => Step expression' next := by
  rcases preservation_steps typing reductions with ⟨typing'⟩
  exact progress typing'

theorem finite_safety
    (typing : Ctx.empty |-e expression : ty)
    (reductions : Steps expression expression') :
    Not (IsStuck expression') := by
  rcases reachable_progress typing reductions with value | ⟨next, step⟩
  · exact fun stuck => stuck.1 value
  · exact fun stuck => stuck.2 ⟨next, step⟩


/-- A closed program goes wrong when a finite reduction reaches a stuck term. -/
def GoesWrong (expression : Exp []) : Prop :=
  Exists fun result => Steps expression result ∧ IsStuck result

theorem soundness
    (typing : Ctx.empty |-e expression : ty) :
    Not (GoesWrong expression) := by
  intro goesWrong
  rcases goesWrong with ⟨result, reductions, stuck⟩
  exact finite_safety typing reductions stuck

end SystemFCoExt.Exp
