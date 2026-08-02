import LambdaP.Repaired.Cont
import LambdaP.Repaired.Store

/-! Indexed configurations and final states for the original CK machine. -/

namespace LambdaP.Repaired

/-- A machine configuration at store/scope size `n`. -/
structure State (n : Nat) where
  σ : Store n
  cont : Tm.Cont n
  term : Tm n

/-- Typing of a complete machine configuration. -/
inductive State.Ty :
    Ctx n -> State n -> LambdaP.Repaired.Ty n -> Prop where
| ok :
    {σ : Store n} ->
    Store.Ty Γ σ ->
    Tm.Cont.Ty Γ S k T ->
    Tm.Ty Γ t S ->
    State.Ty Γ ⟨σ, k, t⟩ T

/-- Final configurations have an empty continuation and contain either a
valid store location or a value. -/
inductive State.IsFinal : State n -> Prop where
| is_var :
    {σ : Store n} ->
    Store.Binds σ x v ->
    State.IsFinal ⟨σ, [], Tm.path (Path.var x)⟩
| is_val :
    {σ : Store n} ->
    v.IsValue ->
    State.IsFinal ⟨σ, [], v⟩

end LambdaP.Repaired
