import LambdaPFC.MachineSupport
import LambdaPFC.SemanticAction
import LambdaPFC.SemanticTyping

/-!
Progress from normalized store-local evidence.

The proof observes only the outer runtime term.  Function canonical forms are
obtained by applying the path's suffix coercion to its singleton realization;
total lookup in intrinsically scoped stores supplies the binding needed for a
final location.
-/

namespace LambdaPFC

noncomputable section

/-- A typed path reducing to `x` makes `x` a possible inhabitant of the
advertised type. -/
noncomputable def TermEvidence.pathPossibleAt
    {n : Nat} {sigma : Store n} {p : Path n} {T : Ty n}
    {x : Fin n}
    (evidence : TermEvidence sigma (.path p) T)
    (reduction : Path.reduce p sigma x) :
    Store.Possible sigma x T :=
  evidence.pathView.suffix.actionPossible (.single reduction.toResolve)

/-- Every runtime term carrying semantic evidence is final or can take a
machine step, independently of its continuation's typing. -/
theorem TermEvidence.progress
    {n : Nat} {sigma : Store n} {term : Tm n} {T : Ty n}
    (evidence : TermEvidence sigma term T) (cont : Tm.Cont n) :
    State.Progress (State.mk sigma cont term) := by
  cases evidence with
  | @path p x T reduction suffix =>
      rcases Path.isVar_or_not p with isVariable | notVariable
      · cases isVariable with
        | var =>
            cases reduction
            obtain ⟨value, binding⟩ := Store.exists_binds sigma x
            exact State.Progress.path_var binding
      · exact State.Progress.path reduction notVariable
  | value valueEvidence =>
      exact State.Progress.value valueEvidence.isValue
  | app function argument suffix =>
      obtain ⟨functionLocation, functionReduction, functionSuffix⟩ :=
        function.pathView
      obtain ⟨argumentLocation, argumentReduction, argumentSuffix⟩ :=
        argument.pathView
      have possibleFunction :=
        function.pathPossibleAt functionReduction
      cases possibleFunction with
      | «fun» binding closure input output =>
          exact State.Progress.app functionReduction argumentReduction binding
  | «let» bound closure suffix =>
      exact State.Progress.let_term
  | typed term suffix =>
      exact State.Progress.ascribed

/-- The complete machine invariant entails progress. -/
theorem State.Evidence.progress
    {n : Nat} {state : State n} {T : LambdaPFC.Ty n}
    (evidence : State.Evidence state T) : State.Progress state := by
  cases evidence with
  | ok continuation term =>
      exact term.progress _

end

end LambdaPFC
