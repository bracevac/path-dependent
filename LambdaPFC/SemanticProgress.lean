import LambdaPFC.SemanticAction
import LambdaPFC.SemanticTyping

/-!
Progress from normalized store-local evidence.

The proof observes only the outer runtime term.  Function canonical forms are
obtained by applying the path's suffix coercion to its singleton realization.
Intrinsic store scope ensures that a runtime variable denotes an allocated
location.
-/

namespace LambdaPFC

noncomputable section

/-- A typed path resolving to `x` makes `x` a possible inhabitant of the
advertised type. -/
noncomputable def TermEvidence.pathPossibleAt
    {n : Nat} {sigma : Store n} {p : Path n} {T : Ty n}
    {x : Fin n}
    (evidence : TermEvidence sigma (.path p) T)
    (resolution : Path.Resolve p sigma (.loc x)) :
    Store.Possible sigma x T :=
  evidence.pathView.suffix.actionPossible (.single resolution)

/-- Every runtime term carrying semantic evidence is final or can take a
machine step, independently of its continuation's typing. -/
theorem TermEvidence.progress
    {n : Nat} {sigma : Store n} {term : Tm n} {T : Ty n}
    (evidence : TermEvidence sigma term T) (cont : Tm.Cont n) :
    State.Progress (State.mk sigma cont term) := by
  cases evidence with
  | @path p x T resolution suffix =>
      cases p with
      | var =>
          cases resolution
          exact State.Progress.path_var
      | fst _ | sel _ _ =>
          exact State.Progress.path resolution nofun
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

/-- The complete machine invariant entails progress. -/
theorem State.Evidence.progress
    {n : Nat} {state : State n} {T : LambdaPFC.Ty n}
    (evidence : State.Evidence state T) : State.Progress state := by
  cases evidence with
  | ok continuation term =>
      exact term.progress _

end

end LambdaPFC
