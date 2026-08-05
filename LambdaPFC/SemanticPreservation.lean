import LambdaPFC.SemanticProgress
import LambdaPFC.SemanticFundamental
import LambdaPFC.SemanticTypingWeakening
import LambdaPFC.SemanticAllocation

/-!
Preservation for the heterogeneous CK transition relation.

Allocation extends the store scope, so the final result type is weakened at
that transition.  `Ty.Extends` records zero or more such extensions.  Since
`State.Step` is proposition-valued, preservation returns the resulting
type-valued state evidence under `Nonempty`.
-/

namespace LambdaPFC

noncomputable section

/-! ## Type extension under allocation -/

/-- A type transported through zero or more fresh store allocations. -/
inductive Ty.Extends : {n m : Nat} -> Ty n -> Ty m -> Prop where
| refl : Ty.Extends T T
| alloc : Ty.Extends S T -> Ty.Extends S T.weaken

/-- Allocation extensions compose. -/
theorem Ty.Extends.trans
    (first : Ty.Extends S T) (second : Ty.Extends T U) :
    Ty.Extends S U := by
  induction second with
  | refl => exact first
  | alloc _ ih => exact .alloc (ih first)

/-! ## Transition-specific evidence -/

/-- Beta reduction preserves the application result type.  The codomain is
first instantiated at the selected argument location and then transported
back to the source argument path by runtime path equality. -/
private noncomputable def TermEvidence.beta
    {n : Nat} {sigma : Store n} {p q : Path n}
    {S T : LambdaPFC.Ty n} {U : LambdaPFC.Ty (n + 1)}
    {f y : Fin n} {A : LambdaPFC.Ty n} {body : Tm (n + 1)}
    (function : TermEvidence sigma (.path p) (.Fun S U))
    (argument : TermEvidence sigma (.path q) S)
    (suffix : Coercion sigma (.ty (U.open q)) (.ty T))
    (functionResolution : Path.Resolve p sigma (.loc f))
    (argumentResolution : Path.Resolve q sigma (.loc y))
    (binding : Store.Binds sigma f (.abs A body)) :
    TermEvidence sigma (body.open y) T := by
  have argumentPossible := argument.pathPossibleAt argumentResolution
  cases function.pathPossibleAt functionResolution with
  | «fun» stored closure input output =>
      cases Store.Binds.unique stored binding
      have relocate :
          Coercion sigma (.ty (U.open (.var y))) (.ty (U.open q)) :=
        .runtime (.replace (.ty U) (.symm (.ofResolve argumentResolution .var)))
      exact ((closure.apply (input.actionPossible argumentPossible)).cast
        (output.instantiate argumentPossible)).cast (relocate.trans suffix)

/-! ## One-step preservation -/

/-- Every CK transition preserves the final type, allowing one weakening at
an allocation transition. -/
theorem State.Evidence.preservation
    {n m : Nat} {source : State n} {target : State m}
    {T : LambdaPFC.Ty n}
    (evidence : State.Evidence source T)
    (step : State.Step source target) :
    exists U : LambdaPFC.Ty m,
      Ty.Extends T U /\ Nonempty (State.Evidence target U) := by
  obtain ⟨continuation, term⟩ := evidence
  cases step with
  | app functionResolution argumentResolution binding =>
      obtain ⟨argumentType, codomain, function, argument, suffix⟩ :=
        term.appView
      have reduced := function.beta argument suffix
        functionResolution argumentResolution binding
      exact ⟨_, .refl, ⟨.ok continuation reduced⟩⟩
  | path resolution notVariable =>
      obtain ⟨location, storedResolution, suffix⟩ := term.pathView
      have back := Coercion.alias resolution .var
      exact ⟨_, .refl, ⟨.ok continuation (.path .var (back.trans suffix))⟩⟩
  | let_push =>
      obtain ⟨boundType, resultType, bound, closure, suffix⟩ :=
        term.letView
      exact ⟨_, .refl,
        ⟨.ok (.cons continuation closure suffix) bound⟩⟩
  | «return» =>
      cases continuation with
      | cons tail closure suffix =>
          have argument := term.pathPossibleAt .var
          have resumed := closure.apply argument
          have resumed' := by
            simpa only [Ty.weaken_open] using resumed
          exact ⟨_, .refl,
            ⟨.ok tail (resumed'.cast suffix)⟩⟩
  | allocate value =>
      cases continuation with
      | cons tail closure suffix =>
          rcases term.nonemptyValueView value with
            ⟨valueEvidence⟩
          have bodyEvidence := closure.allocate valueEvidence value
          have resumed := bodyEvidence.cast (suffix.weaken _ value)
          exact ⟨_, .alloc .refl,
            ⟨.ok (tail.weaken _ value) resumed⟩⟩

end

end LambdaPFC
