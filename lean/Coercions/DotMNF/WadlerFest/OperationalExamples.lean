import Coercions.DotMNF.WadlerFest.Examples
import Coercions.DotMNF.WadlerFest.Readback

/-!
# Closed retained-let executions

The first example projects a self-dependent field. The second evaluates a
function obtained through a nested let right-hand side. Reassociation and
inner alias reduction overlap; both orders reach the same retained answer.
The continuation refers to the outer function, so reassociation exercises
the shift of an ambient variable across the floated binder.
-/

namespace WadlerFest.Examples

open FCdot (Sig BVar)
open DotMNF (Ty)

/-- Projecting `a = self` returns the object variable and retains its binding. -/
theorem program_retained_step : Retained.Red .nil program
    (.let object (.path (.var .here))) :=
  .letValue (.proj (t := .path (.var .here)) rfl (.andRight .trm))

theorem program_retained_runs : Retained.Steps .nil program
    (.let object (.path (.var .here))) :=
  .single program_retained_step

theorem program_retained_answer :
    Retained.Answer (.let object (.path (.var .here))) :=
  .letValue .path

def identityValue : Value [] := .lam .top (.path (.var .here))

/-- `let f = id in let g = (let h = f in h) in g f`. -/
def nestedAlias : Tm [] :=
  .let (.val identityValue)
    (.let (.let (.path (.var .here)) (.path (.var .here)))
      (.app .here (.there .here)))

def nestedAlias_typed : HasTy .nil nestedAlias .top :=
  .let (.lam (T := .top) .var)
    (.let (.let .var .var) (.app (S := .top) (T := .top) .var (.sub .var .top)))

/-- After association, the occurrence of `f` crosses the new `h` binder. -/
def nestedAliasAssociated : Tm [] :=
  .let (.val identityValue)
    (.let (.path (.var .here))
      (.let (.path (.var .here)) (.app .here (.there (.there .here)))))

/-- `let f = id in let g = f in g f`. -/
def nestedAliasJoined : Tm [] :=
  .let (.val identityValue)
    (.let (.path (.var .here)) (.app .here (.there .here)))

def identityCall : Tm [] :=
  .let (.val identityValue) (.app .here .here)

def identityAnswer : Tm [] :=
  .let (.val identityValue) (.path (.var .here))

theorem nestedAlias_assoc :
    Retained.Red .nil nestedAlias nestedAliasAssociated :=
  .letValue .assoc

theorem nestedAlias_innerAlias :
    Retained.Red .nil nestedAlias nestedAliasJoined :=
  .letValue (.letRHS .alias)

theorem nestedAlias_assoc_alias :
    Retained.Red .nil nestedAliasAssociated nestedAliasJoined :=
  .letValue .alias

/-- The two enabled reductions have different intermediate terms. -/
theorem nestedAlias_branches_distinct : nestedAliasAssociated ≠ nestedAliasJoined := by
  intro h
  cases h

/-- Both overlapping orders join before the function is applied. -/
theorem nestedAlias_overlap :
    Retained.Red .nil nestedAlias nestedAliasAssociated ∧
    Retained.Red .nil nestedAlias nestedAliasJoined ∧
    Retained.Red .nil nestedAliasAssociated nestedAliasJoined :=
  ⟨nestedAlias_assoc, nestedAlias_innerAlias, nestedAlias_assoc_alias⟩

theorem nestedAliasJoined_runs :
    Retained.Steps .nil nestedAliasJoined identityAnswer := by
  have hAlias : Retained.Red .nil nestedAliasJoined identityCall := .letValue .alias
  have hApp : Retained.Red .nil identityCall identityAnswer :=
    .letValue (.app (t := .path (.var .here)) rfl)
  exact .tail (.single hAlias) hApp

/-- The reassociation order evaluates to the retained identity function. -/
theorem nestedAlias_runs : Retained.Steps .nil nestedAlias identityAnswer :=
  (Retained.Steps.tail (.single nestedAlias_assoc) nestedAlias_assoc_alias).trans nestedAliasJoined_runs

/-- Reducing the inner alias first reaches the same answer. -/
theorem nestedAlias_runs_innerAlias : Retained.Steps .nil nestedAlias identityAnswer :=
  (Retained.Steps.single nestedAlias_innerAlias).trans nestedAliasJoined_runs

theorem identityAnswer_isAnswer : Retained.Answer identityAnswer := .letValue .path

/-- The store machine reaches the same result after consuming its let frames. -/
theorem nestedAlias_machine_runs : Steps (⟨.nil, .nil, nestedAlias⟩ : State [])
    (⟨.cons .nil identityValue, .nil, .path (.var .here)⟩ : State ([],x)) := by
  have happ : Step (⟨.cons .nil identityValue, .nil, .app .here .here⟩ : State ([],x))
      (⟨.cons .nil identityValue, .nil, .path (.var .here)⟩ : State ([],x)) :=
    .app (t := .path (.var .here)) rfl
  exact .tail (.tail (.tail (.tail (.tail (.tail (.tail .refl
    .let) .alloc) .let) .let) .rename) .rename) happ

/-- Machine readback has exactly the retained-let execution's endpoint. -/
theorem nestedAlias_machine_readback :
    (⟨.cons .nil identityValue, .nil, .path (.var .here)⟩ : State ([],x)).readback =
      identityAnswer := rfl

end WadlerFest.Examples
