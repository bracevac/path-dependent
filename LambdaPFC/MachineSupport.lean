import LambdaPFC.Runtime

/-!
Small totality and case-analysis facts used by the CK-machine proof.
-/

namespace LambdaPFC

/-- Every location in a store has a binding. -/
theorem Store.binds_total :
    (sigma : Store n) -> (x : Fin n) ->
      Nonempty {v : Tm n // Store.Binds sigma x v}
  | .empty, x => Fin.elim0 x
  | .val sigma v _, x =>
      Fin.cases
        (Nonempty.intro ⟨v.weaken, .here⟩)
        (fun y =>
          match Store.binds_total sigma y with
          | ⟨⟨u, hu⟩⟩ => Nonempty.intro ⟨u.weaken, .there hu⟩)
        x

/-- Propositional form of total store lookup. -/
theorem Store.exists_binds (sigma : Store n) (x : Fin n) :
    exists v, Store.Binds sigma x v := by
  rcases sigma.binds_total x with ⟨⟨v, hv⟩⟩
  exact ⟨v, hv⟩

/-- A path is either a variable or is eligible for the non-variable path step. -/
theorem Path.isVar_or_not (p : Path n) : Or p.IsVar (Not p.IsVar) := by
  cases p with
  | var => exact Or.inl Path.IsVar.var
  | fst =>
      exact Or.inr (fun h => by cases h)
  | sel =>
      exact Or.inr (fun h => by cases h)

end LambdaPFC
