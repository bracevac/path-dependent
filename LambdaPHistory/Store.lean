import LambdaPHistory.Typing

/-!
The intrinsically scoped store used by the original development.  Extending a
store weakens every older binding, so a lookup always returns a term scoped at
the current store length.
-/

namespace LambdaPHistory

/-- A store of values, indexed by its scope size.  `empty` is polymorphic in
the index, as in the historical definition. -/
inductive Store : Nat -> Type where
| empty : Store n
| val : Store n -> (t : Tm n) -> t.IsValue -> Store (n + 1)

/-- Lookup in an intrinsically scoped store. -/
inductive Store.Binds : Store n -> Fin n -> Tm n -> Prop where
| here : Binds (Store.val σ v vv) 0 v.weaken
| there :
    Binds σ x v ->
    Binds (Store.val σ u uv) (Fin.succ x) v.weaken

/-- Executable lookup corresponding to `Store.Binds`. -/
def Store.lookup? : (σ : Store n) -> Fin n -> Option (Tm n)
| .empty, _ => none
| .val σ v _, x =>
    Fin.cases (some v.weaken)
      (fun y => (Store.lookup? σ y).map Tm.weaken) x

/-- Store lookup preserves the invariant that stores contain only values. -/
theorem Store.Binds.isValue (h : Store.Binds σ x v) : v.IsValue := by
  induction h with
  | here =>
      apply Tm.IsValue.weaken
      assumption
  | there _ ih => exact ih.weaken

theorem Store.Binds.lookup_eq (h : Store.Binds σ x v) :
    Store.lookup? σ x = some v := by
  induction h with
  | here => rfl
  | there _ ih =>
      simpa [Store.lookup?] using congrArg (Option.map Tm.weaken) ih

/-- A location has at most one stored term. -/
theorem Store.Binds.unique
    (h₁ : Store.Binds σ x v₁) (h₂ : Store.Binds σ x v₂) : v₁ = v₂ := by
  apply Option.some.inj
  exact h₁.lookup_eq.symm.trans h₂.lookup_eq

/-- A store is typed pointwise by a context with the same scope. -/
inductive Store.Ty : Ctx n -> Store n -> Prop where
| empty : Ty Ctx.nil Store.empty
| val :
    Ty Γ σ ->
    Tm.Ty Γ t T ->
    Ty (Γ.snoc T) (Store.val σ t vt)

end LambdaPHistory
