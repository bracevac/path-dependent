import LambdaPFC.Syntax

/-! Intrinsically scoped typing contexts for the calculus. -/

namespace LambdaPFC

/-- A context stores each type in the scope preceding its binder. -/
inductive Ctx : Nat -> Type where
| nil : Ctx 0
| snoc : Ctx n -> Ty n -> Ctx (n + 1)

namespace Ctx

/-- Lookup in a context, with the stored type weakened to the full scope. -/
inductive Binds : Ctx n -> Fin n -> Ty n -> Prop where
| here : Binds (.snoc Γ T) 0 T.weaken
| there : Binds Γ x T -> Binds (.snoc Γ S) x.succ T.weaken

/-- The type stored at a context index, weakened through every newer binder. -/
def lookup : (Γ : Ctx n) -> Fin n -> Ty n
| .nil, x => Fin.elim0 x
| .snoc Γ T, x =>
    Fin.cases T.weaken (fun i => (lookup Γ i).weaken) x

/-- Functional lookup satisfies the inductive lookup judgment. -/
theorem lookup_binds (Γ : Ctx n) (x : Fin n) : Binds Γ x (Γ.lookup x) := by
  induction Γ with
  | nil => exact Fin.elim0 x
  | snoc Γ T ih =>
      refine Fin.cases ?_ (fun i => ?_) x
      · exact .here
      · exact .there (ih i)

/-- An inductive lookup derivation computes the functional lookup. -/
theorem Binds.eq_lookup (h : Binds Γ x T) : T = Γ.lookup x := by
  induction h with
  | here => rfl
  | there _ ih => exact congrArg Ty.weaken ih

theorem Binds.lookup_eq (h : Binds Γ x T) : Γ.lookup x = T :=
  h.eq_lookup.symm

/-- Context lookup is functional. -/
theorem Binds.unique
    (h1 : Binds Γ x T1) (h2 : Binds Γ x T2) : T1 = T2 :=
  h1.eq_lookup.trans h2.eq_lookup.symm

/-- Every intrinsically scoped context index has a binding. -/
theorem Binds.exists (Γ : Ctx n) (x : Fin n) :
    exists T, Binds Γ x T :=
  ⟨Γ.lookup x, Γ.lookup_binds x⟩

end Ctx

end LambdaPFC
