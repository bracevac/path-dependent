/-!
De Bruijn indices and variable renamings for λ_p.

Ported from the CoreCapybara mechanization (`Semantic/CoreCapybara/Debruijn.lean`),
specialized to a single variable kind: λ_p only has term variables, so
capybara's `Sig := List Kind` degenerates to a count of bound variables.
-/

namespace LambdaP

/-- A scope ("signature"): the number of bound variables in context. -/
abbrev Sig : Type := Nat

/-- A bound variable, de Bruijn indexed. -/
inductive BVar : Sig -> Type where
| here : BVar (s+1)
| there : BVar s -> BVar (s+1)

/-- A variable: either bound (de Bruijn indexed) or free (a heap location).
Renamings and substitutions never touch free variables, which is what makes
heap allocation stable (no weakening of configurations at runtime). -/
inductive Var : Sig -> Type where
| bound : BVar s -> Var s
| free : Nat -> Var s

/-- A `Rename` maps bound variables in one scope to another. -/
structure Rename (s1 s2 : Sig) where
  var : BVar s1 -> BVar s2

/-- The identity `Rename`. -/
def Rename.id {s : Sig} : Rename s s where
  var := fun x => x

/-- Composition of two renamings (diagrammatic order). -/
def Rename.comp (f1 : Rename s1 s2) (f2 : Rename s2 s3) : Rename s1 s3 where
  var := fun x => f2.var (f1.var x)

/-- Lifts a renaming under a binder. The newly bound variable maps to itself. -/
def Rename.lift (f : Rename s1 s2) : Rename (s1+1) (s2+1) where
  var := fun
    | .here => .here
    | .there x => .there (f.var x)

/-- The "successor" renaming that weakens all variables by one level. -/
def Rename.succ : Rename s (s+1) where
  var := fun x => x.there

/-- Function extensionality for renamings. -/
theorem Rename.funext {f1 f2 : Rename s1 s2}
    (hvar : ∀ (x : BVar s1), f1.var x = f2.var x) : f1 = f2 := by
  cases f1; cases f2
  congr 1
  funext x
  exact hvar x

/-- The successor renaming commutes with lifting. -/
theorem Rename.succ_lift_comm {f : Rename s1 s2} :
    Rename.succ.comp f.lift = f.comp Rename.succ := by
  apply Rename.funext
  intro x
  rfl

/-- Lifting the identity renaming yields the identity. -/
theorem Rename.lift_id :
    (Rename.id (s := s)).lift = Rename.id := by
  apply Rename.funext
  intro x
  cases x <;> rfl

/-- Lifting distributes over composition of renamings. -/
theorem Rename.lift_comp {f1 : Rename s1 s2} {f2 : Rename s2 s3} :
    (f1.comp f2).lift = f1.lift.comp f2.lift := by
  apply Rename.funext
  intro x
  cases x <;> rfl

/-- Applies a renaming to a variable. Free variables remain unchanged. -/
def Var.rename : Var s1 -> Rename s1 s2 -> Var s2
| .bound x, f => .bound (f.var x)
| .free n, _ => .free n

/-- Renaming by the identity renaming leaves a variable unchanged. -/
theorem Var.rename_id {x : Var s} : x.rename Rename.id = x := by
  cases x <;> rfl

/-- Renaming distributes over composition of renamings. -/
theorem Var.rename_comp {x : Var s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (x.rename f).rename g = x.rename (f.comp g) := by
  cases x <;> rfl

/-- Weakening commutes with renaming under a binder. -/
theorem Var.weaken_rename_comm {x : Var s1} {f : Rename s1 s2} :
    (x.rename Rename.succ).rename f.lift = (x.rename f).rename Rename.succ := by
  simp [Var.rename_comp, Rename.succ_lift_comm]

end LambdaP
