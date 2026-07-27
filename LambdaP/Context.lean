import LambdaP.Substitution

/-!
Typing contexts for bound variables and store typings for heap locations.

Bound variables are typed by an intrinsically scoped context `Ctx s`
(capybara's `Ctx`/`LookupVar`, single-kinded). Free variables are heap
locations, typed by a store typing `Sto`: a list of *closed* types (scope 0;
they may still mention other locations via `Var.free`). Because locations
are stable names, growing the store never requires renaming anything —
the payoff of the capybara-style `Var := bound | free` split.
-/

namespace LambdaP

/-- A typing context for bound variables. -/
inductive Ctx : Sig -> Type where
| empty : Ctx 0
| push : Ctx s -> Ty s -> Ctx (s+1)

/-- Context lookup, weakening the type into the full scope on the way out. -/
inductive Ctx.LookupVar : Ctx s -> BVar s -> Ty s -> Prop where
| here :
  Ctx.LookupVar (.push Γ T) .here T.weaken
| there :
  Ctx.LookupVar Γ x T ->
  Ctx.LookupVar (.push Γ S) (.there x) T.weaken

/-! ### Closed types and their embedding into any scope -/

/-- The vacuous renaming out of the empty scope. -/
def Rename.fromZero : Rename 0 s where
  var := fun x => nomatch x

/-- Any two renamings out of the empty scope are equal. -/
theorem Rename.fromZero_unique (f : Rename 0 s) : f = Rename.fromZero := by
  apply Rename.funext
  intro x
  exact nomatch x

/-- Any two substitutions out of the empty scope are equal. -/
theorem Subst.fromZero_unique (σ1 σ2 : Subst 0 s) : σ1 = σ2 := by
  apply Subst.funext
  intro x
  exact nomatch x

/-- Embeds a closed type into an arbitrary scope. -/
def Ty.fromClosed (T : Ty 0) : Ty s := T.rename Rename.fromZero

/-- Embedded closed types are invariant under renaming. -/
theorem Ty.fromClosed_rename {T : Ty 0} {f : Rename s1 s2} :
    (T.fromClosed : Ty s1).rename f = T.fromClosed := by
  simp [Ty.fromClosed, Ty.rename_comp]
  congr 1
  apply Rename.fromZero_unique

/-- Embedded closed types are invariant under substitution. -/
theorem Ty.fromClosed_subst {T : Ty 0} {σ : Subst s1 s2} :
    (T.fromClosed : Ty s1).subst σ = T.fromClosed := by
  have h : Rename.fromZero.compSubst σ = (Rename.fromZero (s := s2)).asSubst :=
    Subst.fromZero_unique _ _
  simp [Ty.fromClosed, Ty.rename_subst_comm, h, Ty.subst_asSubst]

/-- Embedded closed types are invariant under weakening. -/
theorem Ty.fromClosed_weaken {T : Ty 0} :
    (T.fromClosed : Ty s).weaken = T.fromClosed := by
  simp [Ty.weaken, Ty.fromClosed_rename]

/-- Embedded closed types are invariant under opening. -/
theorem Ty.fromClosed_open {T : Ty 0} {p : Path s} :
    (T.fromClosed : Ty (s+1)).open p = T.fromClosed := by
  simp [Ty.open, Ty.fromClosed_subst]

/-! ### Store typings -/

/-- A store typing: the `ℓ`-th entry is the (closed) type of heap location `ℓ`. -/
abbrev Sto : Type := List (Ty 0)

/-- Store-typing lookup. -/
def Sto.Lookup (Θ : Sto) (ℓ : Nat) (T : Ty 0) : Prop := Θ[ℓ]? = some T

/-- A store typing extends another if it agrees on all existing entries. -/
def Sto.Extends (Θ' Θ : Sto) : Prop :=
  ∀ {ℓ T}, Sto.Lookup Θ ℓ T -> Sto.Lookup Θ' ℓ T

theorem Sto.Extends.refl {Θ : Sto} : Θ.Extends Θ := fun h => h

theorem Sto.Extends.trans {Θ1 Θ2 Θ3 : Sto} (h1 : Θ3.Extends Θ2) (h2 : Θ2.Extends Θ1) :
    Θ3.Extends Θ1 := fun h => h1 (h2 h)

/-- Appending new entries extends a store typing. -/
theorem Sto.extends_append {Θ Θ' : Sto} : (Θ ++ Θ').Extends Θ := by
  intro ℓ T h
  unfold Sto.Lookup at *
  rw [List.getElem?_append_left]
  · exact h
  · exact (List.getElem?_eq_some_iff.mp h).1

/-- Lookup in a snoc-extended store typing hits the new entry at the old length. -/
theorem Sto.lookup_snoc {Θ : Sto} {T : Ty 0} : Sto.Lookup (Θ ++ [T]) Θ.length T := by
  unfold Sto.Lookup
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

end LambdaP
