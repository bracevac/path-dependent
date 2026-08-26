import SystemFSub.Substitution

/-!
# Call-by-value dynamics for System F<:

This is the ordinary weak, left-to-right call-by-value semantics. Type
abstractions and term abstractions are values; evaluation never proceeds below
either binder. The two contractions use the heterogeneous opening operations
from `Substitution`, so both beta rules preserve the single mixed signature.
-/

namespace SystemFSub
namespace Tm

/-- One call-by-value evaluation step. -/
inductive Step : Tm s -> Tm s -> Prop where
| app_left :
    Step f f' ->
    Step (.app f a) (.app f' a)
| app_right :
    IsValue f ->
    Step a a' ->
    Step (.app f a) (.app f a')
| beta :
    IsValue v ->
    Step (.app (.abs S body) v) (body.open v)
| tapp_fun :
    Step f f' ->
    Step (.tapp f U) (.tapp f' U)
| type_beta :
    Step (.tapp (.tabs B body) U) (body.openTy U)

/-- Reflexive-transitive closure of source evaluation. -/
inductive Steps : Tm s -> Tm s -> Prop where
| refl : Steps t t
| tail : Step t u -> Steps u v -> Steps t v

theorem Steps.single (h : Step t u) : Steps t u :=
  .tail h .refl

theorem Steps.trans (h1 : Steps t u) (h2 : Steps u v) : Steps t v := by
  induction h1 with
  | refl => exact h2
  | tail h hrest ih => exact .tail h (ih h2)

/-! ## Values and terminal states -/

theorem IsValue.rename {v : Tm s} (hv : IsValue v) (rho : Rename s s') :
    IsValue (v.rename rho) := by
  cases hv with
  | abs => exact .abs
  | tabs => exact .tabs

theorem IsValue.subst {v : Tm s} (hv : IsValue v) (sigma : Subst s s') :
    IsValue (v.subst sigma) := by
  cases hv with
  | abs => exact .abs
  | tabs => exact .tabs

theorem IsValue.not_step {v t : Tm s} (hv : IsValue v) :
    Not (Step v t) := by
  intro h
  cases hv <;> cases h

theorem Step.not_value {t u : Tm s} (h : Step t u) :
    Not (IsValue t) := by
  intro hv
  exact hv.not_step h

/-- A term is normal when no source reduction applies. -/
def IsNormal (t : Tm s) : Prop :=
  forall u, Not (Step t u)

/-- A stuck term is a non-value normal form. -/
def IsStuck (t : Tm s) : Prop :=
  IsNormal t ∧ Not (IsValue t)

/-- The progress alternative used by the translation-based safety proof. -/
def HasProgress (t : Tm s) : Prop :=
  IsValue t ∨ Exists fun u => Step t u

/-- Closed source terms are represented by the empty mixed signature. -/
abbrev ClosedTerm : Type := Tm {}

/-- Closed progress is kept as a proposition for the later compiler theorem. -/
def ClosedProgress (t : ClosedTerm) : Prop := HasProgress t

/-- Evaluation of a closed term to a value. -/
def EvaluatesTo (t v : ClosedTerm) : Prop :=
  Steps t v ∧ IsValue v

/-- Going wrong means reaching a stuck closed term. -/
def GoesWrong (t : ClosedTerm) : Prop :=
  Exists fun u => Steps t u ∧ IsStuck u

/-! ## Definitional opening equations used by the beta rules -/

@[simp]
theorem open_var_here (u : Tm s) :
    (Tm.var (BVar.here : BVar (s,x) .var)).open u = u := rfl

@[simp]
theorem open_var_there (x : BVar s .var) (u : Tm s) :
    (Tm.var (BVar.there x : BVar (s,x) .var)).open u = .var x := rfl

@[simp]
theorem open_type_here (U : Ty s) :
    (Ty.tvar (BVar.here : BVar (s,X) .tvar)).open U = U := rfl

@[simp]
theorem open_type_there (X : BVar s .tvar) (U : Ty s) :
    (Ty.tvar (BVar.there X : BVar (s,X) .tvar)).open U = .tvar X := rfl

@[simp]
theorem openTy_var_there (x : BVar s .var) (U : Ty s) :
    (Tm.var (BVar.there x : BVar (s,X) .var)).openTy U = .var x := rfl

end Tm
end SystemFSub
