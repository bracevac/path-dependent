import Coercions.DotMNF.WadlerFest.Machine

/-!
# Retained-let reduction

This relation presents the paper's retained-let evaluation rules with an
ambient store for the enclosing value bindings. A let-bound value remains
in the term; reducing its body extends the ambient store temporarily.
Application and projection consult those enclosing bindings. Reduction is
defined directly on terms, independently of the continuation machine.

The two congruence rules correspond to `let x = [] in u` and
`let x = v in []`. They impose no priority: reassociation may overlap with
reduction inside the right-hand side. Projection uses definition membership,
as in the published rule, rather than choosing one definition by lookup.
-/

namespace WadlerFest

open FCdot (Sig BVar Rename Label)

/-- A field definition occurs in an aggregate. Membership does not resolve
duplicate labels; well-formed definitions supply the separate disjointness
condition when comparison with deterministic lookup is needed. -/
inductive Defs.HasField : Defs s → Label → Tm s → Prop where
  | trm : Defs.HasField (.trm a t) a t
  | andLeft : Defs.HasField d₁ a t → Defs.HasField (.and d₁ d₂) a t
  | andRight : Defs.HasField d₂ a t → Defs.HasField (.and d₁ d₂) a t

namespace Retained

/-- A retained-let step under the surrounding value bindings `σ`. -/
inductive Red : Store s → Tm s → Tm s → Prop where
  | app : σ.lookup x = .lam S t → Red σ (.app x y) (t.substVar y)
  | proj : σ.lookup x = .obj T d → Defs.HasField d a t →
      Red σ (.proj x a) (t.substVar x)
  | alias : Red σ (.let (.path (.var y)) u) (u.substVar y)
  /-- `let x = (let y = t in u) in v` becomes
      `let y = t in let x = u in v`. The lifted weakening preserves `x`
      in `v` and shifts its old outer variables past the new binder `y`. -/
  | assoc : Red σ (.let (.let t u) v)
      (.let t (.let u (v.rename Rename.succ.lift)))
  | letRHS : Red σ t t' → Red σ (.let t u) (.let t' u)
  | letValue : Red (.cons σ v) t t' →
      Red σ (.let (.val v) t) (.let (.val v) t')

/-- Finite retained-let evaluation under a fixed ambient store. -/
inductive Steps (σ : Store s) : Tm s → Tm s → Prop where
  | refl : Steps σ t t
  | tail : Steps σ t u → Red σ u v → Steps σ t v

theorem Steps.single (h : Red σ t u) : Steps σ t u := .tail .refl h

theorem Steps.trans (h₁ : Steps σ t u) (h₂ : Steps σ u v) : Steps σ t v := by
  induction h₂ with
  | refl => exact h₁
  | tail _ h ih => exact .tail ih h

/-- Finite reductions close under the right-hand-side evaluation context. -/
theorem Steps.letRHS {σ : Store s} {t t' : Tm s}
    (h : Steps σ t t') (u : Tm (s,x)) :
    Steps σ (.let t u) (.let t' u) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (.letRHS h)

/-- Finite reductions close under a retained value binding. -/
theorem Steps.letValue {σ : Store s} {v : Value s} {t t' : Tm (s,x)}
    (h : Steps (.cons σ v) t t') :
    Steps σ (.let (.val v) t) (.let (.val v) t') := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (.letValue h)

/-- Answers are variables, values, or answers under retained value bindings. -/
inductive Answer : Tm s → Prop where
  | path : Answer (.path p)
  | val : Answer (.val v)
  | letValue : Answer t → Answer (.let (.val v) t)

def Stuck (σ : Store s) (t : Tm s) : Prop :=
  ¬ Answer t ∧ ¬ ∃ u, Red σ t u

end Retained
end WadlerFest
