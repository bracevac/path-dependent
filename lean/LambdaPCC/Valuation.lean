import LambdaPCC.Syntax

/-!
Finite valuations for semantic interpretations.  A valuation maps the free
variables of a source scope to locations in a target scope.  Extending a
valuation beneath a binder maps the newest source variable to an existing
target location.
-/

namespace LambdaPCC

abbrev Valuation (n m : Nat) : Type := FinFun n m

namespace Valuation

/-- Extend a valuation by mapping the newest source variable to `y`. -/
def snoc (rho : Valuation n m) (y : Fin m) : Valuation (n + 1) m :=
  Fin.cases y rho

/-- Weaken every target location into a freshly extended target scope. -/
def weaken (rho : Valuation n m) : Valuation n (m + 1) :=
  rho.comp FinFun.weaken

@[simp] theorem snoc_zero (rho : Valuation n m) (y : Fin m) :
    rho.snoc y 0 = y := rfl

@[simp] theorem snoc_succ
    (rho : Valuation n m) (y : Fin m) (x : Fin n) :
    rho.snoc y x.succ = rho x := rfl

/-- Lift to a fresh target binder and immediately instantiate that binder by
`y`.  This is the central equation used when a semantic closure receives its
runtime argument. -/
theorem ext_comp_openAt (rho : Valuation n m) (y : Fin m) :
    rho.ext.comp (FinFun.openAt y) = rho.snoc y := by
  funext x
  refine Fin.cases ?_ (fun i => ?_) x <;> rfl

end Valuation

/-! ## Renaming through semantic binder extension -/

theorem CaptureSet.rename_ext_openAt
    (C : CaptureSet (n + 1)) (rho : Valuation n m) (y : Fin m) :
    (C.rename rho.ext).rename (FinFun.openAt y) =
      C.rename (rho.snoc y) := by
  rw [CaptureSet.rename_rename, Valuation.ext_comp_openAt]

theorem Ty.rename_ext_openAt
    (T : Ty (n + 1)) (rho : Valuation n m) (y : Fin m) :
    (T.rename rho.ext).rename (FinFun.openAt y) =
      T.rename (rho.snoc y) := by
  rw [Ty.rename_rename, Valuation.ext_comp_openAt]

theorem Shape.rename_ext_openAt
    (S : Shape (n + 1)) (rho : Valuation n m) (y : Fin m) :
    (S.rename rho.ext).rename (FinFun.openAt y) =
      S.rename (rho.snoc y) := by
  rw [Shape.rename_rename, Valuation.ext_comp_openAt]

theorem Tau.rename_ext_openAt
    (d : Tau (n + 1) k) (rho : Valuation n m) (y : Fin m) :
    (d.rename rho.ext).rename (FinFun.openAt y) =
      d.rename (rho.snoc y) := by
  rw [Tau.rename_rename, Valuation.ext_comp_openAt]

theorem Tm.rename_ext_openAt
    (t : Tm (n + 1)) (rho : Valuation n m) (y : Fin m) :
    (t.rename rho.ext).rename (FinFun.openAt y) =
      t.rename (rho.snoc y) := by
  rw [Tm.rename_rename, Valuation.ext_comp_openAt]

end LambdaPCC
