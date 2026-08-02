import LambdaPFC.Syntax

/-!
Finite valuations for semantic interpretations.  A valuation maps the free
variables of a source scope to locations in a target scope.  Extending a
valuation beneath a binder maps the newest source variable to an existing
target location.
-/

namespace LambdaPFC

abbrev Valuation (n m : Nat) : Type := FinFun n m

namespace Valuation

def id : Valuation n n := FinFun.id

/-- Diagrammatic composition: first `rho`, then `theta`. -/
def comp (rho : Valuation n m) (theta : Valuation m l) : Valuation n l :=
  FinFun.comp rho theta

/-- Extend a valuation by mapping the newest source variable to `y`. -/
def snoc (rho : Valuation n m) (y : Fin m) : Valuation (n + 1) m :=
  Fin.cases y rho

/-- Synonym used when the operation is viewed as binder extension. -/
abbrev extend (rho : Valuation n m) (y : Fin m) : Valuation (n + 1) m :=
  rho.snoc y

/-- Weaken every target location into a freshly extended target scope. -/
def weaken (rho : Valuation n m) : Valuation n (m + 1) :=
  rho.comp FinFun.weaken

@[simp] theorem id_apply (x : Fin n) : id x = x := rfl

@[simp] theorem comp_apply
    (rho : Valuation n m) (theta : Valuation m l) (x : Fin n) :
    rho.comp theta x = theta (rho x) := rfl

@[simp] theorem snoc_zero (rho : Valuation n m) (y : Fin m) :
    rho.snoc y 0 = y := rfl

@[simp] theorem snoc_succ
    (rho : Valuation n m) (y : Fin m) (x : Fin n) :
    rho.snoc y x.succ = rho x := rfl

@[simp] theorem extend_zero (rho : Valuation n m) (y : Fin m) :
    rho.extend y 0 = y := rfl

@[simp] theorem extend_succ
    (rho : Valuation n m) (y : Fin m) (x : Fin n) :
    rho.extend y x.succ = rho x := rfl

@[simp] theorem id_comp (rho : Valuation n m) : id.comp rho = rho := by
  exact FinFun.id_comp rho

@[simp] theorem comp_id (rho : Valuation n m) : rho.comp id = rho := by
  exact FinFun.comp_id rho

theorem comp_assoc
    (rho : Valuation n m) (theta : Valuation m l)
    (upsilon : Valuation l r) :
    (rho.comp theta).comp upsilon = rho.comp (theta.comp upsilon) := by
  exact FinFun.comp_assoc rho theta upsilon

/-- Composition maps both the old entries and the distinguished new entry. -/
theorem snoc_comp
    (rho : Valuation n m) (y : Fin m) (theta : Valuation m l) :
    (rho.snoc y).comp theta = (rho.comp theta).snoc (theta y) := by
  apply FinFun.funext
  intro x
  refine Fin.cases ?_ (fun i => ?_) x <;> rfl

/-- Restricting an extended valuation to the old source scope recovers the
original valuation. -/
@[simp] theorem weaken_comp_snoc
    (rho : Valuation n m) (y : Fin m) :
    FinFun.weaken.comp (rho.snoc y) = rho := by
  apply FinFun.funext
  intro x
  rfl

/-- Extending a target-weakened valuation by the fresh target variable is
ordinary binder lifting. -/
theorem weaken_snoc_zero (rho : Valuation n m) :
    rho.weaken.snoc 0 = rho.ext := by
  apply FinFun.funext
  intro x
  refine Fin.cases ?_ (fun i => ?_) x <;> rfl

/-- Lift to a fresh target binder and immediately instantiate that binder by
`y`.  This is the central equation used when a semantic closure receives its
runtime argument. -/
theorem ext_comp_openAt (rho : Valuation n m) (y : Fin m) :
    rho.ext.comp (FinFun.openAt y) = rho.snoc y := by
  apply FinFun.funext
  intro x
  refine Fin.cases ?_ (fun i => ?_) x <;> rfl

/-- Opening after extension agrees pointwise with direct binder extension. -/
@[simp] theorem ext_openAt_apply
    (rho : Valuation n m) (y : Fin m) (x : Fin (n + 1)) :
    FinFun.openAt y (rho.ext x) = rho.snoc y x := by
  have equation := congrFun (rho.ext_comp_openAt y) x
  exact equation

end Valuation

/-! ## Renaming through semantic binder extension -/

theorem Path.rename_ext_openAt
    (p : Path (n + 1)) (rho : Valuation n m) (y : Fin m) :
    (p.rename rho.ext).rename (FinFun.openAt y) =
      p.rename (rho.snoc y) := by
  rw [Path.rename_rename, Valuation.ext_comp_openAt]

theorem Ty.rename_ext_openAt
    (T : Ty (n + 1)) (rho : Valuation n m) (y : Fin m) :
    (T.rename rho.ext).rename (FinFun.openAt y) =
      T.rename (rho.snoc y) := by
  rw [Ty.rename_rename, Valuation.ext_comp_openAt]

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

theorem Def.rename_ext_openAt
    (d : Def (n + 1) k) (rho : Valuation n m) (y : Fin m) :
    (d.rename rho.ext).rename (FinFun.openAt y) =
      d.rename (rho.snoc y) := by
  rw [Def.rename_rename, Valuation.ext_comp_openAt]

/-! ## Weakening under an extended valuation -/

theorem Path.weaken_rename_snoc
    (p : Path n) (rho : Valuation n m) (y : Fin m) :
    p.weaken.rename (rho.snoc y) = p.rename rho := by
  rw [Path.weaken, Path.rename_rename, Valuation.weaken_comp_snoc]

theorem Ty.weaken_rename_snoc
    (T : Ty n) (rho : Valuation n m) (y : Fin m) :
    T.weaken.rename (rho.snoc y) = T.rename rho := by
  rw [Ty.weaken, Ty.rename_rename, Valuation.weaken_comp_snoc]

theorem Tau.weaken_rename_snoc
    (d : Tau n k) (rho : Valuation n m) (y : Fin m) :
    d.weaken.rename (rho.snoc y) = d.rename rho := by
  rw [Tau.weaken, Tau.rename_rename, Valuation.weaken_comp_snoc]

theorem Tm.weaken_rename_snoc
    (t : Tm n) (rho : Valuation n m) (y : Fin m) :
    t.weaken.rename (rho.snoc y) = t.rename rho := by
  rw [Tm.weaken, Tm.rename_rename, Valuation.weaken_comp_snoc]

theorem Def.weaken_rename_snoc
    (d : Def n k) (rho : Valuation n m) (y : Fin m) :
    d.weaken.rename (rho.snoc y) = d.rename rho := by
  rw [Def.weaken, Def.rename_rename, Valuation.weaken_comp_snoc]

end LambdaPFC
