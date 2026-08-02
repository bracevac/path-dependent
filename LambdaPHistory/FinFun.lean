import Init.Data.Fin.Lemmas

/-!
Finite renamings for the intrinsically scoped presentation of the original
`lambda_p` development.  This is the small, core-only replacement for the
historical `PathDependent.FinFun.Basic` module.
-/

namespace LambdaPHistory

/-- A renaming between scopes represented by finite ordinals. -/
abbrev FinFun (n m : Nat) : Type := Fin n -> Fin m

namespace FinFun

/-- The identity renaming. -/
def id : FinFun n n := fun i => i

/-- Weakening by one freshly bound variable. -/
def weaken : FinFun n (n + 1) := Fin.succ

/-- Remove the newest binder, replacing it with the existing variable `x`. -/
def openAt (x : Fin n) : FinFun (n + 1) n :=
  Fin.cases x (fun i => i)

/-- Lift a renaming under one binder. -/
def ext (f : FinFun n m) : FinFun (n + 1) (m + 1) :=
  Fin.cases 0 (fun i => (f i).succ)

@[simp] theorem id_apply (i : Fin n) : id i = i := rfl

@[simp] theorem weaken_apply (i : Fin n) : weaken i = i.succ := rfl

@[simp] theorem openAt_zero (x : Fin n) : openAt x 0 = x := rfl

@[simp] theorem openAt_succ (x : Fin n) (i : Fin n) : openAt x i.succ = i := rfl

@[simp] theorem ext_zero (f : FinFun n m) : f.ext 0 = 0 := rfl

@[simp] theorem ext_succ (f : FinFun n m) (i : Fin n) : f.ext i.succ = (f i).succ := rfl

theorem funext {f g : FinFun n m} (h : forall i, f i = g i) : f = g :=
  _root_.funext h

theorem weaken_injective : Function.Injective (weaken (n := n)) := by
  intro i j h
  exact Fin.succ_inj.mp h

@[simp] theorem ext_id : (id (n := n)).ext = id := by
  apply funext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Weakening commutes with lifting a renaming. -/
theorem comp_weaken {f : FinFun n m} :
    weaken ∘ f = f.ext ∘ weaken := by
  apply funext
  intro i
  rfl

/-- Lifting preserves composition. -/
theorem ext_comp_ext {f : FinFun n m} {g : FinFun m k} :
    g.ext ∘ f.ext = ext (g ∘ f) := by
  apply funext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Opening is natural with respect to renaming. -/
theorem openAt_comp {f : FinFun n m} {x : Fin n} :
    f ∘ openAt x = openAt (f x) ∘ f.ext := by
  apply funext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Opening after weakening is the identity. -/
@[simp] theorem openAt_weaken (x : Fin n) :
    openAt x ∘ weaken = id := by
  apply funext
  intro i
  rfl

end FinFun

end LambdaPHistory
