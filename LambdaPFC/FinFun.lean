/-!
Finite renamings for the intrinsically scoped `lambda_p` development.
-/

namespace LambdaPFC

/-- A renaming between scopes represented by finite ordinals. -/
abbrev FinFun (n m : Nat) : Type := Fin n -> Fin m

namespace FinFun

/-- The identity renaming. -/
def id : FinFun n n := fun i => i

/-- Composition of renamings, in diagrammatic order. -/
def comp (f : FinFun n m) (g : FinFun m k) : FinFun n k :=
  fun i => g (f i)

/-- Weakening by one freshly bound variable. -/
def weaken : FinFun n (n + 1) := Fin.succ

/-- Remove the newest binder, replacing it with the existing variable `x`. -/
def openAt (x : Fin n) : FinFun (n + 1) n :=
  Fin.cases x (fun i => i)

/-- Lift a renaming under one binder. -/
def ext (f : FinFun n m) : FinFun (n + 1) (m + 1) :=
  Fin.cases 0 (fun i => (f i).succ)

@[simp] theorem id_apply (i : Fin n) : id i = i := rfl

@[simp] theorem comp_apply (f : FinFun n m) (g : FinFun m k) (i : Fin n) :
    f.comp g i = g (f i) := rfl

@[simp] theorem weaken_apply (i : Fin n) : weaken i = i.succ := rfl

@[simp] theorem openAt_zero (x : Fin n) : openAt x 0 = x := rfl

@[simp] theorem openAt_succ (x : Fin n) (i : Fin n) : openAt x i.succ = i := rfl

@[simp] theorem ext_zero (f : FinFun n m) : f.ext 0 = 0 := rfl

@[simp] theorem ext_succ (f : FinFun n m) (i : Fin n) : f.ext i.succ = (f i).succ := rfl

@[simp] theorem ext_id : (id (n := n)).ext = id := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Weakening commutes with lifting a renaming. -/
theorem comp_weaken {f : FinFun n m} :
    f.comp weaken = weaken.comp f.ext := by
  funext i
  rfl

/-- Lifting preserves composition. -/
theorem ext_comp {f : FinFun n m} {g : FinFun m k} :
    f.ext.comp g.ext = (f.comp g).ext := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end FinFun

end LambdaPFC
