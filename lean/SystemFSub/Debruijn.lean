import Init.Data.List.Basic

/-!
# Multi-sorted de Bruijn scopes for System F<:

A signature records term- and type-variable binders in their actual nesting
order. A bound variable is indexed both by that signature and by its sort.
-/

namespace SystemFSub

inductive Kind : Type where
| var
| tvar
deriving DecidableEq, Repr

@[reducible]
def Sig : Type := List Kind

instance Sig.instEmptyCollection : EmptyCollection Sig where
  emptyCollection := []

def Sig.extendVar (s : Sig) : Sig := .var :: s
def Sig.extendTVar (s : Sig) : Sig := .tvar :: s
def Sig.extend (s : Sig) (k : Kind) : Sig := k :: s

postfix:80 ",x" => Sig.extendVar
postfix:80 ",X" => Sig.extendTVar
infixl:65 ",," => Sig.extend

def Sig.extendMany : Sig -> Sig -> Sig
| s, [] => s
| s, k :: ks => (s.extendMany ks).extend k

instance Sig.instAppend : Append Sig where
  append := Sig.extendMany

/-- A sort-correct de Bruijn variable in a mixed signature. -/
inductive BVar : Sig -> Kind -> Type where
| here : BVar (s ,, k) k
| there : BVar s k -> BVar (s ,, k0) k

/-- A simultaneous, sort-preserving renaming. -/
structure Rename (s1 s2 : Sig) where
  var : {k : Kind} -> BVar s1 k -> BVar s2 k

def Rename.id {s : Sig} : Rename s s where
  var := fun x => x

def Rename.comp {s1 s2 s3 : Sig}
    (rho : Rename s1 s2) (tau : Rename s2 s3) : Rename s1 s3 where
  var := fun x => tau.var (rho.var x)

def Rename.lift {k : Kind} (rho : Rename s1 s2) :
    Rename (s1 ,, k) (s2 ,, k) where
  var := fun
    | .here => .here
    | .there x => .there (rho.var x)

def Rename.liftMany (rho : Rename s1 s2) (ks : Sig) :
    Rename (s1 ++ ks) (s2 ++ ks) :=
  match ks with
  | [] => rho
  | k :: ks => (rho.liftMany ks).lift (k := k)

def Rename.succ {k : Kind} : Rename s (s ,, k) where
  var := fun x => .there x

theorem Rename.funext {rho tau : Rename s1 s2}
    (h : forall {k} (x : BVar s1 k), rho.var x = tau.var x) :
    rho = tau := by
  cases rho with
  | mk rho =>
    cases tau with
    | mk tau =>
      congr
      funext k x
      exact h x

@[simp]
theorem Rename.lift_id {k : Kind} :
    (Rename.id (s := s)).lift (k := k) = Rename.id := by
  apply Rename.funext
  intro _ x
  cases x <;> rfl

theorem Rename.lift_comp {k : Kind}
    {rho : Rename s1 s2} {tau : Rename s2 s3} :
    (rho.comp tau).lift (k := k) = rho.lift.comp tau.lift := by
  apply Rename.funext
  intro _ x
  cases x <;> rfl

theorem Rename.succ_lift_comm {k : Kind} {rho : Rename s1 s2} :
    (Rename.succ (s := s1) (k := k)).comp (rho.lift (k := k)) =
      rho.comp (Rename.succ (s := s2) (k := k)) := by
  apply Rename.funext
  intro _ x
  cases x <;> rfl

end SystemFSub
