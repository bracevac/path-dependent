import SystemFSub.Syntax

/-!
# Heterogeneous substitution for System F<:

A substitution acts on the whole mixed signature at once: term variables map
to terms and type variables map to types.  Its generic lift works under either
sort of binder.
-/

namespace SystemFSub

/-- A simultaneous substitution for every variable in a mixed signature. -/
structure Subst (s1 s2 : Sig) where
  var : BVar s1 .var -> Tm s2
  tvar : BVar s1 .tvar -> Ty s2

/-- Lift a substitution through one fresh binder of either sort. -/
def Subst.lift {k : Kind} (sigma : Subst s1 s2) :
    Subst (s1 ,, k) (s2 ,, k) where
  var := fun x => by
    cases x with
    | here => exact .var .here
    | there x => exact (sigma.var x).rename Rename.succ
  tvar := fun X => by
    cases X with
    | here => exact .tvar .here
    | there X => exact (sigma.tvar X).rename Rename.succ

/-- Lift a substitution through a telescope of binders. -/
def Subst.liftMany (sigma : Subst s1 s2) (ks : Sig) :
    Subst (s1 ++ ks) (s2 ++ ks) :=
  match ks with
  | [] => sigma
  | k :: ks => (sigma.liftMany ks).lift (k := k)

/-- The identity substitution. -/
def Subst.id {s : Sig} : Subst s s where
  var := fun x => .var x
  tvar := fun X => .tvar X

/-- Substitute throughout a type. -/
def Ty.subst : Ty s1 -> Subst s1 s2 -> Ty s2
| .top, _ => .top
| .tvar X, sigma => sigma.tvar X
| .arrow S T, sigma => .arrow (S.subst sigma) (T.subst sigma)
| .all B T, sigma => .all (B.subst sigma) (T.subst sigma.lift)

/-- Substitute throughout a general term. -/
def Tm.subst : Tm s1 -> Subst s1 s2 -> Tm s2
| .var x, sigma => sigma.var x
| .abs S t, sigma => .abs (S.subst sigma) (t.subst sigma.lift)
| .app t u, sigma => .app (t.subst sigma) (u.subst sigma)
| .tabs B t, sigma => .tabs (B.subst sigma) (t.subst sigma.lift)
| .tapp t U, sigma => .tapp (t.subst sigma) (U.subst sigma)

/-- Regard a sort-preserving renaming as a substitution. -/
def Rename.asSubst (rho : Rename s1 s2) : Subst s1 s2 where
  var := fun x => .var (rho.var x)
  tvar := fun X => .tvar (rho.var X)

/-- Compose substitutions in diagrammatic order. -/
def Subst.comp (sigma : Subst s1 s2) (tau : Subst s2 s3) : Subst s1 s3 where
  var := fun x => (sigma.var x).subst tau
  tvar := fun X => (sigma.tvar X).subst tau

/-- Replace the newest term variable, leaving every older variable unchanged. -/
def Subst.openVar (u : Tm s) : Subst (s,x) s where
  var := fun
    | .here => u
    | .there x => .var x
  tvar := fun
    | .there X => .tvar X

/-- Replace the newest type variable, leaving every older variable unchanged. -/
def Subst.openTVar (U : Ty s) : Subst (s,X) s where
  var := fun
    | .there x => .var x
  tvar := fun
    | .here => U
    | .there X => .tvar X

/-- Instantiate the type variable bound by a universal type. -/
def Ty.open (T : Ty (s,X)) (U : Ty s) : Ty s :=
  T.subst (Subst.openTVar U)

/-- Open the term variable bound by an abstraction. -/
def Tm.open (t : Tm (s,x)) (u : Tm s) : Tm s :=
  t.subst (Subst.openVar u)

/-- Instantiate the type variable bound by a type abstraction. -/
def Tm.openTy (t : Tm (s,X)) (U : Ty s) : Tm s :=
  t.subst (Subst.openTVar U)

/-- Extensionality for heterogeneous substitutions. -/
theorem Subst.funext {sigma tau : Subst s1 s2}
    (hvar : forall x, sigma.var x = tau.var x)
    (htvar : forall X, sigma.tvar X = tau.tvar X) :
    sigma = tau := by
  cases sigma with
  | mk sigmaVar sigmaTVar =>
    cases tau with
    | mk tauVar tauTVar =>
      congr
      · funext x
        exact hvar x
      · funext X
        exact htvar X

end SystemFSub
