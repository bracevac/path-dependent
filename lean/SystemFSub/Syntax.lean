import SystemFSub.Debruijn

/-!
# Intrinsically scoped System F<: syntax

Types and ordinary (non-MNF) terms share one mixed signature. Type syntax can
only refer to `.tvar` entries, while terms use `.var` entries as well.
-/

namespace SystemFSub

/-- Conventional System F<: types. `all B T` binds only a type variable in `T`. -/
inductive Ty : Sig -> Type where
| top : Ty s
| tvar : BVar s .tvar -> Ty s
| arrow : Ty s -> Ty s -> Ty s
| all : Ty s -> Ty (s,X) -> Ty s

/-- Standard general terms, rather than monadic-normal-form terms. -/
inductive Tm : Sig -> Type where
| var : BVar s .var -> Tm s
| abs : Ty s -> Tm (s,x) -> Tm s
| app : Tm s -> Tm s -> Tm s
| tabs : Ty s -> Tm (s,X) -> Tm s
| tapp : Tm s -> Ty s -> Tm s

/-- Apply a sort-preserving renaming to a type. -/
def Ty.rename : Ty s1 -> Rename s1 s2 -> Ty s2
| .top, _ => .top
| .tvar X, rho => .tvar (rho.var X)
| .arrow S T, rho => .arrow (S.rename rho) (T.rename rho)
| .all B T, rho => .all (B.rename rho) (T.rename rho.lift)

/-- Apply a sort-preserving renaming to a term. -/
def Tm.rename : Tm s1 -> Rename s1 s2 -> Tm s2
| .var x, rho => .var (rho.var x)
| .abs S t, rho => .abs (S.rename rho) (t.rename rho.lift)
| .app t u, rho => .app (t.rename rho) (u.rename rho)
| .tabs B t, rho => .tabs (B.rename rho) (t.rename rho.lift)
| .tapp t U, rho => .tapp (t.rename rho) (U.rename rho)

/-- Weaken a type through one new binder of either sort. -/
def Ty.weaken {k : Kind} (T : Ty s) : Ty (s ,, k) :=
  T.rename Rename.succ

/-- Weaken a term through one new binder of either sort. -/
def Tm.weaken {k : Kind} (t : Tm s) : Tm (s ,, k) :=
  t.rename Rename.succ

inductive Tm.IsValue : Tm s -> Prop where
| abs : IsValue (.abs S t)
| tabs : IsValue (.tabs B t)

end SystemFSub
