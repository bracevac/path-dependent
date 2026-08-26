import SystemFCo.Debruijn

/-!
Intrinsically scoped syntax for the explicit-coercion target.

The target separates ordinary polymorphism from coercion abstraction:
`Ty.poly` binds a type variable, while `Ty.qual S T A` binds evidence of
`S => T` in `A`.
-/

namespace SystemFCo

/-- Target types. -/
inductive Ty : Sig -> Type where
| top : Ty sig
| tvar : BVar sig .tvar -> Ty sig
| arrow : Ty sig -> Ty sig -> Ty sig
| poly : Ty (sig ,, .tvar) -> Ty sig
| qual : Ty sig -> Ty sig -> Ty (sig ,, .cvar) -> Ty sig
deriving DecidableEq, Repr

/-- Directed coercion syntax. -/
inductive Co : Sig -> Type where
| cvar : BVar sig .cvar -> Co sig
| refl : Ty sig -> Co sig
| trans : Co sig -> Co sig -> Co sig
| top : Ty sig -> Co sig
| arrow : Co sig -> Co sig -> Co sig
| poly : Co (sig ,, .tvar) -> Co sig
| qual : Co (sig ,, .cvar) -> Co (sig ,, .cvar) -> Co sig
deriving DecidableEq, Repr

/-- Target expressions. -/
inductive Exp : Sig -> Type where
| var : BVar sig .var -> Exp sig
| abs : Ty sig -> Exp (sig ,, .var) -> Exp sig
| app : Exp sig -> Exp sig -> Exp sig
| tabs : Exp (sig ,, .tvar) -> Exp sig
| tapp : Exp sig -> Ty sig -> Exp sig
| cabs : Ty sig -> Ty sig -> Exp (sig ,, .cvar) -> Exp sig
| capp : Exp sig -> Co sig -> Exp sig
| cast : Exp sig -> Co sig -> Exp sig
deriving DecidableEq, Repr

/-! ## Renaming -/

def Ty.rename : Ty sig -> Rename sig sig' -> Ty sig'
| .top, _ => .top
| .tvar x, rename => .tvar (rename.var x)
| .arrow S T, rename => .arrow (S.rename rename) (T.rename rename)
| .poly T, rename => .poly (T.rename (Rename.lift rename .tvar))
| .qual S T U, rename =>
    .qual (S.rename rename) (T.rename rename)
      (U.rename (Rename.lift rename .cvar))

def Co.rename : Co sig -> Rename sig sig' -> Co sig'
| .cvar x, rename => .cvar (rename.var x)
| .refl T, rename => .refl (T.rename rename)
| .trans first second, rename =>
    .trans (first.rename rename) (second.rename rename)
| .top T, rename => .top (T.rename rename)
| .arrow domain codomain, rename =>
    .arrow (domain.rename rename) (codomain.rename rename)
| .poly body, rename => .poly (body.rename (Rename.lift rename .tvar))
| .qual argument result, rename =>
    .qual (argument.rename (Rename.lift rename .cvar))
      (result.rename (Rename.lift rename .cvar))

def Exp.rename : Exp sig -> Rename sig sig' -> Exp sig'
| .var x, rename => .var (rename.var x)
| .abs T body, rename =>
    .abs (T.rename rename) (body.rename (Rename.lift rename .var))
| .app function argument, rename =>
    .app (function.rename rename) (argument.rename rename)
| .tabs body, rename => .tabs (body.rename (Rename.lift rename .tvar))
| .tapp function argument, rename =>
    .tapp (function.rename rename) (argument.rename rename)
| .cabs S T body, rename =>
    .cabs (S.rename rename) (T.rename rename)
      (body.rename (Rename.lift rename .cvar))
| .capp function argument, rename =>
    .capp (function.rename rename) (argument.rename rename)
| .cast expression coercion, rename =>
    .cast (expression.rename rename) (coercion.rename rename)

/-- Weaken syntax past one new binder of arbitrary sort. -/
def Ty.weaken (T : Ty sig) (kind : Kind) : Ty (sig ,, kind) :=
  T.rename (Rename.weaken kind)

def Co.weaken (coercion : Co sig) (kind : Kind) : Co (sig ,, kind) :=
  coercion.rename (Rename.weaken kind)

def Exp.weaken (expression : Exp sig) (kind : Kind) : Exp (sig ,, kind) :=
  expression.rename (Rename.weaken kind)

end SystemFCo
