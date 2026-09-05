import Coercions.FCdot.Syntax

/-!
# FCdot contexts

A binder is opaque (abstract block) or transparent (block defined by
witnesses, fields known).  Transparent binders arise inside object literals
and in store typing.
-/

namespace FCdot

/-- Labels of a field list. -/
def Fields.labels : Fields s → List Label
  | .nil => []
  | .cons F ℓ _ => ℓ :: F.labels

/-- A binding for a term binder.  Witnesses and field labels of a
transparent binder live in the scope that includes the binder itself. -/
inductive Binding : Sig → Type where
  | opaque : Ty s → Binding s
  | transparent : Ty s → Witnesses (s,x) → List Label → Binding s

def Binding.ty : Binding s → Ty s
  | .opaque T => T
  | .transparent T _ _ => T

inductive Ctx : Sig → Type where
  | nil : Ctx []
  | cons : Ctx s → Binding s → Ctx (s,x)

namespace Ctx

/-- Type of a variable, in the current scope. -/
def lookupTy : Ctx s → BVar s .var → Ty s
  | .cons _ b, .here => b.ty↑
  | .cons Γ _, .there y => (lookupTy Γ y)↑

/-- Definition of a block name, if its binder is transparent. -/
def lookupDef : Ctx s → BVar s .var → Label → Option (Ty s)
  | .cons _ (.transparent _ W _), .here, ℓ => some (W.get ℓ)
  | .cons _ (.opaque _), .here, _ => none
  | .cons Γ _, .there y, ℓ => (lookupDef Γ y ℓ).map Ty.weaken

/-- Field labels of a transparent binder. -/
def lookupFields : Ctx s → BVar s .var → Option (List Label)
  | .cons _ (.transparent _ _ Fs), .here => some Fs
  | .cons _ (.opaque _), .here => none
  | .cons Γ _, .there y => lookupFields Γ y

/-- A binder is transparent when it records fields (possibly none). -/
def IsTransparent (Γ : Ctx s) (x : BVar s .var) : Prop := (Γ.lookupFields x).isSome

/-- Every binder is transparent. -/
inductive Transparent : Ctx s → Prop where
  | nil : Transparent .nil
  | cons : Transparent Γ → Transparent (Ctx.cons Γ (.transparent T W Fs))

end Ctx

end FCdot
