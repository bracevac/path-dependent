import Coercions.Captures.FCdot.Syntax

namespace Captures

/-!
# FCdot contexts

A term binder is opaque (abstract block) or transparent (block defined by
witnesses, fields known).  Transparent binders arise inside object literals
and in store typing.  A capture binder carries a `CapBound`: a scope root, a
rigid platform capability, an upper bound, or an instance.  No binding
records a level; every function over a context is by recursion on the spine.
-/

namespace FCdot

/-- Labels of a field list. -/
def Fields.labels : Fields s → List Label
  | .nil => []
  | .cons F ℓ _ => ℓ :: F.labels

/-- What a capture binder stands for.  `root` is a scope root, `star` a rigid
capability that subsumes nothing, `upper C` a bounded binder, and `inst C` an
instance.  All four are present from the start; this stage reads none of
them. -/
inductive CapBound : Sig → Type where
  | root : CapBound s
  | star : CapBound s
  | upper : CaptureSet s → CapBound s
  | inst : CaptureSet s → CapBound s
deriving DecidableEq

def CapBound.rename : CapBound s1 → Rename s1 s2 → CapBound s2
  | .root, _ => .root
  | .star, _ => .star
  | .upper C, ρ => .upper (C.rename ρ)
  | .inst C, ρ => .inst (C.rename ρ)

def CapBound.weaken (b : CapBound s) : CapBound (s,,k) := b.rename Rename.succ

scoped postfix:max "↑" => CapBound.weaken

/-- A binding for a term binder.  Witnesses and field labels of a
transparent binder live in the scope that includes the binder itself. -/
inductive Binding : Sig → Type where
  | opaque : Ty s → Binding s
  | transparent : Ty s → Witnesses (s,x) → List Label → Binding s

def Binding.ty : Binding s → Ty s
  | .opaque T => T
  | .transparent T _ _ => T

/-- A context: term binders and capture binders, newest first.  (`consᶜ` of
the plan: `ᶜ` is not a legal Lean identifier character, so the capture-sort
twin of a name carries the suffix `C`.) -/
inductive Ctx : Sig → Type where
  | nil : Ctx []
  | cons : Ctx s → Binding s → Ctx (s,x)
  | consC : Ctx s → CapBound s → Ctx (s,c)

namespace Ctx

/-- Type of a variable, in the current scope.  A capture binder in the way is
passed by the kind-generic weakening. -/
def lookupTy : Ctx s → BVar s .var → Ty s
  | .cons _ b, .here => b.ty↑
  | .cons Γ _, .there y => (lookupTy Γ y)↑
  | .consC Γ _, .there y => (lookupTy Γ y)↑

/-- The bound of a capture binder, in the current scope. -/
def lookupCap : Ctx s → BVar s .cap → CapBound s
  | .consC _ b, .here => b↑
  | .consC Γ _, .there κ => (lookupCap Γ κ)↑
  | .cons Γ _, .there κ => (lookupCap Γ κ)↑

/-- Definition of a block name, if its binder is transparent. -/
def lookupDef : Ctx s → BVar s .var → Label → Option (Shape s)
  | .cons _ (.transparent _ W _), .here, ℓ => some (W.get ℓ)
  | .cons _ (.opaque _), .here, _ => none
  | .cons Γ _, .there y, ℓ => (lookupDef Γ y ℓ).map Shape.weaken
  | .consC Γ _, .there y, ℓ => (lookupDef Γ y ℓ).map Shape.weaken

/-- Field labels of a transparent binder. -/
def lookupFields : Ctx s → BVar s .var → Option (List Label)
  | .cons _ (.transparent _ _ Fs), .here => some Fs
  | .cons _ (.opaque _), .here => none
  | .cons Γ _, .there y => lookupFields Γ y
  | .consC Γ _, .there y => lookupFields Γ y

/-- A binder is transparent when it records fields (possibly none). -/
def IsTransparent (Γ : Ctx s) (x : BVar s .var) : Prop := (Γ.lookupFields x).isSome

/-- Every term binder is transparent. -/
inductive Transparent : Ctx s → Prop where
  | nil : Transparent .nil
  | cons : Transparent Γ → Transparent (Ctx.cons Γ (.transparent T W Fs))
  | consC : Transparent Γ → Transparent (Ctx.consC Γ b)

end Ctx

end FCdot

end Captures
