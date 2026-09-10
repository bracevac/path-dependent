import Coercions.CapturesCC.FCdot.Syntax

namespace CapturesCC

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
  | .cons F ℓ _ _ => ℓ :: F.labels

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

/-- A binding for a term binder.  Witnesses, capture witnesses and field
labels of a transparent binder live in the scope that includes the binder
itself. -/
inductive Binding : Sig → Type where
  | opaque : Ty s → Binding s
  | transparent : Ty s → Witnesses (s,x) → CapWitnesses (s,x) → List Label → Binding s

def Binding.ty : Binding s → Ty s
  | .opaque T => T
  | .transparent T _ _ _ => T

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

end Ctx

/-! ## Levels

A level is a position on the spine, not a field on a binding.  The level of a
binder is the innermost root binder of the prefix that precedes it, and a
root is its own level.  `none` means the outermost level, the universal root
`⊤ᶜ`.  Everything here is `Bool` valued, so that `decide` closes the
examples of the stage. -/

/-- Age of a bound variable.  Older is deeper. -/
def BVar.depth : BVar s k → Nat
  | .here => 0
  | .there y => y.depth + 1

@[simp] theorem BVar.depth_here : (BVar.here (s := s) (k := k)).depth = 0 := rfl

@[simp] theorem BVar.depth_there (y : BVar s k) :
    (BVar.there (k0 := k0) y).depth = y.depth + 1 := rfl

/-- A capture bound is opaque when it stands for itself: a scope root or a
rigid capability. -/
def CapBound.opaque : CapBound s → Bool
  | .root => true
  | .star => true
  | _ => false

/-- A capture bound is a root when it opens a scope. -/
def CapBound.isRoot : CapBound s → Bool
  | .root => true
  | _ => false

@[simp] theorem CapBound.opaque_rename (b : CapBound s1) (ρ : Rename s1 s2) :
    (b.rename ρ).opaque = b.opaque := by
  cases b <;> rfl

@[simp] theorem CapBound.isRoot_rename (b : CapBound s1) (ρ : Rename s1 s2) :
    (b.rename ρ).isRoot = b.isRoot := by
  cases b <;> rfl

@[simp] theorem CapBound.opaque_weaken (b : CapBound s) :
    (CapBound.weaken (k := k) b).opaque = b.opaque := CapBound.opaque_rename b _

@[simp] theorem CapBound.isRoot_weaken (b : CapBound s) :
    (CapBound.weaken (k := k) b).isRoot = b.isRoot := CapBound.isRoot_rename b _

/-- Depth comparison with `none` read as infinity, the outermost level. -/
def depthGe : Option Nat → Option Nat → Bool
  | none, _ => true
  | some _, none => false
  | some m, some d => decide (d ≤ m)

namespace Ctx

/-- The innermost root binder of a context, if it has one. -/
def root? : Ctx s → Option (BVar s .cap)
  | .nil => none
  | .consC _ .root => some .here
  | .consC Γ _ => Γ.root?.map .there
  | .cons Γ _ => Γ.root?.map .there

/-- The innermost root as an atom.  A context with no root binder is inside
no scope, so its root is the universal one. -/
def rootAtom (Γ : Ctx s) : CapAtom s := Γ.root?.elim .top CapAtom.cvar

/-- The level of a binder: the innermost root of the prefix before it, and
itself when it is a root.  `none` means the outermost level, `⊤ᶜ`. -/
def lvl : Ctx s → BVar s k → Option (BVar s .cap)
  | .consC _ .root, .here => some .here
  | .consC Γ _, .here => Γ.root?.map .there
  | .cons Γ _, .here => Γ.root?.map .there
  | .consC Γ _, .there y => (Γ.lvl y).map .there
  | .cons Γ _, .there y => (Γ.lvl y).map .there

/-- The level of a capture atom.  The universal root is at the outermost
level, which is what `none` says. -/
def lvlAtom (Γ : Ctx s) : CapAtom s → Option (BVar s .cap)
  | .var x => Γ.lvl x
  | .cvar κ => Γ.lvl κ
  | .name x _ => Γ.lvl x
  | .top => none

/-- Depth of a root atom, with the universal root at infinity. -/
def rootDepth? : CapAtom s → Option Nat
  | .top => none
  | .cvar κ => some κ.depth
  | _ => none

/-- The atom is a scope root: the universal root, or a capture binder whose
bound is `root`. -/
def isRootB (Γ : Ctx s) : CapAtom s → Bool
  | .top => true
  | .cvar κ => (Γ.lookupCap κ).isRoot
  | _ => false

/-- `e`'s level is `r` or encloses it.  Inner absorbs outer, never the
reverse. -/
def lvlLeB (Γ : Ctx s) (e r : CapAtom s) : Bool :=
  depthGe ((Γ.lvlAtom e).map BVar.depth) (Ctx.rootDepth? r)

/-- `r` is a scope root of `Γ`.  An `abbrev`, so that `Decidable` is
synthesised and `by decide` works. -/
abbrev IsRoot (Γ : Ctx s) (r : CapAtom s) : Prop := Γ.isRootB r = true

/-- `e` is at or outside the level of `r`.  An `abbrev`, for the same
reason. -/
abbrev LvlLe (Γ : Ctx s) (e r : CapAtom s) : Prop := Γ.lvlLeB e r = true

/-- A capture set is confined to a root when no atom of it is strictly
inside that root. -/
def Confined (Γ : Ctx s) (C : CaptureSet s) (r : CapAtom s) : Prop :=
  ∀ a ∈ C, Γ.LvlLe a r

instance Confined.instDecidable (Γ : Ctx s) (C : CaptureSet s) (r : CapAtom s) :
    Decidable (Γ.Confined C r) := by
  unfold Ctx.Confined
  infer_instance

/-- Definition of a block name, if its binder is transparent. -/
def lookupDef : Ctx s → BVar s .var → Label → Option (Shape s)
  | .cons _ (.transparent _ W _ _), .here, ℓ => some (W.get ℓ)
  | .cons _ (.opaque _), .here, _ => none
  | .cons Γ _, .there y, ℓ => (lookupDef Γ y ℓ).map Shape.weaken
  | .consC Γ _, .there y, ℓ => (lookupDef Γ y ℓ).map Shape.weaken

/-- Definition of a block's capture name, if its binder is transparent.  As
`lookupDef`, the capture witness already lives in the scope that includes the
binder, so it is read at the binder itself.  (`lookupDefᶜ` of the plan.) -/
def lookupDefC : Ctx s → BVar s .var → Label → Option (CaptureSet s)
  | .cons _ (.transparent _ _ Wc _), .here, ℓ => some (Wc.get ℓ)
  | .cons _ (.opaque _), .here, _ => none
  | .cons Γ _, .there y, ℓ => (lookupDefC Γ y ℓ).map CaptureSet.weaken
  | .consC Γ _, .there y, ℓ => (lookupDefC Γ y ℓ).map CaptureSet.weaken

/-- Field labels of a transparent binder. -/
def lookupFields : Ctx s → BVar s .var → Option (List Label)
  | .cons _ (.transparent _ _ _ Fs), .here => some Fs
  | .cons _ (.opaque _), .here => none
  | .cons Γ _, .there y => lookupFields Γ y
  | .consC Γ _, .there y => lookupFields Γ y

/-- A binder is transparent when it records fields (possibly none). -/
def IsTransparent (Γ : Ctx s) (x : BVar s .var) : Prop := (Γ.lookupFields x).isSome

/-- Every term binder is transparent. -/
inductive Transparent : Ctx s → Prop where
  | nil : Transparent .nil
  | cons : Transparent Γ → Transparent (Ctx.cons Γ (.transparent T W Wc Fs))
  | consC : Transparent Γ → Transparent (Ctx.consC Γ b)

end Ctx

end FCdot

end CapturesCC
