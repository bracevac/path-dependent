import Coercions.Separation.FCdot.Syntax

namespace Separation

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
instance.  The separation line adds three consumable flavours: a location,
an heir, and the arrow binder of a consumer body.  Each carries a kill bit,
which is lexical: a store holds every bit live. -/
inductive CapBound : Sig → Type where
  | root : CapBound s
  | star : CapBound s
  | upper : CaptureSet s → CapBound s
  | inst : CaptureSet s → CapBound s
  /-- A location, or a name a consuming construct opens.  The bit is the
      lexical kill.  The set is what the name may come to own: `[]` for a
      location and for a name `newLet` opens, the names its head consumes for
      a name `letexF` opens. -/
  | loc : Bool → CaptureSet s → CapBound s
  /-- An heir: owns the older names `W` and resolves to them. -/
  | own : Bool → CaptureSet s → CapBound s
  /-- The arrow binder of a consumer body: it may come to own any older name.
      Opened in S1, declared here so that the bound family is complete. -/
  | param : Bool → CapBound s
deriving DecidableEq

def CapBound.rename : CapBound s1 → Rename s1 s2 → CapBound s2
  | .root, _ => .root
  | .star, _ => .star
  | .upper C, ρ => .upper (C.rename ρ)
  | .inst C, ρ => .inst (C.rename ρ)
  | .loc k C, ρ => .loc k (C.rename ρ)
  | .own k W, ρ => .own k (W.rename ρ)
  | .param k, _ => .param k

def CapBound.weaken (b : CapBound s) : CapBound (s,,k) := b.rename Rename.succ

scoped postfix:max "↑" => CapBound.weaken

/-- A binding for a term binder.  Witnesses, capture witnesses and field
labels of a transparent binder live in the scope that includes the binder
itself. -/
inductive Binding : Sig → Type where
  | opaque : Ty s → Binding s
  | transparent : Ty s → Witnesses (s,x) → CapWitnesses (s,x) → List Label → Binding s
  /-- The parameter a scope opens.  Read as `opaque` everywhere, except that
      mode bounds stop at it: the machine instantiates it only by an argument
      that `app` made access-only (plan-5h S0.2, decision 37). -/
  | formal : Ty s → Binding s

def Binding.ty : Binding s → Ty s
  | .opaque T => T
  | .transparent T _ _ _ => T
  | .formal T => T

/-- The binder is the parameter a scope opens. -/
def Binding.isFormal : Binding s → Bool
  | .formal _ => true
  | _ => false

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

/-! ### The scope contexts

A lambda body and an object body are scopes.  A scope opens its own root and
then the arrow's capture binder, in that order: the parameter and the arrow
binder are then at the level of the body root, which is what makes a
capability of the body stay inside the body.  The arrow binder is `.star`,
with no declared bound, so the body assumes nothing about the argument
beyond what the level rule gives. -/

/-- A scope: its own root, then the arrow's capture binder. -/
def scope (Γ : Ctx s) : Ctx ((s,c),c) := (Γ.consC .root).consC .star

/-- The scope a pack opens: the pack's own root, then the witness binder as
an instance of the witness set.  A rule of the type sort may open a capture
binder only under a root of its own, because otherwise its premise reads the
level of the opened binder relative to an outer root and the premise is not
closed under renaming into a context with a fresh root. -/
def scopeInst (Γ : Ctx s) (C : CaptureSet s) : Ctx (Sig.scope s) :=
  (Γ.consC .root).consC (.inst C↑)

/-- A lambda body: a scope, then the parameter at the domain read under the
body root.  The parameter is bound `formal`. -/
def body (Γ : Ctx s) (T : Dom s) : Ctx (((s,c),c),x) := Γ.scope.cons (.formal T.underRoot)

/-- A context binds no parameter.  Every store context is formal free. -/
def formalFree : Ctx s → Bool
  | .nil => true
  | .cons Γ b => !b.isFormal && Γ.formalFree
  | .consC Γ _ => Γ.formalFree

/-- An object body: the class root, then the self as a transparent binder at
the literal's own type.  The witnesses are written under the self alone, so
they are read under the class root by the same insertion. -/
def objBody (Γ : Ctx s) (T : Ty s) (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x))
    (ls : List Label) : Ctx ((s,c),x) :=
  (Γ.consC .root).cons
    (.transparent T.weaken (W.rename Rename.succ.lift) (Wc.rename Rename.succ.lift) ls)

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

/-- A capture bound is opaque when it stands for itself: a scope root, a
rigid capability, a location or a consumer's arrow binder.  An heir resolves
to what it owns, as an instance does. -/
def CapBound.opaque : CapBound s → Bool
  | .root => true
  | .star => true
  | .loc _ _ => true
  | .param _ => true
  | _ => false

/-- A capture bound is a root when it opens a scope. -/
def CapBound.isRoot : CapBound s → Bool
  | .root => true
  | _ => false

/-- The set an instance binder was opened at, if it is one. -/
def CapBound.instSet? : CapBound s → Option (CaptureSet s)
  | .inst C => some C
  | _ => none

/-- The names an heir owns, if it is one.  The bit is not read. -/
def CapBound.ownSet? : CapBound s → Option (CaptureSet s)
  | .own _ W => some W
  | _ => none

/-- The bit of a location that claims nothing, if it is one: the place a
cell sits (plan-5h S0.5, `Value.HasType.cell`). -/
def CapBound.locBit? : CapBound s → Option Bool
  | .loc b [] => some b
  | _ => none

theorem CapBound.locBit?_eq_some {b : CapBound s} {k : Bool} :
    b.locBit? = some k ↔ b = .loc k [] := by
  constructor
  · intro h
    match b, h with
    | .loc _ [], h => simp [CapBound.locBit?] at h; rw [h]
  · rintro rfl; rfl

/-- The consumable flavours: a location, an heir, a consumer's arrow
binder. -/
def CapBound.consumable : CapBound s → Bool
  | .loc _ _ | .own _ _ | .param _ => true
  | _ => false

/-- The kill bit.  A flavour without one is always live. -/
def CapBound.live : CapBound s → Bool
  | .loc b _ | .own b _ | .param b => b
  | _ => true

/-- The names an heir owns directly. -/
def CapBound.ownsB : CapBound s → BVar s .cap → Bool
  | .own _ W, κ => W.elem (.cvar κ)
  | _, _ => false

/-- The flavours a store may hold: no consumer parameter, and a location that
claims nothing. -/
def CapBound.storeFlavour : CapBound s → Bool
  | .param _ => false
  | .loc _ C => C.isEmpty
  | _ => true

@[simp] theorem CapBound.consumable_rename (b : CapBound s1) (ρ : Rename s1 s2) :
    (b.rename ρ).consumable = b.consumable := by
  cases b <;> rfl

@[simp] theorem CapBound.live_rename (b : CapBound s1) (ρ : Rename s1 s2) :
    (b.rename ρ).live = b.live := by
  cases b <;> rfl

@[simp] theorem CapBound.storeFlavour_rename (b : CapBound s1) (ρ : Rename s1 s2) :
    (b.rename ρ).storeFlavour = b.storeFlavour := by
  cases b <;> simp [CapBound.rename, CapBound.storeFlavour, CaptureSet.rename]

@[simp] theorem CapBound.consumable_weaken (b : CapBound s) :
    (CapBound.weaken (k := k) b).consumable = b.consumable := CapBound.consumable_rename b _

@[simp] theorem CapBound.live_weaken (b : CapBound s) :
    (CapBound.weaken (k := k) b).live = b.live := CapBound.live_rename b _

@[simp] theorem CapBound.storeFlavour_weaken (b : CapBound s) :
    (CapBound.weaken (k := k) b).storeFlavour = b.storeFlavour :=
  CapBound.storeFlavour_rename b _

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
level, which is what `none` says.  A moded atom is at the level of its base. -/
def lvlAtom (Γ : Ctx s) : CapAtom s → Option (BVar s .cap)
  | .var x => Γ.lvl x
  | .cvar κ => Γ.lvl κ
  | .name x _ => Γ.lvl x
  | .top => none
  | .mode _ a => Γ.lvlAtom a

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

/-- The set a capture atom is an instance of, if it is a capture binder with
an instance bound.  Only a capture binder can be one. -/
def instSet? (Γ : Ctx s) : CapAtom s → Option (CaptureSet s)
  | .cvar κ => (Γ.lookupCap κ).instSet?
  | _ => none

/-- `a` is a binder opened as an instance of `C`.  An `abbrev`, so that
`Decidable` is synthesised and the checker's case decides. -/
abbrev InstOf (Γ : Ctx s) (a : CapAtom s) (C : CaptureSet s) : Prop :=
  Γ.instSet? a = some C

/-- The names a capture atom owns, if it is an heir. -/
def ownSet? (Γ : Ctx s) : CapAtom s → Option (CaptureSet s)
  | .cvar κ => (Γ.lookupCap κ).ownSet?
  | _ => none

/-- `a` is an heir of `W`, whatever its bit.  An `abbrev`, so that
`Decidable` is synthesised and the checker's case decides. -/
abbrev OwnOf (Γ : Ctx s) (a : CapAtom s) (W : CaptureSet s) : Prop :=
  Γ.ownSet? a = some W

/-- The bit of a capture atom that is a location claiming nothing. -/
def locBit? (Γ : Ctx s) : CapAtom s → Option Bool
  | .cvar κ => (Γ.lookupCap κ).locBit?
  | _ => none

/-- `a` is a location with bit `b` that claims nothing.  Stated on the atom,
as `OwnOf` is, so that a substitution carries it structurally. -/
abbrev LocOf (Γ : Ctx s) (a : CapAtom s) (b : Bool) : Prop :=
  Γ.locBit? a = some b

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
  | .cons _ (.formal _), .here, _ => none
  | .cons Γ _, .there y, ℓ => (lookupDef Γ y ℓ).map Shape.weaken
  | .consC Γ _, .there y, ℓ => (lookupDef Γ y ℓ).map Shape.weaken

/-- Definition of a block's capture name, if its binder is transparent.  As
`lookupDef`, the capture witness already lives in the scope that includes the
binder, so it is read at the binder itself.  (`lookupDefᶜ` of the plan.) -/
def lookupDefC : Ctx s → BVar s .var → Label → Option (CaptureSet s)
  | .cons _ (.transparent _ _ Wc _), .here, ℓ => some (Wc.get ℓ)
  | .cons _ (.opaque _), .here, _ => none
  | .cons _ (.formal _), .here, _ => none
  | .cons Γ _, .there y, ℓ => (lookupDefC Γ y ℓ).map CaptureSet.weaken
  | .consC Γ _, .there y, ℓ => (lookupDefC Γ y ℓ).map CaptureSet.weaken

/-- Field labels of a transparent binder. -/
def lookupFields : Ctx s → BVar s .var → Option (List Label)
  | .cons _ (.transparent _ _ _ Fs), .here => some Fs
  | .cons _ (.opaque _), .here => none
  | .cons _ (.formal _), .here => none
  | .cons Γ _, .there y => lookupFields Γ y
  | .consC Γ _, .there y => lookupFields Γ y

/-- A binder is transparent when it records fields (possibly none). -/
def IsTransparent (Γ : Ctx s) (x : BVar s .var) : Prop := (Γ.lookupFields x).isSome

/-! ### Scope order

**T-B1.8.**  In a lambda body the parameter and the arrow's capture binder
have the same level, and that level is the body root.  This is the sentence
"parameter `any`s are at the same level as the function's local `any`" in the
target, and it is what rejects an escape out of a scope.  Both sides compute,
so each proof is `rfl`. -/

/-- The parameter of a body is at the level of the body root. -/
theorem body_lvl_param (Γ : Ctx s) (T : Dom s) :
    (Γ.body T).lvl (k := .var) .here = some (.there (.there .here)) := rfl

/-- The arrow's capture binder is at the same level, the body root. -/
theorem body_lvl_arrow (Γ : Ctx s) (T : Dom s) :
    (Γ.body T).lvl (k := .cap) (.there .here) = some (.there (.there .here)) := rfl

/-- And the body root is its own level. -/
theorem body_lvl_root (Γ : Ctx s) (T : Dom s) :
    (Γ.body T).lvl (k := .cap) (.there (.there .here)) = some (.there (.there .here)) := rfl

/-- The arrow's capture binder carries no declared bound. -/
theorem body_lookupCap_arrow (Γ : Ctx s) (T : Dom s) :
    (Γ.body T).lookupCap (.there .here) = .star := rfl

/-- Every term binder is transparent. -/
inductive Transparent : Ctx s → Prop where
  | nil : Transparent .nil
  | cons : Transparent Γ → Transparent (Ctx.cons Γ (.transparent T W Wc Fs))
  | consC : Transparent Γ → Transparent (Ctx.consC Γ b)

/-! ### Ownership

An heir owns the names it lists.  A name a consuming construct opens may come
to own the names it claims, and a consumer's arrow binder may come to own any
older name.  In a store context the two relations coincide
(`Ctx.SepInv.mayOwn_iff_owns`). -/

/-- The kill bit of a binder is live.  A flavour without a bit is always live. -/
def BitLive (Γ : Ctx s) (κ : BVar s .cap) : Prop := (Γ.lookupCap κ).live = true

/-- `h` owns `κ` directly: an heir that lists it.  The match on the bound is
`CapBound.ownsB`. -/
def ownsB (Γ : Ctx s) (h κ : BVar s .cap) : Bool := (Γ.lookupCap h).ownsB κ

/-- `h` may come to own `κ` directly: an heir that lists it, a name whose
claims list it, or a consumer's arrow binder and an older name. -/
def claimsB (Γ : Ctx s) (h κ : BVar s .cap) : Bool :=
  match Γ.lookupCap h with
  | .own _ W => W.elem (.cvar κ)
  | .loc _ C => C.elem (.cvar κ)
  | .param _ => decide (h.depth < κ.depth)
  | _ => false

/-- Ownership, the transitive closure of `ownsB`. -/
inductive Owns (Γ : Ctx s) : BVar s .cap → BVar s .cap → Prop where
  | direct : Γ.ownsB h κ = true → Γ.Owns h κ
  | trans : Γ.Owns h κ → Γ.Owns κ κ' → Γ.Owns h κ'

/-- Possible ownership, the transitive closure of `claimsB`. -/
inductive MayOwn (Γ : Ctx s) : BVar s .cap → BVar s .cap → Prop where
  | direct : Γ.claimsB h κ = true → Γ.MayOwn h κ
  | trans : Γ.MayOwn h κ → Γ.MayOwn κ κ' → Γ.MayOwn h κ'

/-- Two names are related when one may come to own the other. -/
def Related (Γ : Ctx s) (κ₁ κ₂ : BVar s .cap) : Prop := Γ.MayOwn κ₁ κ₂ ∨ Γ.MayOwn κ₂ κ₁

/-- An heir owns what it lists, so it may come to own it. -/
theorem claimsB_of_ownsB {Γ : Ctx s} {h κ : BVar s .cap} (hh : Γ.ownsB h κ = true) :
    Γ.claimsB h κ = true := by
  unfold ownsB at hh
  unfold claimsB
  cases hb : Γ.lookupCap h <;> rw [hb] at hh <;> simp [CapBound.ownsB] at hh ⊢
  exact hh

theorem MayOwn.of_owns {Γ : Ctx s} {h κ : BVar s .cap} (hh : Γ.Owns h κ) : Γ.MayOwn h κ := by
  induction hh with
  | direct hd => exact .direct (claimsB_of_ownsB hd)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem Related.symm {Γ : Ctx s} {κ₁ κ₂ : BVar s .cap} (h : Γ.Related κ₁ κ₂) :
    Γ.Related κ₂ κ₁ := Or.symm h

end Ctx

end FCdot

end Separation
