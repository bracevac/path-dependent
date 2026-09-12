import Coercions.Classifiers.FCdot.Syntax

namespace Classifiers

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
capability that subsumes nothing, `upper C` a bounded binder, `inst C` an
instance, and `cls c` a rigid capability with a declared classifier.  All five
are present from the start; this stage reads none of them. -/
inductive CapBound : Sig → Type where
  | root : CapBound s
  | star : CapBound s
  | upper : CaptureSet s → CapBound s
  | inst : CaptureSet s → CapBound s
  /-- A rigid capability with a declared classifier.  `star` is this flavour
      at `⊤`, which is what `CapBound.classifier` says. -/
  | cls : Cls.Classifier → CapBound s
deriving DecidableEq

def CapBound.rename : CapBound s1 → Rename s1 s2 → CapBound s2
  | .root, _ => .root
  | .star, _ => .star
  | .upper C, ρ => .upper (C.rename ρ)
  | .inst C, ρ => .inst (C.rename ρ)
  | .cls c, _ => .cls c

/-- The classifier a capture bound declares.  A bound that declares none
reads as the root classifier `⊤`, which is the strict reading: a kind that
does not contain `⊤` admits no unannotated capability. -/
def CapBound.classifier : CapBound s → Cls.Classifier
  | .cls c => c
  | _ => .top

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
body root. -/
def body (Γ : Ctx s) (T : Dom s) : Ctx (((s,c),c),x) := Γ.scope.cons (.opaque T.underRoot)

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

/-- A capture bound is opaque when it stands for itself: a scope root or a
rigid capability. -/
def CapBound.opaque : CapBound s → Bool
  | .root => true
  | .star => true
  | .cls _ => true
  | _ => false

/-- A capture bound is a root when it opens a scope. -/
def CapBound.isRoot : CapBound s → Bool
  | .root => true
  | _ => false

/-- The set an instance binder was opened at, if it is one. -/
def CapBound.instSet? : CapBound s → Option (CaptureSet s)
  | .inst C => some C
  | _ => none

/-- The classifier a capture binder *declares*, if it declares one.  Only the
`cls` flavour does.  `CapBound.classifier` reads a classifier off every
bound, with the root classifier `⊤` as the default; this reader says instead
which bounds carry a declaration a judgment may rely on.  A `star` binder
carries none, because a context map may read a `star` binder as an instance
(`Ctx.Ren.instC`), and an instance declares no classifier. -/
def CapBound.clsOf? : CapBound s → Option Cls.Classifier
  | .cls c => some c
  | _ => none

/-- The capture set a capture binder stands below: the bound of an upper
binder and the set an instance binder was opened at.  These are the two
flavours whose resolution steps to another set. -/
def CapBound.setOf? : CapBound s → Option (CaptureSet s)
  | .upper C => some C
  | .inst C => some C
  | _ => none

@[simp] theorem CapBound.clsOf?_of_cls (c : Cls.Classifier) :
    (CapBound.cls (s := s) c).clsOf? = some c := rfl

@[simp] theorem CapBound.setOf?_of_upper (C : CaptureSet s) :
    (CapBound.upper C).setOf? = some C := rfl

@[simp] theorem CapBound.setOf?_of_inst (C : CaptureSet s) :
    (CapBound.inst C).setOf? = some C := rfl

/-- A declared classifier is opaque and is no root, which is what the kinding
rule `kcls` used to ask for explicitly. -/
theorem CapBound.opaque_of_clsOf? {b : CapBound s} {c : Cls.Classifier}
    (h : b.clsOf? = some c) : b.opaque = true := by
  cases b with
  | cls c0 => rfl
  | root | star | upper C | inst C => simp [CapBound.clsOf?] at h

theorem CapBound.isRoot_of_clsOf? {b : CapBound s} {c : Cls.Classifier}
    (h : b.clsOf? = some c) : b.isRoot = false := by
  cases b with
  | cls c0 => rfl
  | root | star | upper C | inst C => simp [CapBound.clsOf?] at h

theorem CapBound.classifier_of_clsOf? {b : CapBound s} {c : Cls.Classifier}
    (h : b.clsOf? = some c) : b.classifier = c := by
  cases b with
  | cls c0 =>
      have : c0 = c := by simpa [CapBound.clsOf?] using h
      rw [this]
      rfl
  | root | star | upper C | inst C => simp [CapBound.clsOf?] at h

/-- An instance bound is one of the two set bounds. -/
theorem CapBound.setOf?_of_instSet? {b : CapBound s} {C : CaptureSet s}
    (h : b.instSet? = some C) : b.setOf? = some C := by
  cases b with
  | inst C0 =>
      have : C0 = C := by simpa [CapBound.instSet?] using h
      rw [this]
      rfl
  | root | star | upper C1 | cls c => simp [CapBound.instSet?] at h

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
  | .proj a _ => Γ.lvlAtom a

/-- The classifier an atom carries in `Γ`.  Only a capture binder can declare
one: every other atom reads as the root classifier `⊤`.  That is Fact 2, that
resolution lands in capture binders and in the universal root. -/
def classOf (Γ : Ctx s) : CapAtom s → Cls.Classifier
  | .cvar κ => (Γ.lookupCap κ).classifier
  | _ => .top

/-- The kind `φ` admits the atom `a`: the classifier of `a` is a member of
`φ`.  `Bool` valued, so that `decide` closes the examples of the stage. -/
def admitsB (Γ : Ctx s) (a : CapAtom s) (φ : Cls.Kind) : Bool := φ.containsB (Γ.classOf a)

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

/-- The classifier an atom's binder declares, if it declares one.  Only a
capture binder can, which is Fact 2.  Read at the base of an atom, so that a
projection is transparent to it. -/
def clsOf? (Γ : Ctx s) : CapAtom s → Option Cls.Classifier
  | .cvar κ => (Γ.lookupCap κ).clsOf?
  | _ => none

/-- The capture set an atom's binder stands below, if it has one. -/
def setOf? (Γ : Ctx s) : CapAtom s → Option (CaptureSet s)
  | .cvar κ => (Γ.lookupCap κ).setOf?
  | _ => none

/-- `a` is a binder with declared classifier `c`.  An `abbrev`, so that
`Decidable` is synthesised and the checker's case decides. -/
abbrev ClsOf (Γ : Ctx s) (a : CapAtom s) (c : Cls.Classifier) : Prop :=
  Γ.clsOf? a = some c

/-- `a` is a binder standing below the set `C`. -/
abbrev SetOf (Γ : Ctx s) (a : CapAtom s) (C : CaptureSet s) : Prop :=
  Γ.setOf? a = some C

/-- An instance fact is a set fact.  This is the half of `SetOf` that the
fourth capture field of a context map already carries. -/
theorem SetOf.of_instOf {Γ : Ctx s} {a : CapAtom s} {C : CaptureSet s}
    (h : Γ.InstOf a C) : Γ.SetOf a C := by
  cases a with
  | cvar κ => exact CapBound.setOf?_of_instSet? h
  | top | var _ | name _ _ | proj _ _ => simp [Ctx.InstOf, Ctx.instSet?] at h

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

end Ctx

end FCdot

end Classifiers
