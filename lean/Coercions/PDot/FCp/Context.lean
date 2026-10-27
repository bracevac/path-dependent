import Coercions.PDot.FCp.RenameLemmas
import Coercions.PDot.Source.Syntax

/-!
# FCp contexts and blocks (plan T.2)

A context binds each variable opaque at a type, or transparent at a type with the block of its
literal.  A block is what a literal defines at its own path: a node of type definitions and
children, a forward to a path, or a closure.  `Ctx.blockAt x` is the block of `x`, `Ctx.nodeAt p`
follows the children of a block along the fields of `p`, and `Ctx.defAt p A` reads the type
definition at `A` of the node at `p`.  None of them follows a forward.

The block of a transparent binder lives under the binder (decision D3 of the groups file): the
type of `Binding.transparent T B` is in the outer signature and `Ctx.ty` weakens it, the block `B`
reads the binder as `.here` and `Ctx.blockAt` returns it as it is.  `Defs.block` takes no path
(decision D4), and `Ctx.defAt` is by recursion on the path (decision D5).  The plan's equation for
`defAt` over a field list is the theorem `Ctx.defAt_ext`, over X0's `Path.ext`.

Binders are named in comments.  `(Γ, z : b)` adds one variable, `.here` is the newest.
-/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Bindings and contexts -/

inductive Binding : Sig → Type where
  | opaque : Ty s → Binding s                               -- z : opaque T
  | transparent : Ty s → Block (s,x) → Binding s            -- z : transparent T B, B under z (D3)
inductive Ctx : Sig → Type where
  | nil : Ctx []                                            -- []
  | cons : Ctx s → Binding s → Ctx (s,x)                    -- Γ, z : b
def Binding.ty : Binding s → Ty s
  | .opaque T => T
  | .transparent T _ => T
def Ctx.ty : Ctx s → BVar s .var → Ty s
  | .cons _ b, .here => b.ty.weaken                         -- (Γ, z : b).ty z = T↑
  | .cons Γ _, .there y => (Γ.ty y).weaken                  -- (Γ, b).ty y↑ = (Γ.ty y)↑
def Ctx.blockAt : Ctx s → BVar s .var → Option (Block s)
  | .cons _ (.opaque _), .here => none                      -- (Γ, z : opaque T).blockAt z = none
  | .cons _ (.transparent _ B), .here => some B             -- (Γ, z : transparent T B).blockAt z = some B
  | .cons Γ _, .there y => (Γ.blockAt y).map (Block.rename · Rename.succ)

/-! ## Reading blocks -/

def TyDefs.get : TyDefs s → Label → Option (Ty s)          -- W A, the newest
  | .nil, _ => none
  | .cons W A' U, A => if A = A' then some U else W.get A
def Kids.get : Kids s → Label → Option (Block s)            -- C a, the newest
  | .nil, _ => none
  | .cons C a' B, a => if a = a' then some B else C.get a
def Block.child : Block s → Label → Option (Block s)
  | .node _ C, a => C.get a
  | .fwd _, _ => none
  | .clo, _ => none
def Block.def : Block s → Label → Option (Ty s)            -- (node W C).def A = W A, fwd and clo define nothing
  | .node W _, A => W.get A
  | .fwd _, _ => none
  | .clo, _ => none
def Block.walk : Block s → List Label → Option (Block s)   -- plan-10-pdot.md:402-403
  | B, [] => some B
  | B, a :: bs => (B.child a).bind (Block.walk · bs)
mutual
def Defs.tyDefs : Defs s → TyDefs s
  | .nil => .nil
  | .typ ds A U => .cons ds.tyDefs A U
  | .fld ds _ _ => ds.tyDefs
def Defs.kids : Defs s → Kids s
  | .nil => .nil
  | .typ ds _ _ => ds.kids
  | .fld ds a rhs => .cons ds.kids a rhs.child
def Rhs.child : Rhs s → Block s
  | .path P => .fwd P.path                                  -- a path field forwards
  | .fn _ => .clo                                           -- a function field is a closure
  | .nest _ ds => .node ds.tyDefs ds.kids                   -- a nested literal is a node
end
def Defs.block (ds : Defs s) : Block s := .node ds.tyDefs ds.kids     -- block p ds of T.2, with no p (D4)
def Ctx.nodeAt (Γ : Ctx s) : Path s → Option (Block s)     -- follows no forwarding (D5)
  | .var x => Γ.blockAt x
  | .sel p a => (Γ.nodeAt p).bind (·.child a)
def Ctx.defAt (Γ : Ctx s) (p : Path s) (A : Label) : Option (Ty s) := (Γ.nodeAt p).bind (·.def A)

/-! ## Walking along a field list -/

theorem Block.walk_append (B : Block s) (bs : List Label) (a : Label) :
    B.walk (bs ++ [a]) = (B.walk bs).bind (·.child a) := by
  induction bs generalizing B with
  | nil =>
      show (B.child a).bind (Block.walk · []) = B.child a
      cases B.child a <;> rfl
  | cons b bs ih =>
      show (B.child b).bind (Block.walk · (bs ++ [a])) = ((B.child b).bind (Block.walk · bs)).bind _
      cases B.child b with
      | none => rfl
      | some B' => exact ih B'

theorem Ctx.nodeAt_ext (Γ : Ctx s) (p : Path s) (bs : List Label) :
    Γ.nodeAt (p.ext bs) = (Γ.nodeAt p).bind (·.walk bs) := by
  induction bs generalizing p with
  | nil =>
      show Γ.nodeAt p = (Γ.nodeAt p).bind (Block.walk · [])
      cases Γ.nodeAt p <;> rfl
  | cons a bs ih =>
      show Γ.nodeAt ((p.sel a).ext bs) = (Γ.nodeAt p).bind (fun B => (B.child a).bind (Block.walk · bs))
      rw [ih (p.sel a)]
      show ((Γ.nodeAt p).bind (·.child a)).bind (Block.walk · bs) = _
      cases Γ.nodeAt p <;> rfl

/-- The plan's equation for `defAt` (`plan-10-pdot.md:407`), over X0's `Path.ext`. -/
theorem Ctx.defAt_ext (Γ : Ctx s) (x : BVar s .var) (bs : List Label) (A : Label) :
    Γ.defAt ((Path.var x).ext bs) A = (Γ.blockAt x).bind (fun B => (B.walk bs).bind (·.def A)) := by
  show (Γ.nodeAt ((Path.var x).ext bs)).bind (·.def A) = _
  rw [Ctx.nodeAt_ext]
  show ((Γ.blockAt x).bind (·.walk bs)).bind (·.def A) = _
  cases Γ.blockAt x <;> rfl

/-! ## Reading a block commutes with renaming and path substitution -/

theorem TyDefs.get_rename : ∀ (W : TyDefs s₁) (ρ : Rename s₁ s₂) (A : Label),
    (W.rename ρ).get A = (W.get A).map (Ty.rename · ρ)
  | .nil, _, _ => rfl
  | .cons W A' U, ρ, A => by
      show (if A = A' then some (U.rename ρ) else (W.rename ρ).get A) =
        (if A = A' then some U else W.get A).map (Ty.rename · ρ)
      by_cases h : A = A'
      · rw [if_pos h, if_pos h]; rfl
      · rw [if_neg h, if_neg h, TyDefs.get_rename W ρ A]

theorem TyDefs.get_subst : ∀ (W : TyDefs s₁) (σ : PathSubst s₁ s₂) (A : Label),
    (W.subst σ).get A = (W.get A).map (Ty.subst · σ)
  | .nil, _, _ => rfl
  | .cons W A' U, σ, A => by
      show (if A = A' then some (U.subst σ) else (W.subst σ).get A) =
        (if A = A' then some U else W.get A).map (Ty.subst · σ)
      by_cases h : A = A'
      · rw [if_pos h, if_pos h]; rfl
      · rw [if_neg h, if_neg h, TyDefs.get_subst W σ A]

theorem Kids.get_rename : ∀ (C : Kids s₁) (ρ : Rename s₁ s₂) (a : Label),
    (C.rename ρ).get a = (C.get a).map (Block.rename · ρ)
  | .nil, _, _ => rfl
  | .cons C a' B, ρ, a => by
      show (if a = a' then some (B.rename ρ) else (C.rename ρ).get a) =
        (if a = a' then some B else C.get a).map (Block.rename · ρ)
      by_cases h : a = a'
      · rw [if_pos h, if_pos h]; rfl
      · rw [if_neg h, if_neg h, Kids.get_rename C ρ a]

theorem Kids.get_subst : ∀ (C : Kids s₁) (σ : PathSubst s₁ s₂) (a : Label),
    (C.subst σ).get a = (C.get a).map (Block.subst · σ)
  | .nil, _, _ => rfl
  | .cons C a' B, σ, a => by
      show (if a = a' then some (B.subst σ) else (C.subst σ).get a) =
        (if a = a' then some B else C.get a).map (Block.subst · σ)
      by_cases h : a = a'
      · rw [if_pos h, if_pos h]; rfl
      · rw [if_neg h, if_neg h, Kids.get_subst C σ a]

theorem Block.child_rename (B : Block s₁) (ρ : Rename s₁ s₂) (a : Label) :
    (B.rename ρ).child a = (B.child a).map (Block.rename · ρ) := by
  cases B with
  | node W C => exact Kids.get_rename C ρ a
  | fwd q => rfl
  | clo => rfl

theorem Block.def_rename (B : Block s₁) (ρ : Rename s₁ s₂) (A : Label) :
    (B.rename ρ).def A = (B.def A).map (Ty.rename · ρ) := by
  cases B with
  | node W C => exact TyDefs.get_rename W ρ A
  | fwd q => rfl
  | clo => rfl

theorem Block.child_subst (B : Block s₁) (σ : PathSubst s₁ s₂) (a : Label) :
    (B.subst σ).child a = (B.child a).map (Block.subst · σ) := by
  cases B with
  | node W C => exact Kids.get_subst C σ a
  | fwd q => rfl
  | clo => rfl

theorem Block.def_subst (B : Block s₁) (σ : PathSubst s₁ s₂) (A : Label) :
    (B.subst σ).def A = (B.def A).map (Ty.subst · σ) := by
  cases B with
  | node W C => exact TyDefs.get_subst W σ A
  | fwd q => rfl
  | clo => rfl

/-! ## Reading a context after a weakening -/

theorem Ctx.nodeAt_weaken (Γ : Ctx s) (b : Binding s) (p : Path s) :
    (Γ.cons b).nodeAt (p.rename Rename.succ) = (Γ.nodeAt p).map (Block.rename · Rename.succ) := by
  induction p with
  | var x => cases b <;> rfl
  | sel p a ih =>
      show ((Γ.cons b).nodeAt (p.rename Rename.succ)).bind (·.child a) =
        ((Γ.nodeAt p).bind (·.child a)).map (Block.rename · Rename.succ)
      rw [ih]
      cases Γ.nodeAt p with
      | none => rfl
      | some B => exact Block.child_rename B Rename.succ a

theorem Ctx.defAt_weaken (Γ : Ctx s) (b : Binding s) (p : Path s) (A : Label) :
    (Γ.cons b).defAt (p.rename Rename.succ) A = (Γ.defAt p A).map (Ty.rename · Rename.succ) := by
  show ((Γ.cons b).nodeAt (p.rename Rename.succ)).bind (·.def A) =
    ((Γ.nodeAt p).bind (·.def A)).map (Ty.rename · Rename.succ)
  rw [Ctx.nodeAt_weaken]
  cases Γ.nodeAt p with
  | none => rfl
  | some B => exact Block.def_rename B Rename.succ A

/-! ## The block of a literal commutes with renaming and evidence substitution -/

mutual
theorem Defs.tyDefs_rename : ∀ (ds : Defs s₁) (ρ : Rename s₁ s₂),
    ds.tyDefs.rename ρ = (ds.rename ρ).tyDefs
  | .nil, _ => rfl
  | .typ ds A U, ρ => by
      simp only [Defs.tyDefs, Defs.rename, TyDefs.rename, Defs.tyDefs_rename ds ρ]
  | .fld ds _ _, ρ => by
      simp only [Defs.tyDefs, Defs.rename, Defs.tyDefs_rename ds ρ]
theorem Defs.kids_rename : ∀ (ds : Defs s₁) (ρ : Rename s₁ s₂),
    ds.kids.rename ρ = (ds.rename ρ).kids
  | .nil, _ => rfl
  | .typ ds _ _, ρ => by
      simp only [Defs.kids, Defs.rename, Defs.kids_rename ds ρ]
  | .fld ds a rhs, ρ => by
      simp only [Defs.kids, Defs.rename, Kids.rename, Defs.kids_rename ds ρ, Rhs.child_rename rhs ρ]
theorem Rhs.child_rename : ∀ (rhs : Rhs s₁) (ρ : Rename s₁ s₂),
    rhs.child.rename ρ = (rhs.rename ρ).child
  | .path P, ρ => by
      simp only [Rhs.child, Rhs.rename, Block.rename, PathCo.path_rename]
  | .fn _, _ => rfl
  | .nest _ ds, ρ => by
      simp only [Rhs.child, Rhs.rename, Block.rename, Defs.tyDefs_rename ds ρ, Defs.kids_rename ds ρ]
end

mutual
theorem Defs.tyDefs_subst : ∀ (ds : Defs s₁) (σ : CoSubst s₁ s₂),
    ds.tyDefs.subst σ.paths = (ds.subst σ).tyDefs
  | .nil, _ => rfl
  | .typ ds A U, σ => by
      simp only [Defs.tyDefs, Defs.subst, TyDefs.subst, Defs.tyDefs_subst ds σ]
  | .fld ds _ _, σ => by
      simp only [Defs.tyDefs, Defs.subst, Defs.tyDefs_subst ds σ]
theorem Defs.kids_subst : ∀ (ds : Defs s₁) (σ : CoSubst s₁ s₂),
    ds.kids.subst σ.paths = (ds.subst σ).kids
  | .nil, _ => rfl
  | .typ ds _ _, σ => by
      simp only [Defs.kids, Defs.subst, Defs.kids_subst ds σ]
  | .fld ds a rhs, σ => by
      simp only [Defs.kids, Defs.subst, Kids.subst, Defs.kids_subst ds σ, Rhs.child_subst rhs σ]
theorem Rhs.child_subst : ∀ (rhs : Rhs s₁) (σ : CoSubst s₁ s₂),
    rhs.child.subst σ.paths = (rhs.subst σ).child
  | .path P, σ => by
      simp only [Rhs.child, Rhs.subst, Block.subst, PathCo.path_subst]
  | .fn _, _ => rfl
  | .nest _ ds, σ => by
      simp only [Rhs.child, Rhs.subst, Block.subst, Defs.tyDefs_subst ds σ, Defs.kids_subst ds σ]
end

/-- The plan's `block_rename`: the block of a literal renames with the literal. -/
theorem Defs.block_rename (ds : Defs s₁) (ρ : Rename s₁ s₂) : ds.block.rename ρ = (ds.rename ρ).block := by
  simp only [Defs.block, Block.rename, Defs.tyDefs_rename, Defs.kids_rename]

theorem Defs.block_subst (ds : Defs s₁) (σ : CoSubst s₁ s₂) : ds.block.subst σ.paths = (ds.subst σ).block := by
  simp only [Defs.block, Block.subst, Defs.tyDefs_subst, Defs.kids_subst]

end PDot.FCp
