import Coercions.Separation.FCdot.Levels
import Coercions.Separation.FCdot.Typing

namespace Separation

/-!
# FCdot stores

A store holds literals, one per allocated binder, and a capture slot per
capture binder.  Store typing types each entry in the transparent context of
the entries before it; a capture slot carries its bound and no obligation,
since a capture binder has no runtime content.  A write record binds nothing:
it appends the new content of a cell, and the content of a cell is its newest
record (plan-5h S0.6).
-/

namespace FCdot

/-! ## Stores -/

/-- A store: a literal per term binder, a capture bound per capture binder.
(`consᶜ` of the plan: `ᶜ` is not a legal Lean identifier character, so the
capture-sort twin of a name carries the suffix `C`.) -/
inductive Store : Sig → Type where
  | nil : Store []
  | cons : Store s → Value s → Store (s,x)
  | consC : Store s → CapBound s → Store (s,c)
  /-- A write record.  It binds nothing, and the cell and the content are
      binders of the signature it lives in, so a stored value mentions only
      older binders by the type of the constructor. -/
  | write : Store s → BVar s .var → Atom s → Store s

/-- The value stored at a binder, weakened into the current scope.  A write
record passes the lookup on: it changes the content of a cell, not the value
stored at its binder. -/
def Store.lookup : Store s → BVar s .var → Value s
  | .cons _ v, .here => v.weaken
  | .cons σ _, .there y => (σ.lookup y).weaken
  | .consC σ _, .there y => (σ.lookup y).weaken
  | .write σ _ _, y => σ.lookup y

/-- The content of a cell: its newest write record, else its first
content. -/
def Store.content : Store s → BVar s .var → Option (Atom s)
  | .nil, _ => none
  | .cons _ (.cell _ a), .here => some a.weaken
  | .cons _ _, .here => none
  | .cons σ _, .there y => (σ.content y).map Atom.weaken
  | .consC σ _, .there y => (σ.content y).map Atom.weaken
  | .write σ r a, y => if y = r then some a else σ.content y

/-- A write record at one cell leaves the content of every other cell as it
was (the frame property of the write log). -/
theorem Store.content_write_ne {σ : Store s} {r y : BVar s .var} {a : Atom s}
    (h : y ≠ r) : (σ.write r a).content y = σ.content y := by
  simp [Store.content, h]

/-- A write record at a cell is its content. -/
theorem Store.content_write_eq (σ : Store s) (r : BVar s .var) (a : Atom s) :
    (σ.write r a).content r = some a := by
  simp [Store.content]

/-- The cell a read at `x` reads: `x` itself, or the cell under a reader. -/
def Store.cellOf (σ : Store s) (x : BVar s .var) : Option (BVar s .var) :=
  match σ.lookup x with
  | .cell _ _ => some x
  | .reader r => some r
  | _ => none

/-- Block witnesses of a value: those of the underlying literal. -/
def Value.witnesses : Value s → Witnesses (s,x)
  | .lam _ _ _ _ => .nil
  | .obj _ W _ _ => W
  | .box _ => .nil
  | .cast v _ => v.witnesses
  | .pack _ _ _ v => v.witnesses
  | .cell _ _ => .nil
  | .reader _ => .nil
  | .packF _ _ v => v.witnesses

/-- Capture witnesses of a value: those of the underlying literal. -/
def Value.capWitnesses : Value s → CapWitnesses (s,x)
  | .lam _ _ _ _ => .nil
  | .obj _ _ Wc _ => Wc
  | .box _ => .nil
  | .cast v _ => v.capWitnesses
  | .pack _ _ _ v => v.capWitnesses
  | .cell _ _ => .nil
  | .reader _ => .nil
  | .packF _ _ v => v.capWitnesses

/-- Field labels of a value: those of the underlying literal. -/
def Value.fieldLabels : Value s → List Label
  | .lam _ _ _ _ => []
  | .obj _ _ _ F => F.labels
  | .box _ => []
  | .cast v _ => v.fieldLabels
  | .pack _ _ _ v => v.fieldLabels
  | .cell _ _ => []
  | .reader _ => []
  | .packF _ _ v => v.fieldLabels

/-- The literal under the cast wrappers. -/
def Value.core : Value s → Value s
  | .cast v _ => v.core
  | v => v

/-- The cast wrappers of a value, innermost first. -/
def Value.coercions : Value s → List (LeCo s)
  | .cast v e => v.coercions ++ [e]
  | _ => []

/-- The cast wrappers of an atom, innermost first (along the first component
of an intersection).  A recapturing wrapper carries no type inclusion. -/
def Atom.coercions : Atom s → List (LeCo s)
  | .var _ => []
  | .cast a e => a.coercions ++ [e]
  | .foldSelf _ a => a.coercions
  | .unfoldSelf a => a.coercions
  | .both _ _ a _ => a.coercions
  | .recap a _ => a.coercions

/-- A stored value is a literal: no cast wrappers. -/
def Value.IsLiteral : Value s → Prop
  | .cast _ _ => False
  | _ => True

/-- Being a literal is stable under renaming.  A pack falls into the
catch-all of `Value.IsLiteral`, as a literal does. -/
theorem Value.isLiteral_rename {s1 s2 : Sig} :
    ∀ (v : Value s1) (ρ : Rename s1 s2), v.IsLiteral → (v.rename ρ).IsLiteral
  | .lam _ _ _ _, _, _ => trivial
  | .obj _ _ _ _, _, _ => trivial
  | .box _, _, _ => trivial
  | .pack _ _ _ _, _, _ => trivial
  | .cell _ _, _, _ => trivial
  | .reader _, _, _ => trivial
  | .packF _ _ _, _, _ => trivial
  | .cast _ _, _, h => h.elim

set_option hygiene false in
scoped notation:40 "⊢ " σ:51 " : " Γ:51 => Store.Typed σ Γ

/-- `⊢ σ : Γ`, store typing: every entry is a literal typed in the transparent
context of the entries before it, and the context records its witnesses and
fields.  A capture slot records its bound and carries no obligation beyond
being a capability and not a scope: a store binds capabilities, never
scopes, so a store context has no root binder. -/
inductive Store.Typed : Store s → Ctx s → Prop where
  | nil : ⊢ .nil : .nil
  | cons
      (store : ⊢ σ : Γ)
      (literal : v.IsLiteral)
      (value : Γ ⊢ᵥ v : T) :
      ⊢ .cons σ v : .cons Γ (.transparent T v.witnesses v.capWitnesses v.fieldLabels)
  /-- A capture slot is no root and is live: a store kills nothing (plan-5h
      decision 38). -/
  | consC
      (store : ⊢ σ : Γ)
      (hb : b.isRoot = false)
      (hl : b.live = true) :
      ⊢ .consC σ b : .consC Γ b
  /-- A write keeps the context: a cell's type does not move when its
      content does. -/
  | write
      (store : ⊢ σ : Γ)
      (cell : Γ.lookupTy r = (Shape.cell T) ^ [CapAtom.cvar ℓ])
      (content : Γ ⊢ₐ a : T) :
      ⊢ .write σ r a : Γ

/-- **T-B0.7.**  A store context has no scope root: a store binds
capabilities, never scopes.  This is O9's reserved slot, used for the first
time by the premise of `Store.Typed.consC`.  It lives beside the judgement it
inducts on, because the four entering steps of the machine consume it. -/
theorem Store.Typed.rootFree (hσ : ⊢ σ : Γ) : Γ.root? = none := by
  induction hσ with
  | nil => rfl
  | cons _ _ _ ih => rw [Ctx.root?_cons, ih]; rfl
  | consC _ hb _ ih => rw [Ctx.root?_consC_of_not_root _ _ hb, ih]; rfl
  | write _ _ _ ih => exact ih

/-- Entries of a typed store are literals, in any scope.  It stands here
rather than in `ErasureMetatheory.lean`, where the vanilla line keeps it,
because it reads no erasure and `CanonicalForms.lean` needs it. -/
theorem Store.Typed.lookup_isLiteral {s : Sig} {σ : Store s} {Γ : Ctx s}
    (h : ⊢ σ : Γ) : ∀ x : BVar s .var, (σ.lookup x).IsLiteral := by
  induction h with
  | nil => intro x; cases x
  | cons _ hlit _ ih =>
      intro x
      cases x with
      | here => exact Value.isLiteral_rename _ _ hlit
      | there y => exact Value.isLiteral_rename _ _ (ih y)
  | consC _ _ _ ih =>
      intro x
      cases x with
      | there y => exact Value.isLiteral_rename _ _ (ih y)
  | write _ _ _ ih => exact ih

/-- **A store kills nothing**: every capture binder of a store context is
live.  It is the `allLive` clause of `Ctx.SepInv`, read off store typing. -/
theorem Store.Typed.allLive {s : Sig} {σ : Store s} {Γ : Ctx s} (h : ⊢ σ : Γ) :
    ∀ κ, (Γ.lookupCap κ).live = true := by
  induction h with
  | nil => intro κ; cases κ
  | cons _ _ _ ih =>
      intro κ
      cases κ with
      | there κ₀ =>
          show (CapBound.weaken _).live = true
          rw [CapBound.live_weaken]; exact ih κ₀
  | consC _ _ hl ih =>
      intro κ
      cases κ with
      | here =>
          show (CapBound.weaken _).live = true
          rw [CapBound.live_weaken]; exact hl
      | there κ₀ =>
          show (CapBound.weaken _).live = true
          rw [CapBound.live_weaken]; exact ih κ₀
  | write _ _ _ ih => exact ih

open Lean PrettyPrinter in
@[app_unexpander Store.Typed] def Store.Typed.unexpand : Unexpander
  | `($_ $σ $Γ) => `(⊢ $σ : $Γ)
  | _ => throw ()

/-! ## The annotation of a stored value

A stored value is a literal, and the introduction rule of a literal types it
at its own annotation.  So the capture set of a binder's type in a typed
store's context is the annotation of the value stored at that binder, and
`roots {x}` is the roots of that annotation. -/

/-- The annotation of a value travels with a renaming. -/
theorem Value.annot_rename {s1 s2 : Sig} :
    ∀ (v : Value s1) (ρ : Rename s1 s2), (v.rename ρ).annot = v.annot.rename ρ
  | .lam _ _ _ _, _ => rfl
  | .obj _ _ _ _, _ => rfl
  | .box _, _ => rfl
  | .cast v _, ρ => Value.annot_rename v ρ
  | .pack _ _ _ v, ρ => Value.annot_rename v ρ
  | .cell _ _, _ => rfl
  | .reader _, _ => rfl
  | .packF _ _ v, ρ => Value.annot_rename v ρ

/-- The annotation of a value travels with a weakening. -/
@[simp] theorem Value.annot_weaken {k : Kind} (v : Value s) :
    (v.weaken (k := k)).annot = v.annot.weaken :=
  Value.annot_rename v Rename.succ

/-- A literal is typed at its own annotation: the capture set of its type is
the capture set its introduction rule assigns to it.  (A cast value is not a
literal, and a cast may change the capture set.) -/
theorem Value.HasType.captureSet_annot {Γ : Ctx s} {v : Value s} {T : Ty s}
    (h : Γ ⊢ᵥ v : T) (hl : v.IsLiteral) : T.captureSet = v.annot := by
  cases h with
  | lam _ _ => rfl
  | obj _ => rfl
  | box _ => rfl
  | cell _ _ _ => rfl
  | reader _ _ => rfl
  | cast _ _ => exact absurd hl (fun h => h)

/-- In a typed store, the capture set of a binder's type is the annotation of
the value stored at that binder, both read in the current scope. -/
theorem Store.Typed.lookup_annot {s : Sig} {σ : Store s} {Γ : Ctx s}
    (h : ⊢ σ : Γ) (x : BVar s .var) :
    (Γ.lookupTy x).captureSet = (σ.lookup x).annot := by
  induction h with
  | nil => cases x
  | @cons _ σ0 Γ0 v T _ literal value ih =>
      cases x with
      | here =>
          show (Ty.weaken (Binding.ty _)).captureSet = (Value.weaken v).annot
          rw [Ty.captureSet_weaken, Value.annot_weaken]
          exact congrArg CaptureSet.weaken (value.captureSet_annot literal)
      | there y =>
          show ((Γ0.lookupTy y)↑).captureSet = ((σ0.lookup y)↑).annot
          rw [Ty.captureSet_weaken, Value.annot_weaken, ih y]
  | @consC _ σ0 Γ0 _ _ _ _ ih =>
      cases x with
      | there y =>
          show ((Γ0.lookupTy y)↑).captureSet = ((σ0.lookup y)↑).annot
          rw [Ty.captureSet_weaken, Value.annot_weaken, ih y]
  | write _ _ _ ih => exact ih x


end FCdot

end Separation
