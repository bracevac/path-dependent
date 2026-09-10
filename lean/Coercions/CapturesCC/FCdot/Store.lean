import Coercions.CapturesCC.FCdot.Levels
import Coercions.CapturesCC.FCdot.Typing

namespace CapturesCC

/-!
# FCdot stores

A store holds literals, one per allocated binder, and a capture slot per
capture binder.  Store typing types each entry in the transparent context of
the entries before it; a capture slot carries its bound and no obligation,
since a capture binder has no runtime content.
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

/-- The value stored at a binder, weakened into the current scope. -/
def Store.lookup : Store s → BVar s .var → Value s
  | .cons _ v, .here => v.weaken
  | .cons σ _, .there y => (σ.lookup y).weaken
  | .consC σ _, .there y => (σ.lookup y).weaken

/-- Block witnesses of a value: those of the underlying literal. -/
def Value.witnesses : Value s → Witnesses (s,x)
  | .lam _ _ _ _ => .nil
  | .obj _ W _ _ => W
  | .box _ => .nil
  | .cast v _ => v.witnesses

/-- Capture witnesses of a value: those of the underlying literal. -/
def Value.capWitnesses : Value s → CapWitnesses (s,x)
  | .lam _ _ _ _ => .nil
  | .obj _ _ Wc _ => Wc
  | .box _ => .nil
  | .cast v _ => v.capWitnesses

/-- Field labels of a value: those of the underlying literal. -/
def Value.fieldLabels : Value s → List Label
  | .lam _ _ _ _ => []
  | .obj _ _ _ F => F.labels
  | .box _ => []
  | .cast v _ => v.fieldLabels

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
  | consC
      (store : ⊢ σ : Γ)
      (hb : b.isRoot = false) :
      ⊢ .consC σ b : .consC Γ b

/-- **T-B0.7.**  A store context has no scope root: a store binds
capabilities, never scopes.  This is O9's reserved slot, used for the first
time by the premise of `Store.Typed.consC`.  It lives beside the judgement it
inducts on, because the four entering steps of the machine consume it. -/
theorem Store.Typed.rootFree (hσ : ⊢ σ : Γ) : Γ.root? = none := by
  induction hσ with
  | nil => rfl
  | cons _ _ _ ih => rw [Ctx.root?_cons, ih]; rfl
  | consC _ hb ih => rw [Ctx.root?_consC_of_not_root _ _ hb, ih]; rfl

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
  | @consC _ σ0 Γ0 _ _ _ ih =>
      cases x with
      | there y =>
          show ((Γ0.lookupTy y)↑).captureSet = ((σ0.lookup y)↑).annot
          rw [Ty.captureSet_weaken, Value.annot_weaken, ih y]


end FCdot

end CapturesCC
