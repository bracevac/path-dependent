import Coercions.Captures.FCdot.Typing

namespace Captures

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
  | .lam _ _ => .nil
  | .obj W _ _ => W
  | .box _ => .nil
  | .cast v _ => v.witnesses

/-- Capture witnesses of a value: those of the underlying literal. -/
def Value.capWitnesses : Value s → CapWitnesses (s,x)
  | .lam _ _ => .nil
  | .obj _ Wc _ => Wc
  | .box _ => .nil
  | .cast v _ => v.capWitnesses

/-- Field labels of a value: those of the underlying literal. -/
def Value.fieldLabels : Value s → List Label
  | .lam _ _ => []
  | .obj _ _ F => F.labels
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
fields.  A capture slot records its bound and carries no obligation. -/
inductive Store.Typed : Store s → Ctx s → Prop where
  | nil : ⊢ .nil : .nil
  | cons
      (store : ⊢ σ : Γ)
      (literal : v.IsLiteral)
      (value : Γ ⊢ᵥ v : T) :
      ⊢ .cons σ v : .cons Γ (.transparent T v.witnesses v.capWitnesses v.fieldLabels)
  | consC
      (store : ⊢ σ : Γ) :
      ⊢ .consC σ b : .consC Γ b

open Lean PrettyPrinter in
@[app_unexpander Store.Typed] def Store.Typed.unexpand : Unexpander
  | `($_ $σ $Γ) => `(⊢ $σ : $Γ)
  | _ => throw ()


end FCdot

end Captures
