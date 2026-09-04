import Coercions.FCdot.Typing

/-!
# FCdot stores

A store holds literals, one per allocated binder.  Store typing types each
entry in the transparent context of the entries before it.
-/

namespace FCdot

/-! ## Stores -/

inductive Store : Sig → Type where
  | nil : Store []
  | cons : Store s → Value s → Store (s,x)

/-- The value stored at a binder, weakened into the current scope. -/
def Store.lookup : Store s → BVar s .var → Value s
  | .cons _ v, .here => v.weaken
  | .cons σ _, .there y => (σ.lookup y).weaken

/-- Block witnesses of a value: those of the underlying literal. -/
def Value.witnesses : Value s → Witnesses (s,x)
  | .lam _ _ => .nil
  | .obj W _ => W
  | .cast v _ => v.witnesses

/-- Field labels of a value: those of the underlying literal. -/
def Value.fieldLabels : Value s → List Label
  | .lam _ _ => []
  | .obj _ F => F.labels
  | .cast v _ => v.fieldLabels

/-- The literal under the cast wrappers. -/
def Value.core : Value s → Value s
  | .cast v _ => v.core
  | v => v

/-- The cast wrappers of a value, innermost first. -/
def Value.coercions : Value s → List (LeCo s)
  | .cast v e => v.coercions ++ [e]
  | _ => []

/-- The cast wrappers of an atom, innermost first. -/
def Atom.coercions : Atom s → List (LeCo s)
  | .var _ => []
  | .cast a e => a.coercions ++ [e]
  | .foldSelf _ a => a.coercions
  | .unfoldSelf a => a.coercions

/-- A stored value is a literal: no cast wrappers. -/
def Value.IsLiteral : Value s → Prop
  | .cast _ _ => False
  | _ => True

set_option hygiene false in
scoped notation:40 "⊢ " σ:51 " : " Γ:51 => Store.Typed σ Γ

/-- `⊢ σ : Γ`, store typing: every entry is a literal typed in the transparent
context of the entries before it, and the context records its witnesses and
fields. -/
inductive Store.Typed : Store s → Ctx s → Prop where
  | nil : ⊢ .nil : .nil
  | cons :
      ⊢ σ : Γ →
      v.IsLiteral →
      Γ ⊢ᵥ v : T →
      ⊢ .cons σ v : .cons Γ (.transparent T v.witnesses v.fieldLabels)

open Lean PrettyPrinter in
@[app_unexpander Store.Typed] def Store.Typed.unexpand : Unexpander
  | `($_ $σ $Γ) => `(⊢ $σ : $Γ)
  | _ => throw ()


end FCdot
