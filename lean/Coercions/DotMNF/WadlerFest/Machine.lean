import Coercions.DotMNF.WadlerFest.Syntax

/-!
# Store machine for annotated WadlerFest syntax

This machine uses an explicit store and a continuation of let frames, just
like `DotMNF.Machine`, while retaining object self annotations in values.
`Erasure.lean` relates this machine to the DOT-MNF store machine.
`OperationalCorrespondence.lean` relates its finite executions to the
retained-let reduction relation defined independently in `Reduction.lean`.
-/

namespace WadlerFest

open FCdot (Sig BVar Rename Label)

/-- Weaken a stored value into the scope of a new binder. -/
def Value.weaken (v : Value s) : Value (s,x) := v.rename Rename.succ

/-- Field lookup follows the rightmost definition, as in DOT-MNF. -/
def Defs.lookupTrm : Defs s → Label → Option (Tm s)
  | .typ _ _, _ => none
  | .trm a t, ℓ => if ℓ = a then some t else none
  | .and d₁ d₂, ℓ => (d₂.lookupTrm ℓ).or (d₁.lookupTrm ℓ)

inductive Store : Sig → Type where
  | nil : Store []
  | cons : Store s → Value s → Store (s,x)

def Store.lookup : Store s → BVar s .var → Value s
  | .cons _ v, .here => v.weaken
  | .cons σ _, .there x => (σ.lookup x).weaken

inductive Cont : Sig → Type where
  | nil : Cont s
  | cons : Cont s → Tm (s,x) → Cont s

def Cont.rename : Cont s₁ → Rename s₁ s₂ → Cont s₂
  | .nil, _ => .nil
  | .cons K u, ρ => .cons (K.rename ρ) (u.rename ρ.lift)

def Cont.weaken (K : Cont s) : Cont (s,x) := K.rename Rename.succ

structure State (s : Sig) where
  σ : Store s
  K : Cont s
  t : Tm s

/-- Allocation extends the signature. All substitutions replace a variable
by another variable, including the self substitution at projection. -/
inductive Step : State s → State s' → Prop where
  | «let» : Step ⟨σ, K, .let t u⟩ ⟨σ, .cons K u, t⟩
  | alloc : Step ⟨σ, .cons K u, .val v⟩ ⟨.cons σ v, K.weaken, u⟩
  | rename : Step ⟨σ, .cons K u, .path (.var y)⟩ ⟨σ, K, u.substVar y⟩
  | app : σ.lookup x = .lam S t →
      Step ⟨σ, K, .app x y⟩ ⟨σ, K, t.substVar y⟩
  | proj : σ.lookup x = .obj T d → d.lookupTrm a = some t →
      Step ⟨σ, K, .proj x a⟩ ⟨σ, K, t.substVar x⟩

inductive Steps : State s → State s' → Prop where
  | refl : Steps st st
  | tail : Steps st st' → Step st' st'' → Steps st st''

def State.Final (st : State s) : Prop :=
  st.K = .nil ∧ ((∃ v, st.t = .val v) ∨ (∃ p, st.t = .path p))

def State.Stuck (st : State s) : Prop :=
  ¬ st.Final ∧ ¬ ∃ s', ∃ st' : State s', Step st st'

end WadlerFest
