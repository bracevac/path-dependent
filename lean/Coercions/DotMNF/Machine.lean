import Coercions.DotMNF.Typing

/-!
# DOT-MNF store machine

A state is a store of values, a continuation of `let` frames, and a running
term, all indexed by one signature.  Allocation extends the signature; every
substitution performed by the machine is a renaming, so no substitution
operation beyond `rename` is needed.

This is Plan III §3.5 verbatim:

```text
⟨σ, K, let x = t in u⟩                       ⟶  ⟨σ, K ▹ (x. u), t⟩
⟨σ, K ▹ (x. u), v⟩                           ⟶  ⟨σ, v ; K↑, u⟩
⟨σ, K ▹ (x. u), y⟩                           ⟶  ⟨σ, K, u[x := y]⟩
⟨σ, K, x y⟩       σ(x) = λ(z : T) t          ⟶  ⟨σ, K, t[z := y]⟩
⟨σ, K, x.a⟩       σ(x) = ν(z. d), d ∋ {a = t} ⟶  ⟨σ, K, t[z := x]⟩
```
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Stores -/

/-- A store: one value per binder of the signature. -/
inductive Store : Sig → Type where
  | nil : Store []
  | cons : Store s → Value s → Store (s,x)

/-- The value stored at a binder, weakened into the current scope. -/
def Store.lookup : Store s → BVar s .var → Value s
  | .cons _ v, .here => v.weaken
  | .cons σ _, .there y => (σ.lookup y).weaken

/-! ## Continuations -/

/-- A continuation: frames `let x = □ in u`, innermost last. -/
inductive Cont : Sig → Type where
  | nil : Cont s
  | cons : Cont s → Tm (s,x) → Cont s

def Cont.rename : Cont s1 → Rename s1 s2 → Cont s2
  | .nil, _ => .nil
  | .cons K u, ρ => .cons (K.rename ρ) (u.rename ρ.lift)

/-- Weaken a continuation under a newly allocated store binder. -/
def Cont.weaken (K : Cont s) : Cont (s,x) := K.rename Rename.succ

/-! ## States and steps -/

structure State (s : Sig) where
  σ : Store s
  K : Cont s
  t : Tm s

/-- The reduction relation.  `alloc` is the only rule that changes the
signature. -/
inductive Step : State s → State s' → Prop where
  /-- Push a `let` frame. -/
  | «let» : Step ⟨σ, K, .let t u⟩ ⟨σ, .cons K u, t⟩
  /-- Allocate a value answer in the store. -/
  | alloc : Step ⟨σ, .cons K u, .val v⟩ ⟨.cons σ v, K.weaken, u⟩
  /-- A path answer is consumed by a renaming. -/
  | rename : Step ⟨σ, .cons K u, .path (.var y)⟩ ⟨σ, K, u.substVar y⟩
  /-- Application: look the closure up in the store. -/
  | app : σ.lookup x = .lam S t → Step ⟨σ, K, .app x y⟩ ⟨σ, K, t.substVar y⟩
  /-- Selection: look the object up in the store and instantiate the field's
      self binder by the receiver. -/
  | proj :
      σ.lookup x = .obj d → d.lookupTrm a = some t →
      Step ⟨σ, K, .proj x a⟩ ⟨σ, K, t.substVar x⟩

/-- Reflexive transitive closure, across signatures. -/
inductive Steps : State s → State s' → Prop where
  | refl : Steps st st
  | tail : Steps st st' → Step st' st'' → Steps st st''

/-- Answers with an empty continuation are final. -/
def State.Final (st : State s) : Prop :=
  st.K = .nil ∧ ((∃ v, st.t = .val v) ∨ (∃ p, st.t = .path p))

def State.Stuck (st : State s) : Prop :=
  ¬ st.Final ∧ ¬ ∃ s', ∃ st' : State s', Step st st'

end DotMNF
