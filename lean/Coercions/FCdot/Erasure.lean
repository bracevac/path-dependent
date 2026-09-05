import Coercions.FCdot.Machine
import Coercions.Runtime

/-!
# Erasure of FCdot into the shared runtime

Atoms erase to their root variable, casts and evidence vanish, object
literals keep only their fields.  Cast frames erase to nothing.
-/

namespace FCdot

mutual

def Tm.erase : Tm s → Runtime.Tm s
  | .atom a => .var a.root
  | .val v => v.erase
  | .app a b => .app a.root b.root
  | .proj a ℓ _ => .proj a.root ℓ
  | .let t u => .let t.erase u.erase
  | .cast t _ => t.erase

def Value.erase : Value s → Runtime.Tm s
  | .lam _ t => .lam t.erase
  | .obj _ F => .obj F.erase
  | .cast v _ => v.erase

def Fields.erase : Fields s → Runtime.Fields s
  | .nil => .nil
  | .cons F ℓ t => .cons F.erase ℓ t.erase

end

def Store.erase : Store s → Runtime.Store s
  | .nil => .nil
  | .cons σ v => .cons σ.erase v.erase

def Cont.erase : Cont s → Runtime.Cont s
  | .nil => .nil
  | .cons K (.let u) => .cons K.erase u.erase
  | .cons K (.cast _) => K.erase

def State.erase (st : State s) : Runtime.State s :=
  ⟨st.σ.erase, st.K.erase, st.t.erase⟩

/-! ### Notation: `⌊t⌋` erases a term, value, store, continuation, or state. -/

scoped notation:max "⌊" t "⌋" => Tm.erase t
scoped notation:max "⌊" v "⌋" => Value.erase v
scoped notation:max "⌊" σ "⌋" => Store.erase σ
scoped notation:max "⌊" K "⌋" => Cont.erase K
scoped notation:max "⌊" st "⌋" => State.erase st

/-- States whose next step only moves a cast frame; such steps erase to no
runtime step. -/
def State.CastRedex (st : State s) : Prop :=
  (∃ t e, st.t = .cast t e) ∨
  (∃ K e, st.K = .cons K (.cast e) ∧ ((∃ v, st.t = .val v) ∨ (∃ a, st.t = .atom a)))

/-- The executable test for `State.CastRedex`. -/
def State.isCastRedex (st : State s) : Bool :=
  match st.t, st.K with
  | .cast _ _, _ => true
  | .val _, .cons _ (.cast _) => true
  | .atom _, .cons _ (.cast _) => true
  | _, _ => false

theorem State.isCastRedex_iff (st : State s) : st.isCastRedex = true ↔ st.CastRedex := by
  obtain ⟨σ, K, t⟩ := st
  rcases K with _ | ⟨K, f⟩
  · cases t <;> simp [State.isCastRedex, State.CastRedex]
  · cases f <;> cases t <;> simp [State.isCastRedex, State.CastRedex]

/-- Whether a state is about to move a cast frame is decidable, so the case
splits of progress and of the backward simulation need no choice. -/
instance (st : State s) : Decidable st.CastRedex :=
  decidable_of_decidable_of_iff (State.isCastRedex_iff st)

end FCdot
