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
  | .proj a ℓ => .proj a.root ℓ
  | .let t u => .let t.erase u.erase
  | .cast t _ => t.erase

def Value.erase : Value s → Runtime.Tm s
  | .lam _ t => .lam t.erase
  | .obj _ _ _ F => .obj F.erase
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

/-- States whose next step only moves a cast frame; such steps erase to no
runtime step. -/
def State.CastRedex (st : State s) : Prop :=
  (∃ t e, st.t = .cast t e) ∨
  (∃ K e, st.K = .cons K (.cast e) ∧ ((∃ v, st.t = .val v) ∨ (∃ a, st.t = .atom a)))

end FCdot
