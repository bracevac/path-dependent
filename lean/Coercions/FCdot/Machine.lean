import Coercions.FCdot.Canonical

/-!
# FCdot store machine

States are a store of literals, a continuation of frames, and a running
term, all indexed by one signature.  Allocation extends the signature.
Casts on values are wrappers: allocation strips them, stores the literal at
its own type, and rewrites the continuation so that the new variable is used
under the composite cast.  Application on a coerced closure reads the
domain and codomain evidence off the head normal form of the atom's casts
(`Canonical.lean`).  Progress needs that this normalization succeeds on a
closed atom of function type, and preservation needs the resulting evidence
to be typed; both are consequences of the canonical-forms theorem.
-/

namespace FCdot

/-! ## Continuations -/

inductive Frame : Sig → Type where
  | «let» : Tm (s,x) → Frame s
  | cast : LeCo s → Frame s

def Frame.rename : Frame s1 → Rename s1 s2 → Frame s2
  | .let u, ρ => .let (u.rename ρ.lift)
  | .cast e, ρ => .cast (e.rename ρ)

/-- Continuation: frames, innermost last. -/
inductive Cont : Sig → Type where
  | nil : Cont s
  | cons : Cont s → Frame s → Cont s

def Cont.rename : Cont s1 → Rename s1 s2 → Cont s2
  | .nil, _ => .nil
  | .cons K f, ρ => .cons (K.rename ρ) (f.rename ρ)

def Cont.weaken (K : Cont s) : Cont (s,x) := K.rename Rename.succ

/-- `Cont.Typed Γ K T U`: `K` accepts a value of type `T` and produces `U`. -/
inductive Cont.Typed : Ctx s → Cont s → Ty s → Ty s → Prop where
  | nil : Cont.Typed Γ .nil T T
  | «let» :
      Tm.HasType (Γ.cons (.opaque T)) u U.weaken →
      Cont.Typed Γ K U V →
      Cont.Typed Γ (.cons K (.let u)) T V
  | cast :
      LeCo.HasType Γ e T U →
      Cont.Typed Γ K U V →
      Cont.Typed Γ (.cons K (.cast e)) T V

/-! ## States -/

structure State (s : Sig) where
  σ : Store s
  K : Cont s
  t : Tm s

/-- A state is typed when its store is typed in a transparent context in
which the term and continuation are typed. -/
def State.Typed (st : State s) (U : Ty s) : Prop :=
  ∃ (Γ : Ctx s) (T : Ty s),
    Store.Typed st.σ Γ ∧ Tm.HasType Γ st.t T ∧ Cont.Typed Γ st.K T U

def State.Final (st : State s) : Prop :=
  st.K = .nil ∧ (∃ v, st.t = .val v) ∨ st.K = .nil ∧ (∃ a, st.t = .atom a)

/-- Fold a nonempty list of coercions into one, oldest first. -/
def LeCo.composite (e : LeCo s) : List (LeCo s) → LeCo s
  | [] => e
  | f :: fs => LeCo.composite (.trans e f) fs

/-- The composite of a value's wrappers, if any. -/
def Value.composite? (v : Value s) : Option (LeCo s) :=
  match v.coercions with
  | [] => none
  | e :: es => some (LeCo.composite e es)

/-- Adjust a continuation body to a stripped value: if the value carried
casts, every use of the new variable goes under their composite. -/
def Tm.adjust (u : Tm (s,x)) (v : Value s) : Tm (s,x) :=
  match v.composite? with
  | none => u
  | some E => u.subst (Subst.selfCast E.weaken)

/-- Substitute the self binder of a stored object's field by the object's variable. -/
def Tm.selfAt (t : Tm (s,x)) (y : BVar s .var) : Tm s := t.rename (Rename.subst y)

/-! ## Steps -/

/-- Contexts in which a step's evidence side conditions are checked: the
transparent context of the current store. -/
inductive Step : State s → State s' → Prop where
  | «let» :
      Step ⟨σ, K, .let t u⟩ ⟨σ, .cons K (.let u), t⟩
  | castPush :
      Step ⟨σ, K, .cast t e⟩ ⟨σ, .cons K (.cast e), t⟩
  | castVal :
      Step ⟨σ, .cons K (.cast e), .val v⟩ ⟨σ, K, .val (.cast v e)⟩
  | castAtom :
      Step ⟨σ, .cons K (.cast e), .atom a⟩ ⟨σ, K, .atom (.cast a e)⟩
  | alloc :
      Step ⟨σ, .cons K (.let u), .val v⟩ ⟨.cons σ v.core, K.weaken, u.adjust v⟩
  | rename :
      Step ⟨σ, .cons K (.let u), .atom a⟩ ⟨σ, K, u.substAtom a⟩
  /-- Application through a bare variable. -/
  | appVar :
      σ.lookup x = .lam S₀ t₀ →
      Step ⟨σ, K, .app (.var x) b⟩ ⟨σ, K, t₀.substAtom b⟩
  /-- Application through a wrapped atom whose casts normalize to the
      identity: the atom's function type and the closure's coincide. -/
  | appCastRefl :
      σ.lookup a.root = .lam S₀ t₀ →
      a ≠ .var a.root →
      closedAtomForm σ n a = some (a', F) →
      (F = .id ∨ ∃ φ, F = .eqv φ) →
      Step ⟨σ, K, .app a b⟩ ⟨σ, K, t₀.substAtom b⟩
  /-- Application through a wrapped atom whose casts normalize to a function
      coercion `pi d c`: the argument is cast by `d` and the result by `c` at
      the argument. -/
  | appCast :
      σ.lookup a.root = .lam S₀ t₀ →
      a ≠ .var a.root →
      closedAtomForm σ n a = some (a', .pi d c) →
      Step ⟨σ, K, .app a b⟩
        ⟨σ, K, .cast (t₀.substAtom (.cast b d)) (c.subst (Subst.single b))⟩
  | proj :
      σ.lookup a.root = .obj Tel W E F →
      F.get? ℓ = some t →
      Step ⟨σ, K, .proj a ℓ h⟩ ⟨σ, K, t.selfAt a.root⟩

/-- Reflexive transitive closure across signatures. -/
inductive Steps : State s → State s' → Prop where
  | refl : Steps st st
  | tail : Steps st st' → Step st' st'' → Steps st st''

def State.Stuck (st : State s) : Prop :=
  ¬ st.Final ∧ ¬ ∃ s', ∃ st' : State s', Step st st'

end FCdot
