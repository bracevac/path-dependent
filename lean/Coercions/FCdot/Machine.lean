import Coercions.FCdot.Normalizer

/-!
# FCdot store machine

States are a store of literals, a continuation of frames, and a running
term, all indexed by one signature.  Allocation extends the signature.
Casts on values are wrappers: allocation strips them, stores the literal at
its own type, and rewrites the continuation so that the new variable is used
under the composite cast.  Application on a coerced closure reads the
domain and codomain evidence off the head normal form of the atom's casts
(`Normalizer.lean`).  Progress needs that this normalization succeeds on a
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

scoped postfix:max "↑" => Cont.weaken

scoped infixl:65 " ▹ " => Cont.cons

set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ₖ " K:51 " : " T:51 " ⇒ " U:51 => Cont.Typed Γ K T U

/-- `Γ ⊢ₖ K : T ⇒ U`: `K` accepts a value of type `T` and produces `U`. -/
inductive Cont.Typed : Ctx s → Cont s → Ty s → Ty s → Prop where
  | nil : Γ ⊢ₖ .nil : T ⇒ T
  | «let» :
      Γ.cons (.opaque T) ⊢ u : U↑ →
      Γ ⊢ₖ K : U ⇒ V →
      Γ ⊢ₖ K ▹ .let u : T ⇒ V
  | cast :
      Γ ⊢ e : T ≤ U →
      Γ ⊢ₖ K : U ⇒ V →
      Γ ⊢ₖ K ▹ .cast e : T ⇒ V

open Lean PrettyPrinter in
@[app_unexpander Cont.Typed] def Cont.Typed.unexpand : Unexpander
  | `($_ $Γ $K $T $U) => `($Γ ⊢ₖ $K : $T ⇒ $U)
  | _ => throw ()

/-! ## States -/

structure State (s : Sig) where
  σ : Store s
  K : Cont s
  t : Tm s

/-- A state is typed when its store is typed in a transparent context in
which the term and continuation are typed. -/
def State.Typed (st : State s) (U : Ty s) : Prop :=
  ∃ (Γ : Ctx s) (T : Ty s),
    ⊢ st.σ : Γ ∧ Γ ⊢ st.t : T ∧ Γ ⊢ₖ st.K : T ⇒ U

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

set_option hygiene false in
scoped infix:40 " ⟶ " => Step
set_option hygiene false in
scoped infix:40 " ⟶* " => Steps

/-- `st ⟶ st'`.  Contexts in which a step's evidence side conditions are
checked: the transparent context of the current store. -/
inductive Step : State s → State s' → Prop where
  | «let» :
      ⟨σ, K, .let t u⟩ ⟶ ⟨σ, K ▹ .let u, t⟩
  | castPush :
      ⟨σ, K, .cast t e⟩ ⟶ ⟨σ, K ▹ .cast e, t⟩
  | castVal :
      ⟨σ, K ▹ .cast e, .val v⟩ ⟶ ⟨σ, K, .val (.cast v e)⟩
  | castAtom :
      ⟨σ, K ▹ .cast e, .atom a⟩ ⟶ ⟨σ, K, .atom (.cast a e)⟩
  | alloc :
      ⟨σ, K ▹ .let u, .val v⟩ ⟶ ⟨.cons σ v.core, K.weaken, u.adjust v⟩
  | rename :
      ⟨σ, K ▹ .let u, .atom a⟩ ⟶ ⟨σ, K, u.substAtom a⟩
  /-- Application through a bare variable. -/
  | appVar :
      σ.lookup x = .lam S₀ t₀ →
      ⟨σ, K, .app (.var x) b⟩ ⟶ ⟨σ, K, t₀.substAtom b⟩
  /-- Application through a wrapped atom whose casts normalize to the
      identity: the atom's function type and the closure's coincide. -/
  | appCastRefl :
      σ.lookup a.root = .lam S₀ t₀ →
      a ≠ .var a.root →
      σ ⊢ a ⇓ᶜ[n] (a', F) →
      (F = .id ∨ ∃ φ, F = .eqv φ) →
      ⟨σ, K, .app a b⟩ ⟶ ⟨σ, K, t₀.substAtom b⟩
  /-- Application through a wrapped atom whose casts normalize to a function
      coercion `pi d c`: the argument is cast by `d` and the result by `c` at
      the argument. -/
  | appCast :
      σ.lookup a.root = .lam S₀ t₀ →
      a ≠ .var a.root →
      σ ⊢ a ⇓ᶜ[n] (a', .pi d c) →
      ⟨σ, K, .app a b⟩ ⟶
        ⟨σ, K, .cast (t₀.substAtom (.cast b d)) (c.subst (Subst.single b))⟩
  | proj :
      σ.lookup a.root = .obj W F →
      F.get? ℓ = some t →
      ⟨σ, K, .proj a ℓ h⟩ ⟶ ⟨σ, K, t.selfAt a.root⟩

/-- `st ⟶* st'`: reflexive transitive closure across signatures. -/
inductive Steps : State s → State s' → Prop where
  | refl : st ⟶* st
  | tail : st ⟶* st' → st' ⟶ st'' → st ⟶* st''

open Lean PrettyPrinter in
@[app_unexpander Step] def Step.unexpand : Unexpander
  | `($_ $st $st') => `($st ⟶ $st')
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Steps] def Steps.unexpand : Unexpander
  | `($_ $st $st') => `($st ⟶* $st')
  | _ => throw ()

def State.Stuck (st : State s) : Prop :=
  ¬ st.Final ∧ ¬ ∃ s', ∃ st' : State s', Step st st'

end FCdot
