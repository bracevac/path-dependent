import Coercions.Captures.FCdot.Debruijn

namespace Captures

/-!
# Shared untyped runtime

One monadic-normal-form store machine that both the DOT-MNF source and the
FCdot target erase into.  Signatures are reused from `FCdot.Debruijn`.  Only
term binders carry runtime content; a capture binder has a store slot with no
data, so that erasure maps slot to slot.
-/

namespace Runtime

open FCdot (Kind Sig BVar Rename Label)

mutual

inductive Tm : Sig → Type where
  | var : BVar s .var → Tm s
  | lam : Tm (s,x) → Tm s
  /-- Object literal with a self binder. -/
  | obj : Fields (s,x) → Tm s
  | app : BVar s .var → BVar s .var → Tm s
  | proj : BVar s .var → Label → Tm s
  | «let» : Tm s → Tm (s,x) → Tm s

inductive Fields : Sig → Type where
  | nil : Fields s
  | cons : Fields s → Label → Tm s → Fields s

end

deriving instance DecidableEq for Tm, Fields

def Fields.get? : Fields s → Label → Option (Tm s)
  | .nil, _ => none
  | .cons F ℓ' t, ℓ => if ℓ = ℓ' then some t else F.get? ℓ

mutual

def Tm.rename : Tm s1 → Rename s1 s2 → Tm s2
  | .var x, ρ => .var (ρ.var x)
  | .lam t, ρ => .lam (t.rename ρ.lift)
  | .obj F, ρ => .obj (F.rename ρ.lift)
  | .app x y, ρ => .app (ρ.var x) (ρ.var y)
  | .proj x ℓ, ρ => .proj (ρ.var x) ℓ
  | .let t u, ρ => .let (t.rename ρ) (u.rename ρ.lift)

def Fields.rename : Fields s1 → Rename s1 s2 → Fields s2
  | .nil, _ => .nil
  | .cons F ℓ t, ρ => .cons (F.rename ρ) ℓ (t.rename ρ)

end

def Tm.weaken (t : Tm s) : Tm (s,,k) := t.rename Rename.succ
def Tm.substVar (t : Tm (s,,k)) (y : BVar s k) : Tm s := t.rename (Rename.subst y)

/-! ## The inspected root

The variable whose stored value the next step reads: the function of an
application and the receiver of a projection.  Every other runtime term
reads no slot.  The target's `unbox` erases to a projection at the same
root, so the two readings agree; that fact belongs to erasure, and the facts
here are about the runtime alone. -/

def Tm.inspects : Tm s → Option (BVar s .var)
  | .app x _ => some x
  | .proj x _ => some x
  | _ => none

@[simp] theorem Tm.inspects_app (x y : BVar s .var) : (Tm.app x y).inspects = some x := rfl
@[simp] theorem Tm.inspects_proj (x : BVar s .var) (ℓ : Label) :
    (Tm.proj x ℓ).inspects = some x := rfl
@[simp] theorem Tm.inspects_var (x : BVar s .var) : (Tm.var x).inspects = none := rfl
@[simp] theorem Tm.inspects_lam (t : Tm (s,x)) : (Tm.lam t).inspects = none := rfl
@[simp] theorem Tm.inspects_obj (F : Fields (s,x)) : (Tm.obj F).inspects = none := rfl
@[simp] theorem Tm.inspects_let (t : Tm s) (u : Tm (s,x)) : (Tm.let t u).inspects = none := rfl

theorem Tm.inspects_rename {s1 s2 : Sig} (t : Tm s1) (ρ : Rename s1 s2) :
    (t.rename ρ).inspects = t.inspects.map ρ.var := by
  match t with
  | .var x => simp [Tm.rename]
  | .lam t => simp [Tm.rename]
  | .obj F => simp [Tm.rename]
  | .app x y => simp [Tm.rename]
  | .proj x ℓ => simp [Tm.rename]
  | .let t u => simp [Tm.rename]

theorem Tm.inspects_substVar {s : Sig} {k : Kind} (t : Tm (s,,k)) (y : BVar s k) :
    (t.substVar y).inspects = t.inspects.map (Rename.subst y).var :=
  Tm.inspects_rename t (Rename.subst y)

theorem Tm.inspects_weaken {s : Sig} {k : Kind} (t : Tm s) :
    (t.weaken (k := k)).inspects = t.inspects.map Rename.succ.var :=
  Tm.inspects_rename t Rename.succ

inductive IsValue : Tm s → Prop where
  | lam : IsValue (.lam t)
  | obj : IsValue (.obj F)

/-- A store: one slot per term binder, and a data-free slot per capture
binder.  (`consᶜ` of the plan: `ᶜ` is not a legal Lean identifier character,
so the capture-sort twin of a name carries the suffix `C`.) -/
inductive Store : Sig → Type where
  | nil : Store []
  | cons : Store s → Tm s → Store (s,x)
  | consC : Store s → Store (s,c)

def Store.lookup : Store s → BVar s .var → Tm s
  | .cons _ v, .here => v.weaken
  | .cons σ _, .there y => (σ.lookup y).weaken
  | .consC σ, .there y => (σ.lookup y).weaken

inductive Cont : Sig → Type where
  | nil : Cont s
  | cons : Cont s → Tm (s,x) → Cont s

def Cont.rename : Cont s1 → Rename s1 s2 → Cont s2
  | .nil, _ => .nil
  | .cons K u, ρ => .cons (K.rename ρ) (u.rename ρ.lift)

def Cont.weaken (K : Cont s) : Cont (s,,k) := K.rename Rename.succ

structure State (s : Sig) where
  σ : Store s
  K : Cont s
  t : Tm s

inductive Step : State s → State s' → Prop where
  | «let» : Step ⟨σ, K, .let t u⟩ ⟨σ, .cons K u, t⟩
  | alloc : IsValue v → Step ⟨σ, .cons K u, v⟩ ⟨.cons σ v, K.weaken, u⟩
  | rename : Step ⟨σ, .cons K u, .var y⟩ ⟨σ, K, u.substVar y⟩
  | app : σ.lookup x = .lam t → Step ⟨σ, K, .app x y⟩ ⟨σ, K, t.substVar y⟩
  | proj : σ.lookup x = .obj F → F.get? ℓ = some t → Step ⟨σ, K, .proj x ℓ⟩ ⟨σ, K, t.substVar x⟩

inductive Steps : State s → State s' → Prop where
  | refl : Steps st st
  | tail : Steps st st' → Step st' st'' → Steps st st''

def State.Final (st : State s) : Prop :=
  st.K = .nil ∧ (IsValue st.t ∨ ∃ x, st.t = .var x)

def State.Stuck (st : State s) : Prop :=
  ¬ st.Final ∧ ¬ ∃ s', ∃ st' : State s', Step st st'

end Runtime

end Captures
