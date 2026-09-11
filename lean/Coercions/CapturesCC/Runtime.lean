import Coercions.CapturesCC.FCdot.Debruijn

namespace CapturesCC

/-!
# Shared untyped runtime

One monadic-normal-form store machine that both the DOT-MNF source and the
FCdot target erase into.  Signatures are reused from `FCdot.Debruijn`.  Only
term binders carry runtime content; a capture binder has a store slot with no
data, so that erasure maps slot to slot.

The runtime carries an inert box of its own: `Tm.box x` is a value and
`Tm.unbox x` a term, with one step that reads the box the store holds at `x`
and continues at its content.  Both calculi erase their boxes to it, so a box
and an object literal never share an erasure and the backward simulations
need no side condition to tell them apart.
-/

namespace Runtime

open FCdot (Kind Sig BVar Rename Label)

mutual

inductive Tm : Sig → Type where
  | var : BVar s .var → Tm s
  /-- A closure.  Its body lives under the three binders the target's arrow
      opens: the body root, the arrow's capture binder and the parameter.
      A capture binder carries no runtime data, so erasure still maps binder
      to binder. -/
  | lam : Tm (((s,c),c),x) → Tm s
  /-- Object literal with a class root and a self binder. -/
  | obj : Fields ((s,c),x) → Tm s
  | app : BVar s .var → BVar s .var → Tm s
  | proj : BVar s .var → Label → Tm s
  | «let» : Tm s → Tm (s,x) → Tm s
  /-- Unpacking a head: the body lives under two binders, the capture binder
      the head opens and the payload.  A capture binder carries no runtime
      data, so erasure still maps binder to binder.  A `letex` does not erase
      to a `let`: the unpacking moves the signature from `s` to `(s,c)`, and
      no other runtime step extends a signature by a capture binder. -/
  | letex : Tm s → Tm ((s,c),x) → Tm s
  /-- An inert box holding a variable.  It is a value. -/
  | box : BVar s .var → Tm s
  /-- Open a box: read the variable the box at `x` holds. -/
  | unbox : BVar s .var → Tm s

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
  | .lam t, ρ => .lam (t.rename ρ.lift.lift.lift)
  | .obj F, ρ => .obj (F.rename ρ.lift.lift)
  | .app x y, ρ => .app (ρ.var x) (ρ.var y)
  | .proj x ℓ, ρ => .proj (ρ.var x) ℓ
  | .let t u, ρ => .let (t.rename ρ) (u.rename ρ.lift)
  | .letex t u, ρ => .letex (t.rename ρ) (u.rename ρ.lift.lift)
  | .box x, ρ => .box (ρ.var x)
  | .unbox x, ρ => .unbox (ρ.var x)

def Fields.rename : Fields s1 → Rename s1 s2 → Fields s2
  | .nil, _ => .nil
  | .cons F ℓ t, ρ => .cons (F.rename ρ) ℓ (t.rename ρ)

end

def Tm.weaken (t : Tm s) : Tm (s,,k) := t.rename Rename.succ
def Tm.substVar (t : Tm (s,,k)) (y : BVar s k) : Tm s := t.rename (Rename.subst y)

/-! ## Maps of term variables

A renaming is kind preserving, and the target's substitution is not: it sends
a capture binder to a capture atom, which has no runtime content.  So the
erasure of a substitution is a map of term variables alone, and the runtime
carries one.  Renaming is the special case induced by a renaming's term
component (`Tm.rename_eq_map`). -/

/-- A map of term variables between two signatures. -/
@[reducible] def VRen (s1 s2 : Sig) : Type := BVar s1 .var → BVar s2 .var

/-- Pass under a term binder. -/
def VRen.lift (f : VRen s1 s2) : VRen (s1,x) (s2,x) := fun
  | .here => .here
  | .there x => .there (f x)

/-- Pass under a capture binder, which holds no term variable of its own. -/
def VRen.liftC (f : VRen s1 s2) : VRen (s1,c) (s2,c) := fun
  | .there x => .there (f x)

/-- The term component of a renaming. -/
def VRen.ofRename (ρ : Rename s1 s2) : VRen s1 s2 := fun x => ρ.var x

/-- Entering a closure's body: the parameter goes to the argument, the two
capture binders carry no term variable, and an older variable stays. -/
def VRen.enter (y : BVar s .var) : VRen (((s,c),c),x) s := fun
  | .here => y
  | .there (.there (.there z)) => z

/-- Entering an object body: the self goes to the receiver. -/
def VRen.enterObj (y : BVar s .var) : VRen ((s,c),x) s := fun
  | .here => y
  | .there (.there z) => z

mutual

def Tm.map : Tm s1 → VRen s1 s2 → Tm s2
  | .var x, f => .var (f x)
  | .lam t, f => .lam (t.map f.liftC.liftC.lift)
  | .obj F, f => .obj (F.map f.liftC.lift)
  | .app x y, f => .app (f x) (f y)
  | .proj x ℓ, f => .proj (f x) ℓ
  | .let t u, f => .let (t.map f) (u.map f.lift)
  | .letex t u, f => .letex (t.map f) (u.map f.liftC.lift)
  | .box x, f => .box (f x)
  | .unbox x, f => .unbox (f x)

def Fields.map : Fields s1 → VRen s1 s2 → Fields s2
  | .nil, _ => .nil
  | .cons F ℓ t, f => .cons (F.map f) ℓ (t.map f)

end

@[simp] theorem VRen.ofRename_lift {s1 s2 : Sig} (ρ : Rename s1 s2) :
    VRen.ofRename (Rename.lift (k := .var) ρ) = (VRen.ofRename ρ).lift := by
  funext z; cases z <;> rfl

@[simp] theorem VRen.ofRename_liftC {s1 s2 : Sig} (ρ : Rename s1 s2) :
    VRen.ofRename (Rename.lift (k := .cap) ρ) = (VRen.ofRename ρ).liftC := by
  funext z; cases z; rfl

mutual

/-- Renaming is the map of a renaming's term component. -/
theorem Tm.rename_eq_ofRename {s1 s2 : Sig} (t : Tm s1) (ρ : Rename s1 s2) :
    t.rename ρ = t.map (VRen.ofRename ρ) := by
  match t with
  | .var x => rfl
  | .lam t =>
      show Tm.lam _ = Tm.lam _
      rw [Tm.rename_eq_ofRename t ρ.lift.lift.lift, VRen.ofRename_lift,
        VRen.ofRename_liftC, VRen.ofRename_liftC]
  | .obj F =>
      show Tm.obj _ = Tm.obj _
      rw [Fields.rename_eq_ofRename F ρ.lift.lift, VRen.ofRename_lift, VRen.ofRename_liftC]
  | .app x y => rfl
  | .proj x ℓ => rfl
  | .let t u =>
      show Tm.let _ _ = Tm.let _ _
      rw [Tm.rename_eq_ofRename t ρ, Tm.rename_eq_ofRename u ρ.lift, VRen.ofRename_lift]
  | .letex t u =>
      show Tm.letex _ _ = Tm.letex _ _
      rw [Tm.rename_eq_ofRename t ρ, Tm.rename_eq_ofRename u ρ.lift.lift,
        VRen.ofRename_lift, VRen.ofRename_liftC]
  | .box x => rfl
  | .unbox x => rfl

theorem Fields.rename_eq_ofRename {s1 s2 : Sig} (F : Fields s1) (ρ : Rename s1 s2) :
    F.rename ρ = F.map (VRen.ofRename ρ) := by
  match F with
  | .nil => rfl
  | .cons F ℓ t =>
      show Fields.cons _ _ _ = Fields.cons _ _ _
      rw [Fields.rename_eq_ofRename F ρ, Tm.rename_eq_ofRename t ρ]

end

/-- The form B1.6 states: renaming is the map of the renaming's action on
term variables. -/
theorem Tm.rename_eq_map {s1 s2 : Sig} (t : Tm s1) (ρ : Rename s1 s2) :
    t.rename ρ = t.map (fun x => ρ.var x) :=
  Tm.rename_eq_ofRename t ρ

/-! ## The inspected root

The variable whose stored value the next step reads: the function of an
application, the receiver of a projection, and the box an `unbox` opens.
Every other runtime term reads no slot.  Both calculi erase an unboxing to
the runtime's `unbox` at the same root, so the two readings agree; that fact
belongs to erasure, and the facts here are about the runtime alone. -/

def Tm.inspects : Tm s → Option (BVar s .var)
  | .app x _ => some x
  | .proj x _ => some x
  | .unbox x => some x
  | _ => none

@[simp] theorem Tm.inspects_app (x y : BVar s .var) : (Tm.app x y).inspects = some x := rfl
@[simp] theorem Tm.inspects_proj (x : BVar s .var) (ℓ : Label) :
    (Tm.proj x ℓ).inspects = some x := rfl
@[simp] theorem Tm.inspects_var (x : BVar s .var) : (Tm.var x).inspects = none := rfl
@[simp] theorem Tm.inspects_lam (t : Tm (((s,c),c),x)) : (Tm.lam t).inspects = none := rfl
@[simp] theorem Tm.inspects_obj (F : Fields ((s,c),x)) : (Tm.obj F).inspects = none := rfl
@[simp] theorem Tm.inspects_let (t : Tm s) (u : Tm (s,x)) : (Tm.let t u).inspects = none := rfl
@[simp] theorem Tm.inspects_letex (t : Tm s) (u : Tm ((s,c),x)) :
    (Tm.letex t u).inspects = none := rfl
@[simp] theorem Tm.inspects_box (x : BVar s .var) : (Tm.box x).inspects = none := rfl
@[simp] theorem Tm.inspects_unbox (x : BVar s .var) : (Tm.unbox x).inspects = some x := rfl

theorem Tm.inspects_rename {s1 s2 : Sig} (t : Tm s1) (ρ : Rename s1 s2) :
    (t.rename ρ).inspects = t.inspects.map ρ.var := by
  match t with
  | .var x => simp [Tm.rename]
  | .lam t => simp [Tm.rename]
  | .obj F => simp [Tm.rename]
  | .app x y => simp [Tm.rename]
  | .proj x ℓ => simp [Tm.rename]
  | .let t u => simp [Tm.rename]
  | .letex t u => simp [Tm.rename]
  | .box x => simp [Tm.rename]
  | .unbox x => simp [Tm.rename]

theorem Tm.inspects_substVar {s : Sig} {k : Kind} (t : Tm (s,,k)) (y : BVar s k) :
    (t.substVar y).inspects = t.inspects.map (Rename.subst y).var :=
  Tm.inspects_rename t (Rename.subst y)

theorem Tm.inspects_weaken {s : Sig} {k : Kind} (t : Tm s) :
    (t.weaken (k := k)).inspects = t.inspects.map Rename.succ.var :=
  Tm.inspects_rename t Rename.succ

inductive IsValue : Tm s → Prop where
  | lam : IsValue (.lam t)
  | obj : IsValue (.obj F)
  | box : IsValue (.box x)

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
  /-- The frame a `letex` pushes.  Its body lives under the capture binder
      the unpacking opens and the payload. -/
  | consE : Cont s → Tm ((s,c),x) → Cont s

def Cont.rename : Cont s1 → Rename s1 s2 → Cont s2
  | .nil, _ => .nil
  | .cons K u, ρ => .cons (K.rename ρ) (u.rename ρ.lift)
  | .consE K u, ρ => .consE (K.rename ρ) (u.rename ρ.lift.lift)

def Cont.weaken (K : Cont s) : Cont (s,,k) := K.rename Rename.succ

structure State (s : Sig) where
  σ : Store s
  K : Cont s
  t : Tm s

inductive Step : State s → State s' → Prop where
  | «let» : Step ⟨σ, K, .let t u⟩ ⟨σ, .cons K u, t⟩
  | alloc : IsValue v → Step ⟨σ, .cons K u, v⟩ ⟨.cons σ v, K.weaken, u⟩
  | rename : Step ⟨σ, .cons K u, .var y⟩ ⟨σ, K, u.substVar y⟩
  | app : σ.lookup x = .lam t → Step ⟨σ, K, .app x y⟩ ⟨σ, K, t.map (VRen.enter y)⟩
  | proj : σ.lookup x = .obj F → F.get? ℓ = some t →
      Step ⟨σ, K, .proj x ℓ⟩ ⟨σ, K, t.map (VRen.enterObj x)⟩
  /-- Unboxing: read the box the store holds at `x` and continue at its
      content.  The box is inert, so nothing is substituted. -/
  | unbox : σ.lookup x = .box y → Step ⟨σ, K, .unbox x⟩ ⟨σ, K, .var y⟩
  /-- Unpacking pushes its own frame. -/
  | letex : Step ⟨σ, K, .letex t u⟩ ⟨σ, .consE K u, t⟩
  /-- A value at an unpacking frame: the store gains the data-free capture
      slot the head opens and then the value. -/
  | allocE : IsValue v →
      Step ⟨σ, .consE K u, v⟩
        ⟨(σ.consC).cons (Tm.weaken (k := .cap) v),
          Cont.weaken (Cont.weaken (k := .cap) K), u⟩
  /-- A variable at an unpacking frame: the store gains the data-free
      capture slot and the payload is the variable itself. -/
  | unpack :
      Step ⟨σ, .consE K u, .var y⟩
        ⟨σ.consC, Cont.weaken (k := .cap) K, u.substVar (.there y)⟩

inductive Steps : State s → State s' → Prop where
  | refl : Steps st st
  | tail : Steps st st' → Step st' st'' → Steps st st''

def State.Final (st : State s) : Prop :=
  st.K = .nil ∧ (IsValue st.t ∨ ∃ x, st.t = .var x)

def State.Stuck (st : State s) : Prop :=
  ¬ st.Final ∧ ¬ ∃ s', ∃ st' : State s', Step st st'

end Runtime

end CapturesCC
