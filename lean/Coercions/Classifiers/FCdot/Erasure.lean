import Coercions.Classifiers.FCdot.Machine
import Coercions.Classifiers.Runtime

namespace Classifiers

/-!
# Erasure of FCdot into the shared runtime

Atoms erase to their root variable, casts and evidence vanish, object
literals keep only their fields.  Cast frames erase to nothing.  A
`recap a f` carries no runtime content, so it erases to the erasure of `a`,
which is the root variable of `a`.  A box erases to the runtime's inert box
holding the boxed atom's root, and an unbox to the runtime's `unbox` at the
atom's root, so the machine's `unbox` steps erase to the runtime's `unbox`
step and the allocation of a box to the runtime allocation of a box.  A
capture slot of a store erases to the runtime's data-free capture slot.
-/

namespace FCdot

mutual

def Tm.erase : Tm s → Runtime.Tm s
  | .atom p => .var p.root
  | .val v => v.erase
  | .app a b => .app a.root b.root
  | .proj a ℓ _ => .proj a.root ℓ
  -- The declared use set and the avoidance evidence of a let have no runtime
  -- content and vanish.
  | .let t u _ _ => .let t.erase u.erase
  | .cast t _ => t.erase
  -- An answer cast carries no runtime content either.
  | .castE t _ => t.erase
  -- The declared use set and the two evidences of an unpacking vanish, and
  -- the two binders of its body are the two binders of the runtime's own
  -- unpacking.
  | .letex t u _ _ _ => .letex t.erase u.erase
  -- Unboxing opens the runtime box a box erases to.
  | .unbox a _ _ => .unbox a.root

def Value.erase : Value s → Runtime.Tm s
  -- The assigned capture set and the closing evidence are annotations and
  -- vanish with the parameter type.
  | .lam _ _ t _ => .lam t.erase
  | .obj _ _ _ F => .obj F.erase
  -- A box is the runtime's inert box holding the boxed atom's root.
  | .box a => .box a.root
  -- A wrapper carries no runtime content: a packed value erases to its
  -- payload, as a cast one does.
  | .pack _ _ _ v => v.erase
  | .cast v _ => v.erase

def Fields.erase : Fields s → Runtime.Fields s
  | .nil => .nil
  | .cons F ℓ t _ => .cons F.erase ℓ t.erase

end

/-- Erasure of a store, slot for slot: a capture slot has no runtime
content, so it erases to the runtime's data-free capture slot. -/
def Store.erase : Store s → Runtime.Store s
  | .nil => .nil
  | .cons σ v => .cons σ.erase v.erase
  | .consC σ _ => .consC σ.erase

def Cont.erase : Cont s → Runtime.Cont s
  | .nil => .nil
  | .cons K (.let u _ _) => .cons K.erase u.erase
  | .cons K (.cast _) => K.erase
  | .cons K (.castE _) => K.erase
  | .cons K (.letex u _ _ _) => .consE K.erase u.erase

def State.erase (st : State s) : Runtime.State s :=
  ⟨st.σ.erase, st.K.erase, st.t.erase⟩

/-! ### Notation: `⌊t⌋` erases a term, value, store, continuation, or state. -/

scoped notation:max "⌊" t "⌋" => Tm.erase t
scoped notation:max "⌊" v "⌋" => Value.erase v
scoped notation:max "⌊" σ "⌋" => Store.erase σ
scoped notation:max "⌊" K "⌋" => Cont.erase K
scoped notation:max "⌊" st "⌋" => State.erase st

/-! ### The box and its opening

The two equations of the box design: a box erases to the runtime's inert box
at the boxed atom's root, and an unboxing to the runtime's `unbox` at the
atom's root. -/

@[simp] theorem Value.erase_box (a : Atom s) :
    ⌊(Value.box a)⌋ = .box a.root := rfl

@[simp] theorem Tm.erase_unbox (a : Atom s) (U : CaptureSet s) (f : CapCo s) :
    ⌊(Tm.unbox a U f)⌋ = .unbox a.root := rfl

/-! ### The wrapper and the unpacking

A pack is a wrapper, so it erases to the erasure of what it wraps, and an
unpacking erases to the runtime's own, which is the one runtime step that
extends a signature by a capture binder. -/

@[simp] theorem Value.erase_pack (C : CaptureSet s) (h : CapCo s) (e : LeCo (Sig.scope s))
    (v : Value s) : ⌊(Value.pack C h e v)⌋ = ⌊v⌋ := rfl

@[simp] theorem Tm.erase_letex (t : Tm s) (u : Tm ((s,c),x)) (U : CaptureSet s)
    (h : CapCo s) (f : CapCo ((s,c),x)) :
    ⌊(Tm.letex t u U h f)⌋ = .letex ⌊t⌋ ⌊u⌋ := rfl

/-! ### Erasure and the inspected root

The root a term reads survives erasure: an application erases to a runtime
application at the same root, a projection to a projection at the same root,
and an unboxing to a runtime unboxing at the same root.  A cast
term reads no root of its own, while its erasure is the erasure of the term
under the cast, so the equation is stated in the direction the prediction
theorem uses: a root read in `FCdot` is read after erasure. -/

/-- Erasure preserves an inspected root. -/
theorem Tm.inspects_erase {s : Sig} {t : Tm s} {x : BVar s .var}
    (h : t.inspects = some x) : (⌊t⌋ : Runtime.Tm s).inspects = some x := by
  cases t with
  | app a b => rw [Tm.inspects_app] at h; cases h; rfl
  | proj a ℓ p => rw [Tm.inspects_proj] at h; cases h; rfl
  | unbox a U f => rw [Tm.inspects_unbox] at h; cases h; rfl
  | atom a => exact absurd h (by simp)
  | val v => exact absurd h (by simp)
  | «let» t u U f => exact absurd h (by simp)
  | cast t e => exact absurd h (by simp)
  | castE t g => exact absurd h (by simp)
  | letex t u U hh f => exact absurd h (by simp)

/-- Erasure of a state preserves the root the state reads. -/
theorem State.inspects_erase {s : Sig} {st : State s} {x : BVar s .var}
    (h : st.inspects = some x) : (⌊st⌋ : Runtime.State s).t.inspects = some x :=
  Tm.inspects_erase h

/-- States whose next step only moves a cast frame; such steps erase to no
runtime step.  The answer cast joins the plain one: its three steps are
unconditional, so each of them erases to nothing, which is what makes the
backward simulation reach `erase_reflect_aux`. -/
def State.CastRedex (st : State s) : Prop :=
  (∃ t e, st.t = .cast t e) ∨
  (∃ t g, st.t = .castE t g) ∨
  (∃ K e, st.K = .cons K (.cast e) ∧ ((∃ v, st.t = .val v) ∨ (∃ p, st.t = .atom p))) ∨
  (∃ K g, st.K = .cons K (.castE g) ∧ ((∃ v, st.t = .val v) ∨ (∃ p, st.t = .atom p)))

/-- The executable test for `State.CastRedex`. -/
def State.isCastRedex (st : State s) : Bool :=
  match st.t, st.K with
  | .cast _ _, _ => true
  | .castE _ _, _ => true
  | .val _, .cons _ (.cast _) => true
  | .atom _, .cons _ (.cast _) => true
  | .val _, .cons _ (.castE _) => true
  | .atom _, .cons _ (.castE _) => true
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

end Classifiers
