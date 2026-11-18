import Coercions.CoDot.Machine

/-!
# Administrative steps of the machine terminate

The machine's steps split into the five real steps (those of the DOT-MNF
machine: `let`, allocation, substitution of a reference answer, application
of a bare function, selection on a bare object) and nine administrative
steps. Every administrative step lowers a natural-number measure. No typing
assumption is used.

The measure counts only what can be evaluated before the next real step: the
coercion of the head of an elimination, the wrappers of the head view, the
casts around the running term, and the cast frames. It does not count the
coercion of an application's argument or the coercion of a cast frame. The
function-wrapper step (`peelApp`) makes both of these larger; they stay
dormant until a real step, since a frame coercion is only put behind an
answer and an argument is only substituted by `beta`.
-/

namespace CoDot

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ty Path)

/-- The real steps: the rules of `MStep` that erase to a step of DOT-MNF. -/
inductive RStep : State s → State s' → Prop where
  | letPush : RStep ⟨σ, K, .tm (.let t u)⟩ ⟨σ, .let u :: K, .tm t⟩
  | alloc : RStep ⟨σ, .let u :: K, .tm (.val v c)⟩
      ⟨.cons σ v, Cont.weaken K, .tm (u.csubst (CoSub.narrow c.weaken))⟩
  | letRef : RStep ⟨σ, .let u :: K, .tm (.ref y c)⟩ ⟨σ, K, .tm (u.csubst (CoSub.inst y c))⟩
  | beta : σ.lookup f = .lam S t →
      RStep ⟨σ, K, .app (.ret ⟨f, []⟩) z e⟩ ⟨σ, K, .tm (t.csubst (CoSub.inst z e))⟩
  | select : σ.lookup y = .obj d → d.lookupTrm a = some t →
      RStep ⟨σ, K, .sel (.ret ⟨y, []⟩) a⟩ ⟨σ, K, .tm (t.csubst (CoSub.inst y .id))⟩

/-- The administrative steps. They change neither the scope nor the store. -/
inductive AStep : State s → State s → Prop where
  | castPush : AStep ⟨σ, K, .tm (.cast t c)⟩ ⟨σ, .co c :: K, .tm t⟩
  | coRef : AStep ⟨σ, .co c :: K, .tm (.ref y e)⟩ ⟨σ, K, .tm (.ref y (.seq e c))⟩
  | coVal : AStep ⟨σ, .co c :: K, .tm (.val v e)⟩ ⟨σ, K, .tm (.val v (.seq e c))⟩
  | focusSel : AStep ⟨σ, K, .tm (.proj x c a)⟩ ⟨σ, K, .sel (.app (.ret ⟨x, []⟩) c) a⟩
  | focusApp : AStep ⟨σ, K, .tm (.app x c y d)⟩ ⟨σ, K, .app (.app (.ret ⟨x, []⟩) c) y d⟩
  | evSel : Step σ.Defines e e' → AStep ⟨σ, K, .sel e a⟩ ⟨σ, K, .sel e' a⟩
  | evApp : Step σ.Defines e e' → AStep ⟨σ, K, .app e z d⟩ ⟨σ, K, .app e' z d⟩
  | peelSel : AStep ⟨σ, K, .sel (.ret ⟨x, .fld a c :: ws⟩) a⟩
      ⟨σ, .co c :: K, .sel (.ret ⟨x, ws⟩) a⟩
  | peelApp : AStep ⟨σ, K, .app (.ret ⟨f, .all c d :: ws⟩) z e⟩
      ⟨σ, .co (d.csubst (CoSub.inst z e)) :: K, .app (.ret ⟨f, ws⟩) z (.seq e c)⟩

theorem RStep.toMStep {st : State s} {st' : State s'} (h : RStep st st') : MStep st st' := by
  cases h with
  | letPush => exact .letPush
  | alloc => exact .alloc
  | letRef => exact .letRef
  | beta h => exact .beta h
  | select h1 h2 => exact .select h1 h2

theorem AStep.toMStep {st st' : State s} (h : AStep st st') : MStep st st' := by
  cases h with
  | castPush => exact .castPush
  | coRef => exact .coRef
  | coVal => exact .coVal
  | focusSel => exact .focusSel
  | focusApp => exact .focusApp
  | evSel h => exact .evSel h
  | evApp h => exact .evApp h
  | peelSel => exact .peelSel
  | peelApp => exact .peelApp

/-- Every step is real, or administrative within the same scope. -/
theorem MStep.split {st : State s} {st' : State s'} (h : MStep st st') :
    RStep st st' ∨ ∃ (e : s' = s), AStep st (e ▸ st') := by
  cases h with
  | letPush => exact .inl .letPush
  | alloc => exact .inl .alloc
  | letRef => exact .inl .letRef
  | beta h => exact .inl (.beta h)
  | select h1 h2 => exact .inl (.select h1 h2)
  | castPush => exact .inr ⟨rfl, .castPush⟩
  | coRef => exact .inr ⟨rfl, .coRef⟩
  | coVal => exact .inr ⟨rfl, .coVal⟩
  | focusSel => exact .inr ⟨rfl, .focusSel⟩
  | focusApp => exact .inr ⟨rfl, .focusApp⟩
  | evSel h => exact .inr ⟨rfl, .evSel h⟩
  | evApp h => exact .inr ⟨rfl, .evApp h⟩
  | peelSel => exact .inr ⟨rfl, .peelSel⟩
  | peelApp => exact .inr ⟨rfl, .peelApp⟩

/-! ## The measure -/

/-- Administrative work in a term: its outer casts, and the coercion of the
head of an elimination. The coercion of an answer, the coercion of an
argument and everything under `let` count nothing. -/
def Tm.adm : Tm s → Nat
  | .ref _ _ => 0
  | .val _ _ => 0
  | .let _ _ => 0
  | .cast t _ => t.adm + 1
  | .proj _ c _ => c.pend + 1
  | .app _ c _ _ => c.pend + 1

/-- For an elimination in focus: the evaluator's measure of the head. -/
def Run.adm : Run s → Nat
  | .tm t => t.adm
  | .sel e _ => e.measure
  | .app e _ _ => e.measure

/-- The number of cast frames. -/
def Cont.casts : Cont s → Nat
  | [] => 0
  | .let _ :: K => Cont.casts K
  | .co _ :: K => Cont.casts K + 1

def State.adm (st : State s) : Nat := 2 * st.t.adm + Cont.casts st.K

/-- Every administrative step lowers the measure. -/
theorem AStep.adm_lt {st st' : State s} (h : AStep st st') : st'.adm < st.adm := by
  cases h with
  | castPush => simp only [State.adm, Run.adm, Tm.adm, Cont.casts]; omega
  | coRef => simp only [State.adm, Run.adm, Tm.adm, Cont.casts]; omega
  | coVal => simp only [State.adm, Run.adm, Tm.adm, Cont.casts]; omega
  | focusSel =>
      simp only [State.adm, Run.adm, Tm.adm, Ev.measure, Wrap.listWeight]; omega
  | focusApp =>
      simp only [State.adm, Run.adm, Tm.adm, Ev.measure, Wrap.listWeight]; omega
  | evSel h => have := h.measure_lt; simp only [State.adm, Run.adm]; omega
  | evApp h => have := h.measure_lt; simp only [State.adm, Run.adm]; omega
  | peelSel =>
      simp only [State.adm, Run.adm, Ev.measure, Wrap.listWeight, Wrap.stored, Cont.casts]; omega
  | peelApp =>
      simp only [State.adm, Run.adm, Ev.measure, Wrap.listWeight, Wrap.stored, Cont.casts]; omega

/-- Administrative runs. -/
inductive ASteps : State s → State s → Prop where
  | refl : ASteps st st
  | tail : ASteps st st' → AStep st' st'' → ASteps st st''

/-- A run of `n` administrative steps. -/
inductive AStepsN : Nat → State s → State s → Prop where
  | zero : AStepsN 0 st st
  | succ : AStepsN n st st' → AStep st' st'' → AStepsN (n + 1) st st''

/-- An administrative run from `st` has at most `st.adm` steps: there is no
infinite sequence of administrative steps. -/
theorem AStepsN.bound {n : Nat} {st st' : State s} (h : AStepsN n st st') :
    n + st'.adm ≤ st.adm := by
  induction h with
  | zero => omega
  | succ _ hs ih => have := hs.adm_lt; omega

/-- Every state reaches, by administrative steps, a state with no
administrative step. -/
theorem admin_normalizes (st : State s) :
    ∃ st', ASteps st st' ∧ ∀ st'', ¬ AStep st' st'' := by
  generalize hn : st.adm = n
  induction n using Nat.strongRecOn generalizing st with
  | _ n ih =>
    by_cases h : ∃ st1, AStep st st1
    · obtain ⟨st1, h1⟩ := h
      obtain ⟨st', hrun, hnf⟩ := ih st1.adm (by have := h1.adm_lt; omega) st1 rfl
      refine ⟨st', ?_, hnf⟩
      clear hnf ih
      induction hrun with
      | refl => exact .tail .refl h1
      | tail _ hs ih' => exact .tail ih' hs
    · exact ⟨st, .refl, fun st'' hs => h ⟨st'', hs⟩⟩

end CoDot
