import Coercions.DotToFCdot.TermsTyped
import Coercions.DotToFCdot.Erasure
import Coercions.FCdot.Progress

/-!
# Type safety for DOT-MNF, transported from FCdot (Plan III §8.2, M4)

The source calculus has no metatheory of its own: safety is *borrowed* from
the target through the translation.  The bridge is the shared untyped
runtime, into which both machines erase in lockstep (`DotMNF.erase_step` /
`DotMNF.erase_reflect` and `FCdot.erase_step` / `FCdot.erase_reflect'`).

The invariant carried along a source run is `DotMNF.Simulated`:

> a source state `st` is *simulated* when some **typed** FCdot state in the
> **same signature** has the **same erasure**.

The signature is shared because erasure is the identity on signatures on
both sides and every allocation is matched; that is what lets the two
backward-simulation lemmas be composed without transporting states along a
signature equation.

Given the invariant at `st`:

* `FCdot.castRedex_normalize` runs the pending cast-frame steps of the
  target state -- they are invisible to the erasure and bounded by the cast
  measure -- reaching a target state that is not a cast redex, still typed
  by preservation (`FCdot.preservation'`, iterated in
  `FCdot.State.Typed.steps`);
* `FCdot.progress` there gives either finality, which transfers to the
  source by `FCdot.final_erase` and `DotMNF.final_reflect`, or a step, which
  is not a cast shuffle and hence is a genuine runtime step by
  `FCdot.erase_step`, and `DotMNF.erase_reflect` lifts it back to a source
  step.

The invariant is established at the initial state by `HasTy.translate_typed`
and `HasTy.translate_erase`, and is preserved by every source step:
`DotMNF.erase_step` turns the step into a runtime step of the common
erasure, `FCdot.erase_reflect'` realizes that runtime step by a target run,
and preservation retypes its endpoint.
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Final states of the source machine

A source state is final exactly when its erasure is: the continuation is
erased frame by frame, and the running term is an answer exactly when its
erasure is. -/

/-- A final source state erases to a final runtime state. -/
theorem final_erase {s : Sig} {st : State s} (h : st.Final) : st.erase.Final := by
  obtain ⟨σ, K, t⟩ := st
  obtain ⟨hK, ht⟩ := h
  refine ⟨?_, ?_⟩
  · simp only at hK; subst hK; rfl
  · rcases ht with ⟨v, hv⟩ | ⟨p, hp⟩
    · simp only at hv; subst hv
      exact Or.inl (Value.isValue_erase v)
    · simp only at hp; subst hp
      exact Or.inr ⟨p.root, rfl⟩

/-- Conversely, a source state whose erasure is final is itself final.
Unlike in FCdot there is no pending-cast-frame caveat: the source machine
has no cast frames. -/
theorem final_reflect {s : Sig} {st : State s} (h : st.erase.Final) : st.Final := by
  obtain ⟨σ, K, t⟩ := st
  obtain ⟨hK, ht⟩ := h
  refine ⟨?_, ?_⟩
  · cases K with
    | nil => rfl
    | cons K u => simp [State.erase, Cont.erase] at hK
  · cases t with
    | val v => exact Or.inl ⟨v, rfl⟩
    | path p => exact Or.inr ⟨p, rfl⟩
    | app x y =>
        simp only [State.erase, Tm.erase] at ht
        exact ht.elim (fun hv => by cases hv) (fun ⟨_, hy⟩ => by cases hy)
    | proj x a =>
        simp only [State.erase, Tm.erase] at ht
        exact ht.elim (fun hv => by cases hv) (fun ⟨_, hy⟩ => by cases hy)
    | «let» t u =>
        simp only [State.erase, Tm.erase] at ht
        exact ht.elim (fun hv => by cases hv) (fun ⟨_, hy⟩ => by cases hy)

/-! ## Typedness along a target run -/

/-- Preservation, iterated: a typed FCdot state stays typed along a run.
Only the existence of a type is carried, so the renamings that `alloc`
introduces need not be composed. -/
theorem _root_.FCdot.State.Typed.steps {s s' : Sig} {st : FCdot.State s} {st' : FCdot.State s'}
    (h : ∃ U, FCdot.State.Typed st U) (hs : FCdot.Steps st st') :
    ∃ U', FCdot.State.Typed st' U' := by
  induction hs with
  | refl => exact h
  | tail _ hstep ih =>
      obtain ⟨U, hU⟩ := ih h
      obtain ⟨_, hU'⟩ := FCdot.preservation' hU hstep
      exact ⟨_, hU'⟩

/-! ## The simulation invariant -/

/-- The invariant carried along a source run: a typed FCdot state, in the
same signature, with the same erasure. -/
def Simulated {s : Sig} (st : State s) : Prop :=
  ∃ (t : FCdot.State s) (U : FCdot.Ty s), FCdot.State.Typed t U ∧ t.erase = st.erase

/-- The initial state of a closed well-typed term is simulated by the
initial state of its translation. -/
theorem simulated_init {t : Tm []} {T : Ty []} (d : HasTy .nil t T) :
    Simulated (⟨.nil, .nil, t⟩ : State []) :=
  ⟨⟨.nil, .nil, d.translate⟩, T.translate,
    ⟨.nil, T.translate, .nil, d.translate_typed .nil, .nil⟩, by
      simp only [FCdot.State.erase, State.erase, FCdot.Store.erase, Store.erase,
        FCdot.Cont.erase, Cont.erase, HasTy.translate_erase d]⟩

/-- Every source step preserves the invariant: it erases to a runtime step,
which the target realizes by a run out of the state that simulates the
source. -/
theorem Simulated.step {s s' : Sig} {st : State s} {st' : State s'}
    (hsim : Simulated st) (hstep : Step st st') : Simulated st' := by
  obtain ⟨u, U, hU, he⟩ := hsim
  obtain ⟨Γ, T, hσ, ht, hK⟩ := hU
  have hr : Runtime.Step u.erase st'.erase := by
    rw [he]; exact erase_step hstep
  obtain ⟨u', hsteps, he'⟩ := FCdot.erase_reflect' hσ ⟨T, ht⟩ hr
  obtain ⟨U', hU'⟩ := FCdot.State.Typed.steps ⟨U, ⟨Γ, T, hσ, ht, hK⟩⟩ hsteps
  exact ⟨u', U', hU', he'⟩

/-- The invariant along a whole source run. -/
theorem Simulated.steps {s s' : Sig} {st : State s} {st' : State s'}
    (hsim : Simulated st) (run : Steps st st') : Simulated st' := by
  induction run with
  | refl => exact hsim
  | tail _ hstep ih => exact (ih hsim).step hstep

/-- A simulated state is final or steps. -/
theorem Simulated.progress {s : Sig} {st : State s} (hsim : Simulated st) :
    st.Final ∨ ∃ (s' : Sig) (st' : State s'), Step st st' := by
  obtain ⟨u, U, hU, he⟩ := hsim
  obtain ⟨u₁, hsteps, he₁, -, hnc⟩ := FCdot.castRedex_normalize u
  obtain ⟨U₁, hU₁⟩ := FCdot.State.Typed.steps ⟨U, hU⟩ hsteps
  rcases FCdot.progress hU₁ with hfin | ⟨_, u₂, hstep⟩
  · refine Or.inl (final_reflect ?_)
    rw [← he, ← he₁]
    exact FCdot.final_erase hfin
  · rcases FCdot.erase_step hstep with ⟨hcr, -⟩ | hrun
    · exact absurd hcr hnc
    · rw [he₁, he] at hrun
      obtain ⟨st', hst', -⟩ := erase_reflect hrun
      exact Or.inr ⟨_, st', hst'⟩

/-! ## Safety -/

/-- **Safety of DOT-MNF.**  From the initial state of a closed well-typed
term, every reachable state is final or steps: the source machine never gets
stuck.  Nothing is proved about DOT-MNF directly; the whole content is the
translation, its typedness, and its erasure. -/
theorem dot_safety {t : Tm []} {T : Ty []} (d : HasTy .nil t T)
    {s : Sig} {st : State s} (run : Steps (⟨.nil, .nil, t⟩ : State []) st) :
    st.Final ∨ ∃ (s' : Sig) (st' : State s'), Step st st' :=
  ((simulated_init d).steps run).progress

/-- No state reachable from a closed well-typed term is stuck. -/
theorem dot_not_stuck {t : Tm []} {T : Ty []} (d : HasTy .nil t T)
    {s : Sig} {st : State s} (run : Steps (⟨.nil, .nil, t⟩ : State []) st) :
    ¬ st.Stuck := by
  intro ⟨hnf, hns⟩
  rcases dot_safety d run with hf | hs
  · exact hnf hf
  · exact hns hs

end DotMNF
