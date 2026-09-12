import Coercions.Classifiers.DotToFCdot.TermsTyped
import Coercions.Classifiers.DotToFCdot.Erasure
import Coercions.Classifiers.FCdot.Progress
import Coercions.Classifiers.FCdot.ErasureMetatheory

namespace Classifiers

/-!
# Type safety for DOT-MNF, transported from FCdot (Plan III §8.2, M4; stage A3a)

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

## The box, in stage A3a

Stage A3a adds a box to the source.  It erases to the runtime's own inert
box, `Runtime.Tm.box`, and an unboxing erases to the runtime's unboxing,
which reads a box out of the store in one step.  Nothing else of either
calculus erases to a runtime box, so the erasure of a source state says
which head form the store holds at the slot an unboxing reads, and the
backward simulation `DotMNF.erase_reflect` carries no side condition.  The
statements below are therefore the stage A2 statements, on the whole source
of stage A3a.
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
    | cons _ _ => simp [State.erase, Cont.erase] at hK
    | consE _ _ => simp [State.erase, Cont.erase] at hK
  · cases t with
    | val v => exact Or.inl ⟨v, rfl⟩
    | path p => exact Or.inr ⟨p, rfl⟩
    | app _ _ =>
        simp only [State.erase, Tm.erase] at ht
        exact ht.elim (fun hv => by cases hv) (fun ⟨_, hy⟩ => by cases hy)
    | proj _ _ =>
        simp only [State.erase, Tm.erase] at ht
        exact ht.elim (fun hv => by cases hv) (fun ⟨_, hy⟩ => by cases hy)
    | «let» _ _ =>
        simp only [State.erase, Tm.erase] at ht
        exact ht.elim (fun hv => by cases hv) (fun ⟨_, hy⟩ => by cases hy)
    | unbox _ _ =>
        simp only [State.erase, Tm.erase] at ht
        exact ht.elim (fun hv => by cases hv) (fun ⟨_, hy⟩ => by cases hy)
    | letex _ _ =>
        simp only [State.erase, Tm.erase] at ht
        exact ht.elim (fun hv => by cases hv) (fun ⟨_, hy⟩ => by cases hy)

/-! ## Typedness along a target run -/

/-- Preservation, iterated: a typed FCdot state stays typed along a run.
Only the existence of a type is carried, so the renamings that `alloc`
introduces need not be composed. -/
theorem _root_.Classifiers.FCdot.State.Typed.steps {s s' : Sig} {st : FCdot.State s}
    {st' : FCdot.State s'}
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
theorem simulated_init {U : CaptureSet []} {t : Tm []} {T : Ty []}
    (d : HasTy U .nil t (.ty T)) :
    Simulated (⟨.nil, .nil, t⟩ : State []) :=
  ⟨⟨.nil, .nil, d.translate⟩, T.translate,
    ⟨.nil, .ty T.translate, .nil, d.translate_typed .nil, .nil⟩, by
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
  obtain ⟨u', hsteps, he'⟩ := FCdot.erase_reflect' hσ ⟨T, U, ht, hK⟩ hr
  obtain ⟨U', hU'⟩ := FCdot.State.Typed.steps ⟨U, ⟨Γ, T, hσ, ht, hK⟩⟩ hsteps
  exact ⟨u', U', hU', he'⟩

/-- The invariant along a whole source run. -/
theorem Simulated.steps {s s' : Sig} {st : State s} {st' : State s'}
    (hsim : Simulated st) (run : Steps st st') : Simulated st' := by
  induction run with
  | refl => exact hsim
  | tail _ hstep ih => exact (ih hsim).step hstep

/-- A simulated state is final or steps.  The source unbox case is the new
one of stage A3a, and it needs nothing beyond the simulation: the target
state that matches has the same erasure, so its store holds a runtime box at
the slot the unboxing reads, and only a source box erases to one.  That is
what `erase_reflect` reads off the erasure. -/
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
theorem dot_safety {U : CaptureSet []} {t : Tm []} {T : Ty []} (d : HasTy U .nil t (.ty T))
    {s : Sig} {st : State s} (run : Steps (⟨.nil, .nil, t⟩ : State []) st) :
    st.Final ∨ ∃ (s' : Sig) (st' : State s'), Step st st' :=
  ((simulated_init d).steps run).progress

/-- No state reachable from a closed well-typed term is stuck. -/
theorem dot_not_stuck {U : CaptureSet []} {t : Tm []} {T : Ty []}
    (d : HasTy U .nil t (.ty T))
    {s : Sig} {st : State s} (run : Steps (⟨.nil, .nil, t⟩ : State []) st) :
    ¬ st.Stuck := by
  intro ⟨hnf, hns⟩
  rcases dot_safety d run with hf | hs
  · exact hnf hf
  · exact hns hs

end DotMNF

end Classifiers
