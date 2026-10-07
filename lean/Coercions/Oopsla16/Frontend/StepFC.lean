import Coercions.Oopsla16.Frontend.Step

/-!
# The target machine as a function

The target calculus FCdotR gives its abstract machine as a relation,
`FCdotR.Step`: a store, a continuation of `let` and coercion frames, and a
running term.  This module gives the same machine as a function, so that a
translated program runs.

The machine has six rules, and none of them has a premise that needs a search
or a fuel.  The call rule reads the root location of the receiver atom and
looks the method up in the stored object, which drops every coercion on the
atom.  So `fcStep?` takes no fuel, it is not recursive at all, and it reduces
in the kernel.  Its completeness is the full converse of soundness, not a
statement up to the existence of a fuel.

One step may allocate, which extends the signature of the store.  So a step
returns an `FNext`: the new signature, the growth that leads to it, and the new
state.  The growth is the version's `Oopsla16.Grows`, the same index the source
machine of `Step.lean` uses.

What is stated.  The function finds a step exactly when the relation has one,
and the step it finds is the only one, so the target machine is deterministic.
A state with no step is final or stuck, in the sense of `FCdotR.State.Final`
and `FCdotR.State.Stuck`, by a case split on the continuation and the term and
without classical reasoning.  `fcFinal?` decides `FCdotR.State.Final`.  Every
state the driver `fcRun` returns is reachable, and every reachable state is the
one `fcRun` returns at some number of steps.

Nothing in this module is part of the metatheory.  No definition here lives
in the `Oopsla16`, `FCdot` or `FCdotR` namespaces.
-/

namespace Oopsla16Frontend

open FCdot (Sig BVar)
open Oopsla16 (Ty Grows)
open FCdotR (Tm Atom Defs Le MachineStore Frame Cont State Vr.loc)

/-! ## One step -/

/-- The result of one step of the target machine from a state over the
signature `σ`: the signature after the step, how it grew, and the state. -/
structure FNext (σ : Sig) where
  /-- The signature after the step. -/
  σ' : Sig
  /-- The allocation the step performed. -/
  g : Grows σ σ'
  /-- The state after the step. -/
  st' : State σ'

/-- One step of `FCdotR.Step`, or `none` when the relation has no step.

The clauses follow the rules.  A `let` and a coercion push a frame.  An atom
under a coercion frame absorbs the coercion.  An atom under a `let` frame is
substituted into the body by its root location.  A literal allocates.  A call
looks the method up in the object stored at the receiver's root and
substitutes the argument's root into the body.  An atom under the empty
continuation does not step, and neither does a call to a member the object
lacks or to a type member. -/
def fcStep? {σ : Sig} : State σ → Option (FNext σ)
  | ⟨G, K, .let t u⟩ => some ⟨σ, .refl, ⟨G, .cons K (.let u), t⟩⟩
  | ⟨G, K, .cast t e⟩ => some ⟨σ, .refl, ⟨G, .cons K (.cast e), t⟩⟩
  | ⟨G, .cons K (.cast e), .atom a⟩ => some ⟨σ, .refl, ⟨G, K, .atom (.cast a e)⟩⟩
  | ⟨G, .cons K (.let u), .atom a⟩ => some ⟨σ, .refl, ⟨G, K, u.inst .base (Vr.loc a.root)⟩⟩
  | ⟨_, .nil, .atom _⟩ => none
  | ⟨G, K, .new _ ds⟩ => some ⟨_, .snoc .refl,
      ⟨G.weakenStore.cons (ds.weakenStore.inst .base .here), K.weakenStore,
        .atom (.var (.conc .here))⟩⟩
  | ⟨G, K, .app a l b⟩ =>
      match (G.lookup (Vr.loc a.root)).fun? l with
      | some (_, _, t) => some ⟨σ, .refl, ⟨G, K, t.inst .base (Vr.loc b.root)⟩⟩
      | none => none

/-! ## Soundness and completeness -/

/-- **Soundness**: a step the function finds is a step of the relation. -/
theorem fcStep?_sound {σ : Sig} : (st : State σ) → (n : FNext σ) → fcStep? st = some n →
    FCdotR.Step n.g st n.st'
  | ⟨G, K, .let t u⟩, n, h => by
      simp only [fcStep?, Option.some.injEq] at h; subst h; exact .let
  | ⟨G, K, .cast t e⟩, n, h => by
      simp only [fcStep?, Option.some.injEq] at h; subst h; exact .castPush
  | ⟨G, .cons K (.cast e), .atom a⟩, n, h => by
      simp only [fcStep?, Option.some.injEq] at h; subst h; exact .castAtom
  | ⟨G, .cons K (.let u), .atom a⟩, n, h => by
      simp only [fcStep?, Option.some.injEq] at h; subst h; exact .rename
  | ⟨_, .nil, .atom _⟩, n, h => by simp [fcStep?] at h
  | ⟨G, K, .new T ds⟩, n, h => by
      simp only [fcStep?, Option.some.injEq] at h; subst h; exact .alloc
  | ⟨G, K, .app a l b⟩, n, h => by
      simp only [fcStep?] at h
      split at h
      · rename_i S U t hf
        simp only [Option.some.injEq] at h; subst h; exact .app hf
      · simp at h

/-- **Completeness**: every step of the relation is the step the function
finds, with the same signature, growth and state. -/
theorem fcStep?_complete {σ1 σ2 : Sig} {g : Grows σ1 σ2} {st : State σ1} {st' : State σ2}
    (h : FCdotR.Step g st st') : fcStep? st = some ⟨σ2, g, st'⟩ := by
  cases h with
  | «let» => rfl
  | castPush => rfl
  | castAtom => rfl
  | rename => rfl
  | alloc => rfl
  | app hf => simp [fcStep?, hf]

/-- The function has no step exactly when the relation has none. -/
theorem fcStep?_eq_none_iff {σ : Sig} {st : State σ} :
    fcStep? st = none ↔ ¬ ∃ (σ' : Sig) (g : Grows σ σ') (st' : State σ'), FCdotR.Step g st st' := by
  constructor
  · rintro h ⟨σ', g, st', hs⟩
    rw [fcStep?_complete hs] at h; cases h
  · intro h
    cases hs : fcStep? st with
    | none => rfl
    | some n => exact absurd ⟨n.σ', n.g, n.st', fcStep?_sound st n hs⟩ h

/-- **Determinism of `FCdotR.Step`**.  Two steps from one state agree on the
signature, the growth and the state.  It follows from completeness, since
both are the step the function finds. -/
theorem fcStep_det {σ σ1 σ2 : Sig} {g1 : Grows σ σ1} {g2 : Grows σ σ2} {st : State σ}
    {st1 : State σ1} {st2 : State σ2}
    (h1 : FCdotR.Step g1 st st1) (h2 : FCdotR.Step g2 st st2) :
    (⟨σ1, g1, st1⟩ : FNext σ) = ⟨σ2, g2, st2⟩ := by
  have e1 := fcStep?_complete h1
  rw [fcStep?_complete h2] at e1
  exact (Option.some.inj e1).symm

/-! ## Final and stuck states -/

/-- `FCdotR.State.Final` as a test: an atom under the empty continuation. -/
def fcFinal? {σ : Sig} : State σ → Bool
  | ⟨_, .nil, .atom _⟩ => true
  | _ => false

/-- The test decides the final states. -/
theorem fcFinal?_iff {σ : Sig} (st : State σ) : fcFinal? st = true ↔ st.Final := by
  rcases st with ⟨G, K, t⟩
  cases t <;> cases K <;> simp [fcFinal?, FCdotR.State.Final]

/-- **Classification**: a state with no step is final or stuck.  The proof
reads the answer off `fcFinal?`, which matches the continuation and the term,
so it uses no classical reasoning. -/
theorem fcStep?_none_classify {σ : Sig} {st : State σ} (h : fcStep? st = none) :
    st.Final ∨ st.Stuck := by
  have hn := fcStep?_eq_none_iff.mp h
  cases hf : fcFinal? st with
  | true => exact Or.inl ((fcFinal?_iff st).mp hf)
  | false =>
      refine Or.inr ⟨fun hF => ?_, hn⟩
      rw [(fcFinal?_iff st).mpr hF] at hf
      exact Bool.noConfusion hf

/-- A state the function cannot step and that is not final is stuck. -/
theorem stuck_of_fcStep?_none {σ : Sig} {st : State σ} (h : fcStep? st = none)
    (hf : fcFinal? st = false) : st.Stuck := by
  rcases fcStep?_none_classify h with h' | h'
  · rw [(fcFinal?_iff st).mpr h'] at hf; exact Bool.noConfusion hf
  · exact h'

/-- A final state has no step. -/
theorem fcStep?_of_final {σ : Sig} {st : State σ} (h : fcFinal? st = true) : fcStep? st = none := by
  match st, h with
  | ⟨_, .nil, .atom _⟩, _ => rfl

/-! ## The driver -/

/-- At most `m` steps of the target machine from the state `st`.  The result
is the state after `m` steps, or the first one with no step, whichever comes
first, with the composed growth. -/
def fcRun : Nat → {σ : Sig} → State σ → FNext σ
  | 0, _, st => ⟨_, .refl, st⟩
  | m + 1, _, st =>
    match fcStep? st with
    | some n => let r := fcRun m n.st'; ⟨r.σ', n.g.comp r.g, r.st'⟩
    | none => ⟨_, .refl, st⟩
termination_by structural m => m

/-- Prepending a step to a run of the target machine. -/
theorem fcSteps_head {σ1 σ2 σ3 : Sig} {h : Grows σ1 σ2} {st : State σ1} {st1 : State σ2}
    (hs : FCdotR.Step h st st1) :
    {g : Grows σ2 σ3} → {st2 : State σ3} →
    FCdotR.Steps g st1 st2 → ∃ g' : Grows σ1 σ3, FCdotR.Steps g' st st2
  | _, _, .refl => ⟨_, .tail .refl hs⟩
  | _, _, .tail r s => by
      obtain ⟨g', r'⟩ := fcSteps_head hs r
      exact ⟨_, .tail r' s⟩

/-- **The driver's result is reachable.**  The growth is left existential,
as for the source driver `run`. -/
theorem fcRun_steps : (m : Nat) → {σ : Sig} → (st : State σ) →
    ∃ g : Grows σ (fcRun m st).σ', FCdotR.Steps g st (fcRun m st).st'
  | 0, _, _ => ⟨_, .refl⟩
  | m + 1, _, st => by
      simp only [fcRun]
      split
      · rename_i n hn
        obtain ⟨g', r⟩ := fcRun_steps m n.st'
        exact fcSteps_head (fcStep?_sound st n hn) r
      · exact ⟨_, .refl⟩

/-- One more step of the driver, when the state it reached has a step. -/
theorem fcRun_succ_of_step : (m : Nat) → {σ : Sig} → (st : State σ) →
    (n : FNext (fcRun m st).σ') → fcStep? (fcRun m st).st' = some n →
    fcRun (m + 1) st = ⟨n.σ', (fcRun m st).g.comp n.g, n.st'⟩
  | 0, _, st, n, hn => by
      have hn' : fcStep? st = some n := hn
      simp only [fcRun, hn', Grows.refl_comp]
      rfl
  | m + 1, _, st, n, hn => by
      cases h0 : fcStep? st with
      | none =>
          have hr : fcRun (m + 1) st = ⟨_, .refl, st⟩ := by simp only [fcRun, h0]
          have hn' : fcStep? (fcRun (m + 1) st).st' = none := by
            rw [hr]; exact h0
          rw [hn'] at hn; cases hn
      | some n0 =>
          have hr : fcRun (m + 1) st =
              ⟨(fcRun m n0.st').σ', n0.g.comp (fcRun m n0.st').g, (fcRun m n0.st').st'⟩ := by
            simp only [fcRun, h0]
          have hr2 : fcRun (m + 2) st =
              ⟨(fcRun (m + 1) n0.st').σ', n0.g.comp (fcRun (m + 1) n0.st').g,
                (fcRun (m + 1) n0.st').st'⟩ := by
            simp only [fcRun, h0]
          revert n hn
          rw [hr]
          intro n hn
          rw [hr2, fcRun_succ_of_step m n0.st' n hn]
          simp only [Grows.comp_assoc]

/-- One more step of the driver, from a state it is known to reach. -/
theorem fcRun_succ_of_eq {m : Nat} {σ1 σ2 : Sig} {st : State σ1} {g : Grows σ1 σ2}
    {st' : State σ2} {n : FNext σ2}
    (hm : fcRun m st = ⟨σ2, g, st'⟩) (hn : fcStep? st' = some n) :
    fcRun (m + 1) st = ⟨n.σ', g.comp n.g, n.st'⟩ := by
  have key := fcRun_succ_of_step m st
  generalize fcRun m st = r at key hm
  subst hm
  exact key n hn

/-- **The driver is complete.**  A state the relation reaches in any number of
steps is the state `fcRun` returns at some number of steps, with the same
growth. -/
theorem fcRun_complete {σ1 σ2 : Sig} {g : Grows σ1 σ2} {st : State σ1} {st' : State σ2}
    (h : FCdotR.Steps g st st') : ∃ m, fcRun m st = ⟨σ2, g, st'⟩ := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail r s ih =>
      obtain ⟨m, hm⟩ := ih
      exact ⟨m + 1, fcRun_succ_of_eq hm (fcStep?_complete s)⟩

/-! ## Probes

Each rule of the machine, seen through the function, on small states.  The
equations hold by `rfl` and the tests by `decide +kernel`, so the kernel runs
`fcStep?` and `fcRun` itself.

`G1` is a store of one location that holds the identity method at label `0`.
`G0` is a store of one location that holds no member. -/

/-- The identity method, alone in a definition list. -/
private abbrev idDefs : Defs ([],x) [] :=
  .dfun .TTop .TTop (.atom (.var (.abs .here))) .dnil

/-- One location, holding the identity method. -/
private abbrev G1 : MachineStore ([],x) ([],x) := .cons .nil idDefs

/-- One location, holding no member. -/
private abbrev G0 : MachineStore ([],x) ([],x) := .cons .nil .dnil

/-- The atom of the one location. -/
private abbrev here : Atom ([],x) [] := .var (.conc .here)

/-- A reflexive coercion at `⊤`. -/
private abbrev eTop : Le ([],x) [] := .refl .TTop

/-- `let`: the bound term runs first, its body waits in a frame. -/
example : fcStep? (⟨G1, .nil, .let (.atom here) (.atom (.var (.abs .here)))⟩ : State ([],x)) =
    some ⟨_, .refl, ⟨G1, .cons .nil (.let (.atom (.var (.abs .here)))), .atom here⟩⟩ := rfl

/-- `castPush`: the coerced term runs first, its coercion waits in a frame. -/
example : fcStep? (⟨G1, .nil, .cast (.atom here) eTop⟩ : State ([],x)) =
    some ⟨_, .refl, ⟨G1, .cons .nil (.cast eTop), .atom here⟩⟩ := rfl

/-- `castAtom`: an atom under a coercion frame absorbs the coercion. -/
example : fcStep? (⟨G1, .cons .nil (.cast eTop), .atom here⟩ : State ([],x)) =
    some ⟨_, .refl, ⟨G1, .nil, .atom (.cast here eTop)⟩⟩ := rfl

/-- `rename`: an atom under a `let` frame is substituted by its root, here
through a coercion that the substitution drops. -/
example : fcStep? (⟨G1, .cons .nil (.let (.atom (.var (.abs .here)))),
      .atom (.cast here eTop)⟩ : State ([],x)) =
    some ⟨_, .refl, ⟨G1, .nil, .atom here⟩⟩ := rfl

/-- `alloc`: a literal allocates one location and steps to it. -/
example : fcStep? (⟨.nil, .nil, .new .TTop .dnil⟩ : State []) =
    some ⟨_, .snoc .refl, ⟨.cons .nil .dnil, .nil, .atom (.var (.conc .here))⟩⟩ := rfl

/-- `app`: the call looks up the identity method at the receiver's root,
through a coercion on the receiver, and returns the argument. -/
example : fcStep? (⟨G1, .nil, .app (.cast here eTop) 0 here⟩ : State ([],x)) =
    some ⟨_, .refl, ⟨G1, .nil, .atom here⟩⟩ := rfl

/-- The final shape: an atom under the empty continuation, with no step. -/
example : fcFinal? (⟨G1, .nil, .atom (.cast here eTop)⟩ : State ([],x)) = true ∧
    fcStep? (⟨G1, .nil, .atom (.cast here eTop)⟩ : State ([],x)) = none := ⟨rfl, rfl⟩

/-- The stuck shape: a call of a member the object lacks, and a call at a
label that holds no method, have no step and are not final. -/
example : fcStep? (⟨G0, .nil, .app here 0 here⟩ : State ([],x)) = none ∧
    fcFinal? (⟨G0, .nil, .app here 0 here⟩ : State ([],x)) = false ∧
    fcStep? (⟨.cons .nil (.dty .TTop .dnil), .nil, .app here 0 here⟩ : State ([],x)) = none :=
  ⟨rfl, rfl, rfl⟩

/-- So the first of these is stuck in the sense of `FCdotR.State.Stuck`. -/
example : (⟨G0, .nil, .app here 0 here⟩ : State ([],x)).Stuck :=
  stuck_of_fcStep?_none rfl rfl

/-- A whole run: allocate, then call the identity method on the new
location, through a `let`.  Four steps reach a final state and three do
not. -/
private abbrev letCall : Tm [] [] :=
  .let (.new .TTop (.dfun .TTop .TTop (.atom (.var (.abs .here))) .dnil))
    (.app (.var (.abs .here)) 0 (.var (.abs .here)))

example : fcFinal? (fcRun 4 (⟨.nil, .nil, letCall⟩ : State [])).st' = true ∧
    fcFinal? (fcRun 3 (⟨.nil, .nil, letCall⟩ : State [])).st' = false := by
  decide +kernel

/-- The translation of the version's recursive argument example, by the
version's elaboration `FCdotR.elabTm` at the empty store typing. -/
private abbrev recArgTarget : Tm [] [] :=
  (FCdotR.elabTm FCdotR.emptyStoreTy FCdotR.SourceSafety.RecursiveArg.progTy).tm

/-- Its run reaches a final state in thirteen steps and not in twelve.  The
version shows that some final state is reached
(`FCdotR.SourceSafety.RecursiveArg.prog_target_final`), and here the kernel
finds it. -/
example : fcFinal? (fcRun 13 (⟨.nil, .nil, recArgTarget⟩ : State [])).st' = true ∧
    fcFinal? (fcRun 12 (⟨.nil, .nil, recArgTarget⟩ : State [])).st' = false := by
  decide +kernel

end Oopsla16Frontend
