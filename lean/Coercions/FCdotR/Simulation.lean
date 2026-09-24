import Coercions.FCdotR.Correspondence

/-!
# The simulation in both directions, and what it transports

`Correspondence` proves the **forward** simulation (`sim_step`: every source
step from a related configuration is matched by a target run) and the form of
stuck reflection that the safety transport needs (`sim_stuck`).  This module
proves the **backward** simulation and draws the consequences that need both
directions: termination with an answer, getting stuck, and safety are each
equivalent for a related source configuration and target state.

## Backward simulation

`Rel.reflect_step` says every target step from a related state is matched by
zero or one source step, at the **same** `Grows` index, to a related
configuration:

* `let`, `castPush`, `castAtom` and `rename` are matched by **no** source step
  (`Correspondence`'s `Rel.let_`, `Rel.castPush`, `Rel.castAtom`,
  `Rel.rename`);
* `alloc` is matched by `ST_Obj` in the evaluation context the continuation
  denotes (`Rel.alloc_reflect`): the self is instantiated at the new location
  on both sides, and every pending frame is weakened;
* `app` is matched by `ST_AppAbs` in that context (`Rel.app_reflect`): the
  source reads a method at the same label with a corresponding body
  (`DmsCorr.fun?_some`), whatever either side's annotations are, and both
  sides substitute the argument's root.

`ST_App1` and `ST_App2` never appear as such: the context lemma
`ECtx.step` builds them from the redex step, one per enclosing application.
`Rel.reflect_steps` iterates the lemma along a run.

"Every related target state that can step has a source that can step" is
false (`LiteralReflection.literal_reflection_false`).  The corrected forms are
proved here:

* at a **focused** state the statement holds as written
  (`Rel.focused_reflect`);
* if **no** target run from a related state gets stuck, the source is an answer
  or steps (`Rel.progress_reflect`).  The proof is constructive and gives the
  disjunction itself, not just its double negation.

## Consequences of the two directions

* **Answers.**  A related final state has the source answer on the nose, the
  root of its atom (`Rel.final_tm`).  A target run to a final state is matched
  by a source run to an answer (`Rel.final_run`), and conversely
  (`Rel.answer_run`).  So the two reach an answer together
  (`Rel.answer_iff_final`).
* **Stuck states.**  A related stuck target state has a stuck source
  (`Rel.stuck_reflect`).  So the source can reach a stuck configuration exactly
  when the target can reach a stuck state (`Rel.stuck_iff`), and source safety
  is **equivalent** to target safety from any related pair (`Rel.safe_iff`).
  The transport of `Correspondence` uses one direction.
* **No stuttering on source steps.**  `sim_step_plus` refines `sim_step`: every
  source step is matched by administrative steps followed by exactly one
  `alloc` or `app`.
* **The invariant in the shape of `DotMNF.Simulated`.**  A source configuration
  is `Simulated` when a typed target state over an honest machine store is
  related to it.  The invariant is preserved by every source step
  (`Simulated.step`, `Simulated.steps`, by `sim_step` and
  `MethodInversion.preservation_steps'`), and a simulated configuration is an
  answer or steps (`Simulated.progress`, by `Rel.progress_reflect` and
  `MethodInversion.not_stuck'`).  It holds initially for a related typed
  closed term (`Simulated.of_typed`), hence under `ElabSpec`
  (`Simulated.of_elab`) and on the fragment (`Simulated.of_frag`).
* **Adequacy of the elaboration** (`elab_adequacy`, under `ElabSpec`): a
  closed typed source term and the elaborated target term reach an answer
  together.

## The let-free fragment of `Erasure`

`Erasure.Step.simulate` relates a state to its **erasure**, and only while no
`let` frame is pending.  `Rel.of_letFree` says that this is a special case of
the relation used here.  A `let`-free state is related to its own erasure, so
on that fragment the erasure is one of the configurations `Rel` accepts.

## What this module does not contain

No proof of `ElabSpec`: the theorems that need it take it as an explicit
hypothesis and say so.  `ElaborationFull.elabSpec` inhabits it, and
`SourceSafety` restates them without it (`Simulated.init`, `elab_adequacy'`).  No determinism theorem for either machine, and no
statement about divergence.  No change to the machine: `Machine.Step` is used
as it stands.  No source-side typing argument: all typing is the target's.  No
classical logic.
-/

namespace FCdotR

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Lb Dm Dms Ctx Store Subst Grows HasType DmsHasType)

/-! ## Source runs -/

/-- One source step is a source run at the same index. -/
theorem srcSteps_single {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1}
    {t : Oopsla16.Tm σ1 []} {G' : Store σ2 σ2} {t' : Oopsla16.Tm σ2 []}
    (h : Oopsla16.Step g G t G' t') : Oopsla16.Steps g G t G' t' := by
  have hc := Oopsla16.Steps.tail Oopsla16.Steps.refl h
  rwa [growsReflComp] at hc

/-! ## Backward simulation -/

/-- **The allocation case, backwards**: the machine's `alloc` from a related
state is `ST_Obj` in the context the continuation denotes, and the two
allocations give related configurations.  The self is instantiated at the new
location on both sides. -/
theorem Rel.alloc_reflect {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []}
    {Gt : MachineStore σ σ} {K : Cont σ} {T : Ty σ ([],x)} {ds : Defs σ ([],x)}
    (h : Rel G t ⟨Gt, K, .new T ds⟩) :
    ∃ (G' : Store (σ,x) (σ,x)) (t' : Oopsla16.Tm (σ,x) []),
      Oopsla16.Step (.snoc .refl) G t G' t' ∧
        Rel G' t' ⟨Gt.weakenStore.cons (ds.weakenStore.inst .base .here), K.weakenStore,
          .atom (.var (.conc .here))⟩ := by
  obtain ⟨C, r0, hK, ht, hr0⟩ := h.decompose
  obtain ⟨Ds, hr0', hDs⟩ := hr0
  subst ht hr0'
  refine ⟨_, _, ECtx.step .ST_Obj C, StoreCorr.alloc h.store hDs, ?_⟩
  exact (corr_fill_iff _ _ _).2
    ⟨C.renameStore Rename.succ, _, KCorr.renameStore _ K hK, rfl, rfl⟩

/-- **The invocation case, backwards**: the machine's `app` from a related
state is `ST_AppAbs` in the context the continuation denotes.  The source
finds a method at the same label, with some annotations and a body that
corresponds to the one the machine runs, and both sides substitute the
argument's root. -/
theorem Rel.app_reflect {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []}
    {Gt : MachineStore σ σ} {K : Cont σ} {a b : Atom σ []} {l : Lb} {S : Ty σ []}
    {U : Ty σ ([],x)} {body : Tm σ ([],x)} (h : Rel G t ⟨Gt, K, .app a l b⟩)
    (hf : (Gt.lookup (Vr.loc a.root)).fun? l = some (S, U, body)) :
    ∃ t' : Oopsla16.Tm σ [], Oopsla16.Step .refl G t G t' ∧
      Rel G t' ⟨Gt, K, body.inst .base (Vr.loc b.root)⟩ := by
  obtain ⟨C, r0, hK, ht, hr0⟩ := h.decompose
  have hr0' : r0 = .tapp (.tvar a.root) l (.tvar b.root) := hr0
  subst ht hr0'
  obtain ⟨o1, o2, r, hg, hc⟩ := DmsCorr.fun?_some _ (h.store (Vr.loc a.root)) hf
  have hs := ECtx.step (.ST_AppAbs (y := Vr.loc b.root) hg) C
  have he : C.plug (.tapp (.tvar a.root) l (.tvar b.root))
      = C.plug (.tapp (.tvar (.conc (Vr.loc a.root))) l (.tvar (.conc (Vr.loc b.root)))) := by
    rw [Vr.conc_loc, Vr.conc_loc]
  rw [he]
  refine ⟨_, hs, h.store, ?_⟩
  rw [show (Grows.refl : Grows σ σ).rename = Rename.id from rfl, ECtx.renameStore_id]
  exact (corr_fill_iff _ _ _).2 ⟨C, _, hK, rfl, Corr.inst hc .base _⟩

/-- **Backward simulation**: every target step from a related state is matched
by a source run at the same `Grows` index to a related configuration.  The run
is empty for the four administrative rules and a single step for `alloc`
(`ST_Obj`) and `app` (`ST_AppAbs`), each in context. -/
theorem Rel.reflect_step {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1}
    {t : Oopsla16.Tm σ1 []} {st : State σ1} {st' : State σ2} (h : Rel G t st)
    (hs : Step g st st') :
    ∃ (G' : Store σ2 σ2) (t' : Oopsla16.Tm σ2 []),
      Oopsla16.Steps g G t G' t' ∧ Rel G' t' st' := by
  cases hs with
  | «let» => exact ⟨G, t, .refl, h.let_⟩
  | castPush => exact ⟨G, t, .refl, h.castPush⟩
  | castAtom => exact ⟨G, t, .refl, h.castAtom⟩
  | rename => exact ⟨G, t, .refl, h.rename⟩
  | alloc =>
      obtain ⟨G', t', hs', hr⟩ := h.alloc_reflect
      exact ⟨G', t', srcSteps_single hs', hr⟩
  | app hf =>
      obtain ⟨t', hs', hr⟩ := h.app_reflect hf
      exact ⟨G, t', srcSteps_single hs', hr⟩

/-- **Backward simulation along a run**: every target run from a related state
is matched by a source run, at the same `Grows` index, to a related
configuration. -/
theorem Rel.reflect_steps {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1}
    {t : Oopsla16.Tm σ1 []} {st : State σ1} {st' : State σ2} (h : Rel G t st)
    (run : Steps g st st') :
    ∃ (G' : Store σ2 σ2) (t' : Oopsla16.Tm σ2 []),
      Oopsla16.Steps g G t G' t' ∧ Rel G' t' st' := by
  induction run with
  | refl => exact ⟨G, t, .refl, h⟩
  | tail _ hstep ih =>
      obtain ⟨G1, t1, r1, hr1⟩ := ih h
      obtain ⟨G2, t2, r2, hr2⟩ := hr1.reflect_step hstep
      exact ⟨G2, t2, srcStepsTrans r1 r2, hr2⟩

/-! ## Forward simulation, restated -/

/-- **Forward simulation along a source run, with no hypothesis**:
`Correspondence.Rel.steps` at `sim_step`. -/
theorem Rel.steps' {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1}
    {t : Oopsla16.Tm σ1 []} {G' : Store σ2 σ2} {t' : Oopsla16.Tm σ2 []} {st : State σ1}
    (h : Rel G t st) (run : Oopsla16.Steps g G t G' t') :
    ∃ st' : State σ2, Steps g st st' ∧ Rel G' t' st' :=
  Rel.steps sim_step h run

/-- **The forward simulation does not stutter on source steps**: every source
step from a related configuration is matched by administrative target steps,
which allocate nothing, followed by **exactly one** `alloc` or `app` step at
the source step's `Grows` index. -/
theorem sim_step_plus {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1}
    {t : Oopsla16.Tm σ1 []} {G' : Store σ2 σ2} {t' : Oopsla16.Tm σ2 []} {st : State σ1}
    (h : Rel G t st) (hs : Oopsla16.Step g G t G' t') :
    ∃ (st1 : State σ1) (st' : State σ2),
      Steps .refl st st1 ∧ Step g st1 st' ∧ Rel G' t' st' := by
  obtain ⟨Gt, K, d⟩ := st
  obtain ⟨⟨Gt1, K1, d1⟩, h1, hfoc, hrel⟩ := normalize Gt K d
  have hr := hrel G t h
  rcases hfoc with hfin | ⟨T, ds, hd⟩ | ⟨a, l, b, hd⟩
  · exact absurd hs (answer_not_step (hr.final hfin))
  · simp only at hd
    subst hd
    obtain ⟨st2, h2, hr2⟩ := Rel.sim_new hr hs
    exact ⟨_, st2, h1, h2, hr2⟩
  · simp only at hd
    subst hd
    obtain ⟨st2, h2, hr2⟩ := Rel.sim_app hr hs
    exact ⟨_, st2, h1, h2, hr2⟩

/-! ## Answers -/

/-- **A related final state has the source answer on the nose**: the source
term is the root of the state's atom. -/
theorem Rel.final_tm {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {st : State σ}
    (h : Rel G t st) (hf : st.Final) : ∃ a : Atom σ [], st.t = .atom a ∧ t = .tvar a.root := by
  obtain ⟨Gt, K, d⟩ := st
  obtain ⟨hK, a, ha⟩ := hf
  simp only at hK ha
  subst hK ha
  exact ⟨a, rfl, h.tm⟩

/-- **A target run to a final state is matched by a source run to an
answer**, at the same `Grows` index, and the two end configurations are
related. -/
theorem Rel.final_run {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1}
    {t : Oopsla16.Tm σ1 []} {st : State σ1} {st' : State σ2} (h : Rel G t st)
    (run : Steps g st st') (hf : st'.Final) :
    ∃ (G' : Store σ2 σ2) (t' : Oopsla16.Tm σ2 []),
      Oopsla16.Steps g G t G' t' ∧ t'.IsAnswer ∧ Rel G' t' st' := by
  obtain ⟨G', t', srun, hr⟩ := h.reflect_steps run
  exact ⟨G', t', srun, hr.final hf, hr⟩

/-- **A source run to an answer is matched by a target run to a final
state**, at the same `Grows` index, and the two end configurations are
related. -/
theorem Rel.answer_run {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1}
    {t : Oopsla16.Tm σ1 []} {G' : Store σ2 σ2} {t' : Oopsla16.Tm σ2 []} {st : State σ1}
    (h : Rel G t st) (run : Oopsla16.Steps g G t G' t') (ha : t'.IsAnswer) :
    ∃ st' : State σ2, Steps g st st' ∧ st'.Final ∧ Rel G' t' st' := by
  obtain ⟨st1, h1, hr1⟩ := h.steps' run
  obtain ⟨st2, h2, hfin, hr2⟩ := hr1.answer_final ha
  exact ⟨st2, Steps.trans h1 h2, hfin, hr2⟩

/-- **Related pairs reach an answer together**: the source can run to an
answer exactly when the target can run to a final state. -/
theorem Rel.answer_iff_final {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {st : State σ}
    (h : Rel G t st) :
    (∃ (σ' : Sig) (g : Grows σ σ') (G' : Store σ' σ') (t' : Oopsla16.Tm σ' []),
        Oopsla16.Steps g G t G' t' ∧ t'.IsAnswer) ↔
      (∃ (σ' : Sig) (g : Grows σ σ') (st' : State σ'), Steps g st st' ∧ st'.Final) := by
  constructor
  · rintro ⟨σ', g, G', t', run, ha⟩
    obtain ⟨st', h1, hfin, -⟩ := h.answer_run run ha
    exact ⟨σ', g, st', h1, hfin⟩
  · rintro ⟨σ', g, st', run, hfin⟩
    obtain ⟨G', t', srun, ha, -⟩ := h.final_run run hfin
    exact ⟨σ', g, G', t', srun, ha⟩

/-! ## Stuck states -/

/-- **A related stuck target state has a stuck source.**  Every state other
than a final one or an invocation steps administratively or allocates, so a
stuck state invokes a label its receiver does not define, and
`Rel.app_stuck` applies. -/
theorem Rel.stuck_reflect {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {st : State σ}
    (h : Rel G t st) (hst : st.Stuck) : SrcStuck G t := by
  obtain ⟨Gt, K, d⟩ := st
  obtain ⟨hnf, hns⟩ := hst
  cases d with
  | atom a =>
      cases K with
      | nil => exact absurd ⟨rfl, a, rfl⟩ hnf
      | cons K f =>
          cases f with
          | «let» u => exact absurd ⟨_, _, _, Step.rename⟩ hns
          | cast e => exact absurd ⟨_, _, _, Step.castAtom⟩ hns
  | new T ds => exact absurd ⟨_, _, _, Step.alloc⟩ hns
  | app a l b =>
      cases hf : (Gt.lookup (Vr.loc a.root)).fun? l with
      | none => exact Rel.app_stuck h hf
      | some p =>
          obtain ⟨S, U, body⟩ := p
          exact absurd ⟨_, _, _, Step.app hf⟩ hns
  | «let» d u => exact absurd ⟨_, _, _, Step.let⟩ hns
  | cast d e => exact absurd ⟨_, _, _, Step.castPush⟩ hns

/-- **Related pairs get stuck together**: the source can run to a stuck
configuration exactly when the target can run to a stuck state. -/
theorem Rel.stuck_iff {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {st : State σ}
    (h : Rel G t st) :
    (∃ (σ' : Sig) (g : Grows σ σ') (G' : Store σ' σ') (t' : Oopsla16.Tm σ' []),
        Oopsla16.Steps g G t G' t' ∧ SrcStuck G' t') ↔
      (∃ (σ' : Sig) (g : Grows σ σ') (st' : State σ'), Steps g st st' ∧ st'.Stuck) := by
  constructor
  · rintro ⟨σ', g, G', t', run, hst⟩
    obtain ⟨st1, h1, hr1⟩ := h.steps' run
    obtain ⟨σ'', g2, st2, h2, hst2⟩ := sim_stuck hr1 hst
    exact ⟨σ'', g.comp g2, st2, Steps.trans h1 h2, hst2⟩
  · rintro ⟨σ', g, st', run, hst⟩
    obtain ⟨G', t', srun, hr⟩ := h.reflect_steps run
    exact ⟨σ', g, G', t', srun, hr.stuck_reflect hst⟩

/-- **Source safety is target safety**: from a related pair, no source run
reaches a stuck configuration exactly when no target run reaches a stuck state.
`Correspondence.transport_from` uses the direction from right to left. -/
theorem Rel.safe_iff {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {st : State σ}
    (h : Rel G t st) :
    (∀ (σ' : Sig) (g : Grows σ σ') (G' : Store σ' σ') (t' : Oopsla16.Tm σ' []),
        Oopsla16.Steps g G t G' t' → ¬ SrcStuck G' t') ↔
      (∀ (σ' : Sig) (g : Grows σ σ') (st' : State σ'), Steps g st st' → ¬ st'.Stuck) := by
  constructor
  · intro hs σ' g st' run hst
    obtain ⟨G', t', srun, hr⟩ := h.reflect_steps run
    exact hs _ _ _ _ srun (hr.stuck_reflect hst)
  · intro ht σ' g G' t' run hst
    obtain ⟨st1, h1, hr1⟩ := h.steps' run
    obtain ⟨_, _, st2, h2, hst2⟩ := sim_stuck hr1 hst
    exact ht _ _ _ (Steps.trans h1 h2) hst2

/-! ## Progress reflection: the corrected forms of the literal statement -/

/-- **At a focused state the literal reflection holds**: a related state that
is final, about to allocate or about to invoke, and that can step, has a
source that can step.  The counterexample
`LiteralReflection.literal_reflection_false` is not focused: it is about to
push a `let` frame. -/
theorem Rel.focused_reflect {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {st : State σ}
    (h : Rel G t st) (hfoc : st.Focused) (hcs : st.CanStep) :
    ∃ (σ' : Sig) (g : Grows σ σ') (G' : Store σ' σ') (t' : Oopsla16.Tm σ' []),
      Oopsla16.Step g G t G' t' := by
  obtain ⟨Gt, K, d⟩ := st
  obtain ⟨σ', g, st', hs⟩ := hcs
  rcases hfoc with ⟨hK, a, ha⟩ | ⟨T, ds, hd⟩ | ⟨a, l, b, hd⟩
  · simp only at hK ha
    subst hK ha
    cases hs
  · simp only at hd
    subst hd
    obtain ⟨G', t', hs'⟩ := Rel.new_steps h
    exact ⟨_, _, G', t', hs'⟩
  · simp only at hd
    subst hd
    cases hs with
    | app hf =>
        obtain ⟨t', hs'⟩ := Rel.app_steps h hf
        exact ⟨_, _, G, t', hs'⟩

/-- **Target non-stuckness gives source progress**: if no target run from a
related state reaches a stuck state, the source is an answer or steps.  The
disjunction itself is constructed: normalise the target, then a final focus
gives an answer (`Rel.final`), an allocation or a defined invocation gives the
step (`Rel.new_steps`, `Rel.app_steps`), and an undefined invocation would be
a stuck state the hypothesis excludes. -/
theorem Rel.progress_reflect {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []} {st : State σ}
    (h : Rel G t st)
    (hns : ∀ (σ' : Sig) (g : Grows σ σ') (st' : State σ'), Steps g st st' → ¬ st'.Stuck) :
    t.IsAnswer ∨ ∃ (σ' : Sig) (g : Grows σ σ') (G' : Store σ' σ') (t' : Oopsla16.Tm σ' []),
      Oopsla16.Step g G t G' t' := by
  obtain ⟨Gt, K, d⟩ := st
  obtain ⟨⟨Gt1, K1, d1⟩, h1, hfoc, hrel⟩ := normalize Gt K d
  have hr := hrel G t h
  rcases hfoc with hfin | ⟨T, ds, hd⟩ | ⟨a, l, b, hd⟩
  · exact Or.inl (hr.final hfin)
  · simp only at hd
    subst hd
    obtain ⟨G', t', hs⟩ := Rel.new_steps hr
    exact Or.inr ⟨_, _, G', t', hs⟩
  · simp only at hd
    subst hd
    cases hf : (Gt1.lookup (Vr.loc a.root)).fun? l with
    | none => exact absurd (State.stuck_app hf) (hns _ _ _ h1)
    | some p =>
        obtain ⟨S, U, body⟩ := p
        obtain ⟨t', hs⟩ := Rel.app_steps hr hf
        exact Or.inr ⟨_, _, G, t', hs⟩

/-! ## The simulation invariant

The shape of `DotMNF.Simulated`, over this relation instead of a common
erasure: a typed target state over an honest machine store, at the same store
scope, related to the source configuration.  Typing is up to evidence
(`Preservation.StateTy`), as preservation provides it. -/

/-- **A simulated source configuration**: some target state at the same store
scope is related to it, is typed, and has an honest machine store. -/
def Simulated {σ : Sig} (G : Store σ σ) (t : Oopsla16.Tm σ []) : Prop :=
  ∃ (st : State σ) (W : StoreTy σ) (U : Ty σ []),
    Rel G t st ∧ Nonempty (MachineStore.Honest st.G W × StateTy st W U)

/-- **Every source step preserves the invariant**: the forward simulation
gives a related target run, and preservation retypes its endpoint.  No
hypothesis. -/
theorem Simulated.step {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1}
    {t : Oopsla16.Tm σ1 []} {G' : Store σ2 σ2} {t' : Oopsla16.Tm σ2 []}
    (hsim : Simulated G t) (hs : Oopsla16.Step g G t G' t') : Simulated G' t' := by
  obtain ⟨st, W, U, hr, ⟨hH, hT⟩⟩ := hsim
  obtain ⟨st', run, hr'⟩ := sim_step hr hs
  obtain ⟨W', ⟨hH', hT'⟩⟩ := preservation_steps' hH hT run
  exact ⟨st', W', _, hr', ⟨hH', hT'⟩⟩

/-- The invariant along a whole source run.  No hypothesis. -/
theorem Simulated.steps {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1}
    {t : Oopsla16.Tm σ1 []} {G' : Store σ2 σ2} {t' : Oopsla16.Tm σ2 []}
    (hsim : Simulated G t) (run : Oopsla16.Steps g G t G' t') : Simulated G' t' := by
  induction run with
  | refl => exact hsim
  | tail _ hstep ih => exact (ih hsim).step hstep

/-- **A simulated configuration is an answer or steps**: no target run from
its typed witness gets stuck (`MethodInversion.preservation_steps'`,
`MethodInversion.not_stuck'`), so `Rel.progress_reflect` applies.  No
hypothesis. -/
theorem Simulated.progress {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []}
    (hsim : Simulated G t) :
    t.IsAnswer ∨ ∃ (σ' : Sig) (g : Grows σ σ') (G' : Store σ' σ') (t' : Oopsla16.Tm σ' []),
      Oopsla16.Step g G t G' t' := by
  obtain ⟨st, W, U, hr, ⟨hH, hT⟩⟩ := hsim
  refine hr.progress_reflect (fun σ' g st' run => ?_)
  obtain ⟨W', ⟨hH', hT'⟩⟩ := preservation_steps' hH hT run
  exact not_stuck' hH' hT'

/-- A simulated configuration is not stuck.  No hypothesis. -/
theorem Simulated.not_stuck {σ : Sig} {G : Store σ σ} {t : Oopsla16.Tm σ []}
    (hsim : Simulated G t) : ¬ SrcStuck G t := by
  rintro ⟨hna, hns⟩
  rcases hsim.progress with ha | hs
  · exact hna ha
  · exact hns hs

/-- **Progress along every run from a simulated configuration.**  No
hypothesis. -/
theorem Simulated.reachable_progress {σ1 σ2 : Sig} {g : Grows σ1 σ2} {G : Store σ1 σ1}
    {t : Oopsla16.Tm σ1 []} {G' : Store σ2 σ2} {t' : Oopsla16.Tm σ2 []}
    (hsim : Simulated G t) (run : Oopsla16.Steps g G t G' t') :
    t'.IsAnswer ∨ ∃ (σ' : Sig) (g' : Grows σ2 σ') (G'' : Store σ' σ') (t'' : Oopsla16.Tm σ' []),
      Oopsla16.Step g' G' t' G'' t'' :=
  (hsim.steps run).progress

/-- **The invariant holds initially** for a source term related to a closed
target term typed over the empty store.  No hypothesis. -/
theorem Simulated.of_typed {W : StoreTy []} {d : Tm [] []} {T' : Ty [] []}
    (hd : TmTy Store.nil W Ctx.nil d T') {t : Oopsla16.Tm [] []}
    (hc : Rel Store.nil t ⟨MachineStore.nil, .nil, d⟩) : Simulated Store.nil t := by
  obtain ⟨W', ⟨hH, hT⟩⟩ := preservation_init' hd (Steps.refl)
  exact ⟨_, W', _, hc, ⟨hH, hT⟩⟩

/-- **A closed typed source term is simulated, given the elaboration.**

**Stated with a hypothesis:** `hE : ElabSpec`, which this module does **not**
prove (Track ELAB).  `ElaborationFull.elabSpec` inhabits it, and
`SourceSafety`'s `Simulated.init` is this theorem without it.  On the fragment
`TmFrag` it is also `Simulated.of_frag`. -/
theorem Simulated.of_elab (hE : ElabSpec) {t : Oopsla16.Tm [] []} {T : Ty [] []}
    (ht : HasType Store.nil Ctx.nil t T) : Simulated Store.nil t := by
  obtain ⟨W, d, T', ⟨hd⟩, hc⟩ := hE ht
  exact Simulated.of_typed hd hc

/-- **A closed typed source term in the fragment `TmFrag` is simulated**, by
`Correspondence.elabSpec_frag`.  No hypothesis. -/
theorem Simulated.of_frag {t : Oopsla16.Tm [] []} {T : Ty [] []}
    (ht : HasType Store.nil Ctx.nil t T) (ft : TmFrag t) : Simulated Store.nil t := by
  obtain ⟨W, d, T', ⟨hd⟩, hc⟩ := elabSpec_frag ht ft
  exact Simulated.of_typed hd hc

/-! ## Adequacy of the elaboration -/

/-- **The elaboration is adequate for answers**: a closed typed source term
has a typed elaboration, related to it, such that the source reaches an answer
exactly when the target machine run from the elaboration reaches a final
state.

**Stated with a hypothesis:** `hE : ElabSpec`, which this module does **not**
prove (Track ELAB).  `ElaborationFull.elabSpec` inhabits it, and
`SourceSafety`'s `elab_adequacy'` is this theorem without it.  Everything else
is `Rel.answer_iff_final`, with no hypothesis. -/
theorem elab_adequacy (hE : ElabSpec) {t : Oopsla16.Tm [] []} {T : Ty [] []}
    (ht : HasType Store.nil Ctx.nil t T) :
    ∃ (W : StoreTy []) (d : Tm [] []) (T' : Ty [] []),
      Nonempty (TmTy Store.nil W Ctx.nil d T') ∧
        Rel Store.nil t ⟨MachineStore.nil, .nil, d⟩ ∧
        ((∃ (σ : Sig) (g : Grows [] σ) (G' : Store σ σ) (t' : Oopsla16.Tm σ []),
            Oopsla16.Steps g Store.nil t G' t' ∧ t'.IsAnswer) ↔
          (∃ (σ : Sig) (g : Grows [] σ) (st' : State σ),
            Steps g ⟨MachineStore.nil, .nil, d⟩ st' ∧ st'.Final)) := by
  obtain ⟨W, d, T', hd, hc⟩ := hE ht
  exact ⟨W, d, T', hd, hc, hc.answer_iff_final⟩

/-! ## The let-free fragment: `Erasure`'s simulation is a special case -/

mutual

/-- **A `let`-free term corresponds to its erasure.**  Erasure sends an atom
to its root, an object literal to an object literal and an application of
atoms to the application of their roots, and drops casts.  Those are `Corr`'s
own clauses. -/
theorem Corr.of_letFree {σ : Sig} : {s : Sig} → (d : Tm σ s) → d.LetFree → Corr d.erase d
  | _, .atom _, _ => rfl
  | _, .new _ ds, h => ⟨ds.erase, rfl, DmsCorr.of_letFree ds h⟩
  | _, .app _ _ _, _ => rfl
  | _, .let _ _, h => h.elim
  | _, .cast d _, h => Corr.of_letFree d h

/-- A `let`-free definition list corresponds to its erasure; the annotations
the erasure adds play no part. -/
theorem DmsCorr.of_letFree {σ : Sig} : {s : Sig} → (ds : Defs σ s) → ds.LetFree →
    DmsCorr ds.erase ds
  | _, .dnil, _ => rfl
  | _, .dty _ ds, h => ⟨ds.erase, rfl, DmsCorr.of_letFree ds h⟩
  | _, .dfun S U d ds, h =>
      ⟨some S, some U, d.erase, ds.erase, rfl, Corr.of_letFree d h.1, DmsCorr.of_letFree ds h.2⟩

end

/-- Filling a continuation of coercion frames keeps a correspondence: every
frame becomes a term-level `cast`, which `Corr` sees through. -/
theorem Cont.corr_fill_of_evidential {σ : Sig} : (K : Cont σ) → K.Evidential →
    {r : Oopsla16.Tm σ []} → {d : Tm σ []} → Corr r d → Corr r (K.fill d)
  | .nil, _, _, _, h => h
  | .cons K (.cast e), hK, _, d, h => Cont.corr_fill_of_evidential K hK (d := .cast d e) h
  | .cons _ (.let _), hK, _, _, _ => (hK : False).elim

/-- **A `let`-free state is related to its own erasure.**  So on the fragment
where `Erasure.Step.simulate` holds, the configuration it tracks is one that
`Rel` accepts.  Nothing here compares the two simulations' matching runs. -/
theorem Rel.of_letFree {σ : Sig} {st : State σ} (hL : st.LetFree) :
    Rel st.eraseStore st.eraseTm st := by
  obtain ⟨hK, ht, hG⟩ := hL
  refine ⟨fun l => ?_, ?_⟩
  · show DmsCorr (st.G.erase.lookup l) (st.G.lookup l)
    rw [← MachineStore.erase_lookup]
    exact DmsCorr.of_letFree _ (MachineStore.letFree_lookup _ l hG)
  · show Corr (st.K.plug st.t.erase) (st.K.fill st.t)
    rw [Cont.plug_of_evidential st.K hK]
    exact Cont.corr_fill_of_evidential st.K hK (Corr.of_letFree st.t ht)

end FCdotR
