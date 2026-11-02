import Coercions.Nominal.Translation.Erasure
import Coercions.Nominal.FCn.ErasureMetatheory

/-!
# The transport of FCn's safety to pDOT (plan X, stage X7, group g1)

pDOT's safety is proved about pDOT's own reduction `Source.Red` and lookup `Source.LStep`, carried
from FCn through the shared runtime.  The source erases into the runtime in lockstep
(`Source.erase_step`, `Source.erase_reflect`), and so does the FCn machine at a typed state
(`FCn.erase_step`, `FCn.erase_reflect'`).

The invariant is `Simulated c`: a typed state of FCn over the signature of `c` whose erasure is
the erasure of `c` (`plan-10-pdot.md:891`).  It holds at the start of a typed closed program
by `HasTy.translate_typed` and `HasTy.translate_erase` (`simulated_init`).  A source step erases to
a runtime step, which `erase_reflect'` matches by a run of the machine (`lockstep`), and
`preservation'` types the end of that run (`Simulated.step`).  It is read off by three facts of
the target.  The erasure of a typed state is a normal form or steps (`Translation.erase_progress`,
from `progress` and the shuffle measure).  The path in focus of a typed state is a path under casts
(`Translation.path_of_erase`), whose lookup `path_safe` shows safe.  `Source.erase_normForm`,
`Source.erase_reflect_step` and `Source.erase_pathSafe` bring both back to the source.

`reachable_run` keeps the run itself: the machine runs the image of a typed closed program to a
state with the erasure of every configuration the program reaches.  `reachable_typed` reads its
typing from `Steps.typed`, and its consistency from X5's `reachable_consistent`, whose premise is
the typing of the image, `HasTy.translate_typed d .nil`.

The two theorems of the plan's Head are `Nominal.reachable_typed` and `Nominal.safety`, as the Head
states them (`plan-10-pdot.md:40-49`).  The helpers whose subject is a target object are in
`Nominal.Translation`.

Binders are named in comments only.  `(s,x)` adds one variable, and `.here` is the newest variable
of a signature.
-/

namespace Nominal

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Three facts of the target -/

/-- Two runs of the machine compose. -/
theorem Translation.steps_trans {V : FCn.AppView} {st₁ : FCn.State s₁} {st₂ : FCn.State s₂} {st₃ : FCn.State s₃}
    (h₁ : FCn.Steps V st₁ st₂) (h₂ : FCn.Steps V st₂ st₃) : FCn.Steps V st₁ st₃ := by
  induction h₂ with
  | refl => exact h₁
  | tail _ h ih => exact .tail (ih h₁) h

/-- The erasure of a typed state is a runtime normal form or steps, for a state whose shuffle
measure is at most `n`.  A shuffle keeps the erasure and lowers the measure. -/
theorem Translation.erase_progress_fuel (n : Nat) : ∀ {s : Sig} {st : FCn.State s} {U : FCn.Ty s},
    st.shuffleMeasure ≤ n → st.Typed U →
    PDot.Runtime.NormForm st.erase.tm ∨ ∃ k, PDot.Runtime.Step st.erase k := by
  induction n with
  | zero =>
      intro s st U hn hst
      rcases FCn.progress hst with hf | ⟨s₁, st₁, hs⟩
      · exact .inl hf.erase_normForm
      · rcases FCn.erase_step_shuffle FCn.appView_sound hs with hr | ⟨e, hsh⟩
        · exact .inr ⟨_, hr⟩
        · subst e
          exact absurd (Nat.lt_of_lt_of_le hsh.measure_lt hn) (Nat.not_lt_zero _)
  | succ n ih =>
      intro s st U hn hst
      rcases FCn.progress hst with hf | ⟨s₁, st₁, hs⟩
      · exact .inl hf.erase_normForm
      · rcases FCn.erase_step_shuffle FCn.appView_sound hs with hr | ⟨e, hsh⟩
        · exact .inr ⟨_, hr⟩
        · subst e
          obtain ⟨_, hst₁⟩ := FCn.preservation' hst hs
          rw [hsh.erase_eq]
          exact ih (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hsh.measure_lt hn)) hst₁

/-- The erasure of a typed state is a runtime normal form or steps. -/
theorem Translation.erase_progress {s : Sig} {st : FCn.State s} {U : FCn.Ty s} (hst : st.Typed U) :
    PDot.Runtime.NormForm st.erase.tm ∨ ∃ k, PDot.Runtime.Step st.erase k :=
  Translation.erase_progress_fuel st.shuffleMeasure (Nat.le_refl _) hst

/-- A continuation that plugs to a path has no `let` frame, and its hole holds that path. -/
theorem Translation.plug_eq_path : ∀ (K : FCn.Cont s) {r : PDot.Runtime.Tm s} {p : Path s},
    K.plug r = .path p → r = .path p
  | .nil, _, _, h => h                                                -- [].plug r = r
  | .cons K (.lett _), _, _, h => nomatch Translation.plug_eq_path K h  -- K ▹ let z. u plugs a let
  | .cons K (.cast _), _, _, h => Translation.plug_eq_path K h          -- K ▹ cast e plugs r itself

/-- A typed term that erases to a path is that path's evidence under casts, so the path has typed
evidence. -/
theorem Translation.path_of_erase : ∀ {t : FCn.Tm s} {Γ : FCn.Ctx s} {T : FCn.Ty s},
    FCn.Tm.HasType Γ t T → ∀ {p : Path s}, t.erase = .path p →
      ∃ (P : FCn.PathCo s) (T' : FCn.Ty s), FCn.PathCo.HasType Γ P T' ∧ P.path = p
  | .path P, _, _, h, _, e => by                                     -- |path P| = path P.path
      cases e
      exact ⟨P, _, h.path_inv, rfl⟩
  | .cast t _, _, _, h, _, e => by                                   -- |cast t e| = |t|
      obtain ⟨_, ht, _⟩ := h.cast_inv
      exact Translation.path_of_erase ht e
  | .val _, _, _, _, _, e => nomatch e
  | .app _ _, _, _, _, _, e => nomatch e
  | .lett _ _, _, _, _, _, e => nomatch e

/-! ## The simulation -/

/-- The simulation invariant (`plan-10-pdot.md:891`): a typed state of FCn over the
configuration's signature whose erasure is the configuration's. -/
def Simulated (c : Source.Conf) : Prop :=
  ∃ (st : FCn.State c.s) (U : FCn.Ty c.s), st.Typed U ∧ st.erase = c.erase

/-- The state that starts the image of a typed closed program is typed at the translated type. -/
theorem image_typed {t : Source.Tm []} {T : Source.Ty []} (d : Source.HasTy .nil t T) :
    (⟨.nil, .nil, d.translate⟩ : FCn.State []).Typed T.translate :=
  ⟨.nil, T.translate, .nil, Source.HasTy.translate_typed d .nil, .nil⟩

/-- The state that starts the image erases to the configuration that starts the program. -/
theorem image_erase {t : Source.Tm []} {T : Source.Ty []} (d : Source.HasTy .nil t T) :
    (⟨.nil, .nil, d.translate⟩ : FCn.State []).erase = Source.Conf.erase ⟨[], .nil, t⟩ := by
  show (⟨[], .nil, d.translate.erase⟩ : PDot.Runtime.Conf) = ⟨[], .nil, t.erase⟩
  rw [Source.HasTy.translate_erase]

/-- Initial: the configuration that starts a typed closed program is simulated. -/
theorem simulated_init {t : Source.Tm []} {T : Source.Ty []} (d : Source.HasTy .nil t T) :
    Simulated ⟨[], .nil, t⟩ :=
  ⟨_, _, image_typed d, image_erase d⟩

/-- One source step from a configuration with the erasure of a typed state is matched by a run of
the machine from that state, to a state with the erasure of the next configuration.  The source
step erases to a runtime step (`Source.erase_step`), and `erase_reflect'` finds the run. -/
theorem lockstep {c c' : Source.Conf} (hs : Source.Step c c') {st : FCn.State c.s} {U : FCn.Ty c.s}
    (hst : st.Typed U) (he : st.erase = c.erase) :
    ∃ st' : FCn.State c'.s, FCn.Steps FCn.appView st st' ∧ st'.erase = c'.erase := by
  obtain ⟨ρ, hr⟩ := hs
  have hr' : PDot.Runtime.Step st.erase c'.erase := by
    rw [he]
    exact ⟨ρ, Source.erase_step hr⟩
  obtain ⟨ρ', hr''⟩ := hr'
  obtain ⟨s₁, st₁, hrun, he₁⟩ := FCn.erase_reflect' hst hr''
  have e : s₁ = c'.s := congrArg PDot.Runtime.Conf.s he₁
  subst e
  exact ⟨st₁, hrun.steps, he₁⟩

/-- Kept: a source step keeps the invariant. -/
theorem Simulated.step {c c' : Source.Conf} (h : Simulated c) (hs : Source.Step c c') : Simulated c' := by
  obtain ⟨st, U, hst, he⟩ := h
  obtain ⟨st', hrun, he'⟩ := lockstep hs hst he
  obtain ⟨ρ, hst'⟩ := FCn.Steps.typed hst hrun
  exact ⟨st', _, hst', he'⟩

/-- Kept along a run. -/
theorem Simulated.reds {c c' : Source.Conf} (h : Simulated c) (hc : Source.Reds c c') : Simulated c' := by
  induction hc with
  | refl => exact h
  | step hs _ ih => exact ih (h.step hs)

/-- Read off: a simulated configuration is a normal form or steps.  The erasure of the typed state
is a normal form or steps (`Translation.erase_progress`), and `Source.erase_normForm` and
`Source.erase_reflect_step` bring that back to the source. -/
theorem Simulated.progress {c : Source.Conf} (h : Simulated c) :
    Source.NormForm c.tm ∨ ∃ c', Source.Step c c' := by
  obtain ⟨st, U, hst, he⟩ := h
  rcases Translation.erase_progress hst with hn | ⟨k, hk⟩
  · rw [he] at hn
    exact .inl ((Source.erase_normForm c.tm).1 hn)
  · rw [he] at hk
    obtain ⟨c', hs, _⟩ := Source.erase_reflect_step hk
    exact .inr ⟨c', hs⟩

/-- Read off: the path in focus of a simulated configuration has a safe lookup.  The typed state
holds that path's evidence under casts (`Translation.path_of_erase`), whose path is safe in the
erased store (`path_safe`), and `Source.erase_pathSafe` brings that back to the source store. -/
theorem Simulated.pathSafe {c : Source.Conf} (h : Simulated c) :
    ∀ p, c.tm = .path p → Source.PathSafe c.store p := by
  obtain ⟨s, γ, t⟩ := c
  intro p hp
  obtain ⟨⟨σ, K, u⟩, U, ⟨Γ, T, hσ, hu, _⟩, he⟩ := h
  simp only [FCn.State.erase, Source.Conf.erase, PDot.Runtime.Conf.mk.injEq, heq_eq_eq, true_and] at he hp
  obtain ⟨hγ, hK⟩ := he
  rw [hp] at hK
  obtain ⟨P, _, hP, rfl⟩ := Translation.path_of_erase hu (Translation.plug_eq_path K hK)
  have hs := FCn.path_safe hσ hP
  rw [hγ] at hs
  exact Source.erase_pathSafe hs

/-! ## The claim -/

/-- The lockstep run from a configuration that a run of the image reaches with its erasure. -/
theorem reachable_run_from {t : Source.Tm []} {T : Source.Ty []} (d : Source.HasTy .nil t T) :
    ∀ {c₀ c : Source.Conf}, Source.Reds c₀ c → ∀ st₀ : FCn.State c₀.s,
      FCn.Steps FCn.appView ⟨.nil, .nil, d.translate⟩ st₀ → st₀.erase = c₀.erase →
      ∃ st : FCn.State c.s, FCn.Steps FCn.appView ⟨.nil, .nil, d.translate⟩ st ∧ st.erase = c.erase
  | _, _, .refl, st₀, run, he => ⟨st₀, run, he⟩
  | _, _, .step hs rest, st₀, run, he => by
      obtain ⟨_, hst₀⟩ := FCn.Steps.typed (image_typed d) run
      obtain ⟨st₁, run₁, he₁⟩ := lockstep hs hst₀ he
      exact reachable_run_from d rest st₁ (Translation.steps_trans run run₁) he₁

/-- The lockstep run: the machine runs the image of a typed closed program to a state with the
erasure of every configuration the program reaches. -/
theorem reachable_run {t : Source.Tm []} {T : Source.Ty []} (d : Source.HasTy .nil t T)
    {c : Source.Conf} (hc : Source.Reds ⟨[], .nil, t⟩ c) :
    ∃ st : FCn.State c.s, FCn.Steps FCn.appView ⟨.nil, .nil, d.translate⟩ st ∧ st.erase = c.erase :=
  reachable_run_from d hc _ .refl (image_erase d)

/-- The plan's `Nominal.reachable_typed` (`plan-10-pdot.md:45-49`): every configuration a typed closed
program reaches is the erasure of a typed state of FCn, at the translated type renamed into its
signature, and every typing of that state's store proves no inclusion of `⊤` in `⊥`.  The
consistency is X5's `reachable_consistent` at the image, whose premise is
`HasTy.translate_typed d .nil`, and `Store.Typed.ctx_unique` gives it at every typing. -/
theorem reachable_typed {t : Source.Tm []} {T : Source.Ty []} (d : Source.HasTy .nil t T)
    {c : Source.Conf} (hc : Source.Reds ⟨[], .nil, t⟩ c) :
    ∃ (st : FCn.State c.s) (ρ : Rename [] c.s),
      st.Typed (T.translate.rename ρ) ∧ st.erase = c.erase ∧
      ∀ Γ, FCn.Store.Typed st.σ Γ → ¬ ∃ e, FCn.LeCo.HasType Γ e FCn.Ty.top FCn.Ty.bot := by
  obtain ⟨st, run, he⟩ := reachable_run d hc
  obtain ⟨ρ, hst⟩ := FCn.Steps.typed (image_typed d) run
  obtain ⟨Γ₀, hσ₀, hc₀⟩ := FCn.reachable_consistent (Source.HasTy.translate_typed d .nil) run
  refine ⟨st, ρ, hst, he, fun Γ hσ => ?_⟩
  rw [FCn.Store.Typed.ctx_unique hσ hσ₀]
  exact hc₀

/-- The plan's `Nominal.safety` (`plan-10-pdot.md:40-43`): along every run of a typed closed pDOT
program, the configuration is a normal form or steps, and a path in focus has a safe lookup.  The
first conjunct is the progress half of pDOT's `safety` (`Safety.v:416-424`), the second the
constructive content of `path_safety` (`Safety.v:442-447`). -/
theorem safety {t : Source.Tm []} {T : Source.Ty []} (d : Source.HasTy .nil t T)
    {c : Source.Conf} (hc : Source.Reds ⟨[], .nil, t⟩ c) :
    (Source.NormForm c.tm ∨ ∃ c', Source.Step c c') ∧
    (∀ p, c.tm = .path p → Source.PathSafe c.store p) :=
  let h := (simulated_init d).reds hc
  ⟨h.progress, h.pathSafe⟩

end Nominal
