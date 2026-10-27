import Coercions.PDot.FCp.Progress

/-!
# Erasure metatheory and reachable consistency (plan X, X5 g3)

`erase_reflect'`: a runtime step of the erasure of a typed state is matched by one or more steps of
the machine, whose last state erases to the runtime's result.  A typed state is not final when its
erasure steps, since a final state erases to a normal form (`State.Final.erase_normForm`).  So it
steps (`progress`).  By `erase_step_shuffle` at `appView_sound` that step is a runtime step, which is
the given one by `Runtime.Red.det`, or a shuffle, which keeps the erasure and lowers the shuffle
measure.  The recursion is on a bound of the measure, structural on a natural number
(`erase_reflect_fuel`), and the shuffled state is typed by `preservation'`.  `st ⟶⁺ st'` is `Steps1`,
a run followed by one step.

`reachable_consistent`: every store a run reaches from a typed closed program is typed, and its
context proves no inclusion of `⊤` in `⊥` (`Steps.typed`, `no_top_le_bot`).  `Steps.consistent` says
the same from any typed state.

The examples are in `namespace PDot.FCp.X5Ex`.  A closed program that allocates N3's dangling
literal runs to a store with no typing (`X5Ex.DanglingRun`, by the computed context `Store.ctx`).
So `reachable_consistent` needs the typing of the program.  A state that applies N4's path through
an ill-typed cast is stuck while its erasure steps (`X5Ex.N4Bad`).  So `erase_reflect'` needs the
typing of the state.
-/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Runs -/

/-- `st ⟶⁺ st'`: a run of the machine followed by one step. -/
def Steps1 (V : AppView) (st : State s) (st' : State s') : Prop :=
  ∃ (s₁ : Sig) (st₁ : State s₁), Steps V st st₁ ∧ Step V st₁ st'

theorem Steps.head {V : AppView} {st : State s} {st₁ : State s₁} {st' : State s'}
    (h : Step V st st₁) (hs : Steps V st₁ st') : Steps V st st' := by
  induction hs with
  | refl => exact .tail .refl h
  | tail _ h' ih => exact .tail (ih h) h'

theorem Steps1.steps {V : AppView} {st : State s} {st' : State s'} (h : Steps1 V st st') : Steps V st st' :=
  let ⟨_, _, hs, h'⟩ := h
  .tail hs h'

theorem Steps1.head {V : AppView} {st : State s} {st₁ : State s₁} {st' : State s'}
    (h : Step V st st₁) (hs : Steps1 V st₁ st') : Steps1 V st st' :=
  let ⟨_, _, hs', h'⟩ := hs
  ⟨_, _, Steps.head h hs', h'⟩

/-- A run of one or more steps starts with a step. -/
theorem Steps1.first {V : AppView} {st : State s} {st' : State s'} (h : Steps1 V st st') :
    ∃ (s₁ : Sig) (st₁ : State s₁), Step V st st₁ := by
  obtain ⟨_, _, hs, h'⟩ := h
  induction hs generalizing s' st' with
  | refl => exact ⟨_, _, h'⟩
  | tail _ h₁ ih => exact ih h₁

/-! ## Reflection of runtime steps -/

/-- A final state erases to a runtime normal form. -/
theorem State.Final.erase_normForm {st : State s} (h : st.Final) : Runtime.NormForm st.erase.tm := by
  obtain ⟨σ, K, t⟩ := st
  obtain ⟨hK, ht⟩ := h
  simp only at hK ht
  subst hK
  rcases ht with ⟨v, rfl⟩ | ⟨P, rfl⟩
  · exact .val
  · exact .path

/-- One step of a typed state whose erasure steps: the runtime step itself, or a shuffle. -/
theorem erase_reflect_one {s : Sig} {st : State s} {U : Ty s} {k : Runtime.Conf}
    (hst : st.Typed U) (hr : Runtime.Step st.erase k) :
    (∃ (s₁ : Sig) (st₁ : State s₁), Step appView st st₁ ∧ st₁.erase = k) ∨
    ∃ st₁ : State s, Step appView st st₁ ∧ Shuffle st st₁ := by
  obtain ⟨ρ, hr⟩ := hr
  rcases progress hst with hf | ⟨s₁, st₁, hs⟩
  · exact absurd hr (Runtime.NormForm.no_red hf.erase_normForm)
  · rcases erase_step_shuffle appView_sound hs with ⟨ρ', hr'⟩ | ⟨e, hsh⟩
    · obtain ⟨e, -⟩ := Runtime.Red.det hr hr'
      exact .inl ⟨s₁, st₁, hs, e.symm⟩
    · subst e
      exact .inr ⟨st₁, hs, hsh⟩

/-- `erase_reflect'` with a bound on the shuffle measure, by induction on the bound. -/
theorem erase_reflect_fuel (n : Nat) : ∀ {s : Sig} {st : State s} {U : Ty s} {k : Runtime.Conf},
    st.shuffleMeasure ≤ n → st.Typed U → Runtime.Step st.erase k →
    ∃ (s' : Sig) (st' : State s'), Steps1 appView st st' ∧ st'.erase = k := by
  induction n with
  | zero =>
      intro s st U k hn hst hr
      rcases erase_reflect_one hst hr with ⟨s₁, st₁, hs, e⟩ | ⟨st₁, hs, hsh⟩
      · exact ⟨s₁, st₁, ⟨_, _, .refl, hs⟩, e⟩
      · exact absurd (Nat.lt_of_lt_of_le hsh.measure_lt hn) (Nat.not_lt_zero _)
  | succ n ih =>
      intro s st U k hn hst hr
      rcases erase_reflect_one hst hr with ⟨s₁, st₁, hs, e⟩ | ⟨st₁, hs, hsh⟩
      · exact ⟨s₁, st₁, ⟨_, _, .refl, hs⟩, e⟩
      · obtain ⟨_, hst₁⟩ := preservation' hst hs
        have hr₁ : Runtime.Step st₁.erase k := hsh.erase_eq ▸ hr
        obtain ⟨s', st', h1, h2⟩ := ih (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hsh.measure_lt hn)) hst₁ hr₁
        exact ⟨s', st', Steps1.head hs h1, h2⟩

/-- `erase_reflect'` (`plan-10-pdot.md:877`): a runtime step of the erasure of a typed state is
matched by one or more steps of the machine. -/
theorem erase_reflect' {s : Sig} {st : State s} {U : Ty s} {k : Runtime.Conf} {ρ : Rename s k.s}
    (hst : st.Typed U) (h : Runtime.Red st.erase k ρ) :
    ∃ (s' : Sig) (st' : State s'), Steps1 appView st st' ∧ st'.erase = k :=
  erase_reflect_fuel st.shuffleMeasure (Nat.le_refl _) hst ⟨ρ, h⟩

/-! ## Reachable stores are consistent -/

/-- Every store a run reaches from a typed state is typed and proves no `⊤ ≤ ⊥`. -/
theorem Steps.consistent {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hst : st.Typed U) (run : Steps appView st st') :
    ∃ Γ : Ctx s', Store.Typed st'.σ Γ ∧ ¬ ∃ e, LeCo.HasType Γ e .top .bot := by
  obtain ⟨_, Γ, _, hσ, _, _⟩ := Steps.typed hst run
  exact ⟨Γ, hσ, no_top_le_bot hσ⟩

/-- `reachable_consistent` (`plan-10-pdot.md:878`), for a typed closed program. -/
theorem reachable_consistent {t : Tm []} {T : Ty []} {s' : Sig} {st : State s'}
    (ht : Tm.HasType .nil t T) (run : Steps appView ⟨.nil, .nil, t⟩ st) :
    ∃ Γ : Ctx s', Store.Typed st.σ Γ ∧ ¬ ∃ e, LeCo.HasType Γ e .top .bot :=
  Steps.consistent ⟨.nil, T, .nil, ht, .nil⟩ run

end PDot.FCp

/-! # The acceptance of g3 -/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

namespace X5Ex

/-! ## A program that allocates the dangling literal reaches an untyped store -/

namespace DanglingRun

/-- N3's dangling literal `ν(x : {h : (x.zz).type}) {h = x.zz}`. -/
def lit : Value [] := .obj danglingTel (danglingDefs (.sel (.var .here) lzz 0))
/-- `let z = lit in z`. -/
def t : Tm [] := .lett (.val lit) (.path (.var .here))          -- z the .here of the body
def st₂ : State ([],x) := ⟨Store.nil.cons lit, Cont.nil.weaken, (Tm.path (.var .here)).adjust lit⟩   -- the store variable is z

/-- The run: `MS-Let`, then `MS-LetVal`. -/
theorem run : Steps appView ⟨.nil, .nil, t⟩ st₂ := .tail (.tail .refl .lett) .letVal

/-- The program has no typing. -/
theorem t_untyped : ∀ T, ¬ Tm.HasType .nil t T := fun _ h => by
  have := synthTm_complete h
  have e : synthTm .nil t = none := by decide +kernel
  rw [e] at this
  cases this

/-- The store the run reaches has no typing, so `reachable_consistent` fails without `ht`. -/
theorem store_untyped : ¬ ∃ Γ, Store.Typed st₂.σ Γ := fun ⟨_, h⟩ => by
  have := Store.ctx_iff.2 h
  have e : Store.ctx st₂.σ = none := by decide +kernel
  rw [e] at this
  cases this

end DanglingRun

/-! ## An ill-typed application whose erasure steps -/

namespace N4Bad

open C0Ex.N4

/-- `x.f` cast by `refl ⊥`, a cast with no typing at `x.f`'s type. -/
def Pbad : PathCo ([],x) := .cast P (.refl .bot)
def st : State ([],x) := ⟨σ, .nil, .app Pbad X5Ex.N4App.Q⟩

theorem Pbad_untyped : ∀ T, ¬ PathCo.HasType Γ Pbad T := fun _ h => by
  have := synthPath_complete h
  have e : synthPath Γ Pbad = none := by decide +kernel
  rw [e] at this
  cases this

/-- The machine is stuck. -/
theorem stuck : st.Stuck appView :=
  ⟨fun h => (nomatch h.2), fun ⟨_, _, hs⟩ => by
    obtain ⟨_, _, _, Γ', _, _, _, _, _, _, _, hσ', hP, _⟩ := Step.app_view hs
    cases Store.Typed.ctx_unique σ_typed hσ'
    exact Pbad_untyped _ hP⟩

/-- Its erasure `app x.f x` steps by `RR-App`. -/
theorem erase_steps : Runtime.Step st.erase ⟨([],x), σ.erase, .path (.var .here)⟩ :=
  ⟨Rename.id, .app (t := .path (.var .here)) (.single (Runtime.LStep.of_lookPath (by decide +kernel)))⟩

/-- So no run of the machine matches the runtime step: `erase_reflect'` needs `st.Typed U`. -/
theorem no_reflect : ¬ ∃ (s' : Sig) (st' : State s'), Steps1 appView st st' :=
  fun ⟨_, _, h⟩ => stuck.2 h.first

end N4Bad

end X5Ex

end PDot.FCp
