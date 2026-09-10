import Coercions.CapturesCC.DotToFCdot.Safety
import Coercions.CapturesCC.DotToFCdot.Consistency
import Coercions.CapturesCC.FCdot.Prediction

namespace CapturesCC

/-!
# Capture prediction for DOT-MNF, transported from FCdot (stage A3a.7)

The source has no use-set metatheory of its own, as it has no safety of its
own: both are borrowed from the target through the translation.  What the
target proves is `FCdot.capture_prediction` -- along a run the store only
grows and the roots of the use set only shrink -- and `FCdot.effect_safety`
-- a run of a state whose use set has no root `κ` never reads a root with
root `κ`.  This file carries both across the simulation.

The transport has three parts.

* **The platform prefix.**  A program is typed under a prefix of rigid
  capture binders, the platform capabilities: the source context is
  `Platform.ctx`, a chain of `Ctx.consC`, the source store is
  `Platform.store`, a chain of data-free slots, and the target store is
  `Platform.targetStore`, the same chain of slots at the bound `∗`.  The
  three agree: the translation of the context types the target store
  (`Platform.targetStore_typed`) and the two stores have the same erasure
  (`Platform.store_erase`).

* **The run.**  `Platform.simulatedRun` is `Simulated.steps` with the target
  run remembered rather than discarded: a source run from the platform's
  initial state is matched by a target run from the initial state of the
  translation, ending at a state with the same erasure.  It then runs the
  pending cast frames, so that the target state it returns is not a cast
  redex.

* **The inspected root.**  `inspects` is preserved by erasure on both sides
  (`DotMNF.Tm.inspects_erase`, `FCdot.Tm.inspects_erase`), and a target term
  that is not a head cast is determined by its erasure at `inspects`
  (`FCdot.Tm.inspects_reflect`), so the root the source state reads is the
  root the matched target state reads.

`dot_effect_safety` reads its hypothesis `¬ (cvar κ ∈ ⟦U⟧)` as the roots
condition the target asks for: over a platform prefix every atom is a
capture variable and every capture binder is rigid, so resolution stops
where it starts and a root of a set is a member of it
(`Platform.root_iff`).
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)
open scoped FCdot

/-! ## Runs of the target machine compose -/

theorem _root_.CapturesCC.FCdot.Steps.trans {s1 s2 s3 : Sig} {a : FCdot.State s1}
    {b : FCdot.State s2} {c : FCdot.State s3}
    (h₁ : FCdot.Steps a b) (h₂ : FCdot.Steps b c) : FCdot.Steps a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hstep ih => exact .tail (ih h₁) hstep

/-! ## The platform prefix

A platform prefix is a signature of capture binders alone.  It has no term
variable at all, and its capture binders are rigid, which is what makes
membership and rootedness agree there. -/

/-- A platform signature has no term variable. -/
theorem Platform.noVar : ∀ {s : Sig}, Platform s → BVar s .var → False
  | _, .cons P, .there y => Platform.noVar P y

/-- The source context of a platform prefix: one rigid capture binder per
slot, with no bound. -/
def Platform.ctx : Platform s → Ctx s
  | .nil => .nil
  | .cons P => .consC P.ctx

/-- The initial target store over a platform prefix: the same slots, at the
platform's bound `∗`. -/
def Platform.targetStore : Platform s → FCdot.Store s
  | .nil => .nil
  | .cons P => .consC P.targetStore .star

theorem Platform.ctx_wf : ∀ P : Platform s, P.ctx.Wf
  | .nil => .nil
  | .cons P => .consC (Platform.ctx_wf P)

/-- The target store of a platform prefix is typed by the translation of the
source platform context. -/
theorem Platform.targetStore_typed : ∀ P : Platform s,
    FCdot.Store.Typed P.targetStore P.ctx.translate
  | .nil => .nil
  | .cons P => .consC (Platform.targetStore_typed P)

/-- The two initial stores have the same erasure: a capture slot carries no
runtime content on either side. -/
theorem Platform.store_erase : ∀ P : Platform s,
    (FCdot.Store.erase P.targetStore) = P.store.erase
  | .nil => rfl
  | .cons P => by
      simp only [Platform.targetStore, Platform.store, FCdot.Store.erase, Store.erase,
        Platform.store_erase P]

/-! ### Roots over a platform prefix

Every binder of a platform context is rigid, so `caps` stops at every atom,
and a root of a capture set is a member of it. -/

theorem Platform.capsAtom : ∀ {s : Sig} (P : Platform s) (n : Nat) (a : FCdot.CapAtom s),
    P.ctx.translate.capsAtom n a = [a]
  | _, P, _, .var x => (P.noVar x).elim
  | _, P, _, .name x _ => (P.noVar x).elim
  | _, .cons _, _, .cvar .here => by
      simp only [Platform.ctx, Ctx.translate, FCdot.Ctx.capsAtom]
  | _, .cons P, n, .cvar (.there κ) => by
      simp only [Platform.ctx, Ctx.translate, FCdot.Ctx.capsAtom,
        Platform.capsAtom P n (.cvar κ)]
      rfl

theorem Platform.caps : ∀ {s : Sig} (P : Platform s) (n : Nat) (C : FCdot.CaptureSet s),
    P.ctx.translate.caps n C = C
  | _, _, _, [] => by simp
  | _, P, n, a :: C => by
      simp only [FCdot.Ctx.caps_cons, Platform.capsAtom P n a, Platform.caps P n C]
      rfl

/-- Over a platform prefix a root of a capture set is a member of it. -/
theorem Platform.root_iff {s : Sig} (P : Platform s) (a : FCdot.CapAtom s)
    (C : FCdot.CaptureSet s) : P.ctx.translate.Root a C ↔ a ∈ C := by
  constructor
  · rintro ⟨n, hn⟩
    rwa [FCdot.Ctx.roots_eq_caps, Platform.caps P n C] at hn
  · intro h
    exact ⟨0, by rwa [FCdot.Ctx.roots_eq_caps, Platform.caps P 0 C]⟩

/-! ## The inspected root, read through the erasure -/

/-- A value's erasure is a lambda or an object, and reads no root. -/
theorem _root_.CapturesCC.FCdot.Value.erase_inspects {s : Sig} :
    ∀ v : FCdot.Value s, (FCdot.Value.erase v).inspects = none
  | .lam _ _ _ _ => rfl
  | .obj _ _ _ _ => rfl
  | .box _ => rfl
  | .cast v _ => FCdot.Value.erase_inspects v

/-- A target term that is not a head cast reads the root its erasure reads.
A head cast is the one term whose erasure reads a root that it does not read
itself, and a state that is not a cast redex has no head cast. -/
theorem _root_.CapturesCC.FCdot.Tm.inspects_reflect {s : Sig} {t : FCdot.Tm s}
    {x : BVar s .var} (hnc : ∀ (t₀ : FCdot.Tm s) (e : FCdot.LeCo s), t ≠ .cast t₀ e)
    (h : (FCdot.Tm.erase t).inspects = some x) : t.inspects = some x := by
  cases t with
  | atom a => simp [FCdot.Tm.erase] at h
  | val v => rw [FCdot.Tm.erase, FCdot.Value.erase_inspects v] at h; exact absurd h (by simp)
  | app a b => simpa [FCdot.Tm.erase] using h
  | proj a ℓ hh => simpa [FCdot.Tm.erase] using h
  | unbox a U f => simpa [FCdot.Tm.erase] using h
  | «let» t u U f => simp [FCdot.Tm.erase] at h
  | cast t e => exact absurd rfl (hnc t e)

/-- A state that is not a cast redex reads the root its erasure reads. -/
theorem _root_.CapturesCC.FCdot.State.inspects_reflect {s : Sig} {st : FCdot.State s}
    {x : BVar s .var} (hnc : ¬ st.CastRedex)
    (h : (FCdot.State.erase st).t.inspects = some x) : st.inspects = some x :=
  FCdot.Tm.inspects_reflect (fun t₀ e he => hnc (Or.inl ⟨t₀, e, he⟩)) h

/-! ## The matched target run -/

/-- The initial target state of a program typed over a platform prefix is
typed. -/
theorem Platform.initial_typed {s : Sig} (P : Platform s) {U : CaptureSet s} {t : Tm s}
    {T : Ty s} (d : HasTy U P.ctx t T) :
    FCdot.State.Typed (⟨P.targetStore, .nil, d.translate⟩ : FCdot.State s) T.translate :=
  ⟨P.ctx.translate, T.translate, P.targetStore_typed, d.translate_typed P.ctx_wf, .nil⟩

/-- The matched run, with both endpoints general so that the induction on the
source run goes through.  It is `Simulated.step` with the target run
remembered rather than discarded. -/
theorem simulatedRun_aux {s₀ : Sig} {st₀ : State s₀} {stt₀ : FCdot.State s₀}
    (hT : ∃ V, FCdot.State.Typed stt₀ V)
    (he₀ : FCdot.State.erase stt₀ = st₀.erase)
    {s : Sig} {st : State s} (run : Steps st₀ st) :
    ∃ stt : FCdot.State s, FCdot.Steps stt₀ stt ∧ FCdot.State.erase stt = st.erase := by
  induction run with
  | refl => exact ⟨stt₀, .refl, he₀⟩
  | tail run' hstep ih =>
      obtain ⟨stt, hrun, he⟩ := ih he₀
      obtain ⟨V₁, hT₁⟩ := FCdot.State.Typed.steps hT hrun
      obtain ⟨Γ₁, T₁, hσ₁, ht₁, hK₁⟩ := hT₁
      have hr := erase_step hstep
      rw [← he] at hr
      obtain ⟨stt', hsteps, he'⟩ := FCdot.erase_reflect' hσ₁ ⟨T₁, ht₁⟩ hr
      exact ⟨stt', hrun.trans hsteps, he'⟩

/-- **The matched run.**  A source run from the platform's initial state is
matched by a target run from the initial state of the translation, ending at
a state with the same erasure that is not a cast redex.  This is
`Simulated.steps` with the target run remembered, followed by
`FCdot.castRedex_normalize`, whose steps change neither the erasure nor the
store. -/
theorem Platform.simulatedRun {s₀ : Sig} (P : Platform s₀) {U : CaptureSet s₀} {t : Tm s₀}
    {T : Ty s₀} (d : HasTy U P.ctx t T) {s : Sig} {st : State s}
    (run : Steps (⟨P.store, .nil, t⟩ : State s₀) st) :
    ∃ stt : FCdot.State s,
      FCdot.Steps (⟨P.targetStore, .nil, d.translate⟩ : FCdot.State s₀) stt ∧
        FCdot.State.erase stt = st.erase ∧ ¬ stt.CastRedex := by
  have he₀ : FCdot.State.erase (⟨P.targetStore, .nil, d.translate⟩ : FCdot.State s₀)
      = (⟨P.store, .nil, t⟩ : State s₀).erase := by
    simp only [FCdot.State.erase, State.erase, FCdot.Cont.erase, Cont.erase,
      HasTy.translate_erase d, P.store_erase]
  obtain ⟨stt, hrun, he⟩ := simulatedRun_aux ⟨_, P.initial_typed d⟩ he₀ run
  obtain ⟨stt₁, hsteps, he₁, -, hnc⟩ := FCdot.castRedex_normalize stt
  exact ⟨stt₁, hrun.trans hsteps, he₁.trans he, hnc⟩

/-! ## The two theorems -/

/-- **Capture prediction for DOT-MNF.**  Along any run of a closed program
typed over a platform prefix, the matched target state's use set stays below
the translation of the source's declared use set, transported along the
store extension the run performs.  All the content is the target's
`FCdot.capture_prediction`; the new part is the transport along the
simulation. -/
theorem dot_capture_prediction {s₀ : Sig} (P : Platform s₀) {U : CaptureSet s₀} {t : Tm s₀}
    {T : Ty s₀} (d : HasTy U P.ctx t T) {s : Sig} {st : State s}
    (run : Steps (⟨P.store, .nil, t⟩ : State s₀) st) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename s₀ s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext P.targetStore stt.σ ρ ∧
          FCdot.CapLe Γ' stt.uses (U.translate.rename ρ) := by
  obtain ⟨stt, hrun, he, -⟩ := P.simulatedRun d run
  obtain ⟨V₁, hT₁⟩ := FCdot.State.Typed.steps ⟨_, P.initial_typed d⟩ hrun
  obtain ⟨Γ', T₁, hσ', ht₁, hK₁⟩ := hT₁
  obtain ⟨ρ, hE, hpred⟩ := FCdot.capture_prediction (P.initial_typed d) hrun
  refine ⟨stt, Γ', ρ, he, hσ', hE, ?_⟩
  have hbase : FCdot.CapLe P.ctx.translate
      (⟨P.targetStore, .nil, d.translate⟩ : FCdot.State s₀).uses U.translate := by
    simp only [FCdot.State.uses_mk, FCdot.usesK_nil, FCdot.CaptureSet.union_def,
      List.append_nil]
    exact FCdot.cap_canon P.targetStore_typed (d.translate_uses P.ctx_wf)
  exact (hpred Γ' hσ').trans (hE.capLe P.targetStore_typed hσ' hbase)

/-- **Effect safety for DOT-MNF.**  A closed program typed over a platform
prefix whose declared use set does not name the platform capability `κ` never
reads, along any run, a root whose root is `κ`.  The hypothesis is the roots
condition the target asks for: over a platform prefix every atom is a capture
variable and every binder is rigid, so a root of a set is a member of it. -/
theorem dot_effect_safety {s₀ : Sig} (P : Platform s₀) {U : CaptureSet s₀} {t : Tm s₀}
    {T : Ty s₀} (d : HasTy U P.ctx t T) {κ : BVar s₀ .cap}
    (hκ : ¬ (FCdot.CapAtom.cvar κ ∈ U.translate))
    {s : Sig} {st : State s} (run : Steps (⟨P.store, .nil, t⟩ : State s₀) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename s₀ s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext P.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var κ)) [FCdot.CapAtom.var x] := by
  obtain ⟨stt, hrun, he, hnc⟩ := P.simulatedRun d run
  obtain ⟨V₁, hT₁⟩ := FCdot.State.Typed.steps ⟨_, P.initial_typed d⟩ hrun
  obtain ⟨Γ', T₁, hσ', ht₁, hK₁⟩ := hT₁
  -- The root the source reads is the root the matched target state reads.
  have hint : stt.inspects = some x := by
    refine FCdot.State.inspects_reflect hnc ?_
    rw [he]
    exact State.inspects_erase hin
  -- The initial use set has no root `κ`.
  have hbase : FCdot.CapLe P.ctx.translate
      (⟨P.targetStore, .nil, d.translate⟩ : FCdot.State s₀).uses U.translate := by
    simp only [FCdot.State.uses_mk, FCdot.usesK_nil, FCdot.CaptureSet.union_def,
      List.append_nil]
    exact FCdot.cap_canon P.targetStore_typed (d.translate_uses P.ctx_wf)
  have hroot : ¬ P.ctx.translate.Root (FCdot.CapAtom.cvar κ)
      (⟨P.targetStore, .nil, d.translate⟩ : FCdot.State s₀).uses := fun hr =>
    hκ ((P.root_iff _ _).mp (hbase _ hr))
  obtain ⟨ρ, hE, hne⟩ :=
    FCdot.effect_safety (P.initial_typed d) P.targetStore_typed hrun hroot hint hσ'
  exact ⟨stt, Γ', ρ, he, hσ', hE, hne⟩

end DotMNF

end CapturesCC
