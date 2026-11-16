import Coercions.Selective.Dot.Canonical

/-!
# Selective DOT: type safety

Progress and preservation for the machine of `Machine.lean`, which runs erased
terms. A typed state is the erasure of a typed annotated state
(`State.lean`); preservation shows that annotations for the next state exist.
It does not compute them: narrowing, substitution of a path and the canonical
forms are existence statements.

The running annotated term is first stripped of its casts (`HasTy.strip`); the
term under the casts has the same erasure, so its shape is the shape of the
running erased term, and its type converts to the type of the whole by a
certificate, which is carried into the next state as a cast.
-/

namespace SelDot

open FCdot (Kind Sig BVar Rename Label)

/-! ## Continuations -/

/-- Continuation typing is stable under renamings that preserve the types of
variables. -/
theorem ContTy.rename {Γ : Ctx s1} {K : Cont s1} {T U : Ty s1} (h : ContTy Γ K T U) :
    ∀ {s2 : Sig} {Δ : Ctx s2} {ρ : Rename s1 s2}, Γ.Renames Δ ρ →
      ContTy Δ (K.rename ρ) (T.rename ρ) (U.rename ρ) := by
  induction h with
  | nil => intro _ _ _ _; exact .nil
  | cons hu_e hu _ ih =>
      intro _ _ ρ hρ
      have h2 := HasTy.rename hu (hρ.cons _)
      rw [Ty.weaken_rename] at h2
      exact .cons (by rw [Tm.erase_rename, hu_e]) h2 (ih hρ)

/-- Weakening of continuation typing. -/
theorem ContTy.weaken {Γ : Ctx s} {K : Cont s} {T U S : Ty s} (h : ContTy Γ K T U) :
    ContTy (Γ.cons S) K.weaken T.weaken U.weaken :=
  h.rename Ctx.Renames.succ

/-! ## Typed states -/

/-- A closed typed program starts in a typed state. -/
theorem StateTy.init {t : Tm []} {T : Ty []} (h : HasTy .nil t T) :
    StateTy ⟨.nil, .nil, t.erase⟩ :=
  ⟨.nil, t, T, T, .nil, rfl, h, .nil⟩

/-- A typed annotated term whose type converts to the input type of the
continuation makes a typed state. -/
theorem StateTy.of {Γ : Ctx s} {σ : Store s} {K : Cont s} {t t1 : Tm s} {T0 T U : Ty s}
    (hσ : StoreTy Γ σ) (e : t1.erase = t) (h : HasTy Γ t1 T0)
    (hT : T0 = T ∨ ∃ c, CertTy Γ c T0 T) (hK : ContTy Γ K T U) :
    StateTy ⟨σ, K, t⟩ := by
  rcases hT with rfl | ⟨c, hc⟩
  · exact ⟨Γ, t1, T0, U, hσ, e, h, hK⟩
  · exact ⟨Γ, .cast t1 c, T, U, hσ, e, .cast h hc, hK⟩

/-- A path whose type converts to `T` gives a path of type `T` with the same
root. -/
theorem PathTy.retype {Γ : Ctx s} {p : Path s} {T0 T : Ty s} (hp : PathTy Γ p T0)
    (hT : T0 = T ∨ ∃ c, CertTy Γ c T0 T) : ∃ q : Path s, q.root = p.root ∧ PathTy Γ q T := by
  rcases hT with rfl | ⟨c, hc⟩
  · exact ⟨p, rfl, hp⟩
  · have hq := PathTy.cast hp hc
    refine ⟨_, ?_, hq⟩
    rfl

/-- A term that is not a cast and erases to a value is a value. -/
theorem Tm.val_of_erase {t : Tm s} {v : Value s} (hn : ∀ u c, t ≠ .cast u c)
    (e : t.erase = .val v) : ∃ v0, t = .val v0 ∧ v0.erase = v := by
  cases t with
  | val v0 =>
      simp only [Tm.erase, Tm.val.injEq] at e
      exact ⟨v0, rfl, e⟩
  | cast u c => exact absurd rfl (hn u c)
  | _ => simp [Tm.erase] at e

/-! ## Progress -/

/-- A typed state is final or steps. -/
theorem progress {st : State s} (h : StateTy st) :
    st.Final ∨ ∃ (s' : Sig) (st' : State s'), Step st st' := by
  obtain ⟨σ, K, t⟩ := st
  obtain ⟨Γ, t', T, U, hσ, he, ht, hK⟩ := h
  dsimp only at hσ he hK
  obtain ⟨t0, T0, e0, h0, hn, _⟩ := ht.strip
  rw [he] at e0
  subst e0
  cases h0 with
  | path hp =>
      cases K with
      | nil => exact .inl ⟨rfl, .inr ⟨_, rfl⟩⟩
      | cons K u => exact .inr ⟨_, _, .rename⟩
  | lam hb =>
      cases K with
      | nil => exact .inl ⟨rfl, .inl ⟨_, rfl⟩⟩
      | cons K u => exact .inr ⟨_, _, .alloc⟩
  | obj hd hdis =>
      cases K with
      | nil => exact .inl ⟨rfl, .inl ⟨_, rfl⟩⟩
      | cons K u => exact .inr ⟨_, _, .alloc⟩
  | app hp hq hpr =>
      obtain ⟨S0, b, T0b, hl, _⟩ := canonical_fun hσ hp
      exact .inr ⟨_, _, .app hl⟩
  | proj hp =>
      obtain ⟨d, t, b, T0', hl, hlt, _⟩ := canonical_obj hσ hp
      exact .inr ⟨_, _, .proj hl hlt⟩
  | «let» ha hb => exact .inr ⟨_, _, .let⟩
  | cast => exact absurd rfl (hn _ _)

/-! ## Preservation -/

/-- A step of a typed state reaches a typed state. -/
theorem preservation {st : State s} {st' : State s'} (h : StateTy st) (hstep : Step st st') :
    StateTy st' := by
  obtain ⟨Γ, t', T, U, hσ, he, ht, hK⟩ := h
  obtain ⟨t0, T0, e0, h0, hn, hT⟩ := ht.strip
  rw [he] at e0
  clear he ht
  cases hstep with
  | «let» =>
      dsimp only at hσ hK e0 ⊢
      cases h0 with
      | «let» ha hb =>
          simp only [Tm.erase, Tm.let.injEq] at e0
          obtain ⟨rfl, rfl⟩ := e0
          refine ⟨Γ, _, _, U, hσ, rfl, ha, ?_⟩
          rcases hT with rfl | ⟨c, hc⟩
          · exact .cons rfl hb hK
          · exact .cons (u' := .cast _ c.weaken) rfl (.cast hb (hc.weaken _)) hK
      | cast => exact absurd rfl (hn _ _)
      | _ => simp [Tm.erase] at e0
  | alloc =>
      dsimp only at hσ hK e0 ⊢
      cases hK with
      | cons hu_e hu hK' =>
          obtain ⟨v0, rfl, ev⟩ := Tm.val_of_erase hn e0
          have hσ' := StoreTy.cons hσ ⟨v0, ev, h0⟩
          rcases hT with rfl | ⟨c, hc⟩
          · exact ⟨_, _, _, _, hσ', hu_e, hu, hK'.weaken⟩
          · obtain ⟨u'', e'', hu''⟩ := HasTy.narrow hc hu
            exact ⟨_, u'', _, _, hσ', e''.trans hu_e, hu'', hK'.weaken⟩
  | rename =>
      dsimp only at hσ hK e0 ⊢
      cases hK with
      | cons hu_e hu hK' =>
          cases h0 with
          | path hp =>
              simp only [Tm.erase, Tm.path.injEq, Path.var.injEq] at e0
              subst e0
              obtain ⟨q, hqr, hq⟩ := PathTy.retype hp hT
              obtain ⟨u'', e'', hu''⟩ := HasTy.substPath hq hu
              rw [Ty.weaken_substVar] at hu''
              refine ⟨Γ, u'', _, U, hσ, ?_, hu'', hK'⟩
              rw [e'', hqr, hu_e]
          | cast => exact absurd rfl (hn _ _)
          | _ => simp [Tm.erase] at e0
  | app hl =>
      dsimp only at hσ hK e0 ⊢
      cases h0 with
      | app hp hq hpr =>
          simp only [Tm.erase, Tm.app.injEq, Path.var.injEq] at e0
          obtain ⟨rfl, rfl⟩ := e0
          obtain ⟨S0, b, T0b, hl', hb, ⟨c1, hc1⟩, ⟨c2, hc2⟩⟩ := canonical_fun hσ hp
          rw [hl] at hl'
          simp only [Value.lam.injEq] at hl'
          obtain ⟨rfl, rfl⟩ := hl'
          have hq1 := PathTy.cast hq (CertTy.stepEmbed hpr)
          have hq2 := PathTy.cast hq1 hc1
          obtain ⟨b', eb, hb'⟩ := HasTy.substPath hq2 hb
          obtain ⟨d', hd'⟩ := CertTy.substPath hq1 hc2
          exact StateTy.of hσ (t1 := .cast b' d') eb (.cast hb' hd') hT hK
      | cast => exact absurd rfl (hn _ _)
      | _ => simp [Tm.erase] at e0
  | proj hl hlt =>
      dsimp only at hσ hK e0 ⊢
      cases h0 with
      | proj hp =>
          simp only [Tm.erase, Tm.proj.injEq, Path.var.injEq] at e0
          obtain ⟨rfl, rfl⟩ := e0
          obtain ⟨d2, t2, b, T0', hl2, hlt2, eb, hb, ⟨c, hc⟩⟩ := canonical_obj hσ hp
          rw [hl] at hl2
          cases hl2
          rw [hlt] at hlt2
          cases hlt2
          exact StateTy.of hσ (t1 := .cast b c) eb (.cast hb hc) hT hK
      | cast => exact absurd rfl (hn _ _)
      | _ => simp [Tm.erase] at e0

/-! ## Safety -/

/-- Typed states stay typed along any run. -/
theorem StateTy.steps {st : State s} {st' : State s'} (h : StateTy st) (hs : Steps st st') :
    StateTy st' := by
  induction hs with
  | refl => exact h
  | tail _ hstep ih => exact preservation (ih h) hstep

/-- A closed typed program never reaches a stuck state. -/
theorem safety {t : Tm []} {T : Ty []} {st : State s} (ht : HasTy .nil t T)
    (hs : Steps ⟨.nil, .nil, t.erase⟩ st) : ¬ st.Stuck := by
  intro ⟨hnf, hns⟩
  rcases progress ((StateTy.init ht).steps hs) with hf | hst
  · exact hnf hf
  · exact hns hst

end SelDot
