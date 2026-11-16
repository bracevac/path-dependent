import Coercions.Selective.Fsub
/-!
# Probe P1: the reduction relation and the substitution concessions

* A standard capture-avoiding term substitution `Tm.substStd` (it shifts the substituted
  term under term binders) and the matching call-by-value relation `StepStd`.
* On term-closed terms `Tm.subst` agrees with `Tm.substStd`, `Step` preserves term-closedness,
  and `Step` coincides with `StepStd`; hence `safety` is a statement about standard CBV.
* Reducts of cast-free terms are cast-free; `Tm.substTy` never meets a cast along `Steps t.erase`.
* `Step` captures on open terms, and with it preservation is false in a nonempty term context.
* `Step` is deterministic; declarative preservation `fsub_preservation` follows.
-/
namespace SelFsub

/-! ## Term-closedness -/

/-- All free term variables are below `k`. -/
def Tm.cl : {n : Nat} → Nat → Tm n → Prop
  | _, k, .var x => x < k
  | _, k, .lam _ t => Tm.cl (k+1) t
  | _, k, .app t u => Tm.cl k t ∧ Tm.cl k u
  | _, k, .tlam _ t => Tm.cl k t
  | _, k, .tapp t _ => Tm.cl k t
  | _, k, .cast t _ => Tm.cl k t

theorem Tm.cl_mono : (t : Tm n) → ∀ {k k'}, k ≤ k' → Tm.cl k t → Tm.cl k' t
  | .var _, _, _, h, h' => by simp only [Tm.cl] at *; omega
  | .lam _ t, _, _, h, h' => Tm.cl_mono t (by omega) h'
  | .app t u, _, _, h, h' => ⟨Tm.cl_mono t h h'.1, Tm.cl_mono u h h'.2⟩
  | .tlam _ t, _, _, h, h' => Tm.cl_mono t h h'
  | .tapp t _, _, _, h, h' => Tm.cl_mono t h h'
  | .cast t _, _, _, h, h' => Tm.cl_mono t h h'

theorem Tm.cl_renTy : (t : Tm n) → ∀ {m k} (ρ : Fin n → Fin m), Tm.cl k t → Tm.cl k (t.renTy ρ)
  | .var _, _, _, _, h => h
  | .lam _ t, _, _, ρ, h => Tm.cl_renTy t ρ h
  | .app t u, _, _, ρ, h => ⟨Tm.cl_renTy t ρ h.1, Tm.cl_renTy u ρ h.2⟩
  | .tlam _ t, _, _, ρ, h => Tm.cl_renTy t (liftRen ρ) h
  | .tapp t _, _, _, ρ, h => Tm.cl_renTy t ρ h
  | .cast t _, _, _, ρ, h => Tm.cl_renTy t ρ h

theorem Tm.cl_substTy : (t : Tm n) → ∀ {m k} (σ : Fin n → Ty m), Tm.cl k t → Tm.cl k (t.substTy σ)
  | .var _, _, _, _, h => h
  | .lam _ t, _, _, σ, h => Tm.cl_substTy t σ h
  | .app t u, _, _, σ, h => ⟨Tm.cl_substTy t σ h.1, Tm.cl_substTy u σ h.2⟩
  | .tlam _ t, _, _, σ, h => Tm.cl_substTy t (liftS σ) h
  | .tapp t _, _, _, σ, h => Tm.cl_substTy t σ h
  | .cast t _, _, _, σ, h => Tm.cl_substTy t σ h

theorem Tm.cl_subst : (t : Tm n) → ∀ {k} {w : Tm n}, Tm.cl (k+1) t → Tm.cl 0 w →
    Tm.cl k (t.subst k w)
  | .var x, k, w, h, hw => by
    simp only [Tm.subst]; split
    · simp only [Tm.cl]; assumption
    · split
      · exact Tm.cl_mono w (Nat.zero_le _) hw
      · simp only [Tm.cl] at h ⊢; omega
  | .lam _ t, _, _, h, hw => Tm.cl_subst t h hw
  | .app t u, _, _, h, hw => ⟨Tm.cl_subst t h.1 hw, Tm.cl_subst u h.2 hw⟩
  | .tlam _ t, _, _, h, hw => Tm.cl_subst t h (Tm.cl_renTy _ _ hw)
  | .tapp t _, _, _, h, hw => Tm.cl_subst t h hw
  | .cast t _, _, _, h, hw => Tm.cl_subst t h hw

theorem Tm.cl_erase : (t : Tm n) → ∀ {k}, Tm.cl k t → Tm.cl k t.erase
  | .var _, _, h => h
  | .lam _ t, _, h => Tm.cl_erase t h
  | .app t u, _, h => ⟨Tm.cl_erase t h.1, Tm.cl_erase u h.2⟩
  | .tlam _ t, _, h => Tm.cl_erase t h
  | .tapp t _, _, h => Tm.cl_erase t h
  | .cast t _, _, h => Tm.cl_erase t h

/-- Typed terms are closed at the length of their term context. -/
theorem HTy.cl (h : HTy Γ Δ t T) : Tm.cl Δ.length t := by
  induction h with
  | var e => exact (List.getElem?_eq_some_iff.mp e).1
  | lam _ ih => exact ih
  | app _ _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | tlam _ ih => simpa [List.length_map] using ih
  | tapp _ _ ih => exact ih
  | cast _ _ ih => exact ih

/-! ## Standard capture-avoiding substitution -/

/-- Shift term variables `≥ c` up by one. -/
def Tm.shift : {n : Nat} → Nat → Tm n → Tm n
  | _, c, .var x => if x < c then .var x else .var (x+1)
  | _, c, .lam S t => .lam S (Tm.shift (c+1) t)
  | _, c, .app t u => .app (Tm.shift c t) (Tm.shift c u)
  | _, c, .tlam S t => .tlam S (Tm.shift c t)
  | _, c, .tapp t U => .tapp (Tm.shift c t) U
  | _, c, .cast t d => .cast (Tm.shift c t) d

/-- `[k ↦ w]t`, the substituted term shifted under every term binder it crosses. -/
def Tm.substStd : {n : Nat} → Tm n → Nat → Tm n → Tm n
  | _, .var x, k, w => if x < k then .var x else if x = k then w else .var (x - 1)
  | _, .lam S t, k, w => .lam S (Tm.substStd t (k+1) (Tm.shift 0 w))
  | _, .app t u, k, w => .app (Tm.substStd t k w) (Tm.substStd u k w)
  | _, .tlam S t, k, w => .tlam S (Tm.substStd t k (w.renTy Fin.succ))
  | _, .tapp t U, k, w => .tapp (Tm.substStd t k w) U
  | _, .cast t c, k, w => .cast (Tm.substStd t k w) c

theorem Tm.shift_cl : (t : Tm n) → ∀ {c}, Tm.cl c t → Tm.shift c t = t
  | .var x, c, h => by simp only [Tm.cl] at h; simp [Tm.shift, h]
  | .lam _ t, _, h => by simp only [Tm.shift, Tm.shift_cl t h]
  | .app t u, _, h => by simp only [Tm.shift, Tm.shift_cl t h.1, Tm.shift_cl u h.2]
  | .tlam _ t, _, h => by simp only [Tm.shift, Tm.shift_cl t h]
  | .tapp t _, _, h => by simp only [Tm.shift, Tm.shift_cl t h]
  | .cast t _, _, h => by simp only [Tm.shift, Tm.shift_cl t h]

/-- On a term-closed `w`, the authors' substitution is the standard one. -/
theorem Tm.substStd_eq : (t : Tm n) → ∀ {k} {w : Tm n}, Tm.cl 0 w → Tm.substStd t k w = t.subst k w
  | .var _, _, _, _ => rfl
  | .lam _ t, _, w, hw => by
    simp only [Tm.substStd, Tm.subst, Tm.shift_cl w hw, Tm.substStd_eq t hw]
  | .app t u, _, _, hw => by simp only [Tm.substStd, Tm.subst, Tm.substStd_eq t hw, Tm.substStd_eq u hw]
  | .tlam _ t, _, w, hw => by
    simp only [Tm.substStd, Tm.subst, Tm.substStd_eq t (Tm.cl_renTy w _ hw)]
  | .tapp t _, _, _, hw => by simp only [Tm.substStd, Tm.subst, Tm.substStd_eq t hw]
  | .cast t _, _, _, hw => by simp only [Tm.substStd, Tm.subst, Tm.substStd_eq t hw]

/-- Standard call-by-value reduction (TAPL Fig. 26-1, E-App1, E-App2, E-AppAbs, E-TApp,
E-TappTabs). -/
inductive StepStd : Tm n → Tm n → Prop where
  | beta : Value v → StepStd (.app (.lam S e) v) (Tm.substStd e 0 v)
  | tbeta : StepStd (.tapp (.tlam S e) U) (e.substTy (sub0 U))
  | appL : StepStd t t' → StepStd (.app t u) (.app t' u)
  | appR : Value v → StepStd u u' → StepStd (.app v u) (.app v u')
  | tappL : StepStd t t' → StepStd (.tapp t U) (.tapp t' U)

inductive StepsStd : Tm n → Tm n → Prop where
  | refl : StepsStd e e
  | step : StepStd e e' → StepsStd e' e'' → StepsStd e e''

theorem Step.cl (hs : Step e e') (h : Tm.cl 0 e) : Tm.cl 0 e' := by
  induction hs with
  | beta _ => exact Tm.cl_subst _ h.1 h.2
  | tbeta => exact Tm.cl_substTy _ _ h
  | appL _ ih => exact ⟨ih h.1, h.2⟩
  | appR _ _ ih => exact ⟨h.1, ih h.2⟩
  | tappL _ ih => exact ih h

/-- On term-closed terms the authors' `Step` is standard call-by-value. -/
theorem step_iff_std (h : Tm.cl 0 e) : Step e e' ↔ StepStd e e' := by
  constructor
  · intro hs; induction hs with
    | beta hv => rw [← Tm.substStd_eq _ h.2]; exact .beta hv
    | tbeta => exact .tbeta
    | appL _ ih => exact .appL (ih h.1)
    | appR hv _ ih => exact .appR hv (ih h.2)
    | tappL _ ih => exact .tappL (ih h)
  · intro hs; induction hs with
    | beta hv => rw [Tm.substStd_eq _ h.2]; exact .beta hv
    | tbeta => exact .tbeta
    | appL _ ih => exact .appL (ih h.1)
    | appR hv _ ih => exact .appR hv (ih h.2)
    | tappL _ ih => exact .tappL (ih h)

theorem steps_iff_std (h : Tm.cl 0 e) : Steps e e' ↔ StepsStd e e' := by
  constructor
  · intro hs; induction hs with
    | refl => exact .refl
    | step s _ ih => exact .step ((step_iff_std h).mp s) (ih (s.cl h))
  · intro hs; induction hs with
    | refl => exact .refl
    | step s _ ih =>
      have s' := (step_iff_std h).mpr s
      exact .step s' (ih (s'.cl h))

theorem Steps.cl (hs : Steps e e') (h : Tm.cl 0 e) : Tm.cl 0 e' := by
  induction hs with
  | refl => exact h
  | step s _ ih => exact ih (s.cl h)

/-- `safety`, restated for standard call-by-value. -/
theorem safety_std {t : Tm n} (h : HTy Γ [] t T) (hs : StepsStd t.erase e) :
    Value e ∨ ∃ e', StepStd e e' := by
  have hc : Tm.cl 0 t.erase := Tm.cl_erase _ h.cl
  have hs' := (steps_iff_std hc).mpr hs
  have he : Tm.cl 0 e := hs'.cl hc
  rcases safety h hs' with hv | ⟨e', s⟩
  · exact .inl hv
  · exact .inr ⟨e', (step_iff_std he).mp s⟩

/-! ## Cast-freeness along reduction -/

theorem Tm.substTy_castfree : (t : Tm n) → ∀ {m} (σ : Fin n → Ty m),
    (t.substTy σ).erase = t.substTy σ
  | .var _, _, _ => rfl
  | .lam _ t, _, σ => by simp only [Tm.substTy, Tm.erase, Tm.substTy_castfree t]
  | .app t u, _, σ => by simp only [Tm.substTy, Tm.erase, Tm.substTy_castfree t, Tm.substTy_castfree u]
  | .tlam _ t, _, σ => by simp only [Tm.substTy, Tm.erase, Tm.substTy_castfree t]
  | .tapp t _, _, σ => by simp only [Tm.substTy, Tm.erase, Tm.substTy_castfree t]
  | .cast t _, _, σ => Tm.substTy_castfree t σ

/-- `substTy` erases: applied to an annotated term it gives the substituted erasure. -/
theorem Tm.substTy_erase : (t : Tm n) → ∀ {m} (σ : Fin n → Ty m), t.substTy σ = t.erase.substTy σ
  | .var _, _, _ => rfl
  | .lam _ t, _, σ => by simp only [Tm.substTy, Tm.erase, Tm.substTy_erase t]
  | .app t u, _, σ => by simp only [Tm.substTy, Tm.erase, Tm.substTy_erase t, Tm.substTy_erase u]
  | .tlam _ t, _, σ => by simp only [Tm.substTy, Tm.erase, Tm.substTy_erase t]
  | .tapp t _, _, σ => by simp only [Tm.substTy, Tm.erase, Tm.substTy_erase t]
  | .cast t _, _, σ => Tm.substTy_erase t σ

def CastFree (t : Tm n) : Prop := t.erase = t

theorem Step.castfree (hs : Step e e') (h : CastFree e) : CastFree e' := by
  induction hs with
  | beta _ =>
    simp only [CastFree, Tm.erase, Tm.app.injEq, Tm.lam.injEq, true_and] at h
    simp only [CastFree, Tm.erase_subst, h.1, h.2]
  | tbeta => exact Tm.substTy_castfree _ _
  | appL _ ih =>
    simp only [CastFree, Tm.erase, Tm.app.injEq] at h ⊢; exact ⟨ih h.1, h.2⟩
  | appR _ _ ih =>
    simp only [CastFree, Tm.erase, Tm.app.injEq] at h ⊢; exact ⟨h.1, ih h.2⟩
  | tappL _ ih =>
    simp only [CastFree, Tm.erase, Tm.tapp.injEq, and_true] at h ⊢; exact ih h

/-- Every term on a reduction sequence from an erased term is cast-free; in particular the
`tbeta` steps along it apply `substTy` only to cast-free bodies. -/
theorem Steps.castfree {t : Tm n} (hs : Steps t.erase e) : CastFree e := by
  generalize e₀ : t.erase = a at hs
  have h : CastFree a := e₀ ▸ Tm.erase_erase t
  clear e₀; induction hs with
  | refl => exact h
  | step s _ ih => exact ih (s.castfree h)

/-! ## Step is deterministic

These two lemmas now also live in `SelFsub/Safety.lean` (`Value.no_step`, `Step.det`),
so the copies here carry a prime. -/

theorem Value.no_step' (hv : Value v) : ¬ Step v e := by
  intro hs; cases hv <;> cases hs

theorem Step.det' (h₁ : Step e e₁) (h₂ : Step e e₂) : e₁ = e₂ := by
  induction h₁ generalizing e₂ with
  | beta hv =>
    cases h₂ with
    | beta => rfl
    | appL h => cases h
    | appR _ h => exact absurd h hv.no_step
  | tbeta => cases h₂ with
    | tbeta => rfl
    | tappL h => cases h
  | appL h ih => cases h₂ with
    | beta => cases h
    | appL h' => rw [ih h']
    | appR hv _ => exact absurd h hv.no_step
  | appR hv h ih => cases h₂ with
    | beta hv' => exact absurd h hv'.no_step
    | appL h' => exact absurd h' hv.no_step
    | appR _ h' => rw [ih h']
  | tappL h ih => cases h₂ with
    | tbeta => cases h
    | tappL h' => rw [ih h']

/-! ## Declarative preservation, from the direct proof and the two translations -/

theorem fsub_preservation (h : FTy Γ [] e T) (hs : Step e e') : FTy Γ [] e' T := by
  obtain ⟨t, rfl, ht⟩ := elaboration_complete h
  obtain ⟨t', rfl, ht'⟩ := preservation ht hs
  exact elaboration_typed ht'

/-! ## Capture-avoidance on closed programs: the requested examples -/

/-- In `X <: Top` (`X = var 0`): `v = λ(a : X). a`, body `Λ(Y <: Top). λ(z : Y). x`. -/
def capV : Tm 1 := .lam (.var 0) (.var 0)
def capBody : Tm 1 := .tlam .top (.lam (.var 0) (.var 1))
def capRedex : Tm 1 := .app (.lam (.arr (.var 0) (.var 0)) capBody) capV
/-- The capture-avoiding reduct: under `Y`, `X` is `var 1`. -/
def capReduct : Tm 1 := .tlam .top (.lam (.var 0) (.lam (.var 1) (.var 0)))

theorem cap_step : Step capRedex capReduct := .beta .lam
theorem cap_std : Tm.substStd capBody 0 capV = capReduct := rfl
theorem cap_typed :
    HTy (.snoc .nil .top) [] capRedex (.all .top (.arr (.var 0) (.arr (.var 1) (.var 1)))) ∧
    HTy (.snoc .nil .top) [] capReduct (.all .top (.arr (.var 0) (.arr (.var 1) (.var 1)))) := by
  decide

/-- Substitution under `λ` and `Λ` nested twice, with a value whose type mentions the context:
`(λ(x : X → X). λ(p : Top). Λ(Y <: X). λ(q : Y). Λ(W <: Y). x) v`. -/
def cap2Body : Tm 1 :=
  .lam .top (.tlam (.var 0) (.lam (.var 0) (.tlam (.var 0) (.var 2))))
def cap2Redex : Tm 1 := .app (.lam (.arr (.var 0) (.var 0)) cap2Body) capV
def cap2Reduct : Tm 1 :=
  .lam .top (.tlam (.var 0) (.lam (.var 0) (.tlam (.var 0) (.lam (.var 2) (.var 0)))))
theorem cap2_step : Step cap2Redex cap2Reduct := .beta .lam
theorem cap2_std : Tm.substStd cap2Body 0 capV = cap2Reduct := rfl
theorem cap2_types : synthTm (.snoc .nil .top) [] cap2Redex = synthTm (.snoc .nil .top) [] cap2Reduct ∧
    (synthTm (.snoc .nil .top) [] cap2Redex).isSome := by decide

/-! ## Open terms: `Step` captures, and preservation fails in a nonempty term context -/

/-- `x₀ : Top → Top ⊢ (λ(x : Top → Top → Top). λ(y : Top). x) (λ(z : Top). x₀)`. -/
def openW : Tm 0 := .lam .top (.var 1)
def openRedex : Tm 0 :=
  .app (.lam (.arr .top (.arr .top .top)) (.lam .top (.var 1))) openW
/-- What `Step` produces: `x₀` is captured by `λ(y : Top)`. -/
def openReduct : Tm 0 := .lam .top (.lam .top (.var 1))

theorem open_step : Step openRedex openReduct := .beta .lam
theorem open_capture : Tm.substStd (.lam .top (.var 1)) 0 openW ≠ openReduct := by decide
theorem open_typed :
    HTy .nil [.arr .top .top] openRedex (.arr .top (.arr .top (.arr .top .top))) := by decide

/-- A variable under casts. -/
theorem HTy.canon_var {t : Tm n} (h : HTy Γ Δ t T) (e : t.erase = .var x) :
    ∃ T₀ c, Δ[x]? = some T₀ ∧ CTy Γ c T₀ T := by
  induction h with
  | var ex => cases e; exact ⟨_, _, ex, .step .refl⟩
  | cast _ hc ih => obtain ⟨T₀, c, ex, hc'⟩ := ih e; exact ⟨T₀, _, ex, .seq hc' hc⟩
  | _ => cases e

/-- No annotation of the captured reduct has the redex's type: with the authors' `Step`,
preservation is false for the term context `[Top → Top]`. -/
theorem open_preservation_fails :
    ¬ ∃ t' : Tm 0, t'.erase = openReduct ∧
      HTy .nil [.arr .top .top] t' (.arr .top (.arr .top (.arr .top .top))) := by
  rintro ⟨t', e, h⟩
  obtain ⟨b, T₀, c, eb, hb, hc⟩ := h.canon_lam e
  obtain ⟨b', T₁, c', eb', hb', hc'⟩ := hb.canon_lam eb
  obtain ⟨T₂, c'', ex, hc''⟩ := hb'.canon_var eb'
  simp at ex; subst ex
  have hT₁ := hc''.top_inv rfl; subst hT₁
  rcases hc.arr_inv with he | ⟨_, _, he, _, hcod⟩
  · cases he
  · cases he
    rcases hc'.arr_inv with he' | ⟨_, _, he', _, hcod'⟩
    · subst he'; exact absurd (hcod.top_inv rfl) (by simp)
    · subst he'
      rcases hcod.arr_inv with he'' | ⟨_, _, he'', _, hcod''⟩
      · cases he''
      · cases he''; exact absurd (hcod''.top_inv (hcod'.top_inv rfl)) (by simp)

/-! ## Axioms -/

#print axioms step_iff_std
#print axioms steps_iff_std
#print axioms safety_std
#print axioms Steps.castfree
#print axioms Tm.substTy_erase
#print axioms Step.det'
#print axioms fsub_preservation
#print axioms cap_typed
#print axioms cap2_types
#print axioms open_capture
#print axioms open_preservation_fails

end SelFsub
