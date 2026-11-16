import Coercions.Selective.Fsub.Typing
/-!
# Reduction and direct type safety

Call-by-value reduction on erased terms; the values are the abstractions. Safety is
proved for the annotated calculus directly, with the invariant "the erased term has a
typed annotation": a step of the erased term is matched by a new annotated term over the
reduct, of the same type. Neither declarative F-sub (`Sub`, `FTy`) nor its soundness is
used; this module does not import them.

The ingredients are local operations of the subtyping layer:

- canonical forms through casts: an abstraction under any number of casts has its own
  type and the composed certificate (`HTy.canon_lam`, `HTy.canon_tlam`), which
  `CTy.arr_inv` and `CTy.all_inv` split;
- β: the argument is cast to the abstraction's own domain by `step[V, S] ; dom`, and the
  result by the codomain certificate (`HTy.subst` is exact, no re-annotation);
- type-β: `HTy.substTy` transports a typing along a certified substitution. Casts are
  transported by `Cert.subst`; an implicit argument step becomes a cast on the argument,
  and an implicit bound step a cast on the callee by `Cert.allBound`.

Preservation and progress hold in every type context `Γ` for terms closed in term
variables.
-/
namespace SelFsub

inductive Value : Tm n → Prop where
  | lam : Value (.lam S e)
  | tlam : Value (.tlam S e)

inductive Step : Tm n → Tm n → Prop where
  | beta : Value v → Step (.app (.lam S e) v) (e.subst 0 v)
  | tbeta : Step (.tapp (.tlam S e) U) (e.substTy (sub0 U))
  | appL : Step t t' → Step (.app t u) (.app t' u)
  | appR : Value v → Step u u' → Step (.app v u) (.app v u')
  | tappL : Step t t' → Step (.tapp t U) (.tapp t' U)

inductive Steps : Tm n → Tm n → Prop where
  | refl : Steps e e
  | step : Step e e' → Steps e' e'' → Steps e e''

/-! ## Renaming and term substitution -/

theorem HTy.renTy {Γ : Ctx n} {Γ' : Ctx m} {ρ : Fin n → Fin m} (hρ : TyRen Γ Γ' ρ)
    (h : HTy Γ Δ t T) : HTy Γ' (Δ.map (Ty.rename ρ)) (t.renTy ρ) (T.rename ρ) := by
  induction h generalizing m with
  | var e => exact .var (by rw [List.getElem?_map, e]; rfl)
  | lam _ ih => exact .lam (ih hρ)
  | app _ _ hp ih₁ ih₂ => exact .app (ih₁ hρ) (ih₂ hρ) (hp.rename hρ)
  | @tlam _ _ _ _ Δ _ _ ih =>
    have e : (Δ.map Ty.weaken).map (Ty.rename (liftRen ρ)) =
        (Δ.map (Ty.rename ρ)).map Ty.weaken := by
      simp only [List.map_map]; congr 1; funext A; exact (A.rename_weaken ρ).symm
    exact .tlam (e ▸ ih (hρ.lift _))
  | tapp _ hp ih => rw [Ty.rename_sub0]; exact .tapp (ih hρ) (hp.rename hρ)
  | cast _ hc ih => exact .cast (ih hρ) (hc.rename hρ)

/-- Term variables beyond the context may be added on the outside. -/
theorem HTy.append (h : HTy Γ Δ t T) : ∀ Δ', HTy Γ (Δ ++ Δ') t T := by
  induction h with
  | var e =>
    intro Δ'
    exact .var (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp e).1]; exact e)
  | lam _ ih => intro Δ'; exact .lam (ih Δ')
  | app _ _ hp ih₁ ih₂ => intro Δ'; exact .app (ih₁ Δ') (ih₂ Δ') hp
  | tlam _ ih =>
    intro Δ'; have := ih (Δ'.map Ty.weaken); rw [← List.map_append] at this; exact .tlam this
  | tapp _ hp ih => intro Δ'; exact .tapp (ih Δ') hp
  | cast _ hc ih => intro Δ'; exact .cast (ih Δ') hc

/-- Substitution of a term-closed `w` of exactly the variable's type. -/
theorem HTy.subst (h : HTy Γ (Δ ++ [S]) t T) (hw : HTy Γ [] w S) :
    HTy Γ Δ (t.subst Δ.length w) T := by
  generalize e : Δ ++ [S] = Δ₀ at h
  induction h with
  | @var _ _ x _ _ ex =>
    subst e; simp only [Tm.subst]; split
    · next hx => exact .var (by rw [List.getElem?_append_left hx] at ex; exact ex)
    · split
      · next hx => subst hx; rw [List.getElem?_concat_length] at ex; cases ex; exact hw.append Δ
      · rw [List.getElem?_eq_none (by simp; omega)] at ex; cases ex
  | lam _ ih => exact .lam (ih (Δ := _ :: Δ) hw (by rw [← e]; rfl))
  | app _ _ hp ih₁ ih₂ => exact .app (ih₁ hw e) (ih₂ hw e) hp
  | tlam _ ih =>
    have := ih (Δ := Δ.map Ty.weaken) (hw.renTy (TyRen.weaken _ _))
      (by rw [← e, List.map_append]; rfl)
    rw [List.length_map] at this; exact .tlam this
  | tapp _ hp ih => exact .tapp (ih hw e) hp
  | cast _ hc ih => exact .cast (ih hw e) hc

/-! ## Type substitution with re-annotation -/

/-- A typing transported along a certified substitution: some re-annotation of the
substituted erased term is typed. The argument of an application is cast by the
substituted primitive step, and the callee of a type application by the bound lift of
the substituted bound step; casts are transported by `Cert.subst`. -/
theorem HTy.substTy {Γ : Ctx n} {Γ' : Ctx m} {σ τ} (hτ : CSub Γ Γ' σ τ)
    (h : HTy Γ Δ t T) :
    ∃ t', t'.erase = t.erase.substTy σ ∧ HTy Γ' (Δ.map (Ty.subst σ)) t' (T.subst σ) := by
  induction h generalizing m with
  | var e => exact ⟨.var _, rfl, .var (by rw [List.getElem?_map, e]; rfl)⟩
  | lam _ ih =>
    obtain ⟨b, eb, hb⟩ := ih hτ
    exact ⟨.lam _ b, by simp only [Tm.erase, Tm.substTy, eb], .lam hb⟩
  | app _ _ hp ih₁ ih₂ =>
    obtain ⟨f, ef, hf⟩ := ih₁ hτ; obtain ⟨u, eu, hu⟩ := ih₂ hτ
    exact ⟨.app f (.cast u ((Cert.step _ _).subst σ τ)),
      by simp only [Tm.erase, Tm.substTy, ef, eu],
      .app hf (.cast hu ((CTy.step hp).subst hτ)) .refl⟩
  | @tlam _ _ _ _ Δ _ _ ih =>
    obtain ⟨b, eb, hb⟩ := ih (hτ.lift _)
    have e : (Δ.map Ty.weaken).map (Ty.subst (liftS σ)) =
        (Δ.map (Ty.subst σ)).map Ty.weaken := by
      simp only [List.map_map]; congr 1; funext A; exact A.weaken_subst σ
    exact ⟨.tlam _ b, by simp only [Tm.erase, Tm.substTy, eb], .tlam (e ▸ hb)⟩
  | tapp _ hp ih =>
    obtain ⟨f, ef, hf⟩ := ih hτ
    rw [Ty.subst_sub0]
    exact ⟨.tapp (.cast f (((Cert.step _ _).subst σ τ).allBound _)) _,
      by simp only [Tm.erase, Tm.substTy, ef],
      .tapp (.cast hf (((CTy.step hp).subst hτ).allBound _)) .refl⟩
  | cast _ hc ih =>
    obtain ⟨u, eu, hu⟩ := ih hτ; exact ⟨_, by exact eu, .cast hu (hc.subst hτ)⟩

/-! ## Canonical forms through casts -/

theorem HTy.canon_lam {t : Tm n} (h : HTy Γ Δ t T) (e : t.erase = .lam S e₀) :
    ∃ b T₀ c, b.erase = e₀ ∧ HTy Γ (S :: Δ) b T₀ ∧ CTy Γ c (.arr S T₀) T := by
  induction h with
  | lam hb => cases e; exact ⟨_, _, _, rfl, hb, .step .refl⟩
  | cast _ hc ih =>
    obtain ⟨b, T₀, c, eb, hb, hc'⟩ := ih e; exact ⟨b, T₀, _, eb, hb, .seq hc' hc⟩
  | _ => cases e

theorem HTy.canon_tlam {t : Tm n} (h : HTy Γ Δ t T) (e : t.erase = .tlam S e₀) :
    ∃ b T₀ c, b.erase = e₀ ∧ HTy (Γ.snoc S) (Δ.map Ty.weaken) b T₀ ∧
      CTy Γ c (.all S T₀) T := by
  induction h with
  | tlam hb => cases e; exact ⟨_, _, _, rfl, hb, .step .refl⟩
  | cast _ hc ih =>
    obtain ⟨b, T₀, c, eb, hb, hc'⟩ := ih e; exact ⟨b, T₀, _, eb, hb, .seq hc' hc⟩
  | _ => cases e

/-! ## Preservation, progress, safety -/

theorem preservation {t : Tm n} (h : HTy Γ [] t T) (hs : Step t.erase e') :
    ∃ t', t'.erase = e' ∧ HTy Γ [] t' T := by
  generalize eΔ : ([] : List (Ty _)) = Δ at h
  induction h with
  | var | lam | tlam => cases hs
  | @app _ _ _ f S T u V hf hu hp ih₁ ih₂ =>
    subst eΔ; change Step (.app f.erase u.erase) _ at hs
    generalize ef : f.erase = a at hs; generalize eu : u.erase = a' at hs
    cases hs with
    | beta =>
      obtain ⟨b, T₀, c, eb, hb, hc⟩ := hf.canon_lam ef
      rcases hc.arr_inv with he | ⟨_, _, he, hdom, hcod⟩
      · cases he
      · cases he
        refine ⟨.cast (b.subst 0 (.cast u (.seq (.step V S) c.arrInv.1))) c.arrInv.2, ?_,
          .cast (HTy.subst (Δ := []) hb (.cast hu (.seq (.step hp) hdom))) hcod⟩
        simp only [Tm.erase, Tm.erase_subst, eb, eu]
    | appL hs =>
      obtain ⟨f', e₁, h₁⟩ := ih₁ (ef ▸ hs) rfl
      exact ⟨.app f' u, by simp only [Tm.erase, e₁, eu], .app h₁ hu hp⟩
    | appR _ hs =>
      obtain ⟨u', e₁, h₁⟩ := ih₂ (eu ▸ hs) rfl
      exact ⟨.app f u', by simp only [Tm.erase, e₁, ef], .app hf h₁ hp⟩
  | @tapp _ _ _ f S T U hf hp ih =>
    subst eΔ; change Step (.tapp f.erase U) _ at hs
    generalize ef : f.erase = a at hs
    cases hs with
    | tbeta =>
      obtain ⟨b, T₀, c, eb, hb, hc⟩ := hf.canon_tlam ef
      rcases hc.all_inv with he | ⟨_, _, he, hbnd, hbody⟩
      · cases he
      · cases he
        obtain ⟨b', eb', hb'⟩ := hb.substTy (CSub.inst (.seq (.step hp) hbnd) .nil)
        exact ⟨.cast b' (c.allInv.2.inst 0 U (.step U S)),
          by simp only [Tm.erase, eb', eb]; rfl, .cast hb' (CTy.inst .nil (.step hp) hbody)⟩
    | tappL hs =>
      obtain ⟨f', e₁, h₁⟩ := ih (ef ▸ hs) rfl
      exact ⟨.tapp f' U, by simp only [Tm.erase, e₁], .tapp h₁ hp⟩
  | cast _ hc ih =>
    obtain ⟨t', e₁, h₁⟩ := ih hs eΔ; exact ⟨.cast t' _, by exact e₁, .cast h₁ hc⟩

theorem progress {t : Tm n} (h : HTy Γ [] t T) : Value t.erase ∨ ∃ e', Step t.erase e' := by
  generalize eΔ : ([] : List (Ty _)) = Δ at h
  induction h with
  | var e => subst eΔ; simp at e
  | lam => exact .inl .lam
  | tlam => exact .inl .tlam
  | @app _ _ _ f S T u V hf hu hp ih₁ ih₂ =>
    simp only [Tm.erase]
    rcases ih₁ eΔ with hv | ⟨_, hs⟩
    · rcases ih₂ eΔ with hv' | ⟨_, hs'⟩
      · generalize ef : f.erase = a at hv ⊢
        cases hv with
        | lam => exact .inr ⟨_, .beta hv'⟩
        | tlam =>
          obtain ⟨_, _, _, -, -, hc⟩ := hf.canon_tlam ef
          rcases hc.all_inv with he | ⟨_, _, he, -⟩ <;> cases he
      · exact .inr ⟨_, .appR hv hs'⟩
    · exact .inr ⟨_, .appL hs⟩
  | @tapp _ _ _ f S T U hf hp ih =>
    simp only [Tm.erase]
    rcases ih eΔ with hv | ⟨_, hs⟩
    · generalize ef : f.erase = a at hv ⊢
      cases hv with
      | tlam => exact .inr ⟨_, .tbeta⟩
      | lam =>
        obtain ⟨_, _, _, -, -, hc⟩ := hf.canon_lam ef
        rcases hc.arr_inv with he | ⟨_, _, he, -⟩ <;> cases he
    · exact .inr ⟨_, .tappL hs⟩
  | cast _ _ ih => exact ih eΔ

theorem safety {t : Tm n} (h : HTy Γ [] t T) (hs : Steps t.erase e) :
    Value e ∨ ∃ e', Step e e' := by
  generalize e₀ : t.erase = a at hs
  induction hs generalizing t with
  | refl => exact e₀ ▸ progress h
  | step s _ ih => subst e₀; obtain ⟨t', e₁, h'⟩ := preservation h s; exact ih h' e₁

/-! ## Determinism -/

theorem Value.no_step (hv : Value v) : ¬ Step v e := by
  intro hs; cases hv <;> cases hs

theorem Step.det (h₁ : Step e e₁) (h₂ : Step e e₂) : e₁ = e₂ := by
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

end SelFsub
