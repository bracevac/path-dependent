import Coercions.Selective.FsubDeclarative.Sub
/-!
# Declarative typing: renaming, substitution, canonical forms

Lemmas about `FTy`, ordinary full F-sub typing with subsumption over `Sub`. Each is an
induction on the typing; the subsumption case maps the `Sub` derivation by the
corresponding subtyping lemma. Term substitution takes a term of exactly the variable's
type (callers reach it by subsumption). Type substitution is along a `TySub` and maps
each `Sub` premise by `Sub.subst`; canonical forms compose the subsumptions by `trans`.
-/
namespace SelFsub

/-! ## Renaming and term substitution -/

theorem FTy.renTy {Γ : Ctx n} {Γ' : Ctx m} {ρ : Fin n → Fin m} (hρ : TyRen Γ Γ' ρ)
    (h : FTy Γ Δ t T) : FTy Γ' (Δ.map (Ty.rename ρ)) (t.renTy ρ) (T.rename ρ) := by
  induction h generalizing m with
  | var e => exact .var (by rw [List.getElem?_map, e]; rfl)
  | lam _ ih => exact .lam (ih hρ)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ hρ) (ih₂ hρ)
  | @tlam _ _ _ _ Δ _ _ ih =>
    have e : (Δ.map Ty.weaken).map (Ty.rename (liftRen ρ)) =
        (Δ.map (Ty.rename ρ)).map Ty.weaken := by
      simp only [List.map_map]; congr 1; funext A; exact (A.rename_weaken ρ).symm
    exact .tlam (e ▸ ih (hρ.lift _))
  | tapp _ d ih => rw [Ty.rename_sub0]; exact .tapp (ih hρ) (d.rename hρ)
  | sub _ d ih => exact .sub (ih hρ) (d.rename hρ)

/-- Term variables beyond the context may be added on the outside. -/
theorem FTy.append (h : FTy Γ Δ t T) : ∀ Δ', FTy Γ (Δ ++ Δ') t T := by
  induction h with
  | var e =>
    intro Δ'
    exact .var (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp e).1]; exact e)
  | lam _ ih => intro Δ'; exact .lam (ih Δ')
  | app _ _ ih₁ ih₂ => intro Δ'; exact .app (ih₁ Δ') (ih₂ Δ')
  | tlam _ ih =>
    intro Δ'; have := ih (Δ'.map Ty.weaken); rw [← List.map_append] at this; exact .tlam this
  | tapp _ d ih => intro Δ'; exact .tapp (ih Δ') d
  | sub _ d ih => intro Δ'; exact .sub (ih Δ') d

/-- Substitution of a term-closed `w` of exactly the variable's type. -/
theorem FTy.subst (h : FTy Γ (Δ ++ [S]) t T) (hw : FTy Γ [] w S) :
    FTy Γ Δ (t.subst Δ.length w) T := by
  generalize e : Δ ++ [S] = Δ₀ at h
  induction h with
  | @var _ _ x _ _ ex =>
    subst e; simp only [Tm.subst]; split
    · next hx => exact .var (by rw [List.getElem?_append_left hx] at ex; exact ex)
    · split
      · next hx => subst hx; rw [List.getElem?_concat_length] at ex; cases ex; exact hw.append Δ
      · rw [List.getElem?_eq_none (by simp; omega)] at ex; cases ex
  | lam _ ih => exact .lam (ih (Δ := _ :: Δ) hw (by rw [← e]; rfl))
  | app _ _ ih₁ ih₂ => exact .app (ih₁ hw e) (ih₂ hw e)
  | tlam _ ih =>
    have := ih (Δ := Δ.map Ty.weaken) (hw.renTy (TyRen.weaken _ _))
      (by rw [← e, List.map_append]; rfl)
    rw [List.length_map] at this; exact .tlam this
  | tapp _ d ih => exact .tapp (ih hw e) d
  | sub _ d ih => exact .sub (ih hw e) d

/-! ## Type substitution -/

theorem FTy.substTy {Γ : Ctx n} {Γ' : Ctx m} {σ} (hσ : TySub Γ Γ' σ) (h : FTy Γ Δ t T) :
    FTy Γ' (Δ.map (Ty.subst σ)) (t.substTy σ) (T.subst σ) := by
  induction h generalizing m with
  | var e => exact .var (by rw [List.getElem?_map, e]; rfl)
  | lam _ ih => exact .lam (ih hσ)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ hσ) (ih₂ hσ)
  | @tlam _ _ _ _ Δ _ _ ih =>
    have e : (Δ.map Ty.weaken).map (Ty.subst (liftS σ)) =
        (Δ.map (Ty.subst σ)).map Ty.weaken := by
      simp only [List.map_map]; congr 1; funext A; exact A.weaken_subst σ
    exact .tlam (e ▸ ih (hσ.lift _))
  | tapp _ d ih => rw [Ty.subst_sub0]; exact .tapp (ih hσ) (d.subst hσ)
  | sub _ d ih => exact .sub (ih hσ) (d.subst hσ)

/-! ## Canonical forms through subsumption -/

theorem FTy.canon_lam (h : FTy Γ Δ t T) (e : t = .lam S b) :
    ∃ T₀, FTy Γ (S :: Δ) b T₀ ∧ Nonempty (Sub Γ (.arr S T₀) T) := by
  induction h with
  | lam hb => cases e; exact ⟨_, hb, ⟨.refl⟩⟩
  | sub _ d ih => obtain ⟨T₀, hb, ⟨d'⟩⟩ := ih e; exact ⟨T₀, hb, ⟨.trans d' d⟩⟩
  | _ => cases e

theorem FTy.canon_tlam (h : FTy Γ Δ t T) (e : t = .tlam S b) :
    ∃ T₀, FTy (Γ.snoc S) (Δ.map Ty.weaken) b T₀ ∧ Nonempty (Sub Γ (.all S T₀) T) := by
  induction h with
  | tlam hb => cases e; exact ⟨_, hb, ⟨.refl⟩⟩
  | sub _ d ih => obtain ⟨T₀, hb, ⟨d'⟩⟩ := ih e; exact ⟨T₀, hb, ⟨.trans d' d⟩⟩
  | _ => cases e

end SelFsub
