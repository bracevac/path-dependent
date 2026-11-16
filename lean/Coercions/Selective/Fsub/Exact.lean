import Coercions.Selective.Fsub.Safety
import Coercions.Selective.Fsub.Complete
/-!
# Exactness against declarative F-sub typing

`FTy` is ordinary full F-sub term typing on cast-free terms: the five syntax-directed
rules, with the type-application rule checking the bound by `Sub`, and subsumption over
`Sub`. It has no cast rule, so every term it types is cast-free (`FTy.erase_eq`).
Erasure maps annotated typings to `FTy` typings, and every `FTy` typing has an annotated
term over it: subsumption becomes a cast by `Sub.toCert`, and a bound checked by `Sub`
becomes a cast of the callee by the bound lift `Cert.allBound`. With preservation and
safety of the annotated calculus this gives preservation and type safety of declarative
full F-sub.
-/
namespace SelFsub

inductive FTy : Ctx n → List (Ty n) → Tm n → Ty n → Prop where
  | var : Δ[x]? = some T → FTy Γ Δ (.var x) T
  | lam : FTy Γ (S :: Δ) e T → FTy Γ Δ (.lam S e) (.arr S T)
  | app : FTy Γ Δ e (.arr S T) → FTy Γ Δ u S → FTy Γ Δ (.app e u) T
  | tlam : FTy (Γ.snoc S) (Δ.map Ty.weaken) e T → FTy Γ Δ (.tlam S e) (.all S T)
  | tapp : FTy Γ Δ e (.all S T) → Sub Γ U S → FTy Γ Δ (.tapp e U) (T.subst (sub0 U))
  | sub : FTy Γ Δ e S → Sub Γ S T → FTy Γ Δ e T

theorem FTy.erase_eq (h : FTy Γ Δ e T) : e.erase = e := by
  induction h with
  | var | sub _ _ ih => first | rfl | exact ih
  | lam _ ih | tlam _ ih | tapp _ _ ih => simp only [Tm.erase, ih]
  | app _ _ ih₁ ih₂ => simp only [Tm.erase, ih₁, ih₂]

theorem elaboration_typed (h : HTy Γ Δ t T) : FTy Γ Δ t.erase T := by
  induction h with
  | var e => exact .var e
  | lam _ ih => exact .lam ih
  | tlam _ ih => exact .tlam ih
  | app _ _ hp ih₁ ih₂ => obtain ⟨d⟩ := primitive_sound hp; exact .app ih₁ (.sub ih₂ d)
  | tapp _ hp ih => obtain ⟨d⟩ := primitive_sound hp; exact .tapp ih d
  | cast _ hc ih => obtain ⟨d⟩ := coercion_sound hc; exact .sub ih d

theorem elaboration_complete {e : Tm n} (h : FTy Γ Δ e T) :
    ∃ t : Tm n, t.erase = e ∧ HTy Γ Δ t T := by
  induction h with
  | var e => exact ⟨_, rfl, .var e⟩
  | lam _ ih => obtain ⟨t, rfl, ht⟩ := ih; exact ⟨.lam _ t, rfl, .lam ht⟩
  | tlam _ ih => obtain ⟨t, rfl, ht⟩ := ih; exact ⟨.tlam _ t, rfl, .tlam ht⟩
  | app _ _ ih₁ ih₂ =>
    obtain ⟨t, rfl, ht⟩ := ih₁; obtain ⟨u, rfl, hu⟩ := ih₂
    exact ⟨.app t u, rfl, .app ht hu .refl⟩
  | @tapp _ _ _ _ S T U _ d ih =>
    obtain ⟨t, rfl, ht⟩ := ih
    exact ⟨.tapp (.cast t (d.toCert.allBound T)) U, rfl,
      .tapp (.cast ht (d.toCert_typed.allBound T)) .refl⟩
  | sub _ d ih =>
    obtain ⟨t, rfl, ht⟩ := ih; exact ⟨.cast t d.toCert, rfl, .cast ht d.toCert_typed⟩

theorem typability_iff {e : Tm n} :
    (∃ t : Tm n, t.erase = e ∧ HTy Γ Δ t T) ↔ FTy Γ Δ e T :=
  ⟨fun ⟨_, e, h⟩ => e ▸ elaboration_typed h, elaboration_complete⟩

/-- Type safety of declarative full F-sub, from `elaboration_complete` and `safety`. -/
theorem fsub_safety (h : FTy Γ [] e T) (hs : Steps e e') :
    Value e' ∨ ∃ e'', Step e' e'' := by
  obtain ⟨t, rfl, ht⟩ := elaboration_complete h; exact safety ht hs

/-- Preservation for declarative full F-sub, from `elaboration_complete`, `preservation`
and `elaboration_typed`. -/
theorem fsub_preservation (h : FTy Γ [] e T) (hs : Step e e') : FTy Γ [] e' T := by
  obtain ⟨t, rfl, ht⟩ := elaboration_complete h
  obtain ⟨t', rfl, ht'⟩ := preservation ht hs
  exact elaboration_typed ht'

end SelFsub
