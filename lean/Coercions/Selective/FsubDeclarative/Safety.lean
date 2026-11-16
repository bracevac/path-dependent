import Coercions.Selective.FsubDeclarative.Typing
/-!
# Type safety of declarative full F-sub, directly

Preservation and progress for `FTy` over `Step`, for terms closed in term variables in
every type context `Γ`. The invariant is the typing itself.

- β: canonical forms give the abstraction's own typing and `S₀ → T₀ <: S → T`, which
  `Sub.arr_inv` splits; the argument is subsumed to `S₀`, substituted by `FTy.subst`, and
  the result subsumed to `T`.
- type-β: canonical forms and `Sub.all_inv` give `S <: S₀` and `T₀ <: T` under `X <: S`;
  the body is transported by `FTy.substTy` along `TySub.inst` with `U <: S <: S₀`, and
  the result subsumed by `T₀ <: T` instantiated with `U <: S`.
- progress: an abstraction typed at an arrow (a universal) is a `λ` (a `Λ`), since a
  universal is never below an arrow and conversely.
-/
namespace SelFsub

theorem fsub_preservation (h : FTy Γ [] e T) (hs : Step e e') : FTy Γ [] e' T := by
  generalize eΔ : ([] : List (Ty _)) = Δ at h
  induction h with
  | var | lam | tlam => cases hs
  | app hf hu ih₁ ih₂ =>
    subst eΔ
    cases hs with
    | beta =>
      obtain ⟨T₀, hb, ⟨d⟩⟩ := hf.canon_lam rfl
      rcases d.arr_inv with he | ⟨_, _, he, ⟨d₁⟩, ⟨d₂⟩⟩
      · cases he
      · cases he; exact .sub (FTy.subst (Δ := []) hb (.sub hu d₁)) d₂
    | appL hs => exact .app (ih₁ hs rfl) hu
    | appR _ hs => exact .app hf (ih₂ hs rfl)
  | tapp hf d ih =>
    subst eΔ
    cases hs with
    | tbeta =>
      obtain ⟨T₀, hb, ⟨d'⟩⟩ := hf.canon_tlam rfl
      rcases d'.all_inv with he | ⟨_, _, he, ⟨d₁⟩, ⟨d₂⟩⟩
      · cases he
      · cases he; exact .sub (hb.substTy (TySub.inst (.trans d d₁))) (d₂.subst (TySub.inst d))
    | tappL hs => exact .tapp (ih hs rfl) d
  | sub _ d ih => exact .sub (ih hs eΔ) d

theorem fsub_progress (h : FTy Γ [] e T) : Value e ∨ ∃ e', Step e e' := by
  generalize eΔ : ([] : List (Ty _)) = Δ at h
  induction h with
  | var e => subst eΔ; simp at e
  | lam => exact .inl .lam
  | tlam => exact .inl .tlam
  | app hf _ ih₁ ih₂ =>
    rcases ih₁ eΔ with hv | ⟨_, hs⟩
    · rcases ih₂ eΔ with hv' | ⟨_, hs'⟩
      · cases hv with
        | lam => exact .inr ⟨_, .beta hv'⟩
        | tlam =>
          obtain ⟨_, -, ⟨d⟩⟩ := hf.canon_tlam rfl
          rcases d.all_inv with he | ⟨_, _, he, -⟩ <;> cases he
      · exact .inr ⟨_, .appR hv hs'⟩
    · exact .inr ⟨_, .appL hs⟩
  | tapp hf _ ih =>
    rcases ih eΔ with hv | ⟨_, hs⟩
    · cases hv with
      | tlam => exact .inr ⟨_, .tbeta⟩
      | lam =>
        obtain ⟨_, -, ⟨d⟩⟩ := hf.canon_lam rfl
        rcases d.arr_inv with he | ⟨_, _, he, -⟩ <;> cases he
    · exact .inr ⟨_, .tappL hs⟩
  | sub _ _ ih => exact ih eΔ

theorem fsub_safety_direct (h : FTy Γ [] e T) (hs : Steps e e') :
    Value e' ∨ ∃ e'', Step e' e'' := by
  induction hs with
  | refl => exact fsub_progress h
  | step s _ ih => exact ih (fsub_preservation h s)

end SelFsub
