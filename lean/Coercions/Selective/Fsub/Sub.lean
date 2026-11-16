import Coercions.Selective.Fsub.Cert
/-!
# Declarative full F-sub and soundness

`Sub` is declarative full F-sub subtyping: reflexivity, `Top`, the exact bound axiom,
arbitrary transitivity, arrows, and the full bounded-universal rule (bounds
contravariant, bodies compared under the target bound). It is `Type`-valued, so the
converse translation `Sub.toCert` is a function on derivations.
-/
namespace SelFsub

inductive Sub : Ctx n → Ty n → Ty n → Type where
  | refl : Sub Γ A A
  | top : Sub Γ A .top
  | bound (x : Fin n) : Sub Γ (.var x) (Γ.lookup x)
  | trans : Sub Γ A B → Sub Γ B C → Sub Γ A C
  | arr : Sub Γ B₁ A₁ → Sub Γ A₂ B₂ → Sub Γ (.arr A₁ A₂) (.arr B₁ B₂)
  | all : Sub Γ B₁ A₁ → Sub (Γ.snoc B₁) A₂ B₂ → Sub Γ (.all A₁ A₂) (.all B₁ B₂)

theorem primitive_sound (h : Prim Γ S T) : Nonempty (Sub Γ S T) := by
  induction h with
  | refl => exact ⟨.refl⟩
  | top => exact ⟨.top⟩
  | bound x => exact ⟨.bound x⟩
  | arr _ _ i₁ i₂ => obtain ⟨⟨d₁⟩, ⟨d₂⟩⟩ := And.intro i₁ i₂; exact ⟨.arr d₁ d₂⟩
  | all _ _ i₁ i₂ => obtain ⟨⟨d₁⟩, ⟨d₂⟩⟩ := And.intro i₁ i₂; exact ⟨.all d₁ d₂⟩

theorem coercion_sound (h : CTy Γ c S T) : Nonempty (Sub Γ S T) := by
  induction h with
  | step h => exact primitive_sound h
  | seq _ _ i₁ i₂ => obtain ⟨⟨d₁⟩, ⟨d₂⟩⟩ := And.intro i₁ i₂; exact ⟨.trans d₁ d₂⟩

/-- Certificates compose by `;`. -/
theorem coercion_transitive (h₁ : CTy Γ c S M) (h₂ : CTy Γ d M T) : CTy Γ (.seq c d) S T :=
  .seq h₁ h₂

/-- Coercion existence is transitive. -/
theorem coercion_exists_transitive :
    (∃ c, CTy Γ c S M) → (∃ d, CTy Γ d M T) → ∃ e, CTy Γ e S T
  | ⟨c, h₁⟩, ⟨d, h₂⟩ => ⟨.seq c d, .seq h₁ h₂⟩

end SelFsub
