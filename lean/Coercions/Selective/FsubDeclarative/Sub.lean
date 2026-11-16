import Coercions.Selective.Fsub.Exact
/-!
# Declarative subtyping: renaming, substitution, inversion

Lemmas about the declarative relation `Sub` (reflexivity, `Top`, the exact bound axiom,
`trans`, arrows, the full bounded-universal rule). All are functions on derivations or
inductions on them; `trans` maps to `trans` throughout.

- Renaming along `TyRen` and weakening.
- Substitution along `TySub Γ Δ σ`, which supplies for each variable a derivation that its
  image lies below its substituted bound; the bound axiom becomes that derivation.
  Narrowing and instantiation of the innermost variable are instances.
- Inversion out of `Top`, out of an arrow and out of a universal type, by induction on the
  derivation. The `trans` case composes the components; for universals the body of the
  first link is narrowed to the bound of the second.

`SelFsub.Exact` is imported for the definitions `Sub`, `FTy`, `Value`, `Step`, `Steps`;
no certificate typing, operation or result is used (checked in `Deps.lean`).
-/
namespace SelFsub

def Sub.rename {Γ : Ctx n} {Δ : Ctx m} {ρ : Fin n → Fin m} (hρ : TyRen Γ Δ ρ) :
    Sub Γ S T → Sub Δ (S.rename ρ) (T.rename ρ)
  | .refl => .refl
  | .top => .top
  | .bound x => hρ x ▸ .bound (ρ x)
  | .trans d₁ d₂ => .trans (d₁.rename hρ) (d₂.rename hρ)
  | .arr d₁ d₂ => .arr (d₁.rename hρ) (d₂.rename hρ)
  | .all d₁ d₂ => .all (d₁.rename hρ) (d₂.rename (hρ.lift _))

def Sub.weaken (B : Ty n) (d : Sub Γ S T) : Sub (Γ.snoc B) S.weaken T.weaken :=
  d.rename (TyRen.weaken Γ B)

/-! ## Substitution -/

/-- Each variable's image lies below its substituted bound. -/
def TySub (Γ : Ctx n) (Δ : Ctx m) (σ : Fin n → Ty m) : Type :=
  ∀ x, Sub Δ (σ x) ((Γ.lookup x).subst σ)

def TySub.lift {Γ : Ctx n} {Δ : Ctx m} {σ} (h : TySub Γ Δ σ) (B : Ty n) :
    TySub (Γ.snoc B) (Δ.snoc (B.subst σ)) (liftS σ) := fun x => by
  cases x using Fin.cases
  · show Sub _ (.var 0) (B.weaken.subst (liftS σ)); rw [Ty.weaken_subst]; exact .bound 0
  · rename_i i
    show Sub _ (σ i).weaken ((Γ.lookup i).weaken.subst (liftS σ))
    rw [Ty.weaken_subst]; exact (h i).weaken _

def Sub.subst {Γ : Ctx n} {Δ : Ctx m} {σ} (h : TySub Γ Δ σ) :
    Sub Γ S T → Sub Δ (S.subst σ) (T.subst σ)
  | .refl => .refl
  | .top => .top
  | .bound x => h x
  | .trans d₁ d₂ => .trans (d₁.subst h) (d₂.subst h)
  | .arr d₁ d₂ => .arr (d₁.subst h) (d₂.subst h)
  | .all d₁ d₂ => .all (d₁.subst h) (d₂.subst (h.lift _))

/-- Instantiating `X <: U` by `V` with `V <: U`. -/
def TySub.inst (d : Sub Γ V U) : TySub (Γ.snoc U) Γ (sub0 V) := fun x => by
  cases x using Fin.cases
  · show Sub _ _ (U.weaken.subst (sub0 V)); rw [Ty.weaken_sub0]; exact d
  · show Sub _ _ ((Γ.lookup _).weaken.subst (sub0 V)); rw [Ty.weaken_sub0]; exact .bound _

/-- Narrowing `X <: U` to `X <: U'` with `U' <: U`: the bound axiom on `X` becomes
`X <: U' <: U`. -/
def Sub.narrow (h : Sub (Γ.snoc U) S T) (d : Sub Γ U' U) : Sub (Γ.snoc U') S T := by
  have hσ : TySub (Γ.snoc U) (Γ.snoc U') .var := fun x => by
    cases x using Fin.cases
    · show Sub _ _ (U.weaken.subst .var); rw [Ty.subst_var]; exact .trans (.bound 0) (d.weaken _)
    · show Sub _ _ (Ty.subst .var _); rw [Ty.subst_var]; exact .bound _
  have h' := h.subst hσ; rwa [Ty.subst_var, Ty.subst_var] at h'

/-! ## Inversion -/

theorem Sub.top_inv (d : Sub Γ S T) (e : S = .top) : T = .top := by
  induction d with
  | refl | top => first | exact e | rfl
  | bound | arr | all => cases e
  | trans _ _ i₁ i₂ => exact i₂ (i₁ e)

theorem Sub.arr_inv (d : Sub Γ (.arr A₁ A₂) T) :
    T = .top ∨ ∃ B₁ B₂, T = .arr B₁ B₂ ∧ Nonempty (Sub Γ B₁ A₁) ∧ Nonempty (Sub Γ A₂ B₂) := by
  generalize e : Ty.arr A₁ A₂ = S at d
  induction d with
  | refl => subst e; exact .inr ⟨_, _, rfl, ⟨.refl⟩, ⟨.refl⟩⟩
  | top => exact .inl rfl
  | bound | all => cases e
  | arr d₁ d₂ => cases e; exact .inr ⟨_, _, rfl, ⟨d₁⟩, ⟨d₂⟩⟩
  | trans _ d i₁ i₂ =>
    rcases i₁ e with rfl | ⟨_, _, rfl, ⟨c₁⟩, ⟨c₂⟩⟩
    · exact .inl (d.top_inv rfl)
    · rcases i₂ rfl with rfl | ⟨_, _, rfl, ⟨d₁⟩, ⟨d₂⟩⟩
      · exact .inl rfl
      · exact .inr ⟨_, _, rfl, ⟨.trans d₁ c₁⟩, ⟨.trans c₂ d₂⟩⟩

/-- The body derivation lives under the final bound. -/
theorem Sub.all_inv (d : Sub Γ (.all A₁ A₂) T) :
    T = .top ∨ ∃ B₁ B₂, T = .all B₁ B₂ ∧ Nonempty (Sub Γ B₁ A₁) ∧
      Nonempty (Sub (Γ.snoc B₁) A₂ B₂) := by
  generalize e : Ty.all A₁ A₂ = S at d
  induction d with
  | refl => subst e; exact .inr ⟨_, _, rfl, ⟨.refl⟩, ⟨.refl⟩⟩
  | top => exact .inl rfl
  | bound | arr => cases e
  | all d₁ d₂ => cases e; exact .inr ⟨_, _, rfl, ⟨d₁⟩, ⟨d₂⟩⟩
  | trans _ d i₁ i₂ =>
    rcases i₁ e with rfl | ⟨_, _, rfl, ⟨c₁⟩, ⟨c₂⟩⟩
    · exact .inl (d.top_inv rfl)
    · rcases i₂ rfl with rfl | ⟨_, _, rfl, ⟨d₁⟩, ⟨d₂⟩⟩
      · exact .inl rfl
      · exact .inr ⟨_, _, rfl, ⟨.trans d₁ c₁⟩, ⟨.trans (c₂.narrow d₁) d₂⟩⟩

end SelFsub
