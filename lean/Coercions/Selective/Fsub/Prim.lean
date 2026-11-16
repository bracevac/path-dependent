import Coercions.Selective.Fsub.Syntax
/-!
# The primitive relation `≤₀`

`Prim` has reflexivity, `Top`, the structural arrow and full bounded-universal rules,
and exactly one bound rule `X ≤₀ Γ(X)`: lookup returns the declared bound and never
promotes through it. There is no transitivity rule, and transitivity is not
admissible (`primitive_nontrans`). The checker `prim?` is structural recursion on the
left type; a polarity flag handles the contravariant positions.
-/
namespace SelFsub

inductive Prim : Ctx n → Ty n → Ty n → Prop where
  | refl : Prim Γ A A
  | top : Prim Γ A .top
  | bound (x : Fin n) : Prim Γ (.var x) (Γ.lookup x)
  | arr : Prim Γ B₁ A₁ → Prim Γ A₂ B₂ → Prim Γ (.arr A₁ A₂) (.arr B₁ B₂)
  | all : Prim Γ B₁ A₁ → Prim (Γ.snoc B₁) A₂ B₂ → Prim Γ (.all A₁ A₂) (.all B₁ B₂)

/-- `Prim` read in direction `p`: `S ≤₀ T` for `true`, `T ≤₀ S` for `false`. -/
def PrimAt : Bool → Ctx n → Ty n → Ty n → Prop
  | true, Γ, S, T => Prim Γ S T
  | false, Γ, S, T => Prim Γ T S

/-- Whether `L` is a variable whose declared bound is syntactically `R`. -/
def boundIs (Γ : Ctx n) : Ty n → Ty n → Bool
  | .var x, R => decide (Γ.lookup x = R)
  | _, _ => false

theorem boundIs_true {Γ : Ctx n} :
    boundIs Γ L R = true → ∃ x, L = .var x ∧ R = Γ.lookup x := by
  cases L <;> simp [boundIs]; intro h; exact h.symm

/-- `primDir p Γ S T` decides `PrimAt p Γ S T`, by structural recursion on `S`. -/
def primDir : Bool → Ctx n → Ty n → Ty n → Bool
  | p, Γ, S, T =>
    decide (cond p S T = cond p T S) || decide (cond p T S = .top) ||
    boundIs Γ (cond p S T) (cond p T S) ||
    match S, T with
    | .arr A₁ A₂, .arr B₁ B₂ => primDir (!p) Γ A₁ B₁ && primDir p Γ A₂ B₂
    | .all A₁ A₂, .all B₁ B₂ =>
      primDir (!p) Γ A₁ B₁ && primDir p (Γ.snoc (cond p B₁ A₁)) A₂ B₂
    | _, _ => false

/-- The checker for `≤₀`. -/
def prim? (Γ : Ctx n) (S T : Ty n) : Bool := primDir true Γ S T

theorem primDir_base {Γ : Ctx n} :
    (decide (cond p S T = cond p T S) || decide (cond p T S = .top) ||
      boundIs Γ (cond p S T) (cond p T S)) = true → PrimAt p Γ S T := by
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rintro ((h | h) | h)
  · cases p <;> simp at h <;> subst h <;> exact .refl
  · cases p <;> simp at h <;> subst h <;> exact .top
  · obtain ⟨x, hL, hR⟩ := boundIs_true h
    cases p <;> simp at hL hR <;> subst hL hR <;> exact .bound x

theorem primDir_sound (S : Ty n) :
    ∀ p (Γ : Ctx n) T, primDir p Γ S T = true → PrimAt p Γ S T := by
  induction S with
  | top | var =>
    intro p Γ T h; unfold primDir at h; rw [Bool.or_eq_true] at h
    exact h.elim primDir_base (by simp)
  | arr A₁ A₂ i₁ i₂ =>
    intro p Γ T h; unfold primDir at h; rw [Bool.or_eq_true] at h
    refine h.elim primDir_base fun h => ?_
    cases T <;> simp at h
    have h₁ := i₁ _ _ _ h.1; have h₂ := i₂ _ _ _ h.2
    cases p
    · exact .arr h₁ h₂
    · exact .arr h₁ h₂
  | all A₁ A₂ i₁ i₂ =>
    intro p Γ T h; unfold primDir at h; rw [Bool.or_eq_true] at h
    refine h.elim primDir_base fun h => ?_
    cases T <;> simp at h
    have h₁ := i₁ _ _ _ h.1; have h₂ := i₂ _ _ _ h.2
    cases p
    · exact .all h₁ h₂
    · exact .all h₁ h₂

theorem primDir_complete (h : Prim Γ S T) :
    primDir true Γ S T = true ∧ primDir false Γ T S = true := by
  induction h with
  | refl => constructor <;> unfold primDir <;> simp
  | top => constructor <;> unfold primDir <;> simp
  | bound x => constructor <;> unfold primDir <;> simp [boundIs]
  | arr _ _ i₁ i₂ => constructor <;> unfold primDir <;> simp [i₁, i₂]
  | all _ _ i₁ i₂ => constructor <;> unfold primDir <;> simp [i₁, i₂]

theorem prim?_iff : prim? Γ S T = true ↔ Prim Γ S T :=
  ⟨primDir_sound S true Γ T, fun h => (primDir_complete h).1⟩

instance : Decidable (Prim Γ S T) := decidable_of_iff _ prim?_iff

/-- The five rules, read backwards. -/
theorem Prim.inv (h : Prim Γ S T) :
    S = T ∨ T = .top ∨ (∃ x, S = .var x ∧ T = Γ.lookup x) ∨
    (∃ A₁ A₂ B₁ B₂, S = .arr A₁ A₂ ∧ T = .arr B₁ B₂ ∧ Prim Γ B₁ A₁ ∧ Prim Γ A₂ B₂) ∨
    (∃ A₁ A₂ B₁ B₂, S = .all A₁ A₂ ∧ T = .all B₁ B₂ ∧ Prim Γ B₁ A₁ ∧ Prim (Γ.snoc B₁) A₂ B₂) := by
  cases h with
  | refl => exact .inl rfl
  | top => exact .inr (.inl rfl)
  | bound x => exact .inr (.inr (.inl ⟨x, rfl, rfl⟩))
  | arr h₁ h₂ => exact .inr (.inr (.inr (.inl ⟨_, _, _, _, rfl, rfl, h₁, h₂⟩)))
  | all h₁ h₂ => exact .inr (.inr (.inr (.inr ⟨_, _, _, _, rfl, rfl, h₁, h₂⟩)))

/-! ## Renaming -/

/-- `ρ` maps each declared bound of `Γ` to the declared bound of its image in `Δ`. -/
def TyRen (Γ : Ctx n) (Δ : Ctx m) (ρ : Fin n → Fin m) : Prop :=
  ∀ x, Δ.lookup (ρ x) = (Γ.lookup x).rename ρ

theorem TyRen.lift {Γ : Ctx n} {Δ : Ctx m} {ρ : Fin n → Fin m} (h : TyRen Γ Δ ρ) (B : Ty n) :
    TyRen (Γ.snoc B) (Δ.snoc (B.rename ρ)) (liftRen ρ) := by
  intro x; cases x using Fin.cases
  · exact B.rename_weaken ρ
  · show (Δ.lookup (ρ _)).weaken = _; rw [h, Ty.rename_weaken]; rfl

theorem TyRen.weaken (Γ : Ctx n) (B : Ty n) : TyRen Γ (Γ.snoc B) Fin.succ := fun _ => rfl

theorem Prim.rename {Γ : Ctx n} {Δ : Ctx m} {ρ : Fin n → Fin m} (hρ : TyRen Γ Δ ρ)
    (h : Prim Γ S T) : Prim Δ (S.rename ρ) (T.rename ρ) := by
  induction h generalizing m with
  | refl => exact .refl
  | top => exact .top
  | bound x => rw [← hρ x]; exact .bound _
  | arr _ _ i₁ i₂ => exact .arr (i₁ hρ) (i₂ hρ)
  | all _ _ i₁ i₂ => exact .all (i₁ hρ) (i₂ (hρ.lift _))

theorem Prim.weaken (B : Ty n) (h : Prim Γ S T) : Prim (Γ.snoc B) S.weaken T.weaken :=
  h.rename (TyRen.weaken Γ B)

/-! ## Nontransitivity -/

/-- `Y <: Top → Top, X <: Y`, in declaration order; `X` is `var 0`, `Y` is `var 1`. -/
def ctxYX : Ctx 2 := .snoc (.snoc .nil (.arr .top .top)) (.var 0)

theorem ctxYX_XY : Prim ctxYX (.var 0) (.var 1) := .bound 0
theorem ctxYX_Y : Prim ctxYX (.var 1) (.arr .top .top) := .bound 1
/-- The composite fails, and its final endpoint is neither `Top` nor a variable. -/
theorem ctxYX_not : ¬ Prim ctxYX (.var 0) (.arr .top .top) := by intro h; cases h
/-- The checker agrees and discovers no transitive consequence. -/
theorem ctxYX_checker : prim? ctxYX (.var 0) (.arr .top .top) = false := by decide

/-- `Z <: Top, Y <: Z, X <: Y`; `X`, `Y`, `Z` are `var 0`, `var 1`, `var 2`. -/
def ctxZYX : Ctx 3 := .snoc (.snoc (.snoc .nil .top) (.var 0)) (.var 0)

theorem ctxZYX_XY : Prim ctxZYX (.var 0) (.var 1) := .bound 0
theorem ctxZYX_YZ : Prim ctxZYX (.var 1) (.var 2) := .bound 1
theorem ctxZYX_not : ¬ Prim ctxZYX (.var 0) (.var 2) := by intro h; cases h

/-- Transitivity is not admissible for `≤₀`. -/
theorem primitive_nontrans :
    ¬ ∀ {n} (Γ : Ctx n) (S M T : Ty n), Prim Γ S M → Prim Γ M T → Prim Γ S T :=
  fun h => ctxYX_not (h _ _ _ _ ctxYX_XY ctxYX_Y)

end SelFsub
