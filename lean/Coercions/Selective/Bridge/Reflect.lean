import Coercions.Selective.Bridge.Preserve

/-!
# Reflection fails; the encoding is injective

Arrows and universals both become dependent function types, and `P-All` with
`P-Top` on the domain relates `⟦Top → Top⟧ = ∀(_ : ⊤) ⊤` to
`⟦∀(X <: Top). Top⟧ = ∀(x : {A : ⊥ .. ⊤}) ⊤` in one primitive step. In F-sub the
two types are unrelated: no certificate relates them (`sub_not_reflects`, by the
invariant that a step out of an arrow or `Top` lands on an arrow or `Top`), so
no declarative derivation does either. Reflection therefore fails at the level
of primitive steps (`prim_not_reflects`) and of subtyping (`sub_not_reflects`).

The encoding is injective on types, contexts and certificates. A universal
never collides with an arrow because an encoded type is never a type-member
declaration (`enc_ne_typ`).

Every entry of an encoded context is a declaration `{A : ⊥ .. U}`
(`encCtx_lookup`), so the receiver separator's context
`w : {B : ⊥ .. R}, y : w.B` (`Selective.ΓR`) is outside the image
(`separator_outside_image`).
-/

namespace Bridge

open FCdot (Kind Sig BVar Rename Label)

/-! ## The counterexample to reflection -/

/-- `⟦Top → Top⟧ ≤₀ ⟦∀(X <: Top). Top⟧` in the empty context. -/
theorem counter_H :
    Selective.Prim (encCtx .nil) (enc (.arr .top .top)) (enc (.all .top .top)) :=
  .all .top .refl

theorem counter_H_checker :
    Selective.prim? (encCtx .nil) (enc (.arr .top .top)) (enc (.all .top .top)) = true := by
  decide

theorem counter_fsub_checker :
    SelFsub.prim? .nil (.arr .top .top) (.all .top .top) = false := by decide

theorem counter_fsub : ¬ SelFsub.Prim .nil (.arr .top .top) (.all .top .top) := by
  intro h; cases h

/-- `≤₀` on encodings does not reflect F-sub's `≤₀`. -/
theorem prim_not_reflects :
    ¬ ∀ {n : Nat} (Γ : SelFsub.Ctx n) (S T : SelFsub.Ty n),
        Selective.Prim (encCtx Γ) (enc S) (enc T) → SelFsub.Prim Γ S T :=
  fun h => counter_fsub (h _ _ _ counter_H)

/-- Arrow or `Top`: closed under F-sub's `≤₀` steps. -/
def ArrOrTop {n : Nat} : SelFsub.Ty n → Prop
  | .top => True
  | .arr _ _ => True
  | _ => False

theorem ArrOrTop.prim {n : Nat} {Γ : SelFsub.Ctx n} {S T : SelFsub.Ty n}
    (h : SelFsub.Prim Γ S T) (hS : ArrOrTop S) : ArrOrTop T := by
  cases h with
  | refl => exact hS
  | top => trivial
  | bound => exact hS.elim
  | arr => trivial
  | all => exact hS.elim

theorem ArrOrTop.cert {n : Nat} {Γ : SelFsub.Ctx n} {c : SelFsub.Cert n} {S T : SelFsub.Ty n}
    (h : SelFsub.CTy Γ c S T) (hS : ArrOrTop S) : ArrOrTop T := by
  induction h with
  | step h => exact hS.prim h
  | seq _ _ i₁ i₂ => exact i₂ (i₁ hS)

/-- The encodings are DOT-MNF subtypes; the F-sub types are not F-sub subtypes. -/
theorem sub_not_reflects :
    Nonempty (DotMNF.Sub (encCtx .nil) (enc (.arr .top .top)) (enc (.all .top .top))) ∧
    ¬ Nonempty (SelFsub.Sub .nil (.arr .top .top) (.all .top .top)) := by
  refine ⟨Selective.primitive_sound counter_H, fun ⟨d⟩ => ?_⟩
  obtain ⟨c, hc⟩ := SelFsub.coercion_iff.mpr ⟨d⟩
  exact (ArrOrTop.cert hc trivial).elim

/-! ## Injectivity -/

theorem weaken_injective {s : Sig} {A B : DotMNF.Ty s}
    (h : A.weaken (k := .var) = B.weaken) : A = B := by
  have e₁ := (DotMNF.Ty.unweaken?_spec (U := A) (U' := B.weaken)).mpr h
  have e₂ := (DotMNF.Ty.unweaken?_spec (U := B) (U' := B.weaken)).mpr rfl
  rw [e₁] at e₂; exact Option.some.inj e₂

theorem enc_ne_typ {n : Nat} (S : SelFsub.Ty n) (A : Label) (L U : DotMNF.Ty (sig n)) :
    enc S ≠ .typ A L U := by
  cases S <;> simp [enc]

theorem enc_injective {n : Nat} {S T : SelFsub.Ty n} (h : enc S = enc T) : S = T := by
  induction S with
  | top => cases T <;> simp_all [enc]
  | var x =>
    cases T <;> simp [enc] at h
    exact congrArg _ (bv_injective h)
  | arr S₁ S₂ i₁ i₂ =>
    cases T with
    | arr T₁ T₂ =>
      simp only [enc, DotMNF.Ty.all.injEq] at h
      rw [i₁ h.1, i₂ (weaken_injective h.2)]
    | all T₁ T₂ =>
      simp only [enc, DotMNF.Ty.all.injEq] at h
      exact (enc_ne_typ _ _ _ _ h.1).elim
    | _ => simp [enc] at h
  | all S₁ S₂ i₁ i₂ =>
    cases T with
    | all T₁ T₂ =>
      simp only [enc, DotMNF.Ty.all.injEq, DotMNF.Ty.typ.injEq] at h
      rw [i₁ h.1.2.2, i₂ h.2]
    | arr T₁ T₂ =>
      simp only [enc, DotMNF.Ty.all.injEq] at h
      exact (enc_ne_typ _ _ _ _ h.1.symm).elim
    | _ => simp [enc] at h

theorem encCtx_injective {n : Nat} {Γ Δ : SelFsub.Ctx n} (h : encCtx Γ = encCtx Δ) : Γ = Δ := by
  induction Γ with
  | nil => cases Δ; rfl
  | snoc Γ A ih =>
    cases Δ with
    | snoc Δ B =>
      obtain ⟨h₁, h₂⟩ := DotMNF.Ctx.cons.inj h
      simp only [DotMNF.Ty.typ.injEq] at h₂
      rw [ih h₁, enc_injective h₂.2.2]

theorem encCert_injective {n : Nat} {c d : SelFsub.Cert n} (h : encCert c = encCert d) :
    c = d := by
  induction c generalizing d with
  | step S T =>
    cases d with
    | step S' T' =>
      simp only [encCert, Selective.Cert.step.injEq] at h
      rw [enc_injective h.1, enc_injective h.2]
    | seq => simp [encCert] at h
  | seq c₁ c₂ i₁ i₂ =>
    cases d with
    | seq d₁ d₂ =>
      simp only [encCert, Selective.Cert.seq.injEq] at h
      rw [i₁ h.1, i₂ h.2]
    | step => simp [encCert] at h

/-! ## The receiver separator is outside the image -/

/-- `w : {B : ⊥ .. R}, y : w.B` is not the encoding of any F-sub context: its
entry `y : w.B` is not a declaration `{A : ⊥ .. U}`. -/
theorem separator_outside_image (Γ : SelFsub.Ctx 2) : encCtx Γ ≠ Selective.ΓR := by
  intro h
  have e := encCtx_lookup Γ 0
  rw [h] at e
  exact nomatch e

end Bridge
