import Coercions.Selective.Fsub.Cert
/-!
# Structural lifts of certificates

Each lift is a function on certificates. A contravariant position (arrow domain,
universal bound) reverses `;`; a universal body is lifted under one fixed final
bound. The combined lifts change the contravariant part first, keeping the other
part fixed, and then the covariant part.
-/
namespace SelFsub

/-- From `c : B ⇒ A` to `A → C ⇒ B → C`. -/
def Cert.arrDom (C : Ty n) : Cert n → Cert n
  | .step S T => .step (.arr T C) (.arr S C)
  | .seq c d => .seq (d.arrDom C) (c.arrDom C)

/-- From `c : A ⇒ B` to `C → A ⇒ C → B`. -/
def Cert.arrCod (C : Ty n) : Cert n → Cert n
  | .step S T => .step (.arr C S) (.arr C T)
  | .seq c d => .seq (c.arrCod C) (d.arrCod C)

/-- From `c : B ⇒ A` to `∀(X <: A). C ⇒ ∀(X <: B). C`. -/
def Cert.allBound (C : Ty (n+1)) : Cert n → Cert n
  | .step S T => .step (.all T C) (.all S C)
  | .seq c d => .seq (d.allBound C) (c.allBound C)

/-- From `c : B ⇒ C` under `X <: A` to `∀(X <: A). B ⇒ ∀(X <: A). C`. -/
def Cert.allBody (A : Ty n) : Cert (n+1) → Cert n
  | .step S T => .step (.all A S) (.all A T)
  | .seq c d => .seq (c.allBody A) (d.allBody A)

/-- From `dom : B₁ ⇒ A₁` and `cod : A₂ ⇒ B₂` to `A₁ → A₂ ⇒ B₁ → B₂`. -/
def Cert.arr (dom cod : Cert n) : Cert n := .seq (dom.arrDom cod.src) (cod.arrCod dom.src)

/-- From `bound : B₁ ⇒ A₁` and `body : A₂ ⇒ B₂` under `X <: B₁`
to `∀(X <: A₁). A₂ ⇒ ∀(X <: B₁). B₂`. -/
def Cert.all (bound : Cert n) (body : Cert (n+1)) : Cert n :=
  .seq (bound.allBound body.src) (body.allBody bound.src)

theorem CTy.arrDom (C : Ty n) (h : CTy Γ c B A) : CTy Γ (c.arrDom C) (.arr A C) (.arr B C) := by
  induction h with
  | step h => exact .step (.arr h .refl)
  | seq _ _ i₁ i₂ => exact .seq i₂ i₁

theorem CTy.arrCod (C : Ty n) (h : CTy Γ c A B) : CTy Γ (c.arrCod C) (.arr C A) (.arr C B) := by
  induction h with
  | step h => exact .step (.arr .refl h)
  | seq _ _ i₁ i₂ => exact .seq i₁ i₂

theorem CTy.allBound (C : Ty (n+1)) (h : CTy Γ c B A) :
    CTy Γ (c.allBound C) (.all A C) (.all B C) := by
  induction h with
  | step h => exact .step (.all h .refl)
  | seq _ _ i₁ i₂ => exact .seq i₂ i₁

theorem CTy.allBody (h : CTy (Γ.snoc A) c B C) : CTy Γ (c.allBody A) (.all A B) (.all A C) := by
  induction h with
  | step h => exact .step (.all .refl h)
  | seq _ _ i₁ i₂ => exact .seq i₁ i₂

theorem CTy.arr (h₁ : CTy Γ dom B₁ A₁) (h₂ : CTy Γ cod A₂ B₂) :
    CTy Γ (Cert.arr dom cod) (.arr A₁ A₂) (.arr B₁ B₂) := by
  obtain ⟨rfl, -⟩ := h₁.endpoints; obtain ⟨rfl, -⟩ := h₂.endpoints
  exact .seq (h₁.arrDom _) (h₂.arrCod _)

theorem CTy.all (h₁ : CTy Γ bound B₁ A₁) (h₂ : CTy (Γ.snoc B₁) body A₂ B₂) :
    CTy Γ (Cert.all bound body) (.all A₁ A₂) (.all B₁ B₂) := by
  obtain ⟨rfl, -⟩ := h₁.endpoints; obtain ⟨rfl, -⟩ := h₂.endpoints
  exact .seq (h₁.allBound _) h₂.allBody

end SelFsub
