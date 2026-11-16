import Coercions.Selective.Fsub.Subst
/-!
# Inversion of certificates

A certificate out of `Top` ends in `Top`. A certificate out of an arrow (a universal)
ends in `Top` or in an arrow (a universal); the component certificates are computed
from the certificate by `Cert.arrInv` and `Cert.allInv`. For universals the body
certificates of consecutive links live under different bounds, and `Cert.allInv`
aligns them by narrowing. These hold in every context.
-/
namespace SelFsub

theorem CTy.top_inv (h : CTy Γ c S T) (e : S = .top) : T = .top := by
  induction h with
  | step h => subst e; rcases Prim.inv h with e | e | ⟨_, e, _⟩ | ⟨_, _, _, _, e, _⟩ |
      ⟨_, _, _, _, e, _⟩ <;> first | exact e.symm | exact e | cases e
  | seq _ _ i₁ i₂ => exact i₂ (i₁ e)

/-- Domain (reversed) and codomain certificates of a certificate between arrows. -/
def Cert.arrInv : Cert n → Cert n × Cert n
  | .step (.arr A₁ A₂) (.arr B₁ B₂) => (.step B₁ A₁, .step A₂ B₂)
  | c@(.step _ _) => (c, c)
  | .seq c d => (.seq d.arrInv.1 c.arrInv.1, .seq c.arrInv.2 d.arrInv.2)

theorem CTy.arr_inv (h : CTy Γ c (.arr A₁ A₂) T) :
    T = .top ∨ ∃ B₁ B₂, T = .arr B₁ B₂ ∧ CTy Γ c.arrInv.1 B₁ A₁ ∧ CTy Γ c.arrInv.2 A₂ B₂ := by
  generalize e : Ty.arr A₁ A₂ = S at h
  induction h generalizing A₁ A₂ with
  | step h =>
    subst e
    rcases Prim.inv h with e | e | ⟨_, e, _⟩ | ⟨_, _, _, _, e, e', h₁, h₂⟩ | ⟨_, _, _, _, e, _⟩
    · subst e; exact .inr ⟨_, _, rfl, .step .refl, .step .refl⟩
    · exact .inl e
    · cases e
    · cases e; subst e'; exact .inr ⟨_, _, rfl, .step h₁, .step h₂⟩
    · cases e
  | seq _ hd i₁ i₂ =>
    rcases i₁ e with rfl | ⟨B₁, B₂, rfl, c₁, c₂⟩
    · exact .inl (hd.top_inv rfl)
    · rcases i₂ rfl with rfl | ⟨C₁, C₂, rfl, d₁, d₂⟩
      · exact .inl rfl
      · exact .inr ⟨_, _, rfl, .seq d₁ c₁, .seq c₂ d₂⟩

/-- Bound (reversed) and body certificates of a certificate between universals; the body
certificate lives under the final bound. -/
def Cert.allInv : Cert n → Cert n × Cert (n+1)
  | .step (.all A₁ A₂) (.all B₁ B₂) => (.step B₁ A₁, .step A₂ B₂)
  | c@(.step _ _) => (c, c.weaken)
  | .seq c d =>
    (.seq d.allInv.1 c.allInv.1, .seq (c.allInv.2.narrow 0 d.allInv.1) d.allInv.2)

theorem CTy.all_inv (h : CTy Γ c (.all A₁ A₂) T) :
    T = .top ∨ ∃ B₁ B₂, T = .all B₁ B₂ ∧ CTy Γ c.allInv.1 B₁ A₁ ∧
      CTy (Γ.snoc B₁) c.allInv.2 A₂ B₂ := by
  generalize e : Ty.all A₁ A₂ = S at h
  induction h generalizing A₁ A₂ with
  | step h =>
    subst e
    rcases Prim.inv h with e | e | ⟨_, e, _⟩ | ⟨_, _, _, _, e, _⟩ | ⟨_, _, _, _, e, e', h₁, h₂⟩
    · subst e; exact .inr ⟨_, _, rfl, .step .refl, .step .refl⟩
    · exact .inl e
    · cases e
    · cases e
    · cases e; subst e'; exact .inr ⟨_, _, rfl, .step h₁, .step h₂⟩
  | seq _ hd i₁ i₂ =>
    rcases i₁ e with rfl | ⟨B₁, B₂, rfl, c₁, c₂⟩
    · exact .inl (hd.top_inv rfl)
    · rcases i₂ rfl with rfl | ⟨C₁, C₂, rfl, d₁, d₂⟩
      · exact .inl rfl
      · exact .inr ⟨_, _, rfl, .seq d₁ c₁, .seq (CTy.narrow .nil d₁ c₂) d₂⟩

end SelFsub
