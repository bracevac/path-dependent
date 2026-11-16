import Coercions.Selective.Fsub.Prim
/-!
# Stored certificates

A certificate is a primitive step `step[S, T]` or a composition `c ; d`. Typing is
indexed by the stored certificate; composition requires the middle endpoints to be
syntactically equal. The checker recomputes the endpoints from the stored types and
decides each step with `prim?`.
-/
namespace SelFsub

inductive Cert : Nat → Type where
  | step : Ty n → Ty n → Cert n
  | seq : Cert n → Cert n → Cert n
  deriving DecidableEq, Repr

def Cert.src : Cert n → Ty n
  | .step S _ => S
  | .seq c _ => c.src

def Cert.tgt : Cert n → Ty n
  | .step _ T => T
  | .seq _ d => d.tgt

inductive CTy : Ctx n → Cert n → Ty n → Ty n → Prop where
  | step : Prim Γ S T → CTy Γ (.step S T) S T
  | seq : CTy Γ c S M → CTy Γ d M T → CTy Γ (.seq c d) S T

theorem CTy.endpoints (h : CTy Γ c S T) : c.src = S ∧ c.tgt = T := by
  induction h with
  | step => exact ⟨rfl, rfl⟩
  | seq _ _ i₁ i₂ => exact ⟨i₁.1, i₂.2⟩

theorem CTy.endpoints_unique (h : CTy Γ c S T) (h' : CTy Γ c S' T') : S = S' ∧ T = T' := by
  obtain ⟨rfl, rfl⟩ := h.endpoints; exact h'.endpoints

/-! ## Checker -/

def Cert.valid (Γ : Ctx n) : Cert n → Bool
  | .step S T => prim? Γ S T
  | .seq c d => c.valid Γ && d.valid Γ && decide (c.tgt = d.src)

def synthC (Γ : Ctx n) (c : Cert n) : Option (Ty n × Ty n) :=
  if c.valid Γ then some (c.src, c.tgt) else none

def checkC (Γ : Ctx n) (c : Cert n) (S T : Ty n) : Bool := decide (synthC Γ c = some (S, T))

theorem Cert.valid_iff {Γ : Ctx n} : (c : Cert n) → (c.valid Γ = true ↔ CTy Γ c c.src c.tgt)
  | .step S T => by simp only [Cert.valid, prim?_iff]; exact ⟨.step, fun | .step h => h⟩
  | .seq c d => by
    simp only [Cert.valid, Bool.and_eq_true, decide_eq_true_eq, c.valid_iff, d.valid_iff]
    refine ⟨fun ⟨⟨h₁, h₂⟩, e⟩ => .seq h₁ (e ▸ h₂), fun | .seq h₁ h₂ => ?_⟩
    obtain ⟨_, e⟩ := h₁.endpoints; obtain ⟨e', _⟩ := h₂.endpoints
    subst e; exact ⟨⟨h₁, e' ▸ h₂⟩, e'.symm⟩

theorem synthC_iff : synthC Γ c = some (S, T) ↔ CTy Γ c S T := by
  unfold synthC
  split
  · rename_i h; rw [c.valid_iff] at h
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨fun ⟨e₁, e₂⟩ => e₁ ▸ e₂ ▸ h, fun h' => h'.endpoints⟩
  · rename_i h; rw [c.valid_iff] at h
    simp only [reduceCtorEq, false_iff]
    intro h'; obtain ⟨rfl, rfl⟩ := h'.endpoints; exact h h'

theorem checkC_iff : checkC Γ c S T = true ↔ CTy Γ c S T := by
  simp [checkC, synthC_iff]

instance : Decidable (CTy Γ c S T) := decidable_of_iff _ checkC_iff

/-! ## Renaming -/

def Cert.rename (ρ : Fin n → Fin m) : Cert n → Cert m
  | .step S T => .step (S.rename ρ) (T.rename ρ)
  | .seq c d => .seq (c.rename ρ) (d.rename ρ)

def Cert.weaken (c : Cert n) : Cert (n+1) := c.rename Fin.succ

theorem CTy.rename {Γ : Ctx n} {Δ : Ctx m} {ρ : Fin n → Fin m} (hρ : TyRen Γ Δ ρ)
    (h : CTy Γ c S T) : CTy Δ (c.rename ρ) (S.rename ρ) (T.rename ρ) := by
  induction h with
  | step h => exact .step (h.rename hρ)
  | seq _ _ i₁ i₂ => exact .seq i₁ i₂

theorem CTy.weaken (B : Ty n) (h : CTy Γ c S T) : CTy (Γ.snoc B) c.weaken S.weaken T.weaken :=
  h.rename (TyRen.weaken Γ B)

end SelFsub
