import Coercions.DotMNF.WadlerFest.Typing
import Coercions.DotMNF.WadlerFest.Reduction
import Coercions.DotMNF.WadlerFest.Renaming

/-!
# Distinct object definitions throughout a program

Well-formedness checks label distinctness in every object, including objects
inside field and function bodies. It imposes no restrictions on types or on
recursive dependencies. Typing supplies this property, and renaming preserves
it. This invariant reconciles relational field membership with machine lookup.
-/

namespace WadlerFest

open FCdot (Sig BVar Rename Label)

inductive Defs.Distinct : {s : Sig} → Defs s → Prop where
  | typ : Distinct (.typ A T)
  | trm : Distinct (.trm a t)
  | and : Distinct d₁ → Distinct d₂ →
      (∀ ℓ, ℓ ∈ d₁.labels → ℓ ∉ d₂.labels) → Distinct (.and d₁ d₂)

mutual

inductive Tm.Wf : {s : Sig} → Tm s → Prop where
  | path : Tm.Wf (.path p)
  | val : Value.Wf v → Tm.Wf (.val v)
  | app : Tm.Wf (.app x y)
  | proj : Tm.Wf (.proj x a)
  | «let» : Tm.Wf t → Tm.Wf u → Tm.Wf (.let t u)

inductive Value.Wf : {s : Sig} → Value s → Prop where
  | obj : Defs.Wf d → Value.Wf (.obj T d)
  | lam : Tm.Wf t → Value.Wf (.lam S t)

inductive Defs.Wf : {s : Sig} → Defs s → Prop where
  | typ : Defs.Wf (.typ A T)
  | trm : Tm.Wf t → Defs.Wf (.trm a t)
  | and : Defs.Wf d₁ → Defs.Wf d₂ →
      (∀ ℓ, ℓ ∈ d₁.labels → ℓ ∉ d₂.labels) → Defs.Wf (.and d₁ d₂)

end

theorem Defs.Wf.distinct {d : Defs s} (h : Defs.Wf d) : d.Distinct :=
  match h with
  | .typ => .typ
  | .trm _ => .trm
  | .and h₁ h₂ hd => .and h₁.distinct h₂.distinct hd

theorem Defs.Distinct.rename {d : Defs s₁} (h : Defs.Distinct d) (ρ : Rename s₁ s₂) :
    (d.rename ρ).Distinct := by
  induction h with
  | typ => exact .typ
  | trm => exact .trm
  | and _ _ hd ih₁ ih₂ =>
      exact .and ih₁ ih₂ (by simpa only [Defs.labels_rename] using hd)

mutual

theorem Tm.Wf.rename {t : Tm s₁} (h : Tm.Wf t) (ρ : Rename s₁ s₂) :
    Tm.Wf (t.rename ρ) := by
  cases h with
  | path => exact .path
  | val h => exact .val (h.rename ρ)
  | app => exact .app
  | proj => exact .proj
  | «let» h₁ h₂ => exact .let (h₁.rename ρ) (h₂.rename ρ.lift)

theorem Value.Wf.rename {v : Value s₁} (h : Value.Wf v) (ρ : Rename s₁ s₂) :
    Value.Wf (v.rename ρ) := by
  cases h with
  | obj h => exact .obj (h.rename ρ.lift)
  | lam h => exact .lam (h.rename ρ.lift)

theorem Defs.Wf.rename {d : Defs s₁} (h : Defs.Wf d) (ρ : Rename s₁ s₂) :
    Defs.Wf (d.rename ρ) := by
  cases h with
  | typ => exact .typ
  | trm h => exact .trm (h.rename ρ)
  | and h₁ h₂ hd =>
      exact .and (h₁.rename ρ) (h₂.rename ρ)
        (by simpa only [Defs.labels_rename] using hd)

end

theorem Tm.Wf.substVar {t : Tm (s,x)} (h : Tm.Wf t) (y : BVar s .var) :
    Tm.Wf (t.substVar y) := h.rename (Rename.subst y)

theorem Value.Wf.weaken {v : Value s} (h : Value.Wf v) : Value.Wf v.weaken :=
  h.rename Rename.succ

mutual

theorem HasTy.wf {Γ : Ctx s} {t : Tm s} {T : DotMNF.Ty s}
    (h : HasTy Γ t T) : t.Wf :=
  match h with
  | .var => .path
  | .lam h => .val (.lam h.wf)
  | .app _ _ => .app
  | .obj h => .val (.obj h.wf)
  | .proj _ => .proj
  | .let h₁ h₂ => .let h₁.wf h₂.wf
  | .recI _ => .path
  | .recE _ => .path
  | .andI _ _ => .path
  | .sub h _ => h.wf

theorem DefsTy.wf {Γ : Ctx s} {d : Defs s} {T : DotMNF.Ty s}
    (h : DefsTy Γ d T) : d.Wf :=
  match h with
  | .typ => .typ
  | .trm h => .trm h.wf
  | .and h₁ h₂ hd => .and h₁.wf h₂.wf hd

end

inductive Store.Wf : {s : Sig} → Store s → Prop where
  | nil : Store.Wf .nil
  | cons : Store.Wf σ → Value.Wf v → Store.Wf (.cons σ v)

theorem Store.Wf.lookup {σ : Store s} (h : Store.Wf σ) (x : BVar s .var) :
    (σ.lookup x).Wf := by
  induction h with
  | nil => nomatch x
  | cons hσ hv ih =>
      cases x with
      | here => exact hv.weaken
      | there x => exact (ih x).weaken

theorem Defs.HasField.mem_labels (h : HasField d a t) : a ∈ d.labels := by
  induction h with
  | trm => simp only [Defs.labels, List.mem_singleton]
  | andLeft _ ih => exact List.mem_append.mpr (.inl ih)
  | andRight _ ih => exact List.mem_append.mpr (.inr ih)

theorem Defs.lookupTrm_none_of_not_mem (d : Defs s) (a : Label)
    (h : a ∉ d.labels) : d.lookupTrm a = none := by
  cases d with
  | typ => rfl
  | trm b t =>
      simp only [Defs.labels, List.mem_singleton] at h
      simp only [Defs.lookupTrm, if_neg h]
  | and d₁ d₂ =>
      have h₁ : a ∉ d₁.labels := fun hm => h (List.mem_append.mpr (.inl hm))
      have h₂ : a ∉ d₂.labels := fun hm => h (List.mem_append.mpr (.inr hm))
      rw [Defs.lookupTrm, lookupTrm_none_of_not_mem d₁ a h₁,
        lookupTrm_none_of_not_mem d₂ a h₂]
      rfl

/-- In distinct definitions, relational membership agrees with lookup. -/
theorem Defs.HasField.lookupTrm (h : HasField d a t) (hd : d.Distinct) :
    d.lookupTrm a = some t := by
  induction h with
  | trm => simp only [Defs.lookupTrm, ↓reduceIte]
  | andLeft hf ih =>
      cases hd with
      | and hd₁ hd₂ hdis =>
          rw [Defs.lookupTrm, lookupTrm_none_of_not_mem _ _ (hdis _ hf.mem_labels), ih hd₁]
          rfl
  | andRight _ ih =>
      cases hd with
      | and hd₁ hd₂ hdis =>
          rw [Defs.lookupTrm, ih hd₂]
          rfl

theorem Defs.HasField.wf (h : HasField d a t) (hd : d.Wf) : t.Wf := by
  induction h with
  | trm => cases hd with | trm ht => exact ht
  | andLeft _ ih => cases hd with | and hd₁ _ _ => exact ih hd₁
  | andRight _ ih => cases hd with | and _ hd₂ _ => exact ih hd₂

/-- Retained reduction preserves distinctness in all nested objects. -/
theorem Retained.Red.wf {σ : Store s} {t u : Tm s}
    (h : Red σ t u) (hσ : σ.Wf) (ht : t.Wf) : u.Wf := by
  induction h with
  | @app s σ x y S t hl =>
      have hv := hσ.lookup x
      rw [hl] at hv
      cases hv with
      | lam hb => exact hb.substVar _
  | @proj s d a t σ x T hl hf =>
      have hv := hσ.lookup x
      rw [hl] at hv
      cases hv with
      | obj hd => exact (hf.wf hd).substVar _
  | alias => cases ht with | «let» _ hu => exact hu.substVar _
  | assoc =>
      cases ht with
      | «let» ht hv =>
          cases ht with
          | «let» ht hu => exact .let ht (.let hu (hv.rename _))
  | letRHS _ ih =>
      cases ht with
      | «let» ht hu => exact .let (ih hσ ht) hu
  | letValue _ ih =>
      cases ht with
      | «let» hv ht =>
          cases hv with
          | val hv => exact .let (.val hv) (ih (.cons hσ hv) ht)

theorem Retained.Steps.wf {σ : Store s} {t u : Tm s}
    (h : Steps σ t u) (hσ : σ.Wf) (ht : t.Wf) : u.Wf := by
  induction h with
  | refl => exact ht
  | tail _ h ih => exact h.wf hσ ih

end WadlerFest
