import Coercions.DotMNF.WadlerFest.Typing
import Coercions.DotMNF.WadlerFest.Renaming
import Coercions.DotMNF.WadlerFest.Reduction

/-!
# Label discipline for the published source fragment

The internal syntax shares a label type with FCdot. These predicates select
the published fragment: type declarations and selections carry type labels;
field declarations, definitions, and projections carry term labels. The
condition traverses all annotations and nested terms. It is preserved by
renaming and retained-let reduction.
-/

open FCdot (Sig BVar Rename Label)

namespace DotMNF.Ty

inductive LabelSorted : Ty s → Prop where
  | top : LabelSorted .top
  | bot : LabelSorted .bot
  | typ : LabelSorted S → LabelSorted T → LabelSorted (.typ (.typ A) S T)
  | fld : LabelSorted T → LabelSorted (.fld (.trm a) T)
  | sel : LabelSorted (.sel p (.typ A))
  | mu : LabelSorted T → LabelSorted (.mu T)
  | all : LabelSorted S → LabelSorted T → LabelSorted (.all S T)
  | and : LabelSorted S → LabelSorted T → LabelSorted (.and S T)

theorem LabelSorted.rename {T : Ty s₁} (h : T.LabelSorted) (ρ : Rename s₁ s₂) :
    (T.rename ρ).LabelSorted := by
  induction h generalizing s₂ with
  | top => exact .top
  | bot => exact .bot
  | typ _ _ ih₁ ih₂ => exact .typ (ih₁ ρ) (ih₂ ρ)
  | fld _ ih => exact .fld (ih ρ)
  | sel => exact .sel
  | mu _ ih => exact .mu (ih ρ.lift)
  | all _ _ ih₁ ih₂ => exact .all (ih₁ ρ) (ih₂ ρ.lift)
  | and _ _ ih₁ ih₂ => exact .and (ih₁ ρ) (ih₂ ρ)

theorem LabelSorted.weaken {T : Ty s} (h : T.LabelSorted) :
    (T.weaken (k := k)).LabelSorted := h.rename Rename.succ

theorem LabelSorted.substVar {T : Ty (s,,k)} (h : T.LabelSorted) (y : BVar s k) :
    (T.substVar y).LabelSorted := h.rename (Rename.subst y)

end DotMNF.Ty

namespace WadlerFest

mutual

inductive Tm.LabelSorted : Tm s → Prop where
  | path : Tm.LabelSorted (.path p)
  | val : Value.LabelSorted v → Tm.LabelSorted (.val v)
  | app : Tm.LabelSorted (.app x y)
  | proj : Tm.LabelSorted (.proj x (.trm a))
  | «let» : Tm.LabelSorted t → Tm.LabelSorted u → Tm.LabelSorted (.let t u)

inductive Value.LabelSorted : Value s → Prop where
  | obj : T.LabelSorted → Defs.LabelSorted d → Value.LabelSorted (.obj T d)
  | lam : S.LabelSorted → Tm.LabelSorted t → Value.LabelSorted (.lam S t)

inductive Defs.LabelSorted : Defs s → Prop where
  | typ : T.LabelSorted → Defs.LabelSorted (.typ (.typ A) T)
  | trm : Tm.LabelSorted t → Defs.LabelSorted (.trm (.trm a) t)
  | and : Defs.LabelSorted d₁ → Defs.LabelSorted d₂ → Defs.LabelSorted (.and d₁ d₂)

end

mutual

theorem Tm.LabelSorted.rename {t : Tm s₁} (h : t.LabelSorted) (ρ : Rename s₁ s₂) :
    (t.rename ρ).LabelSorted := by
  cases h with
  | path => exact .path
  | val hv => exact .val (hv.rename ρ)
  | app => exact .app
  | proj => exact .proj
  | «let» ht hu => exact .let (ht.rename ρ) (hu.rename ρ.lift)

theorem Value.LabelSorted.rename {v : Value s₁} (h : v.LabelSorted) (ρ : Rename s₁ s₂) :
    (v.rename ρ).LabelSorted := by
  cases h with
  | obj hT hd => exact .obj (hT.rename ρ.lift) (hd.rename ρ.lift)
  | lam hS ht => exact .lam (hS.rename ρ) (ht.rename ρ.lift)

theorem Defs.LabelSorted.rename {d : Defs s₁} (h : d.LabelSorted) (ρ : Rename s₁ s₂) :
    (d.rename ρ).LabelSorted := by
  cases h with
  | typ hT => exact .typ (hT.rename ρ)
  | trm ht => exact .trm (ht.rename ρ)
  | and hd₁ hd₂ => exact .and (hd₁.rename ρ) (hd₂.rename ρ)

end

theorem Tm.LabelSorted.substVar {t : Tm (s,x)} (h : t.LabelSorted) (y : BVar s .var) :
    (t.substVar y).LabelSorted := h.rename (Rename.subst y)

theorem Value.LabelSorted.weaken {v : Value s} (h : v.LabelSorted) :
    v.weaken.LabelSorted := h.rename Rename.succ

def Ctx.LabelSorted (Γ : Ctx s) : Prop := ∀ x, (Γ.lookup x).LabelSorted

theorem Ctx.LabelSorted.nil : Ctx.nil.LabelSorted := fun x => nomatch x

theorem Ctx.LabelSorted.extend {Γ : Ctx s} {T : DotMNF.Ty (s,x)}
    (hΓ : Γ.LabelSorted) (hT : T.LabelSorted) : (Γ.extend T).LabelSorted := by
  intro x
  cases x with
  | here => exact hT
  | there x => exact (hΓ x).weaken

theorem Ctx.LabelSorted.cons {Γ : Ctx s} {T : DotMNF.Ty s}
    (hΓ : Γ.LabelSorted) (hT : T.LabelSorted) : (Γ.cons T).LabelSorted :=
  hΓ.extend hT.weaken

inductive Store.LabelSorted : Store s → Prop where
  | nil : Store.LabelSorted .nil
  | cons : Store.LabelSorted σ → v.LabelSorted → Store.LabelSorted (.cons σ v)

theorem Store.LabelSorted.lookup {σ : Store s} (h : σ.LabelSorted) (x : BVar s .var) :
    (σ.lookup x).LabelSorted := by
  induction h with
  | nil => cases x
  | cons _ hv ih =>
      cases x with
      | here => exact hv.weaken
      | there x => exact (ih x).weaken

theorem Defs.HasField.labelSorted {d : Defs s} (h : d.HasField a t)
    (hd : d.LabelSorted) : t.LabelSorted := by
  induction h with
  | trm => cases hd with | trm ht => exact ht
  | andLeft _ ih => cases hd with | and hd₁ _ => exact ih hd₁
  | andRight _ ih => cases hd with | and _ hd₂ => exact ih hd₂

theorem Retained.Red.labelSorted {σ : Store s} {t u : Tm s}
    (h : Red σ t u) (hσ : σ.LabelSorted) (ht : t.LabelSorted) : u.LabelSorted := by
  induction h with
  | @app s σ x y S t hl =>
      have hv := hσ.lookup x
      rw [hl] at hv
      cases hv with
      | lam _ hb => exact hb.substVar _
  | @proj s d a t σ x T hl hf =>
      have hv := hσ.lookup x
      rw [hl] at hv
      cases hv with
      | obj _ hd => exact (hf.labelSorted hd).substVar _
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

theorem Retained.Steps.labelSorted {σ : Store s} {t u : Tm s}
    (h : Steps σ t u) (hσ : σ.LabelSorted) (ht : t.LabelSorted) : u.LabelSorted := by
  induction h with
  | refl => exact ht
  | tail _ h ih => exact h.labelSorted hσ ih

/-! A certificate checks every judgment in a derivation, including contexts
and intermediate types hidden by transitivity or subsumption. -/

mutual

def Sub.LabelSorted {Γ : Ctx s} {S T : DotMNF.Ty s} (h : Sub Γ S T) : Prop :=
  Γ.LabelSorted ∧ S.LabelSorted ∧ T.LabelSorted ∧
  match h with
  | .top | .bot | .refl | .and1 | .and2 => True
  | .trans h₁ h₂ | .and h₁ h₂ | .typ h₁ h₂ | .all h₁ h₂ => h₁.LabelSorted ∧ h₂.LabelSorted
  | .fld h => h.LabelSorted
  | .selUpper h | .selLower h => h.LabelSorted

def HasTy.LabelSorted {Γ : Ctx s} {t : Tm s} {T : DotMNF.Ty s}
    (h : HasTy Γ t T) : Prop :=
  Γ.LabelSorted ∧ t.LabelSorted ∧ T.LabelSorted ∧
  match h with
  | .var => True
  | .lam h | .proj h | .recI h | .recE h => h.LabelSorted
  | .app h₁ h₂ | .let h₁ h₂ | .andI h₁ h₂ => h₁.LabelSorted ∧ h₂.LabelSorted
  | .obj h => h.LabelSorted
  | .sub h₁ h₂ => h₁.LabelSorted ∧ h₂.LabelSorted

def DefsTy.LabelSorted {Γ : Ctx s} {d : Defs s} {T : DotMNF.Ty s}
    (h : DefsTy Γ d T) : Prop :=
  Γ.LabelSorted ∧ d.LabelSorted ∧ T.LabelSorted ∧
  match h with
  | .typ => True
  | .trm h => h.LabelSorted
  | .and h₁ h₂ _ => h₁.LabelSorted ∧ h₂.LabelSorted

end

end WadlerFest
