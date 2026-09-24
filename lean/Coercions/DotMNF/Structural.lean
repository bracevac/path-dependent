import Coercions.DotMNF.Typing

/-!
# Renaming of source derivations

Typing is preserved by any renaming that preserves context lookup. In
particular, weakening is independent of whether the new binder records an
object's definitions. These lemmas account for the context representation
used by the correspondence with the annotated WadlerFest calculus.
-/

namespace DotMNF

open FCdot (Sig BVar Rename)

@[simp] theorem Path.rename_id (p : Path s) : p.rename Rename.id = p := by
  cases p <;> rfl

theorem Path.rename_comp (p : Path s1) (ρ : Rename s1 s2) (τ : Rename s2 s3) :
    (p.rename ρ).rename τ = p.rename (ρ.comp τ) := by
  cases p <;> rfl

@[simp] theorem Ty.rename_id (T : Ty s) : T.rename Rename.id = T := by
  induction T with
  | top | bot => rfl
  | typ _ _ _ ih1 ih2 => simp [Ty.rename, ih1, ih2]
  | fld _ _ ih => simp [Ty.rename, ih]
  | sel => simp [Ty.rename]
  | mu _ ih => simp [Ty.rename, Rename.lift_id, ih]
  | all _ _ ih1 ih2 => simp [Ty.rename, Rename.lift_id, ih1, ih2]
  | and _ _ ih1 ih2 => simp [Ty.rename, ih1, ih2]

theorem Ty.rename_comp (T : Ty s1) (ρ : Rename s1 s2) (τ : Rename s2 s3) :
    (T.rename ρ).rename τ = T.rename (ρ.comp τ) := by
  induction T generalizing s2 s3 with
  | top | bot => rfl
  | typ _ _ _ ih1 ih2 => simp [Ty.rename, ih1, ih2]
  | fld _ _ ih => simp [Ty.rename, ih]
  | sel => simp [Ty.rename, Path.rename_comp]
  | mu _ ih => simp [Ty.rename, Rename.lift_comp, ih]
  | all _ _ ih1 ih2 => simp [Ty.rename, Rename.lift_comp, ih1, ih2]
  | and _ _ ih1 ih2 => simp [Ty.rename, ih1, ih2]

theorem Ty.weaken_rename (T : Ty s1) (ρ : Rename s1 s2) :
    T.weaken.rename (ρ.lift (k := .var)) = (T.rename ρ).weaken := by
  simp only [Ty.weaken, Ty.rename_comp, Rename.succ_lift]

theorem Ty.substVar_rename (T : Ty (s1,x)) (y : BVar s1 .var) (ρ : Rename s1 s2) :
    (T.substVar y).rename ρ = (T.rename ρ.lift).substVar (ρ.var y) := by
  simp only [Ty.substVar, Ty.rename_comp]
  congr 1
  apply Rename.funext'
  intro k z
  cases z <;> rfl

@[simp] theorem Ty.weaken_substVar (T : Ty s) (y : BVar s .var) :
    T.weaken.substVar y = T := by
  simp [Ty.weaken, Ty.substVar, Ty.rename_comp, Rename.succ_subst]

/-- Unfolding a weakened recursive type at the new self recovers its body. -/
@[simp] theorem Ty.open_self (T : Ty (s,x)) :
    (T.rename Rename.succ.lift).substVar .here = T := by
  simp only [Ty.substVar, Ty.rename_comp]
  have h : (Rename.succ.lift : Rename (s,x) ((s,x),x)).comp
      (Rename.subst .here) = Rename.id := by
    apply Rename.funext'
    intro k z
    cases z <;> rfl
  rw [h, Ty.rename_id]

@[simp] theorem Defs.labels_rename (d : Defs s1) (ρ : Rename s1 s2) :
    (d.rename ρ).labels = d.labels := by
  match d with
  | .typ _ _ | .trm _ _ => rfl
  | .and d1 d2 => simp [Defs.rename, Defs.labels, Defs.labels_rename d1 ρ,
      Defs.labels_rename d2 ρ]

theorem Defs.Distinct.rename {d : Defs s1} (h : d.Distinct) (ρ : Rename s1 s2) :
    (d.rename ρ).Distinct := by
  induction h with
  | typ => exact .typ
  | trm => exact .trm
  | and _ _ hd ih1 ih2 =>
      exact .and ih1 ih2 (by simpa only [Defs.labels_rename] using hd)

/-- Lookup preservation for a renaming between source contexts. -/
def Ctx.Renames (Γ : Ctx s1) (Δ : Ctx s2) (ρ : Rename s1 s2) : Prop :=
  ∀ y, Δ.lookup (ρ.var y) = (Γ.lookup y).rename ρ

theorem Ctx.Renames.cons {Γ : Ctx s1} {Δ : Ctx s2} {ρ : Rename s1 s2}
    (h : Γ.Renames Δ ρ) (S : Ty s1) :
    (Γ.cons S).Renames (Δ.cons (S.rename ρ)) ρ.lift := by
  intro y
  cases y with
  | here => exact (Ty.weaken_rename S ρ).symm
  | there y =>
      change (Δ.lookup (ρ.var y)).weaken = (Γ.lookup y).weaken.rename ρ.lift
      rw [h y, Ty.weaken_rename]

theorem Ctx.Renames.consSelf {Γ : Ctx s1} {Δ : Ctx s2} {ρ : Rename s1 s2}
    (h : Γ.Renames Δ ρ) (d : Defs (s1,x)) (T : Ty (s1,x)) :
    (Γ.consSelf d T).Renames (Δ.consSelf (d.rename ρ.lift) (T.rename ρ.lift))
      ρ.lift := by
  intro y
  cases y with
  | here => exact (Ty.weaken_rename (.mu T) ρ).symm
  | there y =>
      change (Δ.lookup (ρ.var y)).weaken = (Γ.lookup y).weaken.rename ρ.lift
      rw [h y, Ty.weaken_rename]

mutual

def Sub.rename {Γ : Ctx s1} {S T : Ty s1} (h : Sub Γ S T)
    {Δ : Ctx s2} (ρ : Rename s1 s2) (hρ : Γ.Renames Δ ρ) :
    Sub Δ (S.rename ρ) (T.rename ρ) :=
  match h with
  | .top => .top
  | .bot => .bot
  | .refl => .refl
  | .trans h1 h2 => .trans (h1.rename ρ hρ) (h2.rename ρ hρ)
  | .and1 => .and1
  | .and2 => .and2
  | .and h1 h2 => .and (h1.rename ρ hρ) (h2.rename ρ hρ)
  | .fld h => .fld (h.rename ρ hρ)
  | .typ h1 h2 => .typ (h1.rename ρ hρ) (h2.rename ρ hρ)
  | .selUpper h => .selUpper (h.rename ρ hρ)
  | .selLower h => .selLower (h.rename ρ hρ)
  | .all h1 h2 => .all (h1.rename ρ hρ) (h2.rename ρ.lift (hρ.cons _))

def HasTy.rename {Γ : Ctx s1} {t : Tm s1} {T : Ty s1} (h : HasTy Γ t T)
    {Δ : Ctx s2} (ρ : Rename s1 s2) (hρ : Γ.Renames Δ ρ) :
    HasTy Δ (t.rename ρ) (T.rename ρ) :=
  match h with
  | .var => by rw [← hρ]; exact .var
  | .lam h => .lam (h.rename ρ.lift (hρ.cons _))
  | .app h1 h2 => by
      rw [Ty.substVar_rename]
      exact .app (h1.rename ρ hρ) (h2.rename ρ hρ)
  | .obj h hd => .obj (h.rename ρ.lift (hρ.consSelf _ _)) (hd.rename ρ.lift)
  | .proj h => .proj (h.rename ρ hρ)
  | .let h1 h2 => by
      apply HasTy.let (h1.rename ρ hρ)
      simpa only [Ty.weaken_rename] using h2.rename ρ.lift (hρ.cons _)
  | .recI h => by
      apply HasTy.recI
      simpa only [Ty.substVar_rename] using h.rename ρ hρ
  | .recE h => by
      rw [Ty.substVar_rename]
      exact .recE (h.rename ρ hρ)
  | .andI h1 h2 => .andI (h1.rename ρ hρ) (h2.rename ρ hρ)
  | .sub h1 h2 => .sub (h1.rename ρ hρ) (h2.rename ρ hρ)

def DefsTy.rename {Γ : Ctx s1} {d : Defs s1} {T : Ty s1} (h : DefsTy Γ d T)
    {Δ : Ctx s2} (ρ : Rename s1 s2) (hρ : Γ.Renames Δ ρ) :
    DefsTy Δ (d.rename ρ) (T.rename ρ) :=
  match h with
  | .typ => .typ
  | .trm h => .trm (h.rename ρ hρ)
  | .and h1 h2 => .and (h1.rename ρ hρ) (h2.rename ρ hρ)

end

def HasTy.weaken {Γ : Ctx s} {t : Tm s} {T : Ty s} (h : HasTy Γ t T) (S : Ty s) :
    HasTy (Γ.cons S) t.weaken T.weaken :=
  h.rename Rename.succ (fun _ => rfl)

def HasTy.weakenSelf {Γ : Ctx s} {t : Tm s} {T : Ty s} (h : HasTy Γ t T)
    (d : Defs (s,x)) (U : Ty (s,x)) : HasTy (Γ.consSelf d U) t.weaken T.weaken :=
  h.rename Rename.succ (fun _ => rfl)

end DotMNF
