import Coercions.DotMNF.WadlerFest.Machine
import Coercions.DotMNF.Structural

/-!
# Renaming and binder insertion for annotated syntax

All substitutions used by the retained-let semantics replace a variable by
another variable. They are instances of renaming. Insertion below the newest
binder is `Rename.succ.lift`; in particular, this is the renaming of the outer
let body when two lets are reassociated.
-/

namespace WadlerFest

open FCdot (Sig BVar Rename)

def Tm.weaken (t : Tm s) : Tm (s,x) := t.rename Rename.succ
def Defs.weaken (d : Defs s) : Defs (s,x) := d.rename Rename.succ
def Value.substVar (v : Value (s,x)) (y : BVar s .var) : Value s :=
  v.rename (Rename.subst y)

mutual

@[simp] theorem Tm.rename_id : ∀ {s : Sig} (t : Tm s), t.rename Rename.id = t
  | _, .path _ => by simp only [Tm.rename, DotMNF.Path.rename_id]
  | _, .val v => congrArg Tm.val (Value.rename_id v)
  | _, .app _ _ => rfl
  | _, .proj _ _ => rfl
  | _, .let t u => by
      simp only [Tm.rename, Rename.lift_id, Tm.rename_id t, Tm.rename_id u]

@[simp] theorem Value.rename_id : ∀ {s : Sig} (v : Value s), v.rename Rename.id = v
  | _, .obj T d => by
      simp only [Value.rename, Rename.lift_id, DotMNF.Ty.rename_id, Defs.rename_id d]
  | _, .lam S t => by
      simp only [Value.rename, Rename.lift_id, DotMNF.Ty.rename_id, Tm.rename_id t]

@[simp] theorem Defs.rename_id : ∀ {s : Sig} (d : Defs s), d.rename Rename.id = d
  | _, .typ _ _ => by simp only [Defs.rename, DotMNF.Ty.rename_id]
  | _, .trm a t => congrArg (Defs.trm a) (Tm.rename_id t)
  | _, .and d₁ d₂ => by simp only [Defs.rename, Defs.rename_id d₁, Defs.rename_id d₂]

end

mutual

theorem Tm.rename_comp (t : Tm s₁) (ρ : Rename s₁ s₂) (τ : Rename s₂ s₃) :
    (t.rename ρ).rename τ = t.rename (ρ.comp τ) := by
  cases t with
  | path => simp only [Tm.rename, DotMNF.Path.rename_comp]
  | val v => exact congrArg Tm.val (Value.rename_comp v ρ τ)
  | app => rfl
  | proj => rfl
  | «let» t u =>
      simp only [Tm.rename, Rename.lift_comp,
        Tm.rename_comp t ρ τ, Tm.rename_comp u ρ.lift τ.lift]

theorem Value.rename_comp (v : Value s₁) (ρ : Rename s₁ s₂) (τ : Rename s₂ s₃) :
    (v.rename ρ).rename τ = v.rename (ρ.comp τ) := by
  cases v with
  | obj T d =>
      simp only [Value.rename, Rename.lift_comp, DotMNF.Ty.rename_comp,
        Defs.rename_comp d ρ.lift τ.lift]
  | lam S t =>
      simp only [Value.rename, Rename.lift_comp, DotMNF.Ty.rename_comp,
        Tm.rename_comp t ρ.lift τ.lift]

theorem Defs.rename_comp (d : Defs s₁) (ρ : Rename s₁ s₂) (τ : Rename s₂ s₃) :
    (d.rename ρ).rename τ = d.rename (ρ.comp τ) := by
  cases d with
  | typ => simp only [Defs.rename, DotMNF.Ty.rename_comp]
  | trm a t => exact congrArg (Defs.trm a) (Tm.rename_comp t ρ τ)
  | and d₁ d₂ =>
      simp only [Defs.rename, Defs.rename_comp d₁ ρ τ, Defs.rename_comp d₂ ρ τ]

end

private theorem subst_rename (y : BVar s₁ .var) (ρ : Rename s₁ s₂) :
    (Rename.subst y).comp ρ = ρ.lift.comp (Rename.subst (ρ.var y)) := by
  apply Rename.funext'
  intro k z
  cases z <;> rfl

private theorem insert_here :
    (Rename.succ.lift : Rename (s,x) (s,x,x)).comp (Rename.subst .here) = Rename.id := by
  apply Rename.funext'
  intro k z
  cases z <;> rfl

private theorem insert_substLift (y : BVar s .var) :
    (Rename.succ.lift : Rename (s,x) (s,x,x)).comp (Rename.subst y).lift = Rename.id := by
  rw [← Rename.lift_comp, Rename.succ_subst, Rename.lift_id]

private theorem insert_rename (ρ : Rename s₁ s₂) :
    (Rename.succ.lift : Rename (s₁,x) (s₁,x,x)).comp ρ.lift.lift =
      ρ.lift.comp Rename.succ.lift := by
  rw [← Rename.lift_comp, ← Rename.lift_comp, Rename.succ_lift]

theorem Tm.weaken_rename (t : Tm s₁) (ρ : Rename s₁ s₂) :
    t.weaken.rename ρ.lift = (t.rename ρ).weaken := by
  simp only [Tm.weaken, Tm.rename_comp, Rename.succ_lift]

theorem Value.weaken_rename (v : Value s₁) (ρ : Rename s₁ s₂) :
    v.weaken.rename ρ.lift = (v.rename ρ).weaken := by
  simp only [Value.weaken, Value.rename_comp, Rename.succ_lift]

theorem Defs.weaken_rename (d : Defs s₁) (ρ : Rename s₁ s₂) :
    d.weaken.rename ρ.lift = (d.rename ρ).weaken := by
  simp only [Defs.weaken, Defs.rename_comp, Rename.succ_lift]

@[simp] theorem Tm.weaken_substVar (t : Tm s) (y : BVar s .var) :
    t.weaken.substVar y = t := by
  simp only [Tm.weaken, Tm.substVar, Tm.rename_comp, Rename.succ_subst, Tm.rename_id]

@[simp] theorem Value.weaken_substVar (v : Value s) (y : BVar s .var) :
    v.weaken.substVar y = v := by
  simp only [Value.weaken, Value.substVar, Value.rename_comp,
    Rename.succ_subst, Value.rename_id]

@[simp] theorem Defs.weaken_substVar (d : Defs s) (y : BVar s .var) :
    d.weaken.substVar y = d := by
  simp only [Defs.weaken, Defs.substVar, Defs.rename_comp, Rename.succ_subst, Defs.rename_id]

theorem Tm.substVar_rename (t : Tm (s₁,x)) (y : BVar s₁ .var) (ρ : Rename s₁ s₂) :
    (t.substVar y).rename ρ = (t.rename ρ.lift).substVar (ρ.var y) := by
  simp only [Tm.substVar, Tm.rename_comp, subst_rename]

theorem Value.substVar_rename (v : Value (s₁,x)) (y : BVar s₁ .var) (ρ : Rename s₁ s₂) :
    (v.substVar y).rename ρ = (v.rename ρ.lift).substVar (ρ.var y) := by
  simp only [Value.substVar, Value.rename_comp, subst_rename]

theorem Defs.substVar_rename (d : Defs (s₁,x)) (y : BVar s₁ .var) (ρ : Rename s₁ s₂) :
    (d.substVar y).rename ρ = (d.rename ρ.lift).substVar (ρ.var y) := by
  simp only [Defs.substVar, Defs.rename_comp, subst_rename]

theorem Tm.substVar_weaken (t : Tm (s,x)) (y : BVar s .var) :
    (t.substVar y).weaken = (t.rename Rename.succ.lift).substVar (.there y) :=
  t.substVar_rename y Rename.succ

theorem Value.substVar_weaken (v : Value (s,x)) (y : BVar s .var) :
    (v.substVar y).weaken = (v.rename Rename.succ.lift).substVar (.there y) :=
  v.substVar_rename y Rename.succ

theorem Defs.substVar_weaken (d : Defs (s,x)) (y : BVar s .var) :
    (d.substVar y).weaken = (d.rename Rename.succ.lift).substVar (.there y) :=
  d.substVar_rename y Rename.succ

theorem Tm.substVar_substVar (t : Tm (s,x,x)) (y : BVar (s,x) .var)
    (z : BVar s .var) :
    (t.substVar y).substVar z =
      (t.rename (Rename.subst z).lift).substVar ((Rename.subst z).var y) :=
  t.substVar_rename y (Rename.subst z)

theorem Value.substVar_substVar (v : Value (s,x,x)) (y : BVar (s,x) .var)
    (z : BVar s .var) :
    (v.substVar y).substVar z =
      (v.rename (Rename.subst z).lift).substVar ((Rename.subst z).var y) :=
  v.substVar_rename y (Rename.subst z)

theorem Defs.substVar_substVar (d : Defs (s,x,x)) (y : BVar (s,x) .var)
    (z : BVar s .var) :
    (d.substVar y).substVar z =
      (d.rename (Rename.subst z).lift).substVar ((Rename.subst z).var y) :=
  d.substVar_rename y (Rename.subst z)

theorem Tm.weaken_weaken (t : Tm s) :
    t.weaken.rename Rename.succ.lift = t.weaken.weaken := t.weaken_rename Rename.succ

theorem Value.weaken_weaken (v : Value s) :
    v.weaken.rename Rename.succ.lift = v.weaken.weaken := v.weaken_rename Rename.succ

theorem Defs.weaken_weaken (d : Defs s) :
    d.weaken.rename Rename.succ.lift = d.weaken.weaken := d.weaken_rename Rename.succ

/-- Inserting a binder below the newest one, then identifying them, is the identity. -/
@[simp] theorem Tm.insertBinder_substVar (t : Tm (s,x)) :
    (t.rename Rename.succ.lift).substVar .here = t := by
  simp only [Tm.substVar, Tm.rename_comp, insert_here, Tm.rename_id]

@[simp] theorem Value.insertBinder_substVar (v : Value (s,x)) :
    (v.rename Rename.succ.lift).substVar .here = v := by
  simp only [Value.substVar, Value.rename_comp, insert_here, Value.rename_id]

@[simp] theorem Defs.insertBinder_substVar (d : Defs (s,x)) :
    (d.rename Rename.succ.lift).substVar .here = d := by
  simp only [Defs.substVar, Defs.rename_comp, insert_here, Defs.rename_id]

/-- A newly inserted binder does not occur in the original body. -/
@[simp] theorem Tm.insertBinder_substLift (t : Tm (s,x)) (y : BVar s .var) :
    (t.rename Rename.succ.lift).rename (Rename.subst y).lift = t := by
  simp only [Tm.rename_comp, insert_substLift, Tm.rename_id]

@[simp] theorem Value.insertBinder_substLift (v : Value (s,x)) (y : BVar s .var) :
    (v.rename Rename.succ.lift).rename (Rename.subst y).lift = v := by
  simp only [Value.rename_comp, insert_substLift, Value.rename_id]

@[simp] theorem Defs.insertBinder_substLift (d : Defs (s,x)) (y : BVar s .var) :
    (d.rename Rename.succ.lift).rename (Rename.subst y).lift = d := by
  simp only [Defs.rename_comp, insert_substLift, Defs.rename_id]

theorem Tm.insertBinder_rename (t : Tm (s₁,x)) (ρ : Rename s₁ s₂) :
    (t.rename (Rename.succ : Rename s₁ (s₁,x)).lift).rename ρ.lift.lift =
      (t.rename ρ.lift).rename Rename.succ.lift := by
  simp only [Tm.rename_comp, insert_rename]

theorem Value.insertBinder_rename (v : Value (s₁,x)) (ρ : Rename s₁ s₂) :
    (v.rename (Rename.succ : Rename s₁ (s₁,x)).lift).rename ρ.lift.lift =
      (v.rename ρ.lift).rename Rename.succ.lift := by
  simp only [Value.rename_comp, insert_rename]

theorem Defs.insertBinder_rename (d : Defs (s₁,x)) (ρ : Rename s₁ s₂) :
    (d.rename (Rename.succ : Rename s₁ (s₁,x)).lift).rename ρ.lift.lift =
      (d.rename ρ.lift).rename Rename.succ.lift := by
  simp only [Defs.rename_comp, insert_rename]

@[simp] theorem Tm.eraseAnnotations_weaken (t : Tm s) :
    t.weaken.eraseAnnotations = t.eraseAnnotations.weaken := t.eraseAnnotations_rename _

@[simp] theorem Defs.eraseAnnotations_weaken (d : Defs s) :
    d.weaken.eraseAnnotations = d.eraseAnnotations.weaken := d.eraseAnnotations_rename _

@[simp] theorem Value.eraseAnnotations_substVar (v : Value (s,x)) (y : BVar s .var) :
    (v.substVar y).eraseAnnotations = v.eraseAnnotations.substVar y :=
  v.eraseAnnotations_rename _

@[simp] theorem Defs.labels_rename : ∀ {s₁ s₂ : Sig} (d : Defs s₁) (ρ : Rename s₁ s₂),
    (d.rename ρ).labels = d.labels
  | _, _, .typ _ _, _ => rfl
  | _, _, .trm _ _, _ => rfl
  | _, _, .and d₁ d₂, ρ => by
      simp only [Defs.rename, Defs.labels, Defs.labels_rename d₁ ρ, Defs.labels_rename d₂ ρ]

/-- Field lookup commutes with the variable renamings used by evaluation. -/
theorem Defs.lookupTrm_rename :
    ∀ {s₁ s₂ : Sig} (d : Defs s₁) (ρ : Rename s₁ s₂) (a : FCdot.Label),
      (d.rename ρ).lookupTrm a = (d.lookupTrm a).map (fun t => t.rename ρ)
  | _, _, .typ _ _, _, _ => rfl
  | _, _, .trm b t, ρ, a => by
      simp only [Defs.rename, Defs.lookupTrm]
      split <;> rfl
  | _, _, .and d₁ d₂, ρ, a => by
      simp only [Defs.rename, Defs.lookupTrm,
        Defs.lookupTrm_rename d₁ ρ a, Defs.lookupTrm_rename d₂ ρ a]
      cases d₂.lookupTrm a <;> cases d₁.lookupTrm a <;> rfl

theorem Defs.lookupTrm_rename_of_eq {d : Defs s₁} {a : FCdot.Label} {t : Tm s₁}
    (h : d.lookupTrm a = some t) (ρ : Rename s₁ s₂) :
    (d.rename ρ).lookupTrm a = some (t.rename ρ) := by
  rw [Defs.lookupTrm_rename, h]
  rfl

end WadlerFest
