import Coercions.DotMNF.Structural
import Coercions.Selective.Dot.Typing
import Coercions.Selective.Dot.RenameTy

/-!
# Selective DOT and DOT-MNF: translations of syntax

The two calculi have the same types: a selection `x.A` of `SelDot` is the
selection `(var x).A` of DOT-MNF. Their terms agree on cast-free terms whose
paths are variables. `toDot` removes every cast; `ofDot` is its inverse on
the image of erasure.

A context of DOT-MNF may record the definitions of an object at a self
binder. `Ctx.ofDot` forgets them: the binder has the type `μ(x. T)` either
way, so lookup is preserved.
-/

namespace SelDot

open FCdot (Kind Sig BVar Rename Label)

/-! ## Types -/

/-- Types into DOT-MNF. -/
def Ty.toDot : Ty s → DotMNF.Ty s
  | .top => .top
  | .bot => .bot
  | .typ A S T => .typ A S.toDot T.toDot
  | .fld a T => .fld a T.toDot
  | .sel x A => .sel (.var x) A
  | .mu T => .mu T.toDot
  | .all S T => .all S.toDot T.toDot
  | .and S T => .and S.toDot T.toDot

/-- Types from DOT-MNF. -/
def Ty.ofDot : DotMNF.Ty s → Ty s
  | .top => .top
  | .bot => .bot
  | .typ A S T => .typ A (Ty.ofDot S) (Ty.ofDot T)
  | .fld a T => .fld a (Ty.ofDot T)
  | .sel (.var x) A => .sel x A
  | .mu T => .mu (Ty.ofDot T)
  | .all S T => .all (Ty.ofDot S) (Ty.ofDot T)
  | .and S T => .and (Ty.ofDot S) (Ty.ofDot T)

@[simp] theorem Ty.ofDot_toDot : ∀ {s : Sig} (T : Ty s), Ty.ofDot T.toDot = T
  | _, .top => rfl
  | _, .bot => rfl
  | _, .typ _ S T => by simp only [Ty.toDot, Ty.ofDot, Ty.ofDot_toDot S, Ty.ofDot_toDot T]
  | _, .fld _ T => by simp only [Ty.toDot, Ty.ofDot, Ty.ofDot_toDot T]
  | _, .sel _ _ => rfl
  | _, .mu T => by simp only [Ty.toDot, Ty.ofDot, Ty.ofDot_toDot T]
  | _, .all S T => by simp only [Ty.toDot, Ty.ofDot, Ty.ofDot_toDot S, Ty.ofDot_toDot T]
  | _, .and S T => by simp only [Ty.toDot, Ty.ofDot, Ty.ofDot_toDot S, Ty.ofDot_toDot T]

@[simp] theorem Ty.toDot_ofDot : ∀ {s : Sig} (T : DotMNF.Ty s), (Ty.ofDot T).toDot = T
  | _, .top => rfl
  | _, .bot => rfl
  | _, .typ _ S T => by simp only [Ty.toDot, Ty.ofDot, Ty.toDot_ofDot S, Ty.toDot_ofDot T]
  | _, .fld _ T => by simp only [Ty.toDot, Ty.ofDot, Ty.toDot_ofDot T]
  | _, .sel (.var _) _ => rfl
  | _, .mu T => by simp only [Ty.toDot, Ty.ofDot, Ty.toDot_ofDot T]
  | _, .all S T => by simp only [Ty.toDot, Ty.ofDot, Ty.toDot_ofDot S, Ty.toDot_ofDot T]
  | _, .and S T => by simp only [Ty.toDot, Ty.ofDot, Ty.toDot_ofDot S, Ty.toDot_ofDot T]

theorem Ty.toDot_rename : ∀ {s1 s2 : Sig} (T : Ty s1) (ρ : Rename s1 s2),
    (T.rename ρ).toDot = T.toDot.rename ρ
  | _, _, .top, _ => rfl
  | _, _, .bot, _ => rfl
  | _, _, .typ _ S T, ρ => by
      simp only [Ty.rename, Ty.toDot, DotMNF.Ty.rename, Ty.toDot_rename S, Ty.toDot_rename T]
  | _, _, .fld _ T, ρ => by
      simp only [Ty.rename, Ty.toDot, DotMNF.Ty.rename, Ty.toDot_rename T]
  | _, _, .sel _ _, _ => rfl
  | _, _, .mu T, ρ => by
      simp only [Ty.rename, Ty.toDot, DotMNF.Ty.rename, Ty.toDot_rename T]
  | _, _, .all S T, ρ => by
      simp only [Ty.rename, Ty.toDot, DotMNF.Ty.rename, Ty.toDot_rename S, Ty.toDot_rename T]
  | _, _, .and S T, ρ => by
      simp only [Ty.rename, Ty.toDot, DotMNF.Ty.rename, Ty.toDot_rename S, Ty.toDot_rename T]

theorem Ty.ofDot_rename {s1 s2 : Sig} (T : DotMNF.Ty s1) (ρ : Rename s1 s2) :
    Ty.ofDot (T.rename ρ) = (Ty.ofDot T).rename ρ := by
  rw [← Ty.ofDot_toDot ((Ty.ofDot T).rename ρ), Ty.toDot_rename, Ty.toDot_ofDot]

theorem Ty.toDot_weaken {k : Kind} (T : Ty s) :
    (T.weaken : Ty (s,,k)).toDot = T.toDot.weaken := Ty.toDot_rename T _

theorem Ty.ofDot_weaken {k : Kind} (T : DotMNF.Ty s) :
    (Ty.ofDot (T.weaken : DotMNF.Ty (s,,k))) = (Ty.ofDot T).weaken := Ty.ofDot_rename T _

theorem Ty.toDot_substVar {k : Kind} (T : Ty (s,,k)) (y : BVar s k) :
    (T.substVar y).toDot = T.toDot.substVar y := Ty.toDot_rename T _

theorem Ty.ofDot_substVar {k : Kind} (T : DotMNF.Ty (s,,k)) (y : BVar s k) :
    Ty.ofDot (T.substVar y) = (Ty.ofDot T).substVar y := Ty.ofDot_rename T _

/-! ## Contexts -/

/-- Contexts into DOT-MNF. -/
def Ctx.toDot : Ctx s → DotMNF.Ctx s
  | .nil => .nil
  | .cons Γ T => .cons Γ.toDot T.toDot

/-- Contexts from DOT-MNF. A self binder keeps its type `μ(x. T)` and forgets
the definitions. -/
def Ctx.ofDot : DotMNF.Ctx s → Ctx s
  | .nil => .nil
  | .cons Γ T => .cons (Ctx.ofDot Γ) (Ty.ofDot T)
  | .consSelf Γ _ T => .cons (Ctx.ofDot Γ) (.mu (Ty.ofDot T))

@[simp] theorem Ctx.ofDot_toDot : ∀ {s : Sig} (Γ : Ctx s), Ctx.ofDot Γ.toDot = Γ
  | _, .nil => rfl
  | _, .cons Γ T => by simp only [Ctx.toDot, Ctx.ofDot, Ctx.ofDot_toDot Γ, Ty.ofDot_toDot]

theorem Ctx.toDot_lookup : ∀ {s : Sig} (Γ : Ctx s) (x : BVar s .var),
    Γ.toDot.lookup x = (Γ.lookup x).toDot
  | _, .cons _ T, .here => (Ty.toDot_weaken T).symm
  | _, .cons Γ _, .there y => by
      change (Γ.toDot.lookup y).weaken = ((Γ.lookup y).weaken).toDot
      rw [Ctx.toDot_lookup Γ y, Ty.toDot_weaken]

theorem Ctx.ofDot_lookup : ∀ {s : Sig} (Γ : DotMNF.Ctx s) (x : BVar s .var),
    (Ctx.ofDot Γ).lookup x = Ty.ofDot (Γ.lookup x)
  | _, .cons _ T, .here => (Ty.ofDot_weaken T).symm
  | _, .cons Γ _, .there y => by
      change ((Ctx.ofDot Γ).lookup y).weaken = Ty.ofDot ((Γ.lookup y).weaken)
      rw [Ctx.ofDot_lookup Γ y, Ty.ofDot_weaken]
  | _, .consSelf _ _ T, .here => (Ty.ofDot_weaken (.mu T)).symm
  | _, .consSelf Γ _ _, .there y => by
      change ((Ctx.ofDot Γ).lookup y).weaken = Ty.ofDot ((Γ.lookup y).weaken)
      rw [Ctx.ofDot_lookup Γ y, Ty.ofDot_weaken]

/-- The round trip through `SelDot` changes a context only in the definitions
it records, so it preserves lookup. -/
theorem Ctx.toDot_ofDot_lookup {s : Sig} (Γ : DotMNF.Ctx s) (x : BVar s .var) :
    (Ctx.ofDot Γ).toDot.lookup x = Γ.lookup x := by
  rw [Ctx.toDot_lookup, Ctx.ofDot_lookup, Ty.toDot_ofDot]

/-! ## Terms -/

mutual

/-- Terms into DOT-MNF: every cast is removed and every path is replaced by
its root. -/
def Tm.toDot : Tm s → DotMNF.Tm s
  | .path p => .path (.var p.root)
  | .val v => .val v.toDot
  | .app p q => .app p.root q.root
  | .proj p a => .proj p.root a
  | .let t u => .let t.toDot u.toDot
  | .cast t _ => t.toDot

def Value.toDot : Value s → DotMNF.Value s
  | .obj d => .obj d.toDot
  | .lam S t => .lam S.toDot t.toDot

def Defs.toDot : Defs s → DotMNF.Defs s
  | .typ A T => .typ A T.toDot
  | .trm a t => .trm a t.toDot
  | .and d1 d2 => .and d1.toDot d2.toDot

end

mutual

/-- Terms from DOT-MNF: cast-free, with variable paths. -/
def Tm.ofDot : DotMNF.Tm s → Tm s
  | .path (.var x) => .path (.var x)
  | .val v => .val (Value.ofDot v)
  | .app x y => .app (.var x) (.var y)
  | .proj x a => .proj (.var x) a
  | .let t u => .let (Tm.ofDot t) (Tm.ofDot u)

def Value.ofDot : DotMNF.Value s → Value s
  | .obj d => .obj (Defs.ofDot d)
  | .lam S t => .lam (Ty.ofDot S) (Tm.ofDot t)

def Defs.ofDot : DotMNF.Defs s → Defs s
  | .typ A T => .typ A (Ty.ofDot T)
  | .trm a t => .trm a (Tm.ofDot t)
  | .and d1 d2 => .and (Defs.ofDot d1) (Defs.ofDot d2)

end

mutual

@[simp] theorem Tm.toDot_ofDot : ∀ {s : Sig} (t : DotMNF.Tm s), (Tm.ofDot t).toDot = t
  | _, .path (.var _) => rfl
  | _, .val v => by simp only [Tm.ofDot, Tm.toDot, Value.toDot_ofDot v]
  | _, .app _ _ => rfl
  | _, .proj _ _ => rfl
  | _, .let t u => by simp only [Tm.ofDot, Tm.toDot, Tm.toDot_ofDot t, Tm.toDot_ofDot u]

@[simp] theorem Value.toDot_ofDot : ∀ {s : Sig} (v : DotMNF.Value s), (Value.ofDot v).toDot = v
  | _, .obj d => by simp only [Value.ofDot, Value.toDot, Defs.toDot_ofDot d]
  | _, .lam S t => by simp only [Value.ofDot, Value.toDot, Ty.toDot_ofDot, Tm.toDot_ofDot t]

@[simp] theorem Defs.toDot_ofDot : ∀ {s : Sig} (d : DotMNF.Defs s), (Defs.ofDot d).toDot = d
  | _, .typ _ _ => by simp only [Defs.ofDot, Defs.toDot, Ty.toDot_ofDot]
  | _, .trm _ t => by simp only [Defs.ofDot, Defs.toDot, Tm.toDot_ofDot t]
  | _, .and d1 d2 => by simp only [Defs.ofDot, Defs.toDot, Defs.toDot_ofDot d1, Defs.toDot_ofDot d2]

end

mutual

@[simp] theorem Tm.toDot_erase : ∀ {s : Sig} (t : Tm s), t.erase.toDot = t.toDot
  | _, .path _ => rfl
  | _, .val v => by simp only [Tm.erase, Tm.toDot, Value.toDot_erase v]
  | _, .app _ _ => rfl
  | _, .proj _ _ => rfl
  | _, .let t u => by simp only [Tm.erase, Tm.toDot, Tm.toDot_erase t, Tm.toDot_erase u]
  | _, .cast t _ => by simp only [Tm.erase, Tm.toDot, Tm.toDot_erase t]

@[simp] theorem Value.toDot_erase : ∀ {s : Sig} (v : Value s), v.erase.toDot = v.toDot
  | _, .obj d => by simp only [Value.erase, Value.toDot, Defs.toDot_erase d]
  | _, .lam _ t => by simp only [Value.erase, Value.toDot, Tm.toDot_erase t]

@[simp] theorem Defs.toDot_erase : ∀ {s : Sig} (d : Defs s), d.erase.toDot = d.toDot
  | _, .typ _ _ => rfl
  | _, .trm _ t => by simp only [Defs.erase, Defs.toDot, Tm.toDot_erase t]
  | _, .and d1 d2 => by simp only [Defs.erase, Defs.toDot, Defs.toDot_erase d1, Defs.toDot_erase d2]

end

mutual

theorem Tm.ofDot_toDot : ∀ {s : Sig} (t : Tm s), Tm.ofDot t.toDot = t.erase
  | _, .path _ => rfl
  | _, .val v => by simp only [Tm.toDot, Tm.ofDot, Tm.erase, Value.ofDot_toDot v]
  | _, .app _ _ => rfl
  | _, .proj _ _ => rfl
  | _, .let t u => by simp only [Tm.toDot, Tm.ofDot, Tm.erase, Tm.ofDot_toDot t, Tm.ofDot_toDot u]
  | _, .cast t _ => by simp only [Tm.toDot, Tm.erase, Tm.ofDot_toDot t]

theorem Value.ofDot_toDot : ∀ {s : Sig} (v : Value s), Value.ofDot v.toDot = v.erase
  | _, .obj d => by simp only [Value.toDot, Value.ofDot, Value.erase, Defs.ofDot_toDot d]
  | _, .lam _ t => by
      simp only [Value.toDot, Value.ofDot, Value.erase, Ty.ofDot_toDot, Tm.ofDot_toDot t]

theorem Defs.ofDot_toDot : ∀ {s : Sig} (d : Defs s), Defs.ofDot d.toDot = d.erase
  | _, .typ _ _ => by simp only [Defs.toDot, Defs.ofDot, Defs.erase, Ty.ofDot_toDot]
  | _, .trm _ t => by simp only [Defs.toDot, Defs.ofDot, Defs.erase, Tm.ofDot_toDot t]
  | _, .and d1 d2 => by
      simp only [Defs.toDot, Defs.ofDot, Defs.erase, Defs.ofDot_toDot d1, Defs.ofDot_toDot d2]

end

/-- A term from DOT-MNF has no casts. -/
theorem Tm.erase_ofDot {s : Sig} (t : DotMNF.Tm s) : (Tm.ofDot t).erase = Tm.ofDot t := by
  rw [← Tm.ofDot_toDot, Tm.toDot_ofDot]

theorem Defs.erase_ofDot {s : Sig} (d : DotMNF.Defs s) : (Defs.ofDot d).erase = Defs.ofDot d := by
  rw [← Defs.ofDot_toDot, Defs.toDot_ofDot]

/-! ## Labels and distinctness -/

@[simp] theorem Defs.labels_toDot : ∀ {s : Sig} (d : Defs s), d.toDot.labels = d.labels
  | _, .typ _ _ => rfl
  | _, .trm _ _ => rfl
  | _, .and d1 d2 => by
      simp only [Defs.toDot, DotMNF.Defs.labels, Defs.labels, Defs.labels_toDot d1,
        Defs.labels_toDot d2]

@[simp] theorem Defs.labels_ofDot : ∀ {s : Sig} (d : DotMNF.Defs s), (Defs.ofDot d).labels = d.labels
  | _, .typ _ _ => rfl
  | _, .trm _ _ => rfl
  | _, .and d1 d2 => by
      simp only [Defs.ofDot, DotMNF.Defs.labels, Defs.labels, Defs.labels_ofDot d1,
        Defs.labels_ofDot d2]

theorem Defs.Distinct.toDot {d : Defs s} (h : d.Distinct) : d.toDot.Distinct := by
  induction h with
  | typ => exact .typ
  | trm => exact .trm
  | and _ _ hd ih1 ih2 =>
      exact .and ih1 ih2 (by simpa only [Defs.labels_toDot] using hd)

theorem Defs.Distinct.ofDot {d : DotMNF.Defs s} (h : d.Distinct) : (Defs.ofDot d).Distinct := by
  induction h with
  | typ => exact .typ
  | trm => exact .trm
  | and _ _ hd ih1 ih2 =>
      exact .and ih1 ih2 (by simpa only [Defs.labels_ofDot] using hd)

namespace Vanilla

/-- Erasure keeps the labels. -/
theorem labels_erase : ∀ {s : Sig} (d : Defs s), d.erase.labels = d.labels
  | _, .typ _ _ => rfl
  | _, .trm _ _ => rfl
  | _, .and d1 d2 => by
      simp only [Defs.erase, Defs.labels, labels_erase d1, labels_erase d2]

/-- Distinctness is read off the erasure. -/
theorem distinct_of_erase : ∀ {s : Sig} {d : Defs s}, d.erase.Distinct → d.Distinct
  | _, .typ _ _, _ => .typ
  | _, .trm _ _, _ => .trm
  | _, .and d1 d2, h => by
      cases h with
      | and h1 h2 hd =>
          exact .and (distinct_of_erase h1) (distinct_of_erase h2)
            (by simpa only [labels_erase] using hd)

/-! ## Renaming by the identity in DOT-MNF -/

mutual

theorem dotTm_rename_id : ∀ {s : Sig} (t : DotMNF.Tm s), t.rename Rename.id = t
  | _, .path _ => by simp only [DotMNF.Tm.rename, DotMNF.Path.rename_id]
  | _, .val v => by simp only [DotMNF.Tm.rename, dotValue_rename_id v]
  | _, .app _ _ => rfl
  | _, .proj _ _ => rfl
  | _, .let t u => by
      simp only [DotMNF.Tm.rename, Rename.lift_id, dotTm_rename_id t, dotTm_rename_id u]

theorem dotValue_rename_id : ∀ {s : Sig} (v : DotMNF.Value s), v.rename Rename.id = v
  | _, .obj d => by simp only [DotMNF.Value.rename, Rename.lift_id, dotDefs_rename_id d]
  | _, .lam _ t => by
      simp only [DotMNF.Value.rename, Rename.lift_id, DotMNF.Ty.rename_id, dotTm_rename_id t]

theorem dotDefs_rename_id : ∀ {s : Sig} (d : DotMNF.Defs s), d.rename Rename.id = d
  | _, .typ _ _ => by simp only [DotMNF.Defs.rename, DotMNF.Ty.rename_id]
  | _, .trm _ t => by simp only [DotMNF.Defs.rename, dotTm_rename_id t]
  | _, .and d1 d2 => by
      simp only [DotMNF.Defs.rename, dotDefs_rename_id d1, dotDefs_rename_id d2]

end

/-- Source derivations transfer between contexts with the same lookup. -/
def subTransfer {Γ Δ : DotMNF.Ctx s} (h : ∀ x, Δ.lookup x = Γ.lookup x)
    {S T : DotMNF.Ty s} (d : DotMNF.Sub Γ S T) : DotMNF.Sub Δ S T := by
  have d' := d.rename Rename.id (fun x => by rw [DotMNF.Ty.rename_id]; exact h x)
  rwa [DotMNF.Ty.rename_id, DotMNF.Ty.rename_id] at d'

def hasTyTransfer {Γ Δ : DotMNF.Ctx s} (h : ∀ x, Δ.lookup x = Γ.lookup x)
    {t : DotMNF.Tm s} {T : DotMNF.Ty s} (d : DotMNF.HasTy Γ t T) : DotMNF.HasTy Δ t T := by
  have d' := d.rename Rename.id (fun x => by rw [DotMNF.Ty.rename_id]; exact h x)
  rwa [DotMNF.Ty.rename_id, dotTm_rename_id] at d'

def defsTyTransfer {Γ Δ : DotMNF.Ctx s} (h : ∀ x, Δ.lookup x = Γ.lookup x)
    {d : DotMNF.Defs s} {T : DotMNF.Ty s} (D : DotMNF.DefsTy Γ d T) : DotMNF.DefsTy Δ d T := by
  have d' := D.rename Rename.id (fun x => by rw [DotMNF.Ty.rename_id]; exact h x)
  rwa [DotMNF.Ty.rename_id, dotDefs_rename_id] at d'

end Vanilla

end SelDot
