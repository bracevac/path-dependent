import Coercions.Selective.Dot.Typing
import Coercions.Selective.Dot.RenameTy

/-!
# Selective DOT: renaming

The equations of renaming and erasure on paths, endpoints, certificates and
terms, and the exact renaming of every judgment along a renaming that
preserves the types of variables. Weakening and the substitution of a variable
by a variable of the same type are instances.
-/

namespace SelDot

open FCdot (Kind Sig BVar Rename Label)

/-! ## Paths, endpoints, certificates -/

mutual

@[simp] theorem Path.rename_id : ∀ {s : Sig} (p : Path s), p.rename Rename.id = p
  | _, .var _ => rfl
  | _, .cast p c => by
      simp only [Path.rename, Path.rename_id p, Cert.rename_id c]

@[simp] theorem ATy.rename_id : ∀ {s : Sig} (S : ATy s), S.rename Rename.id = S
  | _, .top => rfl
  | _, .bot => rfl
  | _, .typ _ S T => by simp only [ATy.rename, ATy.rename_id S, ATy.rename_id T]
  | _, .fld _ T => by simp only [ATy.rename, ATy.rename_id T]
  | _, .sel p _ => by simp only [ATy.rename, Path.rename_id p]
  | _, .mu T => by simp only [ATy.rename, Rename.lift_id, ATy.rename_id T]
  | _, .all S T => by
      simp only [ATy.rename, Rename.lift_id, ATy.rename_id S, ATy.rename_id T]
  | _, .and S T => by simp only [ATy.rename, ATy.rename_id S, ATy.rename_id T]

@[simp] theorem Cert.rename_id : ∀ {s : Sig} (c : Cert s), c.rename Rename.id = c
  | _, .step S T => by simp only [Cert.rename, ATy.rename_id S, ATy.rename_id T]
  | _, .seq c d => by simp only [Cert.rename, Cert.rename_id c, Cert.rename_id d]

end

mutual

theorem Path.rename_comp : ∀ {s1 s2 s3 : Sig} (p : Path s1) (ρ : Rename s1 s2)
    (τ : Rename s2 s3), (p.rename ρ).rename τ = p.rename (ρ.comp τ)
  | _, _, _, .var _, _, _ => rfl
  | _, _, _, .cast p c, ρ, τ => by
      simp only [Path.rename, Path.rename_comp p ρ τ, Cert.rename_comp c ρ τ]

theorem ATy.rename_comp : ∀ {s1 s2 s3 : Sig} (S : ATy s1) (ρ : Rename s1 s2)
    (τ : Rename s2 s3), (S.rename ρ).rename τ = S.rename (ρ.comp τ)
  | _, _, _, .top, _, _ => rfl
  | _, _, _, .bot, _, _ => rfl
  | _, _, _, .typ _ S T, ρ, τ => by
      simp only [ATy.rename, ATy.rename_comp S ρ τ, ATy.rename_comp T ρ τ]
  | _, _, _, .fld _ T, ρ, τ => by simp only [ATy.rename, ATy.rename_comp T ρ τ]
  | _, _, _, .sel p _, ρ, τ => by simp only [ATy.rename, Path.rename_comp p ρ τ]
  | _, _, _, .mu T, ρ, τ => by
      simp only [ATy.rename, ATy.rename_comp T ρ.lift τ.lift, Rename.lift_comp]
  | _, _, _, .all S T, ρ, τ => by
      simp only [ATy.rename, ATy.rename_comp S ρ τ, ATy.rename_comp T ρ.lift τ.lift,
        Rename.lift_comp]
  | _, _, _, .and S T, ρ, τ => by
      simp only [ATy.rename, ATy.rename_comp S ρ τ, ATy.rename_comp T ρ τ]

theorem Cert.rename_comp : ∀ {s1 s2 s3 : Sig} (c : Cert s1) (ρ : Rename s1 s2)
    (τ : Rename s2 s3), (c.rename ρ).rename τ = c.rename (ρ.comp τ)
  | _, _, _, .step S T, ρ, τ => by
      simp only [Cert.rename, ATy.rename_comp S ρ τ, ATy.rename_comp T ρ τ]
  | _, _, _, .seq c d, ρ, τ => by
      simp only [Cert.rename, Cert.rename_comp c ρ τ, Cert.rename_comp d ρ τ]

end

/-- The root of a renamed path is the renamed root. -/
@[simp] theorem Path.root_rename : ∀ {s1 s2 : Sig} (p : Path s1) (ρ : Rename s1 s2),
    (p.rename ρ).root = ρ.var p.root
  | _, _, .var _, _ => rfl
  | _, _, .cast p _, ρ => Path.root_rename p ρ

/-- Erasure commutes with renaming. -/
theorem ATy.erase_rename : ∀ {s1 s2 : Sig} (S : ATy s1) (ρ : Rename s1 s2),
    (S.rename ρ).erase = S.erase.rename ρ
  | _, _, .top, _ => rfl
  | _, _, .bot, _ => rfl
  | _, _, .typ _ S T, ρ => by
      simp only [ATy.rename, ATy.erase, Ty.rename, ATy.erase_rename S ρ, ATy.erase_rename T ρ]
  | _, _, .fld _ T, ρ => by simp only [ATy.rename, ATy.erase, Ty.rename, ATy.erase_rename T ρ]
  | _, _, .sel p _, ρ => by simp only [ATy.rename, ATy.erase, Ty.rename, Path.root_rename]
  | _, _, .mu T, ρ => by simp only [ATy.rename, ATy.erase, Ty.rename, ATy.erase_rename T ρ.lift]
  | _, _, .all S T, ρ => by
      simp only [ATy.rename, ATy.erase, Ty.rename, ATy.erase_rename S ρ,
        ATy.erase_rename T ρ.lift]
  | _, _, .and S T, ρ => by
      simp only [ATy.rename, ATy.erase, Ty.rename, ATy.erase_rename S ρ, ATy.erase_rename T ρ]

/-- Embedding commutes with renaming. -/
theorem Ty.embed_rename (T : Ty s1) (ρ : Rename s1 s2) :
    (T.rename ρ).embed = T.embed.rename ρ := by
  induction T generalizing s2 with
  | top | bot => rfl
  | typ _ _ _ ih1 ih2 => simp [Ty.rename, Ty.embed, ATy.rename, ih1, ih2]
  | fld _ _ ih => simp [Ty.rename, Ty.embed, ATy.rename, ih]
  | sel => simp [Ty.rename, Ty.embed, ATy.rename, Path.rename]
  | mu _ ih => simp [Ty.rename, Ty.embed, ATy.rename, ih]
  | all _ _ ih1 ih2 => simp [Ty.rename, Ty.embed, ATy.rename, ih1, ih2]
  | and _ _ ih1 ih2 => simp [Ty.rename, Ty.embed, ATy.rename, ih1, ih2]

/-- Erasure undoes embedding. -/
@[simp] theorem Ty.erase_embed (T : Ty s) : T.embed.erase = T := by
  induction T with
  | top | bot => rfl
  | typ _ _ _ ih1 ih2 => simp [Ty.embed, ATy.erase, ih1, ih2]
  | fld _ _ ih => simp [Ty.embed, ATy.erase, ih]
  | sel => rfl
  | mu _ ih => simp [Ty.embed, ATy.erase, ih]
  | all _ _ ih1 ih2 => simp [Ty.embed, ATy.erase, ih1, ih2]
  | and _ _ ih1 ih2 => simp [Ty.embed, ATy.erase, ih1, ih2]

/-! ## Terms -/

mutual

@[simp] theorem Tm.rename_id : ∀ {s : Sig} (t : Tm s), t.rename Rename.id = t
  | _, .path p => by simp only [Tm.rename, Path.rename_id]
  | _, .val v => by simp only [Tm.rename, Value.rename_id v]
  | _, .app p q => by simp only [Tm.rename, Path.rename_id]
  | _, .proj p a => by simp only [Tm.rename, Path.rename_id]
  | _, .let t u => by simp only [Tm.rename, Rename.lift_id, Tm.rename_id t, Tm.rename_id u]
  | _, .cast t c => by simp only [Tm.rename, Cert.rename_id, Tm.rename_id t]

@[simp] theorem Value.rename_id : ∀ {s : Sig} (v : Value s), v.rename Rename.id = v
  | _, .obj d => by simp only [Value.rename, Rename.lift_id, Defs.rename_id d]
  | _, .lam S t => by simp only [Value.rename, Rename.lift_id, Ty.rename_id, Tm.rename_id t]

@[simp] theorem Defs.rename_id : ∀ {s : Sig} (d : Defs s), d.rename Rename.id = d
  | _, .typ _ T => by simp only [Defs.rename, Ty.rename_id]
  | _, .trm _ t => by simp only [Defs.rename, Tm.rename_id t]
  | _, .and d1 d2 => by simp only [Defs.rename, Defs.rename_id d1, Defs.rename_id d2]

end

mutual

theorem Tm.rename_comp : ∀ {s1 s2 s3 : Sig} (t : Tm s1) (ρ : Rename s1 s2)
    (τ : Rename s2 s3), (t.rename ρ).rename τ = t.rename (ρ.comp τ)
  | _, _, _, .path p, ρ, τ => by simp only [Tm.rename, Path.rename_comp]
  | _, _, _, .val v, ρ, τ => by simp only [Tm.rename, Value.rename_comp v ρ τ]
  | _, _, _, .app p q, ρ, τ => by simp only [Tm.rename, Path.rename_comp]
  | _, _, _, .proj p a, ρ, τ => by simp only [Tm.rename, Path.rename_comp]
  | _, _, _, .let t u, ρ, τ => by
      simp only [Tm.rename, Tm.rename_comp t ρ τ, Tm.rename_comp u ρ.lift τ.lift,
        Rename.lift_comp]
  | _, _, _, .cast t c, ρ, τ => by
      simp only [Tm.rename, Tm.rename_comp t ρ τ, Cert.rename_comp]

theorem Value.rename_comp : ∀ {s1 s2 s3 : Sig} (v : Value s1) (ρ : Rename s1 s2)
    (τ : Rename s2 s3), (v.rename ρ).rename τ = v.rename (ρ.comp τ)
  | _, _, _, .obj d, ρ, τ => by
      simp only [Value.rename, Defs.rename_comp d ρ.lift τ.lift, Rename.lift_comp]
  | _, _, _, .lam S t, ρ, τ => by
      simp only [Value.rename, Ty.rename_comp, Tm.rename_comp t ρ.lift τ.lift,
        Rename.lift_comp]

theorem Defs.rename_comp : ∀ {s1 s2 s3 : Sig} (d : Defs s1) (ρ : Rename s1 s2)
    (τ : Rename s2 s3), (d.rename ρ).rename τ = d.rename (ρ.comp τ)
  | _, _, _, .typ _ T, ρ, τ => by simp only [Defs.rename, Ty.rename_comp]
  | _, _, _, .trm _ t, ρ, τ => by simp only [Defs.rename, Tm.rename_comp t ρ τ]
  | _, _, _, .and d1 d2, ρ, τ => by
      simp only [Defs.rename, Defs.rename_comp d1 ρ τ, Defs.rename_comp d2 ρ τ]

end

mutual

/-- Erasure commutes with renaming. -/
theorem Tm.erase_rename : ∀ {s1 s2 : Sig} (t : Tm s1) (ρ : Rename s1 s2),
    (t.rename ρ).erase = t.erase.rename ρ
  | _, _, .path p, ρ => by simp only [Tm.rename, Tm.erase, Path.root_rename, Path.rename]
  | _, _, .val v, ρ => by simp only [Tm.rename, Tm.erase, Value.erase_rename v ρ]
  | _, _, .app p q, ρ => by simp only [Tm.rename, Tm.erase, Path.root_rename, Path.rename]
  | _, _, .proj p a, ρ => by simp only [Tm.rename, Tm.erase, Path.root_rename, Path.rename]
  | _, _, .let t u, ρ => by
      simp only [Tm.rename, Tm.erase, Tm.erase_rename t ρ, Tm.erase_rename u ρ.lift]
  | _, _, .cast t c, ρ => by simp only [Tm.rename, Tm.erase, Tm.erase_rename t ρ]

theorem Value.erase_rename : ∀ {s1 s2 : Sig} (v : Value s1) (ρ : Rename s1 s2),
    (v.rename ρ).erase = v.erase.rename ρ
  | _, _, .obj d, ρ => by simp only [Value.rename, Value.erase, Defs.erase_rename d ρ.lift]
  | _, _, .lam S t, ρ => by simp only [Value.rename, Value.erase, Tm.erase_rename t ρ.lift]

theorem Defs.erase_rename : ∀ {s1 s2 : Sig} (d : Defs s1) (ρ : Rename s1 s2),
    (d.rename ρ).erase = d.erase.rename ρ
  | _, _, .typ _ T, ρ => rfl
  | _, _, .trm _ t, ρ => by simp only [Defs.rename, Defs.erase, Tm.erase_rename t ρ]
  | _, _, .and d1 d2, ρ => by
      simp only [Defs.rename, Defs.erase, Defs.erase_rename d1 ρ, Defs.erase_rename d2 ρ]

end

mutual

/-- Erasure is idempotent. -/
@[simp] theorem Tm.erase_erase : ∀ {s : Sig} (t : Tm s), t.erase.erase = t.erase
  | _, .path p => rfl
  | _, .val v => by simp only [Tm.erase, Value.erase_erase v]
  | _, .app p q => rfl
  | _, .proj p a => rfl
  | _, .let t u => by simp only [Tm.erase, Tm.erase_erase t, Tm.erase_erase u]
  | _, .cast t c => by simp only [Tm.erase, Tm.erase_erase t]

@[simp] theorem Value.erase_erase : ∀ {s : Sig} (v : Value s), v.erase.erase = v.erase
  | _, .obj d => by simp only [Value.erase, Defs.erase_erase d]
  | _, .lam S t => by simp only [Value.erase, Tm.erase_erase t]

@[simp] theorem Defs.erase_erase : ∀ {s : Sig} (d : Defs s), d.erase.erase = d.erase
  | _, .typ _ T => rfl
  | _, .trm _ t => by simp only [Defs.erase, Tm.erase_erase t]
  | _, .and d1 d2 => by simp only [Defs.erase, Defs.erase_erase d1, Defs.erase_erase d2]

end

/-! ## Definitions: labels and lookup -/

@[simp] theorem Defs.labels_rename : ∀ {s1 s2 : Sig} (d : Defs s1) (ρ : Rename s1 s2),
    (d.rename ρ).labels = d.labels
  | _, _, .typ _ _, _ => rfl
  | _, _, .trm _ _, _ => rfl
  | _, _, .and d1 d2, ρ => by
      simp only [Defs.rename, Defs.labels, Defs.labels_rename d1 ρ, Defs.labels_rename d2 ρ]

@[simp] theorem Defs.labels_erase : ∀ {s : Sig} (d : Defs s), d.erase.labels = d.labels
  | _, .typ _ _ => rfl
  | _, .trm _ _ => rfl
  | _, .and d1 d2 => by
      simp only [Defs.erase, Defs.labels, Defs.labels_erase d1, Defs.labels_erase d2]

theorem Defs.Distinct.rename {d : Defs s1} (h : d.Distinct) (ρ : Rename s1 s2) :
    (d.rename ρ).Distinct := by
  induction h with
  | typ => exact .typ
  | trm => exact .trm
  | and _ _ hdis ih1 ih2 =>
      exact .and ih1 ih2 (by simpa only [Defs.labels_rename] using hdis)

theorem Defs.Distinct.erase {d : Defs s} (h : d.Distinct) : d.erase.Distinct := by
  induction h with
  | typ => exact .typ
  | trm => exact .trm
  | and _ _ hdis ih1 ih2 =>
      exact .and ih1 ih2 (by simpa only [Defs.labels_erase] using hdis)

theorem Defs.Distinct.of_erase : ∀ {s : Sig} {d : Defs s}, d.erase.Distinct → d.Distinct
  | _, .typ _ _, _ => .typ
  | _, .trm _ _, _ => .trm
  | _, .and d1 d2, h => by
      cases h with
      | and h1 h2 hdis =>
          exact .and (Defs.Distinct.of_erase h1) (Defs.Distinct.of_erase h2)
            (by simpa only [Defs.labels_erase] using hdis)

private theorem Option.or_map {α β : Type} (f : α → β) (x y : Option α) :
    (x.map f).or (y.map f) = (x.or y).map f := by
  cases x <;> cases y <;> rfl

theorem Defs.lookupTrm_rename : ∀ {s1 s2 : Sig} (d : Defs s1) (ρ : Rename s1 s2) (a : Label),
    (d.rename ρ).lookupTrm a = (d.lookupTrm a).map (·.rename ρ)
  | _, _, .typ _ _, _, _ => rfl
  | _, _, .trm b t, ρ, a => by
      simp only [Defs.rename, Defs.lookupTrm]
      split <;> rfl
  | _, _, .and d1 d2, ρ, a => by
      simp only [Defs.rename, Defs.lookupTrm, Defs.lookupTrm_rename d1 ρ a,
        Defs.lookupTrm_rename d2 ρ a, Option.or_map]

theorem Defs.lookupTrm_erase : ∀ {s : Sig} (d : Defs s) (a : Label),
    d.erase.lookupTrm a = (d.lookupTrm a).map Tm.erase
  | _, .typ _ _, _ => rfl
  | _, .trm b t, a => by
      simp only [Defs.erase, Defs.lookupTrm]
      split <;> rfl
  | _, .and d1 d2, a => by
      simp only [Defs.erase, Defs.lookupTrm, Defs.lookupTrm_erase d1 a,
        Defs.lookupTrm_erase d2 a, Option.or_map]

/-! ## Contexts -/

/-- `ρ` maps the context `Γ` into `Δ`: the type of each renamed variable is the
renamed type. -/
def Ctx.Renames (Γ : Ctx s1) (Δ : Ctx s2) (ρ : Rename s1 s2) : Prop :=
  ∀ y, Δ.lookup (ρ.var y) = (Γ.lookup y).rename ρ

theorem Ctx.Renames.cons {Γ : Ctx s1} {Δ : Ctx s2} {ρ : Rename s1 s2}
    (h : Γ.Renames Δ ρ) (S : Ty s1) : (Γ.cons S).Renames (Δ.cons (S.rename ρ)) ρ.lift := by
  intro y
  cases y with
  | here =>
      show (S.rename ρ).weaken = S.weaken.rename ρ.lift
      rw [Ty.weaken_rename]
  | there y =>
      show (Δ.lookup (ρ.var y)).weaken = (Γ.lookup y).weaken.rename ρ.lift
      rw [h y, Ty.weaken_rename]

theorem Ctx.Renames.succ {Γ : Ctx s} {S : Ty s} : Γ.Renames (Γ.cons S) Rename.succ :=
  fun _ => rfl

theorem Ctx.Renames.id {Γ : Ctx s} : Γ.Renames Γ Rename.id :=
  fun _ => (Ty.rename_id _).symm

/-- Substituting the newest binder by a variable of the same type. -/
theorem Ctx.Renames.subst {Γ : Ctx s} {x : BVar s .var} {T : Ty s}
    (hx : Γ.lookup x = T) : (Γ.cons T).Renames Γ (Rename.subst x) := by
  intro y
  cases y with
  | here =>
      show Γ.lookup x = T.weaken.substVar x
      rw [Ty.weaken_substVar, hx]
  | there y =>
      show Γ.lookup y = (Γ.lookup y).weaken.substVar x
      rw [Ty.weaken_substVar]

/-! ## Renaming of paths, endpoints, primitive subtyping, certificates -/

mutual

theorem PathTy.rename : ∀ {s1 s2 : Sig} {Γ : Ctx s1} {p : Path s1} {T : Ty s1}
    {Δ : Ctx s2} {ρ : Rename s1 s2},
    PathTy Γ p T → Γ.Renames Δ ρ → PathTy Δ (p.rename ρ) (T.rename ρ)
  | _, _, _, _, _, _, _, .var, h => by
      simp only [Path.rename]
      rw [← h]
      exact .var
  | _, _, _, _, _, _, _, .cast hp hc, h => .cast (PathTy.rename hp h) (CertTy.rename hc h)
  | _, _, _, _, _, _, _, .keep hp hc hq, h =>
      .keep (PathTy.rename hp h) (CertTy.rename hc h) (PathTy.rename hq h)
  | _, _, _, _, _, _, _, .recI hp, h => by
      have ih := PathTy.rename hp h
      simp only [Ty.substVar_rename, ← Path.root_rename] at ih
      exact .recI ih
  | _, _, _, _, _, _, _, .recE hp, h => by
      have ih := PathTy.rename hp h
      simp only [Ty.substVar_rename, ← Path.root_rename]
      exact .recE ih
  | _, _, _, _, _, _, _, .andI hp hq, h => .andI (PathTy.rename hp h) (PathTy.rename hq h)

theorem Wf.rename : ∀ {s1 s2 : Sig} {Γ : Ctx s1} {S : ATy s1}
    {Δ : Ctx s2} {ρ : Rename s1 s2},
    Wf Γ S → Γ.Renames Δ ρ → Wf Δ (S.rename ρ)
  | _, _, _, _, _, _, .top, _ => .top
  | _, _, _, _, _, _, .bot, _ => .bot
  | _, _, _, _, _, _, .typ hS hT, h => .typ (Wf.rename hS h) (Wf.rename hT h)
  | _, _, _, _, _, _, .fld hT, h => .fld (Wf.rename hT h)
  | _, _, _, _, _, _, .sel hp, h => .sel (PathTy.rename hp h)
  | _, _, _, _, _, _, .mu hT, h => by
      have ih := Wf.rename hT (h.cons _)
      simp only [Ty.rename, ← ATy.erase_rename] at ih
      exact .mu ih
  | _, _, _, _, _, _, .all hS hT, h => by
      have ih := Wf.rename hT (h.cons _)
      simp only [← ATy.erase_rename] at ih
      exact .all (Wf.rename hS h) ih
  | _, _, _, _, _, _, .and hS hT, h => .and (Wf.rename hS h) (Wf.rename hT h)

theorem Prim.rename : ∀ {s1 s2 : Sig} {Γ : Ctx s1} {S T : ATy s1}
    {Δ : Ctx s2} {ρ : Rename s1 s2},
    Prim Γ S T → Γ.Renames Δ ρ → Prim Δ (S.rename ρ) (T.rename ρ)
  | _, _, _, _, _, _, _, .top hS, h => .top (Wf.rename hS h)
  | _, _, _, _, _, _, _, .bot hT, h => .bot (Wf.rename hT h)
  | _, _, _, _, _, _, _, .refl hS hT e, h =>
      .refl (Wf.rename hS h) (Wf.rename hT h) (by rw [ATy.erase_rename, ATy.erase_rename, e])
  | _, _, _, _, _, _, _, .andL1 hS hT, h => .andL1 (Prim.rename hS h) (Wf.rename hT h)
  | _, _, _, _, _, _, _, .andL2 hS hT, h => .andL2 (Wf.rename hS h) (Prim.rename hT h)
  | _, _, _, _, _, _, _, .andR hT hU, h => .andR (Prim.rename hT h) (Prim.rename hU h)
  | _, _, _, _, _, _, _, .fld hT, h => .fld (Prim.rename hT h)
  | _, _, _, _, _, _, _, .typ hS hT, h => .typ (Prim.rename hS h) (Prim.rename hT h)
  | _, _, _, _, _, _, _, .all hS hT, h => by
      have ih := Prim.rename hT (h.cons _)
      simp only [← ATy.erase_rename] at ih
      exact .all (Prim.rename hS h) ih
  | _, _, _, _, _, _, _, .selU hp hT e, h =>
      .selU (PathTy.rename hp h) (Wf.rename hT h) (by rw [ATy.erase_rename, e])
  | _, _, _, _, _, _, _, .selL hp hS e, h =>
      .selL (PathTy.rename hp h) (Wf.rename hS h) (by rw [ATy.erase_rename, e])

theorem CertTy.rename : ∀ {s1 s2 : Sig} {Γ : Ctx s1} {c : Cert s1} {S T : Ty s1}
    {Δ : Ctx s2} {ρ : Rename s1 s2},
    CertTy Γ c S T → Γ.Renames Δ ρ → CertTy Δ (c.rename ρ) (S.rename ρ) (T.rename ρ)
  | _, _, _, _, _, _, _, _, .step hp, h => by
      have ih := CertTy.step (Prim.rename hp h)
      simp only [ATy.erase_rename] at ih
      exact ih
  | _, _, _, _, _, _, _, _, .seq hc hd, h => .seq (CertTy.rename hc h) (CertTy.rename hd h)

end

/-- The implicit comparison is preserved by renaming. -/
theorem Prim₀.rename {Γ : Ctx s1} {S T : Ty s1} {Δ : Ctx s2} {ρ : Rename s1 s2}
    (hp : Prim₀ Γ S T) (h : Γ.Renames Δ ρ) : Prim₀ Δ (S.rename ρ) (T.rename ρ) := by
  unfold Prim₀ at *
  rw [Ty.embed_rename, Ty.embed_rename]
  exact Prim.rename hp h

/-! ## Renaming of terms and definitions -/

mutual

theorem HasTy.rename : ∀ {s1 s2 : Sig} {Γ : Ctx s1} {t : Tm s1} {T : Ty s1}
    {Δ : Ctx s2} {ρ : Rename s1 s2},
    HasTy Γ t T → Γ.Renames Δ ρ → HasTy Δ (t.rename ρ) (T.rename ρ)
  | _, _, _, _, _, _, _, .path hp, h => .path (PathTy.rename hp h)
  | _, _, _, _, _, _, _, .lam ht, h => .lam (HasTy.rename ht (h.cons _))
  | _, _, _, _, _, _, _, .app hp hq hpr, h => by
      simp only [Ty.substVar_rename, ← Path.root_rename]
      exact .app (PathTy.rename hp h) (PathTy.rename hq h) (Prim₀.rename hpr h)
  | _, _, _, _, _, _, _, .obj hd hdis, h => .obj (DefsTy.rename hd (h.cons _)) (hdis.rename _)
  | _, _, _, _, _, _, _, .proj hp, h => .proj (PathTy.rename hp h)
  | _, _, _, _, _, _, _, .let ht hu, h => by
      have ih := HasTy.rename hu (h.cons _)
      simp only [Ty.weaken_rename] at ih
      exact .let (HasTy.rename ht h) ih
  | _, _, _, _, _, _, _, .cast ht hc, h => .cast (HasTy.rename ht h) (CertTy.rename hc h)

theorem DefsTy.rename : ∀ {s1 s2 : Sig} {Γ : Ctx s1} {d : Defs s1} {T : Ty s1}
    {Δ : Ctx s2} {ρ : Rename s1 s2},
    DefsTy Γ d T → Γ.Renames Δ ρ → DefsTy Δ (d.rename ρ) (T.rename ρ)
  | _, _, _, _, _, _, _, .typ, _ => .typ
  | _, _, _, _, _, _, _, .trm ht, h => .trm (HasTy.rename ht h)
  | _, _, _, _, _, _, _, .and hd1 hd2, h => .and (DefsTy.rename hd1 h) (DefsTy.rename hd2 h)

end

/-! ## Weakening and substitution of a variable -/

theorem PathTy.weaken {Γ : Ctx s} {p : Path s} {T : Ty s} (h : PathTy Γ p T) (S : Ty s) :
    PathTy (Γ.cons S) p.weaken T.weaken := h.rename .succ

theorem Wf.weaken {Γ : Ctx s} {T : ATy s} (h : Wf Γ T) (S : Ty s) :
    Wf (Γ.cons S) T.weaken := h.rename .succ

theorem Prim.weaken {Γ : Ctx s} {T U : ATy s} (h : Prim Γ T U) (S : Ty s) :
    Prim (Γ.cons S) T.weaken U.weaken := h.rename .succ

theorem CertTy.weaken {Γ : Ctx s} {c : Cert s} {T U : Ty s} (h : CertTy Γ c T U) (S : Ty s) :
    CertTy (Γ.cons S) c.weaken T.weaken U.weaken := h.rename .succ

theorem HasTy.weaken {Γ : Ctx s} {t : Tm s} {T : Ty s} (h : HasTy Γ t T) (S : Ty s) :
    HasTy (Γ.cons S) t.weaken T.weaken := h.rename .succ

/-- A derivation under a binder of type `T` instantiates at a variable `x` of
declared type `T`. -/
theorem HasTy.substVar_self {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {U : Ty (s,x)}
    {t : Tm (s,x)}
    (hx : Γ.lookup x = T) (h : HasTy (Γ.cons T) t U) : HasTy Γ (t.substVar x) (U.substVar x) :=
  h.rename (Ctx.Renames.subst hx)

theorem PathTy.substVar_self {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {U : Ty (s,x)}
    {p : Path (s,x)} (hx : Γ.lookup x = T) (h : PathTy (Γ.cons T) p U) :
    PathTy Γ (p.rename (Rename.subst x)) (U.substVar x) :=
  h.rename (Ctx.Renames.subst hx)

theorem CertTy.substVar_self {Γ : Ctx s} {x : BVar s .var} {T : Ty s} {U V : Ty (s,x)}
    {c : Cert (s,x)} (hx : Γ.lookup x = T) (h : CertTy (Γ.cons T) c U V) :
    CertTy Γ (c.rename (Rename.subst x)) (U.substVar x) (V.substVar x) :=
  h.rename (Ctx.Renames.subst hx)

end SelDot
