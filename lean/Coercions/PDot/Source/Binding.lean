import Coercions.PDot.Source.Syntax

/-!
# Binding: renaming, path substitution, weakening, opening at a path

For each family of the source, `rename` along a renaming, `subst` along a path substitution, `weaken`
past one new variable, and `substPath`, which instantiates `.here` by a path.  `substPath` keeps the
field suffix of every path rooted at `.here`, as Coq's `open_rec_path_p` does
(`Definitions.v:308-315`): `(z.a).substPath (y.b)` is `y.b.a`.

The laws are the tree's for `Path` (`Paths/FCdot/RenameLemmas.lean`,
`Paths/FCdot/TypingPathSubst.lean`), lifted to every family: `rename_id`, `rename_rename`,
`subst_ofRename`, `subst_subst`, `weaken_substPath`, `substPath_subst`.  Each is one structural
recursion over its mutual block.

The context lookup and the store read of plan S.1 weaken their result, so they are defined here,
after `Ty.weaken` and `Val.weaken`.
-/

namespace PDot.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Types and declarations -/

mutual
def Ty.rename : Ty s₁ → Rename s₁ s₂ → Ty s₂
  | .top, _ => .top
  | .bot, _ => .bot
  | .rcd D, ρ => .rcd (D.rename ρ)
  | .and T U, ρ => .and (T.rename ρ) (U.rename ρ)
  | .sel p A, ρ => .sel (p.rename ρ) A
  | .mu T, ρ => .mu (T.rename ρ.lift)                        -- under z of μ(z. T)
  | .all S T, ρ => .all (S.rename ρ) (T.rename ρ.lift)       -- under z of ∀(z : S) T
  | .sngl p, ρ => .sngl (p.rename ρ)
def Dec.rename : Dec s₁ → Rename s₁ s₂ → Dec s₂
  | .typ A S U, ρ => .typ A (S.rename ρ) (U.rename ρ)
  | .trm a T, ρ => .trm a (T.rename ρ)
end

mutual
def Ty.subst : Ty s₁ → PathSubst s₁ s₂ → Ty s₂
  | .top, _ => .top
  | .bot, _ => .bot
  | .rcd D, σ => .rcd (D.subst σ)
  | .and T U, σ => .and (T.subst σ) (U.subst σ)
  | .sel p A, σ => .sel (p.subst σ) A
  | .mu T, σ => .mu (T.subst σ.lift)                         -- under z of μ(z. T)
  | .all S T, σ => .all (S.subst σ) (T.subst σ.lift)        -- under z of ∀(z : S) T
  | .sngl p, σ => .sngl (p.subst σ)
def Dec.subst : Dec s₁ → PathSubst s₁ s₂ → Dec s₂
  | .typ A S U, σ => .typ A (S.subst σ) (U.subst σ)
  | .trm a T, σ => .trm a (T.subst σ)
end

/-- Weakening past one new variable, `T↑`. -/
def Ty.weaken (T : Ty s) : Ty (s,x) := T.rename Rename.succ
def Dec.weaken (D : Dec s) : Dec (s,x) := D.rename Rename.succ

/-- Instantiate `.here` by a path, `T⟨p⟩`, Coq's `open_typ_p` (`Definitions.v:363`). -/
def Ty.substPath (T : Ty (s,x)) (p : Path s) : Ty s := T.subst (PathSubst.one p)
def Dec.substPath (D : Dec (s,x)) (p : Path s) : Dec s := D.subst (PathSubst.one p)

/-! ## Terms, values, definitions -/

mutual
def Tm.rename : Tm s₁ → Rename s₁ s₂ → Tm s₂
  | .val v, ρ => .val (v.rename ρ)
  | .app p q, ρ => .app (p.rename ρ) (q.rename ρ)
  | .lett t u, ρ => .lett (t.rename ρ) (u.rename ρ.lift)    -- under z of let z = t in u
  | .path p, ρ => .path (p.rename ρ)
def Val.rename : Val s₁ → Rename s₁ s₂ → Val s₂
  | .new T ds, ρ => .new (T.rename ρ.lift) (ds.rename ρ.lift)  -- under z of ν(z : T) ds
  | .lam T t, ρ => .lam (T.rename ρ) (t.rename ρ.lift)        -- under z of λ(z : T) t
def Def.rename : Def s₁ → Rename s₁ s₂ → Def s₂
  | .typ A T, ρ => .typ A (T.rename ρ)
  | .trm a r, ρ => .trm a (r.rename ρ)
def Defs.rename : Defs s₁ → Rename s₁ s₂ → Defs s₂
  | .nil, _ => .nil
  | .cons ds d, ρ => .cons (ds.rename ρ) (d.rename ρ)
def Rhs.rename : Rhs s₁ → Rename s₁ s₂ → Rhs s₂
  | .defp p, ρ => .defp (p.rename ρ)
  | .defv v, ρ => .defv (v.rename ρ)
end

mutual
def Tm.subst : Tm s₁ → PathSubst s₁ s₂ → Tm s₂
  | .val v, σ => .val (v.subst σ)
  | .app p q, σ => .app (p.subst σ) (q.subst σ)
  | .lett t u, σ => .lett (t.subst σ) (u.subst σ.lift)     -- under z of let z = t in u
  | .path p, σ => .path (p.subst σ)
def Val.subst : Val s₁ → PathSubst s₁ s₂ → Val s₂
  | .new T ds, σ => .new (T.subst σ.lift) (ds.subst σ.lift)  -- under z of ν(z : T) ds
  | .lam T t, σ => .lam (T.subst σ) (t.subst σ.lift)         -- under z of λ(z : T) t
def Def.subst : Def s₁ → PathSubst s₁ s₂ → Def s₂
  | .typ A T, σ => .typ A (T.subst σ)
  | .trm a r, σ => .trm a (r.subst σ)
def Defs.subst : Defs s₁ → PathSubst s₁ s₂ → Defs s₂
  | .nil, _ => .nil
  | .cons ds d, σ => .cons (ds.subst σ) (d.subst σ)
def Rhs.subst : Rhs s₁ → PathSubst s₁ s₂ → Rhs s₂
  | .defp p, σ => .defp (p.subst σ)
  | .defv v, σ => .defv (v.subst σ)
end

def Tm.weaken (t : Tm s) : Tm (s,x) := t.rename Rename.succ
def Val.weaken (v : Val s) : Val (s,x) := v.rename Rename.succ
def Def.weaken (d : Def s) : Def (s,x) := d.rename Rename.succ
def Defs.weaken (ds : Defs s) : Defs (s,x) := ds.rename Rename.succ
def Rhs.weaken (r : Rhs s) : Rhs (s,x) := r.rename Rename.succ

/-- Coq's `open_trm_p`, `open_val_p`, `open_def_p`, `open_defs_p`, `open_defrhs_p`
(`Definitions.v:366-370`). -/
def Tm.substPath (t : Tm (s,x)) (p : Path s) : Tm s := t.subst (PathSubst.one p)
def Val.substPath (v : Val (s,x)) (p : Path s) : Val s := v.subst (PathSubst.one p)
def Def.substPath (d : Def (s,x)) (p : Path s) : Def s := d.subst (PathSubst.one p)
def Defs.substPath (ds : Defs (s,x)) (p : Path s) : Defs s := ds.subst (PathSubst.one p)
def Rhs.substPath (r : Rhs (s,x)) (p : Path s) : Rhs s := r.subst (PathSubst.one p)

/-! ## Weakening against opening -/

/-- Weakening, then instantiating `.here`, is the identity. -/
theorem PathSubst.ofRename_succ_comp_one (p : Path s) :
    (PathSubst.ofRename (Rename.succ (k := .var))).comp (PathSubst.one p)
      = PathSubst.ofRename Rename.id :=
  PathSubst.funext' (fun _ => rfl)

/-! ## Laws for types and declarations -/

mutual
theorem Ty.rename_id : ∀ (T : Ty s), T.rename Rename.id = T
  | .top => rfl
  | .bot => rfl
  | .rcd D => by simp only [Ty.rename, Dec.rename_id D]
  | .and T U => by simp only [Ty.rename, Ty.rename_id T, Ty.rename_id U]
  | .sel p A => by simp only [Ty.rename, Path.rename_id]
  | .mu T => by simp only [Ty.rename, Rename.lift_id, Ty.rename_id T]
  | .all S T => by simp only [Ty.rename, Rename.lift_id, Ty.rename_id S, Ty.rename_id T]
  | .sngl p => by simp only [Ty.rename, Path.rename_id]
theorem Dec.rename_id : ∀ (D : Dec s), D.rename Rename.id = D
  | .typ A S U => by simp only [Dec.rename, Ty.rename_id S, Ty.rename_id U]
  | .trm a T => by simp only [Dec.rename, Ty.rename_id T]
end

mutual
theorem Ty.rename_rename : ∀ (T : Ty s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (T.rename ρ).rename ρ' = T.rename (ρ.comp ρ')
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .rcd D, ρ, ρ' => by simp only [Ty.rename, Dec.rename_rename D ρ ρ']
  | .and T U, ρ, ρ' => by simp only [Ty.rename, Ty.rename_rename T ρ ρ', Ty.rename_rename U ρ ρ']
  | .sel p A, ρ, ρ' => by simp only [Ty.rename, Path.rename_comp]
  | .mu T, ρ, ρ' => by simp only [Ty.rename, Ty.rename_rename T ρ.lift ρ'.lift, Rename.lift_comp]
  | .all S T, ρ, ρ' => by
      simp only [Ty.rename, Ty.rename_rename S ρ ρ', Ty.rename_rename T ρ.lift ρ'.lift,
        Rename.lift_comp]
  | .sngl p, ρ, ρ' => by simp only [Ty.rename, Path.rename_comp]
theorem Dec.rename_rename : ∀ (D : Dec s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (D.rename ρ).rename ρ' = D.rename (ρ.comp ρ')
  | .typ A S U, ρ, ρ' => by
      simp only [Dec.rename, Ty.rename_rename S ρ ρ', Ty.rename_rename U ρ ρ']
  | .trm a T, ρ, ρ' => by simp only [Dec.rename, Ty.rename_rename T ρ ρ']
end

mutual
theorem Ty.subst_ofRename : ∀ (T : Ty s₁) (ρ : Rename s₁ s₂),
    T.subst (PathSubst.ofRename ρ) = T.rename ρ
  | .top, _ => rfl
  | .bot, _ => rfl
  | .rcd D, ρ => by simp only [Ty.subst, Ty.rename, Dec.subst_ofRename D ρ]
  | .and T U, ρ => by
      simp only [Ty.subst, Ty.rename, Ty.subst_ofRename T ρ, Ty.subst_ofRename U ρ]
  | .sel p A, ρ => by simp only [Ty.subst, Ty.rename, Path.subst_ofRename]
  | .mu T, ρ => by
      simp only [Ty.subst, Ty.rename, PathSubst.lift_ofRename, Ty.subst_ofRename T ρ.lift]
  | .all S T, ρ => by
      simp only [Ty.subst, Ty.rename, PathSubst.lift_ofRename, Ty.subst_ofRename S ρ,
        Ty.subst_ofRename T ρ.lift]
  | .sngl p, ρ => by simp only [Ty.subst, Ty.rename, Path.subst_ofRename]
theorem Dec.subst_ofRename : ∀ (D : Dec s₁) (ρ : Rename s₁ s₂),
    D.subst (PathSubst.ofRename ρ) = D.rename ρ
  | .typ A S U, ρ => by
      simp only [Dec.subst, Dec.rename, Ty.subst_ofRename S ρ, Ty.subst_ofRename U ρ]
  | .trm a T, ρ => by simp only [Dec.subst, Dec.rename, Ty.subst_ofRename T ρ]
end

mutual
theorem Ty.subst_subst : ∀ (T : Ty s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (T.subst σ).subst τ = T.subst (σ.comp τ)
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .rcd D, σ, τ => by simp only [Ty.subst, Dec.subst_subst D σ τ]
  | .and T U, σ, τ => by simp only [Ty.subst, Ty.subst_subst T σ τ, Ty.subst_subst U σ τ]
  | .sel p A, σ, τ => by simp only [Ty.subst, Path.subst_subst]
  | .mu T, σ, τ => by
      simp only [Ty.subst, Ty.subst_subst T σ.lift τ.lift, PathSubst.comp_lift]
  | .all S T, σ, τ => by
      simp only [Ty.subst, Ty.subst_subst S σ τ, Ty.subst_subst T σ.lift τ.lift,
        PathSubst.comp_lift]
  | .sngl p, σ, τ => by simp only [Ty.subst, Path.subst_subst]
theorem Dec.subst_subst : ∀ (D : Dec s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (D.subst σ).subst τ = D.subst (σ.comp τ)
  | .typ A S U, σ, τ => by simp only [Dec.subst, Ty.subst_subst S σ τ, Ty.subst_subst U σ τ]
  | .trm a T, σ, τ => by simp only [Dec.subst, Ty.subst_subst T σ τ]
end

theorem Ty.weaken_substPath (X : Ty s) (p : Path s) : X.weaken.substPath p = X := by
  rw [Ty.weaken, ← Ty.subst_ofRename, Ty.substPath, Ty.subst_subst,
    PathSubst.ofRename_succ_comp_one, Ty.subst_ofRename, Ty.rename_id]

theorem Dec.weaken_substPath (X : Dec s) (p : Path s) : X.weaken.substPath p = X := by
  rw [Dec.weaken, ← Dec.subst_ofRename, Dec.substPath, Dec.subst_subst,
    PathSubst.ofRename_succ_comp_one, Dec.subst_ofRename, Dec.rename_id]

theorem Ty.substPath_subst (X : Ty (s₁,x)) (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (X.substPath q).subst σ = (X.subst σ.lift).substPath (q.subst σ) := by
  rw [Ty.substPath, Ty.substPath, Ty.subst_subst, Ty.subst_subst, PathSubst.one_comp]

theorem Dec.substPath_subst (X : Dec (s₁,x)) (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (X.substPath q).subst σ = (X.subst σ.lift).substPath (q.subst σ) := by
  rw [Dec.substPath, Dec.substPath, Dec.subst_subst, Dec.subst_subst, PathSubst.one_comp]

/-! ## Laws for terms, values, definitions -/

mutual
theorem Tm.rename_id : ∀ (t : Tm s), t.rename Rename.id = t
  | .val v => by simp only [Tm.rename, Val.rename_id v]
  | .app p q => by simp only [Tm.rename, Path.rename_id]
  | .lett t u => by simp only [Tm.rename, Rename.lift_id, Tm.rename_id t, Tm.rename_id u]
  | .path p => by simp only [Tm.rename, Path.rename_id]
theorem Val.rename_id : ∀ (v : Val s), v.rename Rename.id = v
  | .new T ds => by simp only [Val.rename, Rename.lift_id, Ty.rename_id T, Defs.rename_id ds]
  | .lam T t => by simp only [Val.rename, Rename.lift_id, Ty.rename_id T, Tm.rename_id t]
theorem Def.rename_id : ∀ (d : Def s), d.rename Rename.id = d
  | .typ A T => by simp only [Def.rename, Ty.rename_id T]
  | .trm a r => by simp only [Def.rename, Rhs.rename_id r]
theorem Defs.rename_id : ∀ (ds : Defs s), ds.rename Rename.id = ds
  | .nil => rfl
  | .cons ds d => by simp only [Defs.rename, Defs.rename_id ds, Def.rename_id d]
theorem Rhs.rename_id : ∀ (r : Rhs s), r.rename Rename.id = r
  | .defp p => by simp only [Rhs.rename, Path.rename_id]
  | .defv v => by simp only [Rhs.rename, Val.rename_id v]
end

mutual
theorem Tm.rename_rename : ∀ (t : Tm s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (t.rename ρ).rename ρ' = t.rename (ρ.comp ρ')
  | .val v, ρ, ρ' => by simp only [Tm.rename, Val.rename_rename v ρ ρ']
  | .app p q, ρ, ρ' => by simp only [Tm.rename, Path.rename_comp]
  | .lett t u, ρ, ρ' => by
      simp only [Tm.rename, Tm.rename_rename t ρ ρ', Tm.rename_rename u ρ.lift ρ'.lift,
        Rename.lift_comp]
  | .path p, ρ, ρ' => by simp only [Tm.rename, Path.rename_comp]
theorem Val.rename_rename : ∀ (v : Val s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (v.rename ρ).rename ρ' = v.rename (ρ.comp ρ')
  | .new T ds, ρ, ρ' => by
      simp only [Val.rename, Ty.rename_rename T ρ.lift ρ'.lift,
        Defs.rename_rename ds ρ.lift ρ'.lift, Rename.lift_comp]
  | .lam T t, ρ, ρ' => by
      simp only [Val.rename, Ty.rename_rename T ρ ρ', Tm.rename_rename t ρ.lift ρ'.lift,
        Rename.lift_comp]
theorem Def.rename_rename : ∀ (d : Def s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (d.rename ρ).rename ρ' = d.rename (ρ.comp ρ')
  | .typ A T, ρ, ρ' => by simp only [Def.rename, Ty.rename_rename T ρ ρ']
  | .trm a r, ρ, ρ' => by simp only [Def.rename, Rhs.rename_rename r ρ ρ']
theorem Defs.rename_rename : ∀ (ds : Defs s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (ds.rename ρ).rename ρ' = ds.rename (ρ.comp ρ')
  | .nil, _, _ => rfl
  | .cons ds d, ρ, ρ' => by
      simp only [Defs.rename, Defs.rename_rename ds ρ ρ', Def.rename_rename d ρ ρ']
theorem Rhs.rename_rename : ∀ (r : Rhs s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (r.rename ρ).rename ρ' = r.rename (ρ.comp ρ')
  | .defp p, ρ, ρ' => by simp only [Rhs.rename, Path.rename_comp]
  | .defv v, ρ, ρ' => by simp only [Rhs.rename, Val.rename_rename v ρ ρ']
end

mutual
theorem Tm.subst_ofRename : ∀ (t : Tm s₁) (ρ : Rename s₁ s₂),
    t.subst (PathSubst.ofRename ρ) = t.rename ρ
  | .val v, ρ => by simp only [Tm.subst, Tm.rename, Val.subst_ofRename v ρ]
  | .app p q, ρ => by simp only [Tm.subst, Tm.rename, Path.subst_ofRename]
  | .lett t u, ρ => by
      simp only [Tm.subst, Tm.rename, PathSubst.lift_ofRename, Tm.subst_ofRename t ρ,
        Tm.subst_ofRename u ρ.lift]
  | .path p, ρ => by simp only [Tm.subst, Tm.rename, Path.subst_ofRename]
theorem Val.subst_ofRename : ∀ (v : Val s₁) (ρ : Rename s₁ s₂),
    v.subst (PathSubst.ofRename ρ) = v.rename ρ
  | .new T ds, ρ => by
      simp only [Val.subst, Val.rename, PathSubst.lift_ofRename, Ty.subst_ofRename T ρ.lift,
        Defs.subst_ofRename ds ρ.lift]
  | .lam T t, ρ => by
      simp only [Val.subst, Val.rename, PathSubst.lift_ofRename, Ty.subst_ofRename T ρ,
        Tm.subst_ofRename t ρ.lift]
theorem Def.subst_ofRename : ∀ (d : Def s₁) (ρ : Rename s₁ s₂),
    d.subst (PathSubst.ofRename ρ) = d.rename ρ
  | .typ A T, ρ => by simp only [Def.subst, Def.rename, Ty.subst_ofRename T ρ]
  | .trm a r, ρ => by simp only [Def.subst, Def.rename, Rhs.subst_ofRename r ρ]
theorem Defs.subst_ofRename : ∀ (ds : Defs s₁) (ρ : Rename s₁ s₂),
    ds.subst (PathSubst.ofRename ρ) = ds.rename ρ
  | .nil, _ => rfl
  | .cons ds d, ρ => by
      simp only [Defs.subst, Defs.rename, Defs.subst_ofRename ds ρ, Def.subst_ofRename d ρ]
theorem Rhs.subst_ofRename : ∀ (r : Rhs s₁) (ρ : Rename s₁ s₂),
    r.subst (PathSubst.ofRename ρ) = r.rename ρ
  | .defp p, ρ => by simp only [Rhs.subst, Rhs.rename, Path.subst_ofRename]
  | .defv v, ρ => by simp only [Rhs.subst, Rhs.rename, Val.subst_ofRename v ρ]
end

mutual
theorem Tm.subst_subst : ∀ (t : Tm s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (t.subst σ).subst τ = t.subst (σ.comp τ)
  | .val v, σ, τ => by simp only [Tm.subst, Val.subst_subst v σ τ]
  | .app p q, σ, τ => by simp only [Tm.subst, Path.subst_subst]
  | .lett t u, σ, τ => by
      simp only [Tm.subst, Tm.subst_subst t σ τ, Tm.subst_subst u σ.lift τ.lift,
        PathSubst.comp_lift]
  | .path p, σ, τ => by simp only [Tm.subst, Path.subst_subst]
theorem Val.subst_subst : ∀ (v : Val s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (v.subst σ).subst τ = v.subst (σ.comp τ)
  | .new T ds, σ, τ => by
      simp only [Val.subst, Ty.subst_subst T σ.lift τ.lift, Defs.subst_subst ds σ.lift τ.lift,
        PathSubst.comp_lift]
  | .lam T t, σ, τ => by
      simp only [Val.subst, Ty.subst_subst T σ τ, Tm.subst_subst t σ.lift τ.lift,
        PathSubst.comp_lift]
theorem Def.subst_subst : ∀ (d : Def s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (d.subst σ).subst τ = d.subst (σ.comp τ)
  | .typ A T, σ, τ => by simp only [Def.subst, Ty.subst_subst T σ τ]
  | .trm a r, σ, τ => by simp only [Def.subst, Rhs.subst_subst r σ τ]
theorem Defs.subst_subst : ∀ (ds : Defs s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (ds.subst σ).subst τ = ds.subst (σ.comp τ)
  | .nil, _, _ => rfl
  | .cons ds d, σ, τ => by
      simp only [Defs.subst, Defs.subst_subst ds σ τ, Def.subst_subst d σ τ]
theorem Rhs.subst_subst : ∀ (r : Rhs s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (r.subst σ).subst τ = r.subst (σ.comp τ)
  | .defp p, σ, τ => by simp only [Rhs.subst, Path.subst_subst]
  | .defv v, σ, τ => by simp only [Rhs.subst, Val.subst_subst v σ τ]
end

theorem Tm.weaken_substPath (X : Tm s) (p : Path s) : X.weaken.substPath p = X := by
  rw [Tm.weaken, ← Tm.subst_ofRename, Tm.substPath, Tm.subst_subst,
    PathSubst.ofRename_succ_comp_one, Tm.subst_ofRename, Tm.rename_id]

theorem Val.weaken_substPath (X : Val s) (p : Path s) : X.weaken.substPath p = X := by
  rw [Val.weaken, ← Val.subst_ofRename, Val.substPath, Val.subst_subst,
    PathSubst.ofRename_succ_comp_one, Val.subst_ofRename, Val.rename_id]

theorem Def.weaken_substPath (X : Def s) (p : Path s) : X.weaken.substPath p = X := by
  rw [Def.weaken, ← Def.subst_ofRename, Def.substPath, Def.subst_subst,
    PathSubst.ofRename_succ_comp_one, Def.subst_ofRename, Def.rename_id]

theorem Defs.weaken_substPath (X : Defs s) (p : Path s) : X.weaken.substPath p = X := by
  rw [Defs.weaken, ← Defs.subst_ofRename, Defs.substPath, Defs.subst_subst,
    PathSubst.ofRename_succ_comp_one, Defs.subst_ofRename, Defs.rename_id]

theorem Rhs.weaken_substPath (X : Rhs s) (p : Path s) : X.weaken.substPath p = X := by
  rw [Rhs.weaken, ← Rhs.subst_ofRename, Rhs.substPath, Rhs.subst_subst,
    PathSubst.ofRename_succ_comp_one, Rhs.subst_ofRename, Rhs.rename_id]

theorem Tm.substPath_subst (X : Tm (s₁,x)) (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (X.substPath q).subst σ = (X.subst σ.lift).substPath (q.subst σ) := by
  rw [Tm.substPath, Tm.substPath, Tm.subst_subst, Tm.subst_subst, PathSubst.one_comp]

theorem Val.substPath_subst (X : Val (s₁,x)) (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (X.substPath q).subst σ = (X.subst σ.lift).substPath (q.subst σ) := by
  rw [Val.substPath, Val.substPath, Val.subst_subst, Val.subst_subst, PathSubst.one_comp]

theorem Def.substPath_subst (X : Def (s₁,x)) (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (X.substPath q).subst σ = (X.subst σ.lift).substPath (q.subst σ) := by
  rw [Def.substPath, Def.substPath, Def.subst_subst, Def.subst_subst, PathSubst.one_comp]

theorem Defs.substPath_subst (X : Defs (s₁,x)) (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (X.substPath q).subst σ = (X.subst σ.lift).substPath (q.subst σ) := by
  rw [Defs.substPath, Defs.substPath, Defs.subst_subst, Defs.subst_subst, PathSubst.one_comp]

theorem Rhs.substPath_subst (X : Rhs (s₁,x)) (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (X.substPath q).subst σ = (X.subst σ.lift).substPath (q.subst σ) := by
  rw [Rhs.substPath, Rhs.substPath, Rhs.subst_subst, Rhs.subst_subst, PathSubst.one_comp]

/-! ## Paths followed by fields -/

theorem Path.ext_subst (p : Path s₁) (bs : List Label) (σ : PathSubst s₁ s₂) :
    (p.ext bs).subst σ = (p.subst σ).ext bs := by
  induction bs generalizing p with
  | nil => rfl
  | cons a bs ih => exact ih (p.sel a)

/-! ## Context lookup and store read (plan S.1) -/

/-- The type of a variable in a context.  A plain binder's type is of the outer signature and is
weakened.  A self binder's type already mentions the self and is returned as it is, which is Coq's
`open_typ z T` at the self `z` (`Definitions.v:628-631`). -/
def Ctx.lookup : Ctx s → BVar s .var → Ty s
  | .cons _ T, .here => T.weaken                         -- (G, z : T).lookup z = T↑
  | .consSelf _ T, .here => T                            -- (G, z :ˢ T).lookup z = T
  | .cons G _, .there y => (G.lookup y).weaken           -- (G, b).lookup y↑ = (G.lookup y)↑
  | .consSelf G _, .there y => (G.lookup y).weaken       -- (G, b).lookup y↑ = (G.lookup y)↑

/-- The value of a variable in a store.  Coq's `binds x v γ` (`Definitions.v:483`), total because a
store binds every variable of its signature. -/
def Store.get : Store s → BVar s .var → Val s
  | .cons _ v, .here => v.weaken                         -- (γ, x ↦ v).get x = v↑
  | .cons γ _, .there y => (γ.get y).weaken              -- (γ, x ↦ v).get y↑ = (γ.get y)↑

theorem Ctx.lookup_consSelf_here (G : Ctx s) (T : Ty (s,x)) : (G.consSelf T).lookup .here = T := rfl

theorem Ctx.lookup_cons_here (G : Ctx s) (T : Ty s) : (G.cons T).lookup .here = T.weaken := rfl

/-! ## The newest definition wins -/

/-- Two definitions at one label: `get` reads the newer.  This is `get_def`, and it is why
`lookup_sel_v` reads one field and not any member of a list. -/
theorem Defs.get_shadow (ds : Defs s) (a : Label) (r₁ r₂ : Rhs s) :
    ((ds.cons (.trm a r₁)).cons (.trm a r₂)).get a = some (.trm a r₂) :=
  if_pos rfl

end PDot.Source
