import Coercions.Nominal.Source.Syntax

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

namespace Nominal.Source

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
  | .cls C T, ρ => .cls C (T.rename ρ)
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
  | .cls C T, σ => .cls C (T.subst σ)
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
  | .cls C T => by simp only [Def.rename, Ty.rename_id T]
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
  | .cls C T, ρ, ρ' => by simp only [Def.rename, Ty.rename_rename T ρ ρ']
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
  | .cls C T, ρ => by simp only [Def.subst, Def.rename, Ty.subst_ofRename T ρ]
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
  | .cls C T, σ, τ => by simp only [Def.subst, Ty.subst_subst T σ τ]
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
    (p.nomExt bs).subst σ = (p.subst σ).nomExt bs := by
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


/-! ## The class reading of a self binder (plan XII)

A self binder `z :ˢ T` declares a class `C` when its type holds a declaration `{C : ⊥..U}` whose `U`
is a class body, at the top or inside a nested object `{b : μ(o. V)}`.  `G.selfCls p C = some U`
reads that body at the path `p`, and `subtyp_seal` reads it.  `Ctx.selfCls_ext` is the plan's
equation.  A context is class-free when no self type declares a class, and then `selfCls` is `none`
everywhere (`Ctx.selfCls_none_of_classFree`), which is plan X's pDOT as a restriction of pDOT-C. -/

/-- Whether a variable is bound by a self binder `z :ˢ T` of the context. -/
def Ctx.isSelf : Ctx s → BVar s .var → Bool
  | .cons _ _, .here => false                                 -- (G, z : T): a plain binder
  | .consSelf _ _, .here => true                              -- (G, z :ˢ T): a self binder
  | .cons G _, .there y => G.isSelf y                         -- (G, z : T), y older than z
  | .consSelf G _, .there y => G.isSelf y                     -- (G, z :ˢ T), y older than z

/-- `T.clsBody`: `T` is a class body, a type whose translation is an object type.  True at `⊤`, a
record, `∧` and `μ`, false at `⊥`, `p.A`, `∀` and `p.type`. -/
def Ty.clsBody : Ty s → Bool
  | .top => true                                 -- ⊤
  | .rcd _ => true                               -- {D}
  | .and _ _ => true                             -- T ∧ U
  | .mu _ => true                                -- μ(z. T)
  | .bot => false                                -- ⊥
  | .sel _ _ => false                            -- p.A
  | .all _ _ => false                            -- ∀(z : S) T
  | .sngl _ => false                             -- p.type

/-- `T.muBody`: `some U` at `μ(z. U)`, `none` at the seven other formers. -/
def Ty.muBody : Ty s → Option (Ty (s,x))
  | .mu U => some U                              -- μ(z. U)
  | .top => none
  | .bot => none
  | .rcd _ => none
  | .and _ _ => none
  | .sel _ _ => none
  | .all _ _ => none
  | .sngl _ => none

/-- `T.findCls C`: the body `U` of a declaration `{C : ⊥..U}` of `T` with `U` a class body, the
rightmost one in an intersection. -/
def Ty.findCls : Ty s → Label → Option (Ty s)
  | .and T U, C => (U.findCls C).orElse (fun _ => T.findCls C)       -- (T ∧ U).findCls C
  | .rcd (.typ C' L U), C => if L = .bot ∧ C = C' ∧ U.clsBody = true then some U else none  -- {C' : L..U}
  | .rcd (.trm _ _), _ => none                                        -- {a : T}
  | .top, _ => none
  | .bot, _ => none
  | .sel _ _, _ => none
  | .mu _, _ => none
  | .all _ _, _ => none
  | .sngl _, _ => none

/-- `T.findNest b`: the body `U` of a field `{b : μ(o. U)}` of `T`, the rightmost one in an
intersection.  `U` mentions the nested self `o`. -/
def Ty.findNest : Ty s → Label → Option (Ty (s,x))
  | .and T U, b => (U.findNest b).orElse (fun _ => T.findNest b)     -- (T ∧ U).findNest b
  | .rcd (.trm b' T), b => if b = b' then T.muBody else none          -- {b' : T}
  | .rcd (.typ _ _ _), _ => none                                      -- {A : S..U}
  | .top, _ => none
  | .bot, _ => none
  | .sel _ _, _ => none
  | .mu _, _ => none
  | .all _ _, _ => none
  | .sngl _, _ => none

/-- `T.clsAt r bs C`: the class body of `C` in the object at the fields `bs` of the self type `T`,
which is read at the path `r`.  Each nested self is opened at `r.b`. -/
def Ty.clsAt : Ty s → Path s → List Label → Label → Option (Ty s)
  | T, _, [], C => T.findCls C                                        -- T.clsAt r [] C = T.findCls C
  | T, r, b :: bs, C =>                                               -- T.clsAt r (b :: bs) C
      (T.findNest b).bind (fun U => (U.substPath (r.sel b)).clsAt (r.sel b) bs C)

/-- `G.selfAt p`: the self type of the object at `p`, when `p` is a self variable `z :ˢ T` followed by
fields at nested objects.  Structural on the path, as `FCn.Ctx.nodeAt`. -/
def Ctx.selfAt (G : Ctx s) : Path s → Option (Ty s)
  | .var x => if G.isSelf x then some (G.lookup x) else none          -- G.selfAt x
  | .sel p b => (G.selfAt p).bind (fun T => (T.findNest b).map (·.substPath (p.sel b)))  -- G.selfAt p.b

/-- `G.selfCls p C`: the class body of `C` declared by the self type of the object at `p`. -/
def Ctx.selfCls (G : Ctx s) (p : Path s) (C : Label) : Option (Ty s) := (G.selfAt p).bind (·.findCls C)

/-- `G.selfCls (p.nomExt bs) C` reads the self type at `p` and then the fields `bs`. -/
theorem Ctx.selfCls_ext_gen (G : Ctx s) (bs : List Label) : ∀ (p : Path s) (C : Label),
    G.selfCls (p.nomExt bs) C = (G.selfAt p).bind (fun T => T.clsAt p bs C) := by
  induction bs with
  | nil => intro p C; rfl
  | cons b bs ih =>
      intro p C
      show G.selfCls ((p.sel b).nomExt bs) C = _
      rw [ih (p.sel b) C]
      show ((G.selfAt p).bind (fun T => (T.findNest b).map (·.substPath (p.sel b)))).bind _ = _
      cases G.selfAt p with
      | none => rfl
      | some T =>
          show ((T.findNest b).map _).bind _ = (T.findNest b).bind _
          cases T.findNest b <;> rfl

/-- The plan's equation: `G.selfCls ((var x).ext bs) C = if G.isSelf x then (G.lookup x).clsAt (var x)
bs C else none`. -/
theorem Ctx.selfCls_ext (G : Ctx s) (x : BVar s .var) (bs : List Label) (C : Label) :
    G.selfCls ((Path.var x).nomExt bs) C = if G.isSelf x then (G.lookup x).clsAt (.var x) bs C else none := by
  rw [Ctx.selfCls_ext_gen]
  show (if G.isSelf x then some (G.lookup x) else none).bind _ = _
  cases G.isSelf x <;> rfl

mutual
/-- `T.clsFree`: no declaration `{C : ⊥..U}` with `U` a class body in `T`, at the top or in a nested
object `{b : μ(o. U)}`. -/
def Ty.clsFree : Ty s → Bool
  | .and T U => T.clsFree && U.clsFree           -- T ∧ U
  | .rcd D => D.clsFree                          -- {D}
  | .top => true
  | .bot => true
  | .sel _ _ => true
  | .mu _ => true
  | .all _ _ => true
  | .sngl _ => true
/-- `D.clsFree`: `D` declares no class and no nested object of `D` does. -/
def Dec.clsFree : Dec s → Bool
  | .typ _ L U => !(decide (L = .bot) && U.clsBody)   -- {A : L..U}
  | .trm _ (.mu U) => U.clsFree                       -- {b : μ(o. U)}
  | .trm _ .top => true
  | .trm _ .bot => true
  | .trm _ (.rcd _) => true
  | .trm _ (.and _ _) => true
  | .trm _ (.sel _ _) => true
  | .trm _ (.all _ _) => true
  | .trm _ (.sngl _) => true
end

/-- `G.clsFree`: no self type of the context declares a class. -/
def Ctx.clsFree : Ctx s → Bool
  | .nil => true                                 -- []
  | .cons G _ => G.clsFree                       -- G, z : T
  | .consSelf G T => G.clsFree && T.clsFree      -- G, z :ˢ T

/-- A substitution keeps the head former, so it keeps `clsBody`. -/
theorem Ty.clsBody_subst : ∀ (T : Ty s₁) (σ : PathSubst s₁ s₂), (T.subst σ).clsBody = T.clsBody
  | .top, _ => rfl
  | .bot, _ => rfl
  | .rcd _, _ => rfl
  | .and _ _, _ => rfl
  | .sel _ _, _ => rfl
  | .mu _, _ => rfl
  | .all _ _, _ => rfl
  | .sngl _, _ => rfl

/-- `T.subst σ = ⊥` exactly when `T = ⊥`. -/
theorem Ty.subst_eq_bot_iff : ∀ (T : Ty s₁) (σ : PathSubst s₁ s₂), T.subst σ = .bot ↔ T = .bot
  | .top, _ => by simp [Ty.subst]
  | .bot, _ => by simp [Ty.subst]
  | .rcd _, _ => by simp [Ty.subst]
  | .and _ _, _ => by simp [Ty.subst]
  | .sel _ _, _ => by simp [Ty.subst]
  | .mu _, _ => by simp [Ty.subst]
  | .all _ _, _ => by simp [Ty.subst]
  | .sngl _, _ => by simp [Ty.subst]

mutual
/-- A substitution keeps `clsFree`. -/
theorem Ty.clsFree_subst : ∀ (T : Ty s₁) (σ : PathSubst s₁ s₂), (T.subst σ).clsFree = T.clsFree
  | .and T U, σ => by simp only [Ty.subst, Ty.clsFree, Ty.clsFree_subst T σ, Ty.clsFree_subst U σ]
  | .rcd D, σ => Dec.clsFree_subst D σ
  | .top, _ => rfl
  | .bot, _ => rfl
  | .sel _ _, _ => rfl
  | .mu _, _ => rfl
  | .all _ _, _ => rfl
  | .sngl _, _ => rfl
/-- A substitution keeps `clsFree` of a declaration. -/
theorem Dec.clsFree_subst : ∀ (D : Dec s₁) (σ : PathSubst s₁ s₂), (D.subst σ).clsFree = D.clsFree
  | .typ _ L U, σ => by
      simp only [Dec.subst, Dec.clsFree, Ty.clsBody_subst]
      congr 2
      exact decide_eq_decide.mpr (Ty.subst_eq_bot_iff L σ)
  | .trm _ (.mu U), σ => Ty.clsFree_subst U σ.lift
  | .trm _ .top, _ => rfl
  | .trm _ .bot, _ => rfl
  | .trm _ (.rcd _), _ => rfl
  | .trm _ (.and _ _), _ => rfl
  | .trm _ (.sel _ _), _ => rfl
  | .trm _ (.all _ _), _ => rfl
  | .trm _ (.sngl _), _ => rfl
end

/-- A class-free type declares no class. -/
theorem Ty.findCls_none_of_clsFree : ∀ {T : Ty s} (C : Label), T.clsFree = true → T.findCls C = none
  | .and T U, C, h => by
      simp only [Ty.clsFree, Bool.and_eq_true] at h
      simp only [Ty.findCls, Ty.findCls_none_of_clsFree C h.2, Ty.findCls_none_of_clsFree C h.1]; rfl
  | .rcd (.typ C' L U), C, h => by
      simp only [Ty.clsFree, Dec.clsFree, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
      simp only [Ty.findCls]
      split
      · next hc => rcases h with h | h
                   · exact absurd hc.1 h
                   · rw [hc.2.2] at h; cases h
      · rfl
  | .rcd (.trm _ _), _, _ => rfl
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .sel _ _, _, _ => rfl
  | .mu _, _, _ => rfl
  | .all _ _, _, _ => rfl
  | .sngl _, _, _ => rfl

/-- A nested object of a class-free type is class-free. -/
theorem Ty.findNest_clsFree : ∀ {T : Ty s} {b : Label} {U : Ty (s,x)}, T.clsFree = true → T.findNest b = some U → U.clsFree = true
  | .and T₁ T₂, b, U, h, e => by
      simp only [Ty.clsFree, Bool.and_eq_true] at h
      simp only [Ty.findNest] at e
      cases h₂ : T₂.findNest b with
      | some V => rw [h₂] at e; cases e; exact Ty.findNest_clsFree h.2 h₂
      | none => rw [h₂] at e; exact Ty.findNest_clsFree h.1 e
  | .rcd (.trm b' (.mu V)), b, U, h, e => by
      simp only [Ty.findNest, Ty.muBody] at e
      split at e
      · cases e; exact h
      · cases e
  | .rcd (.trm b' .top), b, U, _, e => by simp only [Ty.findNest, Ty.muBody] at e; split at e <;> cases e
  | .rcd (.trm b' .bot), b, U, _, e => by simp only [Ty.findNest, Ty.muBody] at e; split at e <;> cases e
  | .rcd (.trm b' (.rcd _)), b, U, _, e => by simp only [Ty.findNest, Ty.muBody] at e; split at e <;> cases e
  | .rcd (.trm b' (.and _ _)), b, U, _, e => by simp only [Ty.findNest, Ty.muBody] at e; split at e <;> cases e
  | .rcd (.trm b' (.sel _ _)), b, U, _, e => by simp only [Ty.findNest, Ty.muBody] at e; split at e <;> cases e
  | .rcd (.trm b' (.all _ _)), b, U, _, e => by simp only [Ty.findNest, Ty.muBody] at e; split at e <;> cases e
  | .rcd (.trm b' (.sngl _)), b, U, _, e => by simp only [Ty.findNest, Ty.muBody] at e; split at e <;> cases e
  | .rcd (.typ _ _ _), _, _, _, e => nomatch e
  | .top, _, _, _, e => nomatch e
  | .bot, _, _, _, e => nomatch e
  | .sel _ _, _, _, _, e => nomatch e
  | .mu _, _, _, _, e => nomatch e
  | .all _ _, _, _, _, e => nomatch e
  | .sngl _, _, _, _, e => nomatch e

/-- In a class-free context, the type of a self variable is class-free. -/
theorem Ctx.clsFree_lookup : ∀ {G : Ctx s} {x : BVar s .var}, G.clsFree = true → G.isSelf x = true → (G.lookup x).clsFree = true
  | .consSelf _ T, .here, h, _ => by simp only [Ctx.clsFree, Bool.and_eq_true] at h; exact h.2
  | .cons _ _, .here, _, hs => nomatch hs
  | .cons G _, .there y, h, hs => by
      show (Ty.weaken _).clsFree = true
      rw [Ty.weaken, ← Ty.subst_ofRename, Ty.clsFree_subst]; exact Ctx.clsFree_lookup (G := G) h hs
  | .consSelf G _, .there y, h, hs => by
      simp only [Ctx.clsFree, Bool.and_eq_true] at h
      show (Ty.weaken _).clsFree = true
      rw [Ty.weaken, ← Ty.subst_ofRename, Ty.clsFree_subst]; exact Ctx.clsFree_lookup (G := G) h.1 hs

/-- In a class-free context, every self type `G.selfAt p` is class-free. -/
theorem Ctx.selfAt_clsFree {G : Ctx s} (hG : G.clsFree = true) : ∀ {p : Path s} {T : Ty s}, G.selfAt p = some T → T.clsFree = true
  | .var x, T, e => by
      simp only [Ctx.selfAt] at e
      split at e
      · next hs => cases e; exact Ctx.clsFree_lookup hG hs
      · cases e
  | .sel p b, T, e => by
      simp only [Ctx.selfAt] at e
      cases h₁ : G.selfAt p with
      | none => rw [h₁] at e; cases e
      | some V =>
          rw [h₁, Option.bind_some] at e
          cases h₂ : V.findNest b with
          | none => rw [h₂] at e; cases e
          | some U =>
              rw [h₂] at e; cases e
              show (U.subst _).clsFree = true
              rw [Ty.clsFree_subst]
              exact Ty.findNest_clsFree (Ctx.selfAt_clsFree hG h₁) h₂

/-- The class-free restriction (plan P7): no self binder of a class-free context declares a class,
so `subtyp_seal` has no instance there. -/
theorem Ctx.selfCls_none_of_classFree {G : Ctx s} (hG : G.clsFree = true) (p : Path s) (C : Label) : G.selfCls p C = none := by
  unfold Ctx.selfCls
  cases h : G.selfAt p with
  | none => rfl
  | some T => exact Ty.findCls_none_of_clsFree C (Ctx.selfAt_clsFree hG h)

/-- A class-free self type declares no class at any fields `bs`. -/
theorem Ty.clsAt_none_of_clsFree : ∀ (bs : List Label) {T : Ty s} (r : Path s) (C : Label), T.clsFree = true → T.clsAt r bs C = none
  | [], T, _, C, h => Ty.findCls_none_of_clsFree C h
  | b :: bs, T, r, C, h => by
      simp only [Ty.clsAt]
      cases h₂ : T.findNest b with
      | none => rfl
      | some U =>
          show (U.substPath (r.sel b)).clsAt (r.sel b) bs C = none
          apply Ty.clsAt_none_of_clsFree bs
          rw [Ty.substPath, Ty.clsFree_subst]; exact Ty.findNest_clsFree h h₂

namespace ClsReadTests
abbrev tC : Label := .typ 7
abbrev tA : Label := .typ 8
abbrev tb : Label := .trm 9
/-- `{A : ⊤..⊤} ∧ {C : ⊥..⊤}` over `([], z)`. -/
abbrev tSelf : Ty ([],x) := .and (.rcd (.typ tA .top .top)) (.rcd (.typ tC .bot .top))
example : (Ctx.nil.consSelf tSelf).selfCls (.var .here) tC = some .top := by decide
example : (Ctx.nil.consSelf tSelf).selfCls (.var .here) tA = none := by decide
example : (Ctx.nil.cons (.mu tSelf)).selfCls (.var .here) tC = none := by decide
example : (Ctx.nil.consSelf tSelf).clsFree = false := by decide
/-- `{b : μ(o. {C : ⊥..⊤})}` over `([], z)`: a class in a nested object. -/
abbrev tNest : Ty ([],x) := .rcd (.trm tb (.mu (.rcd (.typ tC .bot .top))))
example : (Ctx.nil.consSelf tNest).selfCls ((Path.var .here).sel tb) tC = some .top := by decide
example : (Ctx.nil.consSelf tNest).selfCls (.var .here) tC = none := by decide
example : (Ctx.nil.cons (.rcd (.typ tA .top .top))).clsFree = true := rfl
end ClsReadTests

end Nominal.Source
