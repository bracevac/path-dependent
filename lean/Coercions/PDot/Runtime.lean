import Coercions.Paths.FCdot.TypingPathSubst

/-!
# The runtime: untyped pDOT

pDOT's reduction with the types erased, as Part R of plan X states it (`plan-10-pdot.md:283-311`).
A nested literal carries no self binder.  It is a `nest`, named by its path from the enclosing
top-level self, which is pDOT's own reading of Def-New.  The source erases into this runtime in
`Source/Erasure.lean`.

* `Tm`, `Val`, `Defs` and `Rhs` are the syntax of R.1.  A right side `defv` holds any value, a
  literal or a lambda, so that RL-Var returns the stored value.  A `nest` binds nothing.
* `LStep γ r r'` is one lookup step `γ ⊢ r ⤳ᴿ r'`, 4 constructors, RL-Var to RL-SelN.  `Lookups` is
  its reflexive transitive closure `⤳ᴿ*`.  `Defs.get` returns the newest definition at a label, so
  lookup is deterministic (`LStep.det`).
* `Red c c' ρ` is `c ⟼ᴿ[ρ] c'`, 4 constructors, RR-App to RR-LetTgt, on configurations `⟨s, γ, t⟩`.
  `ρ` renames the store of `c` into the store of `c'`, `Rename.id` or `Rename.succ`.  `NormForm` has
  the 2 constructors RNF-Path and RNF-Val.  Reduction is deterministic (`Red.det`).
* `Joinable γ p q` is `p ⋈ q`: the lookups of `p` and `q` meet at a path.  It is an equivalence and a
  congruence for selection.  Two joinable locations, paths that look up in one step to a right side
  that is no path, are one path (`Joinable.locations`).
* `PathSafe γ p` says that every right side `p` looks up to is a value, a `nest`, or takes one more
  step.  `CyclicPath γ p` is an infinite lookup from `p`, given by a function.
* `lookPath`, `lookStar`, `stepFuel` and `runFuel` compute lookup and reduction.  `lookPath` is
  structural on the path and `stepFuel` on the term.  `lookStar` and `runFuel` recurse on their
  fuel, and `stepFuel` hands its fuel to `lookStar`.  Each has a soundness theorem, so a run by
  `decide +kernel` proves a lookup or a reduction sequence.

Binders are named in comments only.  `(s,x)` adds one variable, and `.here` is the newest variable of
a signature.  `X.weaken` is `X.rename Rename.succ`, and `X.substPath p` instantiates `.here` by `p`.
-/

namespace PDot.Runtime

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Syntax (plan R.1) -/

mutual
/-- Terms. -/
inductive Tm : Sig → Type where
  | path : Path s → Tm s                     -- path p
  | val : Val s → Tm s                       -- val v
  | app : Path s → Path s → Tm s             -- app q p applies q to p
  | lett : Tm s → Tm (s,x) → Tm s            -- let z = t in u, z the .here of u
/-- Values. -/
inductive Val : Sig → Type where
  | new : Defs (s,x) → Val s                 -- ν(z) ds, z the .here of ds
  | lam : Tm (s,x) → Val s                   -- λ(z) t, z the .here of t
/-- Definitions, the newest last. -/
inductive Defs : Sig → Type where
  | nil : Defs s                             -- []
  | cons : Defs s → Label → Rhs s → Defs s   -- ds ▹ (a = r)
/-- Right sides of definitions. -/
inductive Rhs : Sig → Type where
  | defp : Path s → Rhs s                    -- defp p
  | defv : Val s → Rhs s                     -- defv v
  | nest : Defs s → Rhs s                    -- nest ds, no binder, its self named by its path
end

deriving instance DecidableEq for Tm, Val, Defs, Rhs

/-- Stores, the newest variable last. -/
inductive Store : Sig → Type where
  | nil : Store []                           -- []
  | cons : Store s → Val s → Store (s,x)     -- γ, x ↦ v, x the new .here

deriving instance DecidableEq for Store

/-- A configuration `⟨s, γ, t⟩`, a store and a term over one signature. -/
structure Conf where
  s : Sig
  store : Store s
  tm : Tm s

deriving instance DecidableEq for Conf

/-! ## Binding -/

mutual
def Tm.rename : Tm s₁ → Rename s₁ s₂ → Tm s₂
  | .path p, ρ => .path (p.rename ρ)
  | .val v, ρ => .val (v.rename ρ)
  | .app q p, ρ => .app (q.rename ρ) (p.rename ρ)
  | .lett t u, ρ => .lett (t.rename ρ) (u.rename ρ.lift)       -- under z of let z = t in u
def Val.rename : Val s₁ → Rename s₁ s₂ → Val s₂
  | .new ds, ρ => .new (ds.rename ρ.lift)                       -- under z of ν(z) ds
  | .lam t, ρ => .lam (t.rename ρ.lift)                         -- under z of λ(z) t
def Defs.rename : Defs s₁ → Rename s₁ s₂ → Defs s₂
  | .nil, _ => .nil
  | .cons ds a r, ρ => .cons (ds.rename ρ) a (r.rename ρ)
def Rhs.rename : Rhs s₁ → Rename s₁ s₂ → Rhs s₂
  | .defp p, ρ => .defp (p.rename ρ)
  | .defv v, ρ => .defv (v.rename ρ)
  | .nest ds, ρ => .nest (ds.rename ρ)                          -- nest binds nothing
end

mutual
def Tm.subst : Tm s₁ → PathSubst s₁ s₂ → Tm s₂
  | .path p, σ => .path (p.subst σ)
  | .val v, σ => .val (v.subst σ)
  | .app q p, σ => .app (q.subst σ) (p.subst σ)
  | .lett t u, σ => .lett (t.subst σ) (u.subst σ.lift)         -- under z of let z = t in u
def Val.subst : Val s₁ → PathSubst s₁ s₂ → Val s₂
  | .new ds, σ => .new (ds.subst σ.lift)                        -- under z of ν(z) ds
  | .lam t, σ => .lam (t.subst σ.lift)                          -- under z of λ(z) t
def Defs.subst : Defs s₁ → PathSubst s₁ s₂ → Defs s₂
  | .nil, _ => .nil
  | .cons ds a r, σ => .cons (ds.subst σ) a (r.subst σ)
def Rhs.subst : Rhs s₁ → PathSubst s₁ s₂ → Rhs s₂
  | .defp p, σ => .defp (p.subst σ)
  | .defv v, σ => .defv (v.subst σ)
  | .nest ds, σ => .nest (ds.subst σ)                           -- nest binds nothing
end

def Tm.weaken (t : Tm s) : Tm (s,x) := t.rename Rename.succ
def Val.weaken (v : Val s) : Val (s,x) := v.rename Rename.succ
def Defs.weaken (ds : Defs s) : Defs (s,x) := ds.rename Rename.succ
def Rhs.weaken (r : Rhs s) : Rhs (s,x) := r.rename Rename.succ

def Tm.substPath (t : Tm (s,x)) (p : Path s) : Tm s := t.subst (PathSubst.one p)
def Val.substPath (v : Val (s,x)) (p : Path s) : Val s := v.subst (PathSubst.one p)
def Defs.substPath (ds : Defs (s,x)) (p : Path s) : Defs s := ds.subst (PathSubst.one p)
def Rhs.substPath (r : Rhs (s,x)) (p : Path s) : Rhs s := r.subst (PathSubst.one p)

mutual
theorem Tm.rename_id : ∀ (t : Tm s), t.rename Rename.id = t
  | .path p => by simp only [Tm.rename, Path.rename_id]
  | .val v => by simp only [Tm.rename, Val.rename_id v]
  | .app q p => by simp only [Tm.rename, Path.rename_id]
  | .lett t u => by simp only [Tm.rename, Rename.lift_id, Tm.rename_id t, Tm.rename_id u]
theorem Val.rename_id : ∀ (v : Val s), v.rename Rename.id = v
  | .new ds => by simp only [Val.rename, Rename.lift_id, Defs.rename_id ds]
  | .lam t => by simp only [Val.rename, Rename.lift_id, Tm.rename_id t]
theorem Defs.rename_id : ∀ (ds : Defs s), ds.rename Rename.id = ds
  | .nil => rfl
  | .cons ds a r => by simp only [Defs.rename, Defs.rename_id ds, Rhs.rename_id r]
theorem Rhs.rename_id : ∀ (r : Rhs s), r.rename Rename.id = r
  | .defp p => by simp only [Rhs.rename, Path.rename_id]
  | .defv v => by simp only [Rhs.rename, Val.rename_id v]
  | .nest ds => by simp only [Rhs.rename, Defs.rename_id ds]
end

mutual
theorem Tm.subst_ofRename : ∀ (t : Tm s₁) (ρ : Rename s₁ s₂),
    t.subst (PathSubst.ofRename ρ) = t.rename ρ
  | .path p, ρ => by simp only [Tm.subst, Tm.rename, Path.subst_ofRename]
  | .val v, ρ => by simp only [Tm.subst, Tm.rename, Val.subst_ofRename v ρ]
  | .app q p, ρ => by simp only [Tm.subst, Tm.rename, Path.subst_ofRename]
  | .lett t u, ρ => by
      simp only [Tm.subst, Tm.rename, PathSubst.lift_ofRename, Tm.subst_ofRename t ρ,
        Tm.subst_ofRename u ρ.lift]
theorem Val.subst_ofRename : ∀ (v : Val s₁) (ρ : Rename s₁ s₂),
    v.subst (PathSubst.ofRename ρ) = v.rename ρ
  | .new ds, ρ => by
      simp only [Val.subst, Val.rename, PathSubst.lift_ofRename, Defs.subst_ofRename ds ρ.lift]
  | .lam t, ρ => by
      simp only [Val.subst, Val.rename, PathSubst.lift_ofRename, Tm.subst_ofRename t ρ.lift]
theorem Defs.subst_ofRename : ∀ (ds : Defs s₁) (ρ : Rename s₁ s₂),
    ds.subst (PathSubst.ofRename ρ) = ds.rename ρ
  | .nil, _ => rfl
  | .cons ds a r, ρ => by
      simp only [Defs.subst, Defs.rename, Defs.subst_ofRename ds ρ, Rhs.subst_ofRename r ρ]
theorem Rhs.subst_ofRename : ∀ (r : Rhs s₁) (ρ : Rename s₁ s₂),
    r.subst (PathSubst.ofRename ρ) = r.rename ρ
  | .defp p, ρ => by simp only [Rhs.subst, Rhs.rename, Path.subst_ofRename]
  | .defv v, ρ => by simp only [Rhs.subst, Rhs.rename, Val.subst_ofRename v ρ]
  | .nest ds, ρ => by simp only [Rhs.subst, Rhs.rename, Defs.subst_ofRename ds ρ]
end

mutual
theorem Tm.subst_subst : ∀ (t : Tm s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (t.subst σ).subst τ = t.subst (σ.comp τ)
  | .path p, σ, τ => by simp only [Tm.subst, Path.subst_subst]
  | .val v, σ, τ => by simp only [Tm.subst, Val.subst_subst v σ τ]
  | .app q p, σ, τ => by simp only [Tm.subst, Path.subst_subst]
  | .lett t u, σ, τ => by
      simp only [Tm.subst, Tm.subst_subst t σ τ, Tm.subst_subst u σ.lift τ.lift,
        PathSubst.comp_lift]
theorem Val.subst_subst : ∀ (v : Val s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (v.subst σ).subst τ = v.subst (σ.comp τ)
  | .new ds, σ, τ => by
      simp only [Val.subst, Defs.subst_subst ds σ.lift τ.lift, PathSubst.comp_lift]
  | .lam t, σ, τ => by
      simp only [Val.subst, Tm.subst_subst t σ.lift τ.lift, PathSubst.comp_lift]
theorem Defs.subst_subst : ∀ (ds : Defs s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (ds.subst σ).subst τ = ds.subst (σ.comp τ)
  | .nil, _, _ => rfl
  | .cons ds a r, σ, τ => by
      simp only [Defs.subst, Defs.subst_subst ds σ τ, Rhs.subst_subst r σ τ]
theorem Rhs.subst_subst : ∀ (r : Rhs s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (r.subst σ).subst τ = r.subst (σ.comp τ)
  | .defp p, σ, τ => by simp only [Rhs.subst, Path.subst_subst]
  | .defv v, σ, τ => by simp only [Rhs.subst, Val.subst_subst v σ τ]
  | .nest ds, σ, τ => by simp only [Rhs.subst, Defs.subst_subst ds σ τ]
end

mutual
theorem Tm.rename_rename : ∀ (t : Tm s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (t.rename ρ).rename ρ' = t.rename (ρ.comp ρ')
  | .path p, ρ, ρ' => by simp only [Tm.rename, Path.rename_comp]
  | .val v, ρ, ρ' => by simp only [Tm.rename, Val.rename_rename v ρ ρ']
  | .app q p, ρ, ρ' => by simp only [Tm.rename, Path.rename_comp]
  | .lett t u, ρ, ρ' => by
      simp only [Tm.rename, Tm.rename_rename t ρ ρ', Tm.rename_rename u ρ.lift ρ'.lift,
        Rename.lift_comp]
theorem Val.rename_rename : ∀ (v : Val s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (v.rename ρ).rename ρ' = v.rename (ρ.comp ρ')
  | .new ds, ρ, ρ' => by
      simp only [Val.rename, Defs.rename_rename ds ρ.lift ρ'.lift, Rename.lift_comp]
  | .lam t, ρ, ρ' => by
      simp only [Val.rename, Tm.rename_rename t ρ.lift ρ'.lift, Rename.lift_comp]
theorem Defs.rename_rename : ∀ (ds : Defs s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (ds.rename ρ).rename ρ' = ds.rename (ρ.comp ρ')
  | .nil, _, _ => rfl
  | .cons ds a r, ρ, ρ' => by
      simp only [Defs.rename, Defs.rename_rename ds ρ ρ', Rhs.rename_rename r ρ ρ']
theorem Rhs.rename_rename : ∀ (r : Rhs s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (r.rename ρ).rename ρ' = r.rename (ρ.comp ρ')
  | .defp p, ρ, ρ' => by simp only [Rhs.rename, Path.rename_comp]
  | .defv v, ρ, ρ' => by simp only [Rhs.rename, Val.rename_rename v ρ ρ']
  | .nest ds, ρ, ρ' => by simp only [Rhs.rename, Defs.rename_rename ds ρ ρ']
end

/-- Weakening then instantiating `.here` is the identity.  The runtime's copy of the source's lemma
(`Source/Binding.lean:123-126`), since the runtime imports nothing of the source. -/
theorem PathSubst.ofRename_succ_comp_one (p : Path s) :
    (PathSubst.ofRename (Rename.succ (k := .var))).comp (PathSubst.one p)
      = PathSubst.ofRename Rename.id :=
  PathSubst.funext' (fun _ => rfl)

theorem Tm.weaken_substPath (X : Tm s) (p : Path s) : X.weaken.substPath p = X := by
  rw [Tm.weaken, ← Tm.subst_ofRename, Tm.substPath, Tm.subst_subst,
    PathSubst.ofRename_succ_comp_one, Tm.subst_ofRename, Tm.rename_id]

theorem Val.weaken_substPath (X : Val s) (p : Path s) : X.weaken.substPath p = X := by
  rw [Val.weaken, ← Val.subst_ofRename, Val.substPath, Val.subst_subst,
    PathSubst.ofRename_succ_comp_one, Val.subst_ofRename, Val.rename_id]

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

theorem Defs.substPath_subst (X : Defs (s₁,x)) (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (X.substPath q).subst σ = (X.subst σ.lift).substPath (q.subst σ) := by
  rw [Defs.substPath, Defs.substPath, Defs.subst_subst, Defs.subst_subst, PathSubst.one_comp]

theorem Rhs.substPath_subst (X : Rhs (s₁,x)) (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (X.substPath q).subst σ = (X.subst σ.lift).substPath (q.subst σ) := by
  rw [Rhs.substPath, Rhs.substPath, Rhs.subst_subst, Rhs.subst_subst, PathSubst.one_comp]

/-! ## Stores and definitions -/

/-- The value a store holds at a variable, weakened to the store's signature. -/
def Store.get : Store s → BVar s .var → Val s
  | .cons _ v, .here => v.weaken                                -- (γ, x ↦ v).get x = v↑
  | .cons γ _, .there y => (γ.get y).weaken                     -- (γ, x ↦ v).get y↑ = (γ.get y)↑

/-- The newest definition at a label. -/
def Defs.get : Defs s → Label → Option (Rhs s)
  | .nil, _ => none                                             -- [].get b = none
  | .cons ds a r, b => if a = b then some r else ds.get b       -- (ds ▹ (a = r)).get b

/-- Every definition at a label removed. -/
def Defs.drop : Defs s → Label → Defs s
  | .nil, _ => .nil                                             -- [].drop b = []
  | .cons ds a r, b => if a = b then ds.drop b else .cons (ds.drop b) a r   -- (ds ▹ (a = r)).drop b

theorem Defs.get_subst : ∀ (ds : Defs s₁) (σ : PathSubst s₁ s₂) (a : Label),
    (ds.subst σ).get a = (ds.get a).map (·.subst σ)
  | .nil, _, _ => rfl
  | .cons ds b r, σ, a => by
      simp only [Defs.subst, Defs.get]
      split
      · rfl
      · exact Defs.get_subst ds σ a

theorem Defs.drop_subst : ∀ (ds : Defs s₁) (σ : PathSubst s₁ s₂) (a : Label),
    (ds.drop a).subst σ = (ds.subst σ).drop a
  | .nil, _, _ => rfl
  | .cons ds b r, σ, a => by
      simp only [Defs.subst, Defs.drop]
      split
      · exact Defs.drop_subst ds σ a
      · simp only [Defs.subst, Defs.drop_subst ds σ a]

theorem Defs.get_drop_self : ∀ (ds : Defs s) (a : Label), (ds.drop a).get a = none
  | .nil, _ => rfl
  | .cons ds b r, a => by
      simp only [Defs.drop]
      split
      · exact Defs.get_drop_self ds a
      · simp only [Defs.get]
        rw [if_neg ‹_›]
        exact Defs.get_drop_self ds a

theorem Defs.drop_of_get_none : ∀ (ds : Defs s) {a : Label}, ds.get a = none → ds.drop a = ds
  | .nil, _, _ => rfl
  | .cons ds b r, a, h => by
      simp only [Defs.get] at h
      split at h
      · cases h
      · rename_i hba
        simp only [Defs.drop]
        rw [if_neg hba, Defs.drop_of_get_none ds h]

theorem Defs.get_drop_ne : ∀ (ds : Defs s) {a b : Label}, a ≠ b → (ds.drop a).get b = ds.get b
  | .nil, _, _, _ => rfl
  | .cons ds c r, a, b, h => by
      simp only [Defs.drop]
      split
      · rename_i hca
        subst hca
        simp only [Defs.get]
        rw [if_neg h]
        exact Defs.get_drop_ne ds h
      · simp only [Defs.get]
        split
        · rfl
        · exact Defs.get_drop_ne ds h

/-! ## Lookup (plan R.1, RL-Var, RL-SelP, RL-SelV, RL-SelN) -/

/-- One lookup step `γ ⊢ r ⤳ᴿ r'`.  Only a path steps. -/
inductive LStep (γ : Store s) : Rhs s → Rhs s → Prop where
  -- RL-Var   γ.get x = v  ⟹  γ ⊢ defp x ⤳ᴿ defv v   binder x
  | var : LStep γ (.defp (.var x)) (.defv (γ.get x))
  -- RL-SelP  γ ⊢ defp p ⤳ᴿ defp q  ⟹  γ ⊢ defp p.a ⤳ᴿ defp q.a   binders p q a
  | selP : LStep γ (.defp p) (.defp q) → LStep γ (.defp (p.sel a)) (.defp (q.sel a))
  -- RL-SelV  γ ⊢ defp p ⤳ᴿ defv ν(z) ds,  ds.get a = some r  ⟹  γ ⊢ defp p.a ⤳ᴿ r⟨p⟩   binders p, ds and r under z, a
  | selV : LStep γ (.defp p) (.defv (.new ds)) → ds.get a = some r →
      LStep γ (.defp (p.sel a)) (r.substPath p)
  -- RL-SelN  γ ⊢ defp p ⤳ᴿ nest ds,  ds.get a = some r  ⟹  γ ⊢ defp p.a ⤳ᴿ r   binders p ds a r
  | selN : LStep γ (.defp p) (.nest ds) → ds.get a = some r → LStep γ (.defp (p.sel a)) r

/-- `γ ⊢ r ⤳ᴿ* r'`, the reflexive transitive closure of `LStep`. -/
inductive Lookups (γ : Store s) : Rhs s → Rhs s → Prop where
  -- γ ⊢ r ⤳ᴿ* r   binder r
  | refl : Lookups γ r r
  -- γ ⊢ r ⤳ᴿ r',  γ ⊢ r' ⤳ᴿ* r''  ⟹  γ ⊢ r ⤳ᴿ* r''   binders r r' r''
  | step : LStep γ r r' → Lookups γ r' r'' → Lookups γ r r''

/-- A right side is a path. -/
def Rhs.isPath : Rhs s → Bool
  | .defp _ => true
  | .defv _ => false
  | .nest _ => false

/-- An infinite lookup from `p`, given by a function. -/
def CyclicPath (γ : Store s) (p : Path s) : Prop :=
  ∃ f : Nat → Rhs s, f 0 = .defp p ∧ ∀ n, LStep γ (f n) (f (n+1))

/-- Every lookup from `p` ends at a value, at a `nest`, or takes one more step. -/
def PathSafe (γ : Store s) (p : Path s) : Prop :=
  ∀ k, Lookups γ (.defp p) k → (∃ v, k = .defv v) ∨ (∃ ds, k = .nest ds) ∨ ∃ k', LStep γ k k'

theorem Lookups.single {γ : Store s} {r r' : Rhs s} (h : LStep γ r r') : Lookups γ r r' :=
  .step h .refl

theorem Lookups.trans {γ : Store s} {r r' r'' : Rhs s} :
    Lookups γ r r' → Lookups γ r' r'' → Lookups γ r r'' := by
  intro h₁ h₂
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem LStep.isPath {γ : Store s} {r r' : Rhs s} (h : LStep γ r r') : r.isPath = true := by
  cases h <;> rfl

theorem Lookups.of_not_path {γ : Store s} {r r' : Rhs s} (h : Lookups γ r r')
    (hr : r.isPath = false) : r' = r := by
  cases h with
  | refl => rfl
  | step h _ =>
      rw [h.isPath] at hr
      cases hr

/-- Lookup is deterministic.  The two field reads agree because `Defs.get` returns one right side. -/
theorem LStep.det {γ : Store s} {r r₁ r₂ : Rhs s} : LStep γ r r₁ → LStep γ r r₂ → r₁ = r₂ := by
  intro h₁
  induction h₁ generalizing r₂ with
  | var =>
      intro h₂
      cases h₂
      rfl
  | selP _ ih =>
      intro h₂
      cases h₂ with
      | selP h =>
          cases ih h
          rfl
      | selV h _ => cases ih h
      | selN h _ => cases ih h
  | selV _ hg ih =>
      intro h₂
      cases h₂ with
      | selP h => cases ih h
      | selV h hg' =>
          cases ih h
          rw [hg] at hg'
          cases hg'
          rfl
      | selN h _ => cases ih h
  | selN _ hg ih =>
      intro h₂
      cases h₂ with
      | selP h => cases ih h
      | selV h _ => cases ih h
      | selN h hg' =>
          cases ih h
          rw [hg] at hg'
          cases hg'
          rfl

theorem Lookups.det_cmp {γ : Store s} {r r₁ r₂ : Rhs s} :
    Lookups γ r r₁ → Lookups γ r r₂ → Lookups γ r₁ r₂ ∨ Lookups γ r₂ r₁ := by
  intro h₁
  induction h₁ generalizing r₂ with
  | refl =>
      intro h₂
      exact .inl h₂
  | step h _ ih =>
      intro h₂
      cases h₂ with
      | refl => exact .inr (.step h ‹_›)
      | step h' hs' =>
          cases LStep.det h h'
          exact ih hs'

theorem Lookups.end_unique {γ : Store s} {r k₁ k₂ : Rhs s} (h₁ : Lookups γ r k₁)
    (h₂ : Lookups γ r k₂) (n₁ : k₁.isPath = false) (n₂ : k₂.isPath = false) : k₁ = k₂ := by
  rcases Lookups.det_cmp h₁ h₂ with h | h
  · exact (h.of_not_path n₁).symm
  · exact h.of_not_path n₂

theorem Lookups.val_unique {γ : Store s} {r : Rhs s} {v₁ v₂ : Val s} :
    Lookups γ r (.defv v₁) → Lookups γ r (.defv v₂) → v₁ = v₂ := by
  intro h₁ h₂
  cases Lookups.end_unique h₁ h₂ rfl rfl
  rfl

/-- `Lookups.sel_path` in its equation form. -/
theorem Lookups.sel_path_of_eq {γ : Store s} {k k' : Rhs s} (h : Lookups γ k k') :
    ∀ {p r : Path s} (a : Label), k = .defp p → k' = .defp r →
      Lookups γ (.defp (p.sel a)) (.defp (r.sel a)) := by
  induction h with
  | refl =>
      intro p r a h1 h2
      subst h1
      cases h2
      exact .refl
  | step h hs ih =>
      intro p r a h1 h2
      subst h1
      subst h2
      rename_i b
      cases b with
      | defp q => exact .step (.selP h) (ih a rfl rfl)
      | defv v => cases hs.of_not_path rfl
      | nest ds => cases hs.of_not_path rfl

theorem Lookups.sel_path {γ : Store s} {p r : Path s} (a : Label)
    (h : Lookups γ (.defp p) (.defp r)) : Lookups γ (.defp (p.sel a)) (.defp (r.sel a)) :=
  h.sel_path_of_eq a rfl rfl

/-! ## Joinability (`D3_Proto.lean:400-453`) -/

/-- `p ⋈ q`: the lookups of `p` and `q` meet at a path.  It does not ask that lookup terminates, so
two paths of one cycle are joinable. -/
def Joinable (γ : Store s) (p q : Path s) : Prop :=
  ∃ r, Lookups γ (.defp p) (.defp r) ∧ Lookups γ (.defp q) (.defp r)

theorem Joinable.refl (γ : Store s) (p : Path s) : Joinable γ p p := ⟨p, .refl, .refl⟩

theorem Joinable.symm {γ : Store s} {p q : Path s} (h : Joinable γ p q) : Joinable γ q p :=
  let ⟨r, h1, h2⟩ := h
  ⟨r, h2, h1⟩

theorem Joinable.trans {γ : Store s} {p q w : Path s} (h₁ : Joinable γ p q)
    (h₂ : Joinable γ q w) : Joinable γ p w := by
  obtain ⟨r1, hp, hq1⟩ := h₁
  obtain ⟨r2, hq2, hw⟩ := h₂
  rcases Lookups.det_cmp hq1 hq2 with h | h
  · exact ⟨r2, hp.trans h, hw⟩
  · exact ⟨r1, hp, hw.trans h⟩

theorem Joinable.sel {γ : Store s} {p q : Path s} (h : Joinable γ p q) (a : Label) :
    Joinable γ (p.sel a) (q.sel a) := by
  obtain ⟨r, h1, h2⟩ := h
  exact ⟨r.sel a, h1.sel_path a, h2.sel_path a⟩

theorem Joinable.of_step {γ : Store s} {p q : Path s} (h : LStep γ (.defp p) (.defp q)) :
    Joinable γ p q := ⟨q, .single h, .refl⟩

theorem Joinable.subst {γ : Store s} {τ τ' : PathSubst s' s}
    (h : ∀ x, Joinable γ (τ.var x) (τ'.var x)) :
    ∀ (q : Path s'), Joinable γ (q.subst τ) (q.subst τ')
  | .var x => h x
  | .sel q a => (Joinable.subst h q).sel a

/-- A path that looks up to a right side that is no path, and a path joinable with it, look up to
the same right side. -/
theorem Joinable.star_val {γ : Store s} {p p' : Path s} {k : Rhs s}
    (hv : Lookups γ (.defp p) k) (hk : k.isPath = false) (hj : Joinable γ p p') :
    Lookups γ (.defp p') k := by
  obtain ⟨r, h1, h2⟩ := hj
  rcases Lookups.det_cmp h1 hv with h | h
  · exact h2.trans h
  · have e := h.of_not_path hk
    subst e
    cases hk

/-- A location looks up in one step to a right side that is no path, so the only path it reaches is
itself.  Two joinable locations are one location. -/
theorem Joinable.locations {γ : Store s} {l l' : Path s} {k₁ k₂ : Rhs s}
    (h₁ : LStep γ (.defp l) k₁) (h₂ : LStep γ (.defp l') k₂)
    (n₁ : k₁.isPath = false) (n₂ : k₂.isPath = false) (hj : Joinable γ l l') : l = l' := by
  obtain ⟨r, hr1, hr2⟩ := hj
  have e1 : r = l := by
    cases hr1 with
    | refl => rfl
    | step h hs =>
        cases LStep.det h h₁
        have e := hs.of_not_path n₁
        subst e
        cases n₁
  have e2 : r = l' := by
    cases hr2 with
    | refl => rfl
    | step h hs =>
        cases LStep.det h h₂
        have e := hs.of_not_path n₂
        subst e
        cases n₂
  rw [← e1, e2]

/-! ## Reduction (plan R.1, RR-App, RR-LetVal, RR-LetPath, RR-LetTgt) -/

/-- `c ⟼ᴿ[ρ] c'`.  `ρ` renames the store of `c` into the store of `c'`. -/
inductive Red : (c c' : Conf) → Rename c.s c'.s → Prop where
  -- RR-App     γ ⊢ defp q ⤳ᴿ* defv λ(z) t  ⟹  ⟨s, γ, app q p⟩ ⟼ᴿ[id] ⟨s, γ, t⟨p⟩⟩   binders s γ q p, t under z
  | app {s : Sig} {γ : Store s} {q p : Path s} {t : Tm (s,x)} :
      Lookups γ (.defp q) (.defv (.lam t)) → Red ⟨s, γ, .app q p⟩ ⟨s, γ, t.substPath p⟩ Rename.id
  -- RR-LetVal  ⟨s, γ, let z = val v in t⟩ ⟼ᴿ[succ] ⟨(s,z), (γ, z ↦ v), t⟩   binders s γ v, t under z
  | letVal : Red ⟨s, γ, .lett (.val v) t⟩ ⟨(s,x), γ.cons v, t⟩ Rename.succ
  -- RR-LetPath ⟨s, γ, let z = path p in t⟩ ⟼ᴿ[id] ⟨s, γ, t⟨p⟩⟩   binders s γ p, t under z
  | letPath : Red ⟨s, γ, .lett (.path p) t⟩ ⟨s, γ, t.substPath p⟩ Rename.id
  -- RR-LetTgt  ⟨s, γ, t₀⟩ ⟼ᴿ[ρ] ⟨s', γ', t₀'⟩  ⟹  ⟨s, γ, let z = t₀ in t⟩ ⟼ᴿ[ρ] ⟨s', γ', let z = t₀' in t.rename ρ.lift⟩
  --             binders s γ t₀ s' γ' t₀' ρ, t under z
  | letTgt : Red ⟨s, γ, t₀⟩ ⟨s', γ', t₀'⟩ ρ →
      Red ⟨s, γ, .lett t₀ t⟩ ⟨s', γ', .lett t₀' (t.rename ρ.lift)⟩ ρ

/-- Paths and values are normal forms. -/
inductive NormForm : Tm s → Prop where
  -- RNF-Path  NormForm (path p)   binder p
  | path : NormForm (.path p)
  -- RNF-Val   NormForm (val v)   binder v
  | val : NormForm (.val v)

/-- One reduction step, its store renaming forgotten. -/
def Step (c c' : Conf) : Prop := ∃ ρ, Red c c' ρ

/-- `c ⟼ᴿ* c'`, the reflexive transitive closure of `Step`. -/
inductive Reds : Conf → Conf → Prop where
  -- c ⟼ᴿ* c   binder c
  | refl : Reds c c
  -- c ⟼ᴿ c',  c' ⟼ᴿ* c''  ⟹  c ⟼ᴿ* c''   binders c c' c''
  | step : Step c c' → Reds c' c'' → Reds c c''

/-- Reduction is deterministic, its store renaming too. -/
theorem Red.det : Red c c₁ ρ₁ → Red c c₂ ρ₂ → c₁ = c₂ ∧ HEq ρ₁ ρ₂ := by
  intro h₁
  induction h₁ generalizing c₂ with
  | app hl =>
      intro h₂
      cases h₂ with
      | app hl' =>
          cases Lookups.val_unique hl hl'
          exact ⟨rfl, HEq.rfl⟩
  | letVal =>
      intro h₂
      cases h₂ with
      | letVal => exact ⟨rfl, HEq.rfl⟩
      | letTgt h => cases h
  | letPath =>
      intro h₂
      cases h₂ with
      | letPath => exact ⟨rfl, HEq.rfl⟩
      | letTgt h => cases h
  | letTgt h ih =>
      intro h₂
      cases h₂ with
      | letVal => cases h
      | letPath => cases h
      | letTgt h' =>
          obtain ⟨e, he⟩ := ih h'
          cases e
          cases he
          exact ⟨rfl, HEq.rfl⟩

theorem NormForm.no_red : NormForm c.tm → ¬ Red c c' ρ := by
  intro hn hr
  cases hr <;> cases hn

/-! ## The evaluator, fuelled -/

/-- One lookup step from `defp p`, computed.  Structural on the path. -/
def lookPath (γ : Store s) : Path s → Option (Rhs s)
  | .var x => some (.defv (γ.get x))
  | .sel p a =>
      match lookPath γ p with
      | some (.defp q) => some (.defp (q.sel a))
      | some (.defv (.new ds)) => (ds.get a).map (·.substPath p)
      | some (.nest ds) => ds.get a
      | some (.defv (.lam _)) => none
      | none => none

theorem LStep.of_lookPath {γ : Store s} : ∀ {p : Path s} {k : Rhs s},
    lookPath γ p = some k → LStep γ (.defp p) k
  | .var x, k, h => by
      simp only [lookPath, Option.some.injEq] at h
      subst h
      exact .var
  | .sel p a, k, h => by
      simp only [lookPath] at h
      split at h
      · rename_i q hq
        simp only [Option.some.injEq] at h
        subst h
        exact .selP (LStep.of_lookPath hq)
      · rename_i ds hq
        cases hg : ds.get a with
        | none =>
            rw [hg] at h
            cases h
        | some r =>
            rw [hg] at h
            simp only [Option.map_some, Option.some.injEq] at h
            subst h
            exact .selV (LStep.of_lookPath hq) hg
      · rename_i ds hq
        exact .selN (LStep.of_lookPath hq) h
      · cases h
      · cases h

/-- Lookup iterated at most `n` times. -/
def lookStar (γ : Store s) : Nat → Rhs s → Rhs s
  | 0, r => r
  | n+1, .defp p =>
      match lookPath γ p with
      | some k => lookStar γ n k
      | none => .defp p
  | _+1, r => r

theorem Lookups.of_lookStar {γ : Store s} : ∀ (n : Nat) (r : Rhs s), Lookups γ r (lookStar γ n r)
  | 0, _ => .refl
  | n+1, .defp p => by
      simp only [lookStar]
      split
      · rename_i k hk
        exact .step (LStep.of_lookPath hk) (Lookups.of_lookStar n k)
      · exact .refl
  | _+1, .defv _ => .refl
  | _+1, .nest _ => .refl

/-- One reduction step, computed: the next configuration with the renaming of its store.  The lookup
of RR-App runs with fuel `n`.  Structural on the term. -/
def stepFuel (n : Nat) (γ : Store s) : Tm s → Option ((s' : Sig) × Store s' × Tm s' × Rename s s')
  | .app q p =>
      match lookStar γ n (.defp q) with
      | .defv (.lam t) => some ⟨s, γ, t.substPath p, Rename.id⟩
      | _ => none
  | .lett (.val v) t => some ⟨(s,x), γ.cons v, t, Rename.succ⟩
  | .lett (.path p) t => some ⟨s, γ, t.substPath p, Rename.id⟩
  | .lett t₀ t =>
      match stepFuel n γ t₀ with
      | some ⟨s', γ', t₀', ρ⟩ => some ⟨s', γ', .lett t₀' (t.rename ρ.lift), ρ⟩
      | none => none
  | _ => none

theorem Red.of_stepFuel {n : Nat} : ∀ {s : Sig} {γ : Store s} {t : Tm s} {s' : Sig}
    {γ' : Store s'} {t' : Tm s'} {ρ : Rename s s'},
    stepFuel n γ t = some ⟨s', γ', t', ρ⟩ → Red ⟨s, γ, t⟩ ⟨s', γ', t'⟩ ρ
  | s, γ, .app q p, s', γ', t', ρ, h => by
      simp only [stepFuel] at h
      split at h
      · rename_i t hl
        simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h
        simp only [heq_eq_eq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have := Lookups.of_lookStar (γ := γ) n (.defp q)
        rw [hl] at this
        exact .app this
      · cases h
  | s, γ, .lett (.val v) t, s', γ', t', ρ, h => by
      simp only [stepFuel, Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [heq_eq_eq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .letVal
  | s, γ, .lett (.path p) t, s', γ', t', ρ, h => by
      simp only [stepFuel, Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [heq_eq_eq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .letPath
  | s, γ, .lett (.app q p) t, s', γ', t', ρ, h => by
      simp only [stepFuel] at h
      split at h
      · rename_i s'' γ'' t₀' ρ' h0
        simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h
        simp only [heq_eq_eq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .letTgt (Red.of_stepFuel h0)
      · cases h
  | s, γ, .lett (.lett t₀ t₁) t, s', γ', t', ρ, h => by
      simp only [stepFuel] at h
      split at h
      · rename_i s'' γ'' t₀' ρ' h0
        simp only [Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h
        simp only [heq_eq_eq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .letTgt (Red.of_stepFuel h0)
      · cases h
  | _, _, .path _, _, _, _, _, h => by
      simp only [stepFuel] at h
      cases h
  | _, _, .val _, _, _, _, _, h => by
      simp only [stepFuel] at h
      cases h

/-- At most `m` steps, each with lookup fuel `n`. -/
def runFuel (n : Nat) : Nat → Conf → Conf
  | 0, c => c
  | m+1, ⟨s, γ, t⟩ =>
      match stepFuel n γ t with
      | some ⟨s', γ', t', _⟩ => runFuel n m ⟨s', γ', t'⟩
      | none => ⟨s, γ, t⟩

theorem Reds.of_runFuel (n : Nat) : ∀ (m : Nat) (c : Conf), Reds c (runFuel n m c)
  | 0, _ => .refl
  | m+1, ⟨s, γ, t⟩ => by
      simp only [runFuel]
      split
      · rename_i s' γ' t' ρ h
        exact .step ⟨ρ, Red.of_stepFuel h⟩ (Reds.of_runFuel n m _)
      · exact .refl

/-! ## Regressions -/

/-- Two definitions at one label: `get` reads the newer (g9a1, `refute-d3.md:103-110`). -/
theorem Defs.get_shadow (ds : Defs s) (a : Label) (r₁ r₂ : Rhs s) :
    ((ds.cons a r₁).cons a r₂).get a = some r₂ :=
  if_pos rfl

abbrev c4r_b : Label := .trm 1
abbrev c4r_f : Label := .trm 3

/-- `y ↦ ν(w){f = λ(u) w}`, then `x ↦ ν(v){b = y}`.  `x` is `.here`, `y` is `.there .here`. -/
abbrev γC4r : Store ((([] : Sig),x),x) :=
  (Store.nil.cons (.new (Defs.nil.cons c4r_f (.defv (.lam (.path (.var (.there .here))))))))
    |>.cons (.new (Defs.nil.cons c4r_b (.defp (.var (.there .here)))))

/-- d1's C4 (`R_D1.lean:916`): `x.b.f ⤳ᴿ* λ(u) y`, the field opened at the location `y` by RL-SelV,
and not `λ(u) x.b`, the field opened at the written prefix. -/
theorem C4_runtime :
    Lookups γC4r (.defp (((Path.var .here).sel c4r_b).sel c4r_f))
      (.defv (.lam (.path (.var (.there (.there .here)))))) ∧
    Val.lam (.path (.var (.there (.there .here)))) ≠
      (Val.lam (.path ((Path.var (.there .here)).sel c4r_b)) : Val ((([] : Sig),x),x)) := by
  refine ⟨?_, by decide⟩
  have h : lookStar γC4r 4 (.defp (((Path.var .here).sel c4r_b).sel c4r_f))
      = .defv (.lam (.path (.var (.there (.there .here))))) := by decide +kernel
  exact h ▸ Lookups.of_lookStar 4 _

end PDot.Runtime
