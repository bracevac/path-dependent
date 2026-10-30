import Coercions.Nominal.FCn.Syntax

/-!
# FCn binding laws

The composition laws of renaming and of the two substitutions, for every family of `Syntax.lean`.
A law proved by recursion is one mutual block over the families of one inductive block, as in
`PDot/Source/Binding.lean`.  The laws of `Path` and `PathSubst` are the Paths target's
(`Paths/FCdot/RenameLemmas.lean`, `Paths/FCdot/TypingPathSubst.lean`).

The type-level families `Ty`, `Pr`, `Telescope`, `TyDefs`, `Block` and `Kids` get `rename_id`,
`rename_rename`, `subst_ofRename`, `rename_subst`, `subst_rename`, `subst_subst`, `weaken_substPath`
and `substPath_subst`.  The evidence and term families `PEq`, `PathCo`, `LeCo`, `EqCo`, `Morphism`,
`Side`, `Tm`, `Value`, `Defs` and `Rhs` get the same six composition laws over `CoSubst`, with
`subst_id`, `weaken_substCo` and `substCo_subst`.  `Frame` and `Cont` get `rename_id` and
`rename_rename`.  The laws of `CoSubst` itself come in the order the proofs need them: those that
read the path of evidence after `PathCo.path_rename` and `PathCo.path_subst`, the lifting laws after
the renaming laws of `PathCo`, and `CoSubst.one_comp` after `PathCo.weaken_substCo`.

No law moves a telescope across an opening, `tel (T⟨p⟩) = (tel T)⟨p⟩`, which is false
(`refute-d2.md:34`).  The one law that moves a type across an opening is `Ty.substPath_subst`.
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Type-level families: `rename_id` and `rename_rename` -/

mutual
theorem Ty.rename_id : ∀ (X : Ty s), X.rename Rename.id = X
  | .bot => rfl
  | .sel p A => by simp only [Ty.rename, Path.rename_id]
  | .pi S T => by simp only [Ty.rename, Rename.lift_id, Ty.rename_id S, Ty.rename_id T]
  | .mu Tel => by simp only [Ty.rename, Rename.lift_id, Telescope.rename_id Tel]
theorem Pr.rename_id : ∀ (X : Pr s), X.rename Rename.id = X
  | .le S T => by simp only [Pr.rename, Ty.rename_id S, Ty.rename_id T]
  | .fld a T => by simp only [Pr.rename, Ty.rename_id T]
  | .alias q => by simp only [Pr.rename, Path.rename_id]
  | .is T => by simp only [Pr.rename, Ty.rename_id T]
theorem Telescope.rename_id : ∀ (X : Telescope s), X.rename Rename.id = X
  | .nil => rfl
  | .cons Tel pr => by simp only [Telescope.rename, Telescope.rename_id Tel, Pr.rename_id pr]
end

mutual
theorem Ty.rename_rename : ∀ (X : Ty s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .bot, _, _ => rfl
  | .sel p A, ρ, ρ' => by simp only [Ty.rename, Path.rename_comp]
  | .pi S T, ρ, ρ' => by
      simp only [Ty.rename, Ty.rename_rename S ρ ρ', Ty.rename_rename T ρ.lift ρ'.lift,
        Rename.lift_comp]
  | .mu Tel, ρ, ρ' => by
      simp only [Ty.rename, Telescope.rename_rename Tel ρ.lift ρ'.lift, Rename.lift_comp]
theorem Pr.rename_rename : ∀ (X : Pr s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .le S T, ρ, ρ' => by simp only [Pr.rename, Ty.rename_rename S ρ ρ', Ty.rename_rename T ρ ρ']
  | .fld a T, ρ, ρ' => by simp only [Pr.rename, Ty.rename_rename T ρ ρ']
  | .alias q, ρ, ρ' => by simp only [Pr.rename, Path.rename_comp]
  | .is T, ρ, ρ' => by simp only [Pr.rename, Ty.rename_rename T ρ ρ']
theorem Telescope.rename_rename : ∀ (X : Telescope s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .nil, _, _ => rfl
  | .cons Tel pr, ρ, ρ' => by
      simp only [Telescope.rename, Telescope.rename_rename Tel ρ ρ', Pr.rename_rename pr ρ ρ']
end

/-! ## Type-level families: `subst_ofRename`, `rename_subst`, `subst_rename`, `subst_subst` -/

mutual
theorem Ty.subst_ofRename : ∀ (X : Ty s₁) (ρ : Rename s₁ s₂),
    X.subst (PathSubst.ofRename ρ) = X.rename ρ
  | .bot, _ => rfl
  | .sel p A, ρ => by simp only [Ty.subst, Ty.rename, Path.subst_ofRename]
  | .pi S T, ρ => by
      simp only [Ty.subst, Ty.rename, PathSubst.lift_ofRename, Ty.subst_ofRename S ρ,
        Ty.subst_ofRename T ρ.lift]
  | .mu Tel, ρ => by
      simp only [Ty.subst, Ty.rename, PathSubst.lift_ofRename, Telescope.subst_ofRename Tel ρ.lift]
theorem Pr.subst_ofRename : ∀ (X : Pr s₁) (ρ : Rename s₁ s₂),
    X.subst (PathSubst.ofRename ρ) = X.rename ρ
  | .le S T, ρ => by simp only [Pr.subst, Pr.rename, Ty.subst_ofRename S ρ, Ty.subst_ofRename T ρ]
  | .fld a T, ρ => by simp only [Pr.subst, Pr.rename, Ty.subst_ofRename T ρ]
  | .alias q, ρ => by simp only [Pr.subst, Pr.rename, Path.subst_ofRename]
  | .is T, ρ => by simp only [Pr.subst, Pr.rename, Ty.subst_ofRename T ρ]
theorem Telescope.subst_ofRename : ∀ (X : Telescope s₁) (ρ : Rename s₁ s₂),
    X.subst (PathSubst.ofRename ρ) = X.rename ρ
  | .nil, _ => rfl
  | .cons Tel pr, ρ => by
      simp only [Telescope.subst, Telescope.rename, Telescope.subst_ofRename Tel ρ,
        Pr.subst_ofRename pr ρ]
end

mutual
theorem Ty.rename_subst : ∀ (X : Ty s₁) (ρ : Rename s₁ s₂) (σ : PathSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (ρ.pathComp σ)
  | .bot, _, _ => rfl
  | .sel p A, ρ, σ => by simp only [Ty.rename, Ty.subst, Path.rename_subst]
  | .pi S T, ρ, σ => by
      simp only [Ty.rename, Ty.subst, Ty.rename_subst S ρ σ, Ty.rename_subst T ρ.lift σ.lift,
        Rename.lift_pathComp]
  | .mu Tel, ρ, σ => by
      simp only [Ty.rename, Ty.subst, Telescope.rename_subst Tel ρ.lift σ.lift,
        Rename.lift_pathComp]
theorem Pr.rename_subst : ∀ (X : Pr s₁) (ρ : Rename s₁ s₂) (σ : PathSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (ρ.pathComp σ)
  | .le S T, ρ, σ => by
      simp only [Pr.rename, Pr.subst, Ty.rename_subst S ρ σ, Ty.rename_subst T ρ σ]
  | .fld a T, ρ, σ => by simp only [Pr.rename, Pr.subst, Ty.rename_subst T ρ σ]
  | .alias q, ρ, σ => by simp only [Pr.rename, Pr.subst, Path.rename_subst]
  | .is T, ρ, σ => by simp only [Pr.rename, Pr.subst, Ty.rename_subst T ρ σ]
theorem Telescope.rename_subst : ∀ (X : Telescope s₁) (ρ : Rename s₁ s₂) (σ : PathSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (ρ.pathComp σ)
  | .nil, _, _ => rfl
  | .cons Tel pr, ρ, σ => by
      simp only [Telescope.rename, Telescope.subst, Telescope.rename_subst Tel ρ σ,
        Pr.rename_subst pr ρ σ]
end

mutual
theorem Ty.subst_rename : ∀ (X : Ty s₁) (σ : PathSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .bot, _, _ => rfl
  | .sel p A, σ, ρ => by simp only [Ty.subst, Ty.rename, Path.subst_rename]
  | .pi S T, σ, ρ => by
      simp only [Ty.subst, Ty.rename, Ty.subst_rename S σ ρ, Ty.subst_rename T σ.lift ρ.lift,
        PathSubst.lift_compRename]
  | .mu Tel, σ, ρ => by
      simp only [Ty.subst, Ty.rename, Telescope.subst_rename Tel σ.lift ρ.lift,
        PathSubst.lift_compRename]
theorem Pr.subst_rename : ∀ (X : Pr s₁) (σ : PathSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .le S T, σ, ρ => by
      simp only [Pr.subst, Pr.rename, Ty.subst_rename S σ ρ, Ty.subst_rename T σ ρ]
  | .fld a T, σ, ρ => by simp only [Pr.subst, Pr.rename, Ty.subst_rename T σ ρ]
  | .alias q, σ, ρ => by simp only [Pr.subst, Pr.rename, Path.subst_rename]
  | .is T, σ, ρ => by simp only [Pr.subst, Pr.rename, Ty.subst_rename T σ ρ]
theorem Telescope.subst_rename : ∀ (X : Telescope s₁) (σ : PathSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .nil, _, _ => rfl
  | .cons Tel pr, σ, ρ => by
      simp only [Telescope.subst, Telescope.rename, Telescope.subst_rename Tel σ ρ,
        Pr.subst_rename pr σ ρ]
end

mutual
theorem Ty.subst_subst : ∀ (X : Ty s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .bot, _, _ => rfl
  | .sel p A, σ, τ => by simp only [Ty.subst, Path.subst_subst]
  | .pi S T, σ, τ => by
      simp only [Ty.subst, Ty.subst_subst S σ τ, Ty.subst_subst T σ.lift τ.lift,
        PathSubst.comp_lift]
  | .mu Tel, σ, τ => by
      simp only [Ty.subst, Telescope.subst_subst Tel σ.lift τ.lift, PathSubst.comp_lift]
theorem Pr.subst_subst : ∀ (X : Pr s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .le S T, σ, τ => by simp only [Pr.subst, Ty.subst_subst S σ τ, Ty.subst_subst T σ τ]
  | .fld a T, σ, τ => by simp only [Pr.subst, Ty.subst_subst T σ τ]
  | .alias q, σ, τ => by simp only [Pr.subst, Path.subst_subst]
  | .is T, σ, τ => by simp only [Pr.subst, Ty.subst_subst T σ τ]
theorem Telescope.subst_subst : ∀ (X : Telescope s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .nil, _, _ => rfl
  | .cons Tel pr, σ, τ => by
      simp only [Telescope.subst, Telescope.subst_subst Tel σ τ, Pr.subst_subst pr σ τ]
end

/-! ## `TyDefs`, `Block` and `Kids`: the six composition laws -/

theorem TyDefs.rename_id : ∀ (X : TyDefs s), X.rename Rename.id = X
  | .nil => rfl
  | .cons W A U => by simp only [TyDefs.rename, TyDefs.rename_id W, Ty.rename_id U]
  | .cls W C U => by simp only [TyDefs.rename, TyDefs.rename_id W, Ty.rename_id U]

theorem TyDefs.rename_rename : ∀ (X : TyDefs s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .nil, _, _ => rfl
  | .cons W A U, ρ, ρ' => by
      simp only [TyDefs.rename, TyDefs.rename_rename W ρ ρ', Ty.rename_rename U ρ ρ']
  | .cls W C U, ρ, ρ' => by
      simp only [TyDefs.rename, TyDefs.rename_rename W ρ ρ', Ty.rename_rename U ρ ρ']

theorem TyDefs.subst_ofRename : ∀ (X : TyDefs s₁) (ρ : Rename s₁ s₂),
    X.subst (PathSubst.ofRename ρ) = X.rename ρ
  | .nil, _ => rfl
  | .cons W A U, ρ => by
      simp only [TyDefs.subst, TyDefs.rename, TyDefs.subst_ofRename W ρ, Ty.subst_ofRename U ρ]
  | .cls W C U, ρ => by
      simp only [TyDefs.subst, TyDefs.rename, TyDefs.subst_ofRename W ρ, Ty.subst_ofRename U ρ]

theorem TyDefs.rename_subst : ∀ (X : TyDefs s₁) (ρ : Rename s₁ s₂) (σ : PathSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (ρ.pathComp σ)
  | .nil, _, _ => rfl
  | .cons W A U, ρ, σ => by
      simp only [TyDefs.rename, TyDefs.subst, TyDefs.rename_subst W ρ σ, Ty.rename_subst U ρ σ]
  | .cls W C U, ρ, σ => by
      simp only [TyDefs.rename, TyDefs.subst, TyDefs.rename_subst W ρ σ, Ty.rename_subst U ρ σ]

theorem TyDefs.subst_rename : ∀ (X : TyDefs s₁) (σ : PathSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .nil, _, _ => rfl
  | .cons W A U, σ, ρ => by
      simp only [TyDefs.subst, TyDefs.rename, TyDefs.subst_rename W σ ρ, Ty.subst_rename U σ ρ]
  | .cls W C U, σ, ρ => by
      simp only [TyDefs.subst, TyDefs.rename, TyDefs.subst_rename W σ ρ, Ty.subst_rename U σ ρ]

theorem TyDefs.subst_subst : ∀ (X : TyDefs s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .nil, _, _ => rfl
  | .cons W A U, σ, τ => by
      simp only [TyDefs.subst, TyDefs.subst_subst W σ τ, Ty.subst_subst U σ τ]
  | .cls W C U, σ, τ => by
      simp only [TyDefs.subst, TyDefs.subst_subst W σ τ, Ty.subst_subst U σ τ]

mutual
theorem Block.rename_id : ∀ (X : Block s), X.rename Rename.id = X
  | .node W C => by simp only [Block.rename, TyDefs.rename_id W, Kids.rename_id C]
  | .fwd q => by simp only [Block.rename, Path.rename_id]
  | .clo => rfl
theorem Kids.rename_id : ∀ (X : Kids s), X.rename Rename.id = X
  | .nil => rfl
  | .cons C a B => by simp only [Kids.rename, Kids.rename_id C, Block.rename_id B]
end

mutual
theorem Block.rename_rename : ∀ (X : Block s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .node W C, ρ, ρ' => by
      simp only [Block.rename, TyDefs.rename_rename W ρ ρ', Kids.rename_rename C ρ ρ']
  | .fwd q, ρ, ρ' => by simp only [Block.rename, Path.rename_comp]
  | .clo, _, _ => rfl
theorem Kids.rename_rename : ∀ (X : Kids s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .nil, _, _ => rfl
  | .cons C a B, ρ, ρ' => by
      simp only [Kids.rename, Kids.rename_rename C ρ ρ', Block.rename_rename B ρ ρ']
end

mutual
theorem Block.subst_ofRename : ∀ (X : Block s₁) (ρ : Rename s₁ s₂),
    X.subst (PathSubst.ofRename ρ) = X.rename ρ
  | .node W C, ρ => by
      simp only [Block.subst, Block.rename, TyDefs.subst_ofRename W ρ, Kids.subst_ofRename C ρ]
  | .fwd q, ρ => by simp only [Block.subst, Block.rename, Path.subst_ofRename]
  | .clo, _ => rfl
theorem Kids.subst_ofRename : ∀ (X : Kids s₁) (ρ : Rename s₁ s₂),
    X.subst (PathSubst.ofRename ρ) = X.rename ρ
  | .nil, _ => rfl
  | .cons C a B, ρ => by
      simp only [Kids.subst, Kids.rename, Kids.subst_ofRename C ρ, Block.subst_ofRename B ρ]
end

mutual
theorem Block.rename_subst : ∀ (X : Block s₁) (ρ : Rename s₁ s₂) (σ : PathSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (ρ.pathComp σ)
  | .node W C, ρ, σ => by
      simp only [Block.rename, Block.subst, TyDefs.rename_subst W ρ σ, Kids.rename_subst C ρ σ]
  | .fwd q, ρ, σ => by simp only [Block.rename, Block.subst, Path.rename_subst]
  | .clo, _, _ => rfl
theorem Kids.rename_subst : ∀ (X : Kids s₁) (ρ : Rename s₁ s₂) (σ : PathSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (ρ.pathComp σ)
  | .nil, _, _ => rfl
  | .cons C a B, ρ, σ => by
      simp only [Kids.rename, Kids.subst, Kids.rename_subst C ρ σ, Block.rename_subst B ρ σ]
end

mutual
theorem Block.subst_rename : ∀ (X : Block s₁) (σ : PathSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .node W C, σ, ρ => by
      simp only [Block.subst, Block.rename, TyDefs.subst_rename W σ ρ, Kids.subst_rename C σ ρ]
  | .fwd q, σ, ρ => by simp only [Block.subst, Block.rename, Path.subst_rename]
  | .clo, _, _ => rfl
theorem Kids.subst_rename : ∀ (X : Kids s₁) (σ : PathSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .nil, _, _ => rfl
  | .cons C a B, σ, ρ => by
      simp only [Kids.subst, Kids.rename, Kids.subst_rename C σ ρ, Block.subst_rename B σ ρ]
end

mutual
theorem Block.subst_subst : ∀ (X : Block s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .node W C, σ, τ => by
      simp only [Block.subst, TyDefs.subst_subst W σ τ, Kids.subst_subst C σ τ]
  | .fwd q, σ, τ => by simp only [Block.subst, Path.subst_subst]
  | .clo, _, _ => rfl
theorem Kids.subst_subst : ∀ (X : Kids s₁) (σ : PathSubst s₁ s₂) (τ : PathSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .nil, _, _ => rfl
  | .cons C a B, σ, τ => by
      simp only [Kids.subst, Kids.subst_subst C σ τ, Block.subst_subst B σ τ]
end

/-! ## Type-level families: weakening and instantiation by a path

`weaken_substPath` is `rename_subst` at `Rename.succ`, where the path substitution of the
instantiation undoes the weakening (`PathSubst.succ_pathComp_one`).  `substPath_subst` is
`subst_subst` twice around `PathSubst.one_comp`. -/

theorem Ty.weaken_substPath (X : Ty s) (p : Path s) : X.weaken.substPath p = X := by
  rw [Ty.substPath, Ty.weaken, Ty.rename_subst, PathSubst.succ_pathComp_one, Ty.subst_ofRename,
    Ty.rename_id]

theorem Pr.weaken_substPath (X : Pr s) (p : Path s) : X.weaken.substPath p = X := by
  rw [Pr.substPath, Pr.weaken, Pr.rename_subst, PathSubst.succ_pathComp_one, Pr.subst_ofRename,
    Pr.rename_id]

theorem Telescope.weaken_substPath (X : Telescope s) (p : Path s) : X.weaken.substPath p = X := by
  rw [Telescope.substPath, Telescope.weaken, Telescope.rename_subst, PathSubst.succ_pathComp_one,
    Telescope.subst_ofRename, Telescope.rename_id]

theorem TyDefs.weaken_substPath (X : TyDefs s) (p : Path s) : X.weaken.substPath p = X := by
  rw [TyDefs.substPath, TyDefs.weaken, TyDefs.rename_subst, PathSubst.succ_pathComp_one,
    TyDefs.subst_ofRename, TyDefs.rename_id]

theorem Block.weaken_substPath (X : Block s) (p : Path s) : X.weaken.substPath p = X := by
  rw [Block.substPath, Block.weaken, Block.rename_subst, PathSubst.succ_pathComp_one,
    Block.subst_ofRename, Block.rename_id]

theorem Kids.weaken_substPath (X : Kids s) (p : Path s) : X.weaken.substPath p = X := by
  rw [Kids.substPath, Kids.weaken, Kids.rename_subst, PathSubst.succ_pathComp_one,
    Kids.subst_ofRename, Kids.rename_id]

theorem Ty.substPath_subst (X : Ty (s₁,x)) (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (X.substPath q).subst σ = (X.subst σ.lift).substPath (q.subst σ) := by
  rw [Ty.substPath, Ty.substPath, Ty.subst_subst, Ty.subst_subst, PathSubst.one_comp]

theorem Pr.substPath_subst (X : Pr (s₁,x)) (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (X.substPath q).subst σ = (X.subst σ.lift).substPath (q.subst σ) := by
  rw [Pr.substPath, Pr.substPath, Pr.subst_subst, Pr.subst_subst, PathSubst.one_comp]

theorem Telescope.substPath_subst (X : Telescope (s₁,x)) (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (X.substPath q).subst σ = (X.subst σ.lift).substPath (q.subst σ) := by
  rw [Telescope.substPath, Telescope.substPath, Telescope.subst_subst, Telescope.subst_subst,
    PathSubst.one_comp]

theorem TyDefs.substPath_subst (X : TyDefs (s₁,x)) (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (X.substPath q).subst σ = (X.subst σ.lift).substPath (q.subst σ) := by
  rw [TyDefs.substPath, TyDefs.substPath, TyDefs.subst_subst, TyDefs.subst_subst,
    PathSubst.one_comp]

theorem Block.substPath_subst (X : Block (s₁,x)) (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (X.substPath q).subst σ = (X.subst σ.lift).substPath (q.subst σ) := by
  rw [Block.substPath, Block.substPath, Block.subst_subst, Block.subst_subst, PathSubst.one_comp]

theorem Kids.substPath_subst (X : Kids (s₁,x)) (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (X.substPath q).subst σ = (X.subst σ.lift).substPath (q.subst σ) := by
  rw [Kids.substPath, Kids.substPath, Kids.subst_subst, Kids.subst_subst, PathSubst.one_comp]

/-! ## Evidence and term families: `rename_id` and `rename_rename` -/

mutual
theorem PEq.rename_id : ∀ (X : PEq s), X.rename Rename.id = X
  | .refl p => by simp only [PEq.rename, Path.rename_id]
  | .symm π => by simp only [PEq.rename, PEq.rename_id π]
  | .trans π π' => by simp only [PEq.rename, PEq.rename_id π, PEq.rename_id π']
  | .sel π a => by simp only [PEq.rename, PEq.rename_id π]
  | .member P e i => by simp only [PEq.rename, PathCo.rename_id P, LeCo.rename_id e]
theorem PathCo.rename_id : ∀ (X : PathCo s), X.rename Rename.id = X
  | .var _ => rfl
  | .sel P a i => by simp only [PathCo.rename, PathCo.rename_id P]
  | .cast P e => by simp only [PathCo.rename, PathCo.rename_id P, LeCo.rename_id e]
  | .alias P₀ π Q => by
      simp only [PathCo.rename, PathCo.rename_id P₀, PEq.rename_id π, PathCo.rename_id Q]
  | .sngl P q π => by
      simp only [PathCo.rename, PathCo.rename_id P, Path.rename_id, PEq.rename_id π]
  | .fldI p a Q => by simp only [PathCo.rename, Path.rename_id, PathCo.rename_id Q]
  | .fold Tel P => by
      simp only [PathCo.rename, Rename.lift_id, Telescope.rename_id, PathCo.rename_id P]
  | .unfold P => by simp only [PathCo.rename, PathCo.rename_id P]
  | .both Tel Tel' P Q => by
      simp only [PathCo.rename, Rename.lift_id, Telescope.rename_id, PathCo.rename_id P,
        PathCo.rename_id Q]
theorem LeCo.rename_id : ∀ (X : LeCo s), X.rename Rename.id = X
  | .refl T => by simp only [LeCo.rename, Ty.rename_id]
  | .trans e f => by simp only [LeCo.rename, LeCo.rename_id e, LeCo.rename_id f]
  | .top T => by simp only [LeCo.rename, Ty.rename_id]
  | .bot T => by simp only [LeCo.rename, Ty.rename_id]
  | .eqToLe φ => by simp only [LeCo.rename, EqCo.rename_id φ]
  | .pi e f => by simp only [LeCo.rename, Rename.lift_id, LeCo.rename_id e, LeCo.rename_id f]
  | .obj Tel m => by
      simp only [LeCo.rename, Rename.lift_id, Telescope.rename_id, Morphism.rename_id m]
  | .pair Tel Tel' e f => by
      simp only [LeCo.rename, Rename.lift_id, Telescope.rename_id, LeCo.rename_id e,
        LeCo.rename_id f]
  | .bound Tel i => by simp only [LeCo.rename, Rename.lift_id, Telescope.rename_id]
  | .intoBnd e => by simp only [LeCo.rename, LeCo.rename_id e]
  | .member P e i => by simp only [LeCo.rename, PathCo.rename_id P, LeCo.rename_id e]
  | .seal p C => by simp only [LeCo.rename, Path.rename_id]
theorem EqCo.rename_id : ∀ (X : EqCo s), X.rename Rename.id = X
  | .refl T => by simp only [EqCo.rename, Ty.rename_id]
  | .symm φ => by simp only [EqCo.rename, EqCo.rename_id φ]
  | .trans φ ψ => by simp only [EqCo.rename, EqCo.rename_id φ, EqCo.rename_id ψ]
  | .defP p A => by simp only [EqCo.rename, Path.rename_id]
  | .lift T π => by simp only [EqCo.rename, Rename.lift_id, Ty.rename_id, PEq.rename_id π]
  | .dom φ => by simp only [EqCo.rename, EqCo.rename_id φ]
  | .cod φ p => by simp only [EqCo.rename, EqCo.rename_id φ, Path.rename_id]
theorem Morphism.rename_id : ∀ (X : Morphism s), X.rename Rename.id = X
  | .nil => rfl
  | .le m pre j post => by
      simp only [Morphism.rename, Morphism.rename_id m, Side.rename_id pre, Side.rename_id post]
  | .fld m j sd => by simp only [Morphism.rename, Morphism.rename_id m, Side.rename_id sd]
  | .alias m j => by simp only [Morphism.rename, Morphism.rename_id m]
  | .is m e => by simp only [Morphism.rename, Morphism.rename_id m, LeCo.rename_id e]
theorem Side.rename_id : ∀ (X : Side s), X.rename Rename.id = X
  | .none => rfl
  | .some e => by simp only [Side.rename, LeCo.rename_id e]
  | .bot X => by simp only [Side.rename, Rename.lift_id, Ty.rename_id]
  | .top X => by simp only [Side.rename, Rename.lift_id, Ty.rename_id]
end

mutual
theorem Tm.rename_id : ∀ (X : Tm s), X.rename Rename.id = X
  | .path P => by simp only [Tm.rename, PathCo.rename_id]
  | .val v => by simp only [Tm.rename, Value.rename_id v]
  | .app P Q => by simp only [Tm.rename, PathCo.rename_id]
  | .lett t u => by simp only [Tm.rename, Rename.lift_id, Tm.rename_id t, Tm.rename_id u]
  | .cast t e => by simp only [Tm.rename, Tm.rename_id t, LeCo.rename_id]
theorem Value.rename_id : ∀ (X : Value s), X.rename Rename.id = X
  | .lam S t => by simp only [Value.rename, Rename.lift_id, Ty.rename_id, Tm.rename_id t]
  | .obj Tel ds => by
      simp only [Value.rename, Rename.lift_id, Telescope.rename_id, Defs.rename_id ds]
  | .cast v e => by simp only [Value.rename, Value.rename_id v, LeCo.rename_id]
theorem Defs.rename_id : ∀ (X : Defs s), X.rename Rename.id = X
  | .nil => rfl
  | .typ ds A U => by simp only [Defs.rename, Defs.rename_id ds, Ty.rename_id]
  | .fld ds a rhs => by simp only [Defs.rename, Defs.rename_id ds, Rhs.rename_id rhs]
  | .cls ds C U => by simp only [Defs.rename, Defs.rename_id ds, Ty.rename_id]
theorem Rhs.rename_id : ∀ (X : Rhs s), X.rename Rename.id = X
  | .path P => by simp only [Rhs.rename, PathCo.rename_id]
  | .fn v => by simp only [Rhs.rename, Value.rename_id v]
  | .nest Tel ds => by
      simp only [Rhs.rename, Rename.lift_id, Telescope.rename_id, Defs.rename_id ds]
end

theorem Frame.rename_id : ∀ (X : Frame s), X.rename Rename.id = X
  | .lett u => by simp only [Frame.rename, Rename.lift_id, Tm.rename_id]
  | .cast e => by simp only [Frame.rename, LeCo.rename_id]

theorem Cont.rename_id : ∀ (X : Cont s), X.rename Rename.id = X
  | .nil => rfl
  | .cons K fr => by simp only [Cont.rename, Cont.rename_id K, Frame.rename_id]

mutual
theorem PEq.rename_rename : ∀ (X : PEq s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .refl p, ρ, ρ' => by simp only [PEq.rename, Path.rename_comp]
  | .symm π, ρ, ρ' => by simp only [PEq.rename, PEq.rename_rename π ρ ρ']
  | .trans π π', ρ, ρ' => by
      simp only [PEq.rename, PEq.rename_rename π ρ ρ', PEq.rename_rename π' ρ ρ']
  | .sel π a, ρ, ρ' => by simp only [PEq.rename, PEq.rename_rename π ρ ρ']
  | .member P e i, ρ, ρ' => by
      simp only [PEq.rename, PathCo.rename_rename P ρ ρ', LeCo.rename_rename e ρ ρ']
theorem PathCo.rename_rename : ∀ (X : PathCo s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .var _, _, _ => rfl
  | .sel P a i, ρ, ρ' => by simp only [PathCo.rename, PathCo.rename_rename P ρ ρ']
  | .cast P e, ρ, ρ' => by
      simp only [PathCo.rename, PathCo.rename_rename P ρ ρ', LeCo.rename_rename e ρ ρ']
  | .alias P₀ π Q, ρ, ρ' => by
      simp only [PathCo.rename, PathCo.rename_rename P₀ ρ ρ', PEq.rename_rename π ρ ρ',
        PathCo.rename_rename Q ρ ρ']
  | .sngl P q π, ρ, ρ' => by
      simp only [PathCo.rename, PathCo.rename_rename P ρ ρ', Path.rename_comp,
        PEq.rename_rename π ρ ρ']
  | .fldI p a Q, ρ, ρ' => by
      simp only [PathCo.rename, Path.rename_comp, PathCo.rename_rename Q ρ ρ']
  | .fold Tel P, ρ, ρ' => by
      simp only [PathCo.rename, Telescope.rename_rename, Rename.lift_comp,
        PathCo.rename_rename P ρ ρ']
  | .unfold P, ρ, ρ' => by simp only [PathCo.rename, PathCo.rename_rename P ρ ρ']
  | .both Tel Tel' P Q, ρ, ρ' => by
      simp only [PathCo.rename, Telescope.rename_rename, Rename.lift_comp,
        PathCo.rename_rename P ρ ρ', PathCo.rename_rename Q ρ ρ']
theorem LeCo.rename_rename : ∀ (X : LeCo s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .refl T, ρ, ρ' => by simp only [LeCo.rename, Ty.rename_rename]
  | .trans e f, ρ, ρ' => by
      simp only [LeCo.rename, LeCo.rename_rename e ρ ρ', LeCo.rename_rename f ρ ρ']
  | .top T, ρ, ρ' => by simp only [LeCo.rename, Ty.rename_rename]
  | .bot T, ρ, ρ' => by simp only [LeCo.rename, Ty.rename_rename]
  | .eqToLe φ, ρ, ρ' => by simp only [LeCo.rename, EqCo.rename_rename φ ρ ρ']
  | .pi e f, ρ, ρ' => by
      simp only [LeCo.rename, LeCo.rename_rename e ρ ρ', LeCo.rename_rename f ρ.lift ρ'.lift,
        Rename.lift_comp]
  | .obj Tel m, ρ, ρ' => by
      simp only [LeCo.rename, Telescope.rename_rename, Rename.lift_comp,
        Morphism.rename_rename m ρ ρ']
  | .pair Tel Tel' e f, ρ, ρ' => by
      simp only [LeCo.rename, Telescope.rename_rename, Rename.lift_comp,
        LeCo.rename_rename e ρ ρ', LeCo.rename_rename f ρ ρ']
  | .bound Tel i, ρ, ρ' => by simp only [LeCo.rename, Telescope.rename_rename, Rename.lift_comp]
  | .intoBnd e, ρ, ρ' => by simp only [LeCo.rename, LeCo.rename_rename e ρ ρ']
  | .member P e i, ρ, ρ' => by
      simp only [LeCo.rename, PathCo.rename_rename P ρ ρ', LeCo.rename_rename e ρ ρ']
  | .seal p C, ρ, ρ' => by simp only [LeCo.rename, Path.rename_comp]
theorem EqCo.rename_rename : ∀ (X : EqCo s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .refl T, ρ, ρ' => by simp only [EqCo.rename, Ty.rename_rename]
  | .symm φ, ρ, ρ' => by simp only [EqCo.rename, EqCo.rename_rename φ ρ ρ']
  | .trans φ ψ, ρ, ρ' => by
      simp only [EqCo.rename, EqCo.rename_rename φ ρ ρ', EqCo.rename_rename ψ ρ ρ']
  | .defP p A, ρ, ρ' => by simp only [EqCo.rename, Path.rename_comp]
  | .lift T π, ρ, ρ' => by
      simp only [EqCo.rename, Ty.rename_rename, Rename.lift_comp, PEq.rename_rename π ρ ρ']
  | .dom φ, ρ, ρ' => by simp only [EqCo.rename, EqCo.rename_rename φ ρ ρ']
  | .cod φ p, ρ, ρ' => by simp only [EqCo.rename, EqCo.rename_rename φ ρ ρ', Path.rename_comp]
theorem Morphism.rename_rename : ∀ (X : Morphism s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .nil, _, _ => rfl
  | .le m pre j post, ρ, ρ' => by
      simp only [Morphism.rename, Morphism.rename_rename m ρ ρ', Side.rename_rename pre ρ ρ',
        Side.rename_rename post ρ ρ']
  | .fld m j sd, ρ, ρ' => by
      simp only [Morphism.rename, Morphism.rename_rename m ρ ρ', Side.rename_rename sd ρ ρ']
  | .alias m j, ρ, ρ' => by simp only [Morphism.rename, Morphism.rename_rename m ρ ρ']
  | .is m e, ρ, ρ' => by
      simp only [Morphism.rename, Morphism.rename_rename m ρ ρ', LeCo.rename_rename e ρ ρ']
theorem Side.rename_rename : ∀ (X : Side s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .none, _, _ => rfl
  | .some e, ρ, ρ' => by simp only [Side.rename, LeCo.rename_rename e ρ ρ']
  | .bot X, ρ, ρ' => by simp only [Side.rename, Ty.rename_rename, Rename.lift_comp]
  | .top X, ρ, ρ' => by simp only [Side.rename, Ty.rename_rename, Rename.lift_comp]
end

mutual
theorem Tm.rename_rename : ∀ (X : Tm s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .path P, ρ, ρ' => by simp only [Tm.rename, PathCo.rename_rename]
  | .val v, ρ, ρ' => by simp only [Tm.rename, Value.rename_rename v ρ ρ']
  | .app P Q, ρ, ρ' => by simp only [Tm.rename, PathCo.rename_rename]
  | .lett t u, ρ, ρ' => by
      simp only [Tm.rename, Tm.rename_rename t ρ ρ', Tm.rename_rename u ρ.lift ρ'.lift,
        Rename.lift_comp]
  | .cast t e, ρ, ρ' => by simp only [Tm.rename, Tm.rename_rename t ρ ρ', LeCo.rename_rename]
theorem Value.rename_rename : ∀ (X : Value s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .lam S t, ρ, ρ' => by
      simp only [Value.rename, Ty.rename_rename, Tm.rename_rename t ρ.lift ρ'.lift,
        Rename.lift_comp]
  | .obj Tel ds, ρ, ρ' => by
      simp only [Value.rename, Telescope.rename_rename, Defs.rename_rename ds ρ.lift ρ'.lift,
        Rename.lift_comp]
  | .cast v e, ρ, ρ' => by
      simp only [Value.rename, Value.rename_rename v ρ ρ', LeCo.rename_rename]
theorem Defs.rename_rename : ∀ (X : Defs s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .nil, _, _ => rfl
  | .typ ds A U, ρ, ρ' => by simp only [Defs.rename, Defs.rename_rename ds ρ ρ', Ty.rename_rename]
  | .fld ds a rhs, ρ, ρ' => by
      simp only [Defs.rename, Defs.rename_rename ds ρ ρ', Rhs.rename_rename rhs ρ ρ']
  | .cls ds C U, ρ, ρ' => by simp only [Defs.rename, Defs.rename_rename ds ρ ρ', Ty.rename_rename]
theorem Rhs.rename_rename : ∀ (X : Rhs s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .path P, ρ, ρ' => by simp only [Rhs.rename, PathCo.rename_rename]
  | .fn v, ρ, ρ' => by simp only [Rhs.rename, Value.rename_rename v ρ ρ']
  | .nest Tel ds, ρ, ρ' => by
      simp only [Rhs.rename, Telescope.rename_rename, Rename.lift_comp,
        Defs.rename_rename ds ρ ρ']
end

theorem Frame.rename_rename : ∀ (X : Frame s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .lett u, ρ, ρ' => by simp only [Frame.rename, Tm.rename_rename, Rename.lift_comp]
  | .cast e, ρ, ρ' => by simp only [Frame.rename, LeCo.rename_rename]

theorem Cont.rename_rename : ∀ (X : Cont s₁) (ρ : Rename s₁ s₂) (ρ' : Rename s₂ s₃),
    (X.rename ρ).rename ρ' = X.rename (ρ.comp ρ')
  | .nil, _, _ => rfl
  | .cons K fr, ρ, ρ' => by
      simp only [Cont.rename, Cont.rename_rename K ρ ρ', Frame.rename_rename]

/-! ## The path of evidence, and the paths of an evidence substitution -/

theorem PathCo.path_rename : ∀ (P : PathCo s₁) (ρ : Rename s₁ s₂),
    (P.rename ρ).path = P.path.rename ρ
  | .var _, _ => rfl
  | .sel P a _, ρ => congrArg (Path.sel · a) (PathCo.path_rename P ρ)
  | .cast P _, ρ => PathCo.path_rename P ρ
  | .alias P₀ _ _, ρ => PathCo.path_rename P₀ ρ
  | .sngl P _ _, ρ => PathCo.path_rename P ρ
  | .fldI _ _ _, _ => rfl
  | .fold _ P, ρ => PathCo.path_rename P ρ
  | .unfold P, ρ => PathCo.path_rename P ρ
  | .both _ _ P _, ρ => PathCo.path_rename P ρ

theorem PathCo.path_subst (σ : CoSubst s₁ s₂) : ∀ (P : PathCo s₁),
    (P.subst σ).path = P.path.subst σ.paths
  | .var _ => rfl
  | .sel P a _ => congrArg (Path.sel · a) (PathCo.path_subst σ P)
  | .cast P _ => PathCo.path_subst σ P
  | .alias P₀ _ _ => PathCo.path_subst σ P₀
  | .sngl P _ _ => PathCo.path_subst σ P
  | .fldI _ _ _ => rfl
  | .fold _ P => PathCo.path_subst σ P
  | .unfold P => PathCo.path_subst σ P
  | .both _ _ P _ => PathCo.path_subst σ P

/-- Two evidence substitutions that agree on every variable are equal. -/
theorem CoSubst.funext' {σ τ : CoSubst s₁ s₂} (h : ∀ x, σ.var x = τ.var x) : σ = τ := by
  cases σ
  cases τ
  exact congrArg CoSubst.mk (funext h)

theorem CoSubst.lift_paths (σ : CoSubst s₁ s₂) : σ.lift.paths = σ.paths.lift :=
  PathSubst.funext' fun x => by
    cases x with
    | here => rfl
    | there y => exact PathCo.path_rename (σ.var y) Rename.succ

theorem CoSubst.one_paths (Q : PathCo s) : (CoSubst.one Q).paths = PathSubst.one Q.path :=
  PathSubst.funext' fun x => by cases x <;> rfl

theorem CoSubst.ofRename_paths (ρ : Rename s₁ s₂) :
    (CoSubst.ofRename ρ).paths = PathSubst.ofRename ρ :=
  PathSubst.funext' fun _ => rfl

theorem CoSubst.id_paths : (CoSubst.id : CoSubst s s).paths = PathSubst.ofRename Rename.id :=
  PathSubst.funext' fun _ => rfl

theorem CoSubst.comp_paths (σ : CoSubst s₁ s₂) (τ : CoSubst s₂ s₃) :
    (σ.comp τ).paths = σ.paths.comp τ.paths :=
  PathSubst.funext' fun x => PathCo.path_subst τ (σ.var x)

theorem CoSubst.selfCast_paths (E : LeCo s) :
    (CoSubst.selfCast E).paths = PathSubst.ofRename Rename.id :=
  PathSubst.funext' fun x => by cases x <;> rfl

theorem CoSubst.compRename_paths (σ : CoSubst s₁ s₂) (ρ : Rename s₂ s₃) :
    (σ.compRename ρ).paths = σ.paths.compRename ρ :=
  PathSubst.funext' fun x => PathCo.path_rename (σ.var x) ρ

theorem Rename.coComp_paths (ρ : Rename s₁ s₂) (σ : CoSubst s₂ s₃) :
    (Rename.coComp ρ σ).paths = ρ.pathComp σ.paths :=
  PathSubst.funext' fun _ => rfl

/-! ## Lifting an evidence substitution -/

theorem CoSubst.ofRename_id : CoSubst.ofRename (Rename.id : Rename s s) = CoSubst.id := rfl

theorem CoSubst.lift_ofRename (ρ : Rename s₁ s₂) :
    (CoSubst.ofRename ρ).lift = CoSubst.ofRename ρ.lift :=
  CoSubst.funext' fun x => by cases x <;> rfl

theorem Rename.lift_coComp (ρ : Rename s₁ s₂) (σ : CoSubst s₂ s₃) :
    (Rename.coComp ρ σ).lift = Rename.coComp ρ.lift σ.lift :=
  CoSubst.funext' fun x => by cases x <;> rfl

theorem CoSubst.compRename_lift (σ : CoSubst s₁ s₂) (ρ : Rename s₂ s₃) :
    (σ.compRename ρ).lift = σ.lift.compRename ρ.lift :=
  CoSubst.funext' fun x => by
    cases x with
    | here => rfl
    | there y =>
        show ((σ.var y).rename ρ).rename Rename.succ = ((σ.var y).rename Rename.succ).rename ρ.lift
        rw [PathCo.rename_rename, PathCo.rename_rename, Rename.succ_lift]

/-- A weakening followed by a lifted substitution is the substitution followed by a
weakening. -/
theorem Rename.succ_coComp_lift (σ : CoSubst s₁ s₂) :
    Rename.coComp Rename.succ σ.lift = σ.compRename Rename.succ :=
  CoSubst.funext' fun _ => rfl

/-- Instantiating `.here` undoes a weakening. -/
theorem Rename.succ_coComp_one (Q : PathCo s) :
    Rename.coComp Rename.succ (CoSubst.one Q) = CoSubst.id :=
  CoSubst.funext' fun _ => rfl

/-! ## Evidence and term families: `subst_ofRename` -/

mutual
theorem PEq.subst_ofRename : ∀ (X : PEq s₁) (ρ : Rename s₁ s₂),
    X.subst (CoSubst.ofRename ρ) = X.rename ρ
  | .refl p, ρ => by simp only [PEq.subst, PEq.rename, CoSubst.ofRename_paths, Path.subst_ofRename]
  | .symm π, ρ => by simp only [PEq.subst, PEq.rename, PEq.subst_ofRename π ρ]
  | .trans π π', ρ => by
      simp only [PEq.subst, PEq.rename, PEq.subst_ofRename π ρ, PEq.subst_ofRename π' ρ]
  | .sel π a, ρ => by simp only [PEq.subst, PEq.rename, PEq.subst_ofRename π ρ]
  | .member P e i, ρ => by
      simp only [PEq.subst, PEq.rename, PathCo.subst_ofRename P ρ, LeCo.subst_ofRename e ρ]
theorem PathCo.subst_ofRename : ∀ (X : PathCo s₁) (ρ : Rename s₁ s₂),
    X.subst (CoSubst.ofRename ρ) = X.rename ρ
  | .var _, _ => rfl
  | .sel P a i, ρ => by simp only [PathCo.subst, PathCo.rename, PathCo.subst_ofRename P ρ]
  | .cast P e, ρ => by
      simp only [PathCo.subst, PathCo.rename, PathCo.subst_ofRename P ρ, LeCo.subst_ofRename e ρ]
  | .alias P₀ π Q, ρ => by
      simp only [PathCo.subst, PathCo.rename, PathCo.subst_ofRename P₀ ρ,
        PEq.subst_ofRename π ρ, PathCo.subst_ofRename Q ρ]
  | .sngl P q π, ρ => by
      simp only [PathCo.subst, PathCo.rename, PathCo.subst_ofRename P ρ, CoSubst.ofRename_paths,
        Path.subst_ofRename, PEq.subst_ofRename π ρ]
  | .fldI p a Q, ρ => by
      simp only [PathCo.subst, PathCo.rename, CoSubst.ofRename_paths, Path.subst_ofRename,
        PathCo.subst_ofRename Q ρ]
  | .fold Tel P, ρ => by
      simp only [PathCo.subst, PathCo.rename, CoSubst.ofRename_paths, PathSubst.lift_ofRename,
        Telescope.subst_ofRename, PathCo.subst_ofRename P ρ]
  | .unfold P, ρ => by simp only [PathCo.subst, PathCo.rename, PathCo.subst_ofRename P ρ]
  | .both Tel Tel' P Q, ρ => by
      simp only [PathCo.subst, PathCo.rename, CoSubst.ofRename_paths, PathSubst.lift_ofRename,
        Telescope.subst_ofRename, PathCo.subst_ofRename P ρ, PathCo.subst_ofRename Q ρ]
theorem LeCo.subst_ofRename : ∀ (X : LeCo s₁) (ρ : Rename s₁ s₂),
    X.subst (CoSubst.ofRename ρ) = X.rename ρ
  | .refl T, ρ => by
      simp only [LeCo.subst, LeCo.rename, CoSubst.ofRename_paths, Ty.subst_ofRename]
  | .trans e f, ρ => by
      simp only [LeCo.subst, LeCo.rename, LeCo.subst_ofRename e ρ, LeCo.subst_ofRename f ρ]
  | .top T, ρ => by
      simp only [LeCo.subst, LeCo.rename, CoSubst.ofRename_paths, Ty.subst_ofRename]
  | .bot T, ρ => by
      simp only [LeCo.subst, LeCo.rename, CoSubst.ofRename_paths, Ty.subst_ofRename]
  | .eqToLe φ, ρ => by simp only [LeCo.subst, LeCo.rename, EqCo.subst_ofRename φ ρ]
  | .pi e f, ρ => by
      simp only [LeCo.subst, LeCo.rename, LeCo.subst_ofRename e ρ, CoSubst.lift_ofRename,
        LeCo.subst_ofRename f ρ.lift]
  | .obj Tel m, ρ => by
      simp only [LeCo.subst, LeCo.rename, CoSubst.ofRename_paths, PathSubst.lift_ofRename,
        Telescope.subst_ofRename, Morphism.subst_ofRename m ρ]
  | .pair Tel Tel' e f, ρ => by
      simp only [LeCo.subst, LeCo.rename, CoSubst.ofRename_paths, PathSubst.lift_ofRename,
        Telescope.subst_ofRename, LeCo.subst_ofRename e ρ, LeCo.subst_ofRename f ρ]
  | .bound Tel i, ρ => by
      simp only [LeCo.subst, LeCo.rename, CoSubst.ofRename_paths, PathSubst.lift_ofRename,
        Telescope.subst_ofRename]
  | .intoBnd e, ρ => by simp only [LeCo.subst, LeCo.rename, LeCo.subst_ofRename e ρ]
  | .member P e i, ρ => by
      simp only [LeCo.subst, LeCo.rename, PathCo.subst_ofRename P ρ, LeCo.subst_ofRename e ρ]
  | .seal p C, ρ => by
      simp only [LeCo.subst, LeCo.rename, CoSubst.ofRename_paths, Path.subst_ofRename]
theorem EqCo.subst_ofRename : ∀ (X : EqCo s₁) (ρ : Rename s₁ s₂),
    X.subst (CoSubst.ofRename ρ) = X.rename ρ
  | .refl T, ρ => by
      simp only [EqCo.subst, EqCo.rename, CoSubst.ofRename_paths, Ty.subst_ofRename]
  | .symm φ, ρ => by simp only [EqCo.subst, EqCo.rename, EqCo.subst_ofRename φ ρ]
  | .trans φ ψ, ρ => by
      simp only [EqCo.subst, EqCo.rename, EqCo.subst_ofRename φ ρ, EqCo.subst_ofRename ψ ρ]
  | .defP p A, ρ => by
      simp only [EqCo.subst, EqCo.rename, CoSubst.ofRename_paths, Path.subst_ofRename]
  | .lift T π, ρ => by
      simp only [EqCo.subst, EqCo.rename, CoSubst.ofRename_paths, PathSubst.lift_ofRename,
        Ty.subst_ofRename, PEq.subst_ofRename π ρ]
  | .dom φ, ρ => by simp only [EqCo.subst, EqCo.rename, EqCo.subst_ofRename φ ρ]
  | .cod φ p, ρ => by
      simp only [EqCo.subst, EqCo.rename, EqCo.subst_ofRename φ ρ, CoSubst.ofRename_paths,
        Path.subst_ofRename]
theorem Morphism.subst_ofRename : ∀ (X : Morphism s₁) (ρ : Rename s₁ s₂),
    X.subst (CoSubst.ofRename ρ) = X.rename ρ
  | .nil, _ => rfl
  | .le m pre j post, ρ => by
      simp only [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m ρ,
        Side.subst_ofRename pre ρ, Side.subst_ofRename post ρ]
  | .fld m j sd, ρ => by
      simp only [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m ρ,
        Side.subst_ofRename sd ρ]
  | .alias m j, ρ => by simp only [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m ρ]
  | .is m e, ρ => by
      simp only [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m ρ,
        LeCo.subst_ofRename e ρ]
theorem Side.subst_ofRename : ∀ (X : Side s₁) (ρ : Rename s₁ s₂),
    X.subst (CoSubst.ofRename ρ) = X.rename ρ
  | .none, _ => rfl
  | .some e, ρ => by simp only [Side.subst, Side.rename, LeCo.subst_ofRename e ρ]
  | .bot X, ρ => by
      simp only [Side.subst, Side.rename, CoSubst.ofRename_paths, PathSubst.lift_ofRename,
        Ty.subst_ofRename]
  | .top X, ρ => by
      simp only [Side.subst, Side.rename, CoSubst.ofRename_paths, PathSubst.lift_ofRename,
        Ty.subst_ofRename]
end

mutual
theorem Tm.subst_ofRename : ∀ (X : Tm s₁) (ρ : Rename s₁ s₂),
    X.subst (CoSubst.ofRename ρ) = X.rename ρ
  | .path P, ρ => by simp only [Tm.subst, Tm.rename, PathCo.subst_ofRename]
  | .val v, ρ => by simp only [Tm.subst, Tm.rename, Value.subst_ofRename v ρ]
  | .app P Q, ρ => by simp only [Tm.subst, Tm.rename, PathCo.subst_ofRename]
  | .lett t u, ρ => by
      simp only [Tm.subst, Tm.rename, Tm.subst_ofRename t ρ, CoSubst.lift_ofRename,
        Tm.subst_ofRename u ρ.lift]
  | .cast t e, ρ => by simp only [Tm.subst, Tm.rename, Tm.subst_ofRename t ρ, LeCo.subst_ofRename]
theorem Value.subst_ofRename : ∀ (X : Value s₁) (ρ : Rename s₁ s₂),
    X.subst (CoSubst.ofRename ρ) = X.rename ρ
  | .lam S t, ρ => by
      simp only [Value.subst, Value.rename, CoSubst.ofRename_paths, Ty.subst_ofRename,
        CoSubst.lift_ofRename, Tm.subst_ofRename t ρ.lift]
  | .obj Tel ds, ρ => by
      simp only [Value.subst, Value.rename, CoSubst.ofRename_paths, PathSubst.lift_ofRename,
        Telescope.subst_ofRename, CoSubst.lift_ofRename, Defs.subst_ofRename ds ρ.lift]
  | .cast v e, ρ => by
      simp only [Value.subst, Value.rename, Value.subst_ofRename v ρ, LeCo.subst_ofRename]
theorem Defs.subst_ofRename : ∀ (X : Defs s₁) (ρ : Rename s₁ s₂),
    X.subst (CoSubst.ofRename ρ) = X.rename ρ
  | .nil, _ => rfl
  | .typ ds A U, ρ => by
      simp only [Defs.subst, Defs.rename, Defs.subst_ofRename ds ρ, CoSubst.ofRename_paths,
        Ty.subst_ofRename]
  | .fld ds a rhs, ρ => by
      simp only [Defs.subst, Defs.rename, Defs.subst_ofRename ds ρ, Rhs.subst_ofRename rhs ρ]
  | .cls ds C U, ρ => by
      simp only [Defs.subst, Defs.rename, Defs.subst_ofRename ds ρ, CoSubst.ofRename_paths,
        Ty.subst_ofRename]
theorem Rhs.subst_ofRename : ∀ (X : Rhs s₁) (ρ : Rename s₁ s₂),
    X.subst (CoSubst.ofRename ρ) = X.rename ρ
  | .path P, ρ => by simp only [Rhs.subst, Rhs.rename, PathCo.subst_ofRename]
  | .fn v, ρ => by simp only [Rhs.subst, Rhs.rename, Value.subst_ofRename v ρ]
  | .nest Tel ds, ρ => by
      simp only [Rhs.subst, Rhs.rename, CoSubst.ofRename_paths, PathSubst.lift_ofRename,
        Telescope.subst_ofRename, Defs.subst_ofRename ds ρ]
end

/-! ## Evidence and term families: `rename_subst` -/

mutual
theorem PEq.rename_subst : ∀ (X : PEq s₁) (ρ : Rename s₁ s₂) (σ : CoSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (Rename.coComp ρ σ)
  | .refl p, ρ, σ => by simp only [PEq.rename, PEq.subst, Path.rename_subst, Rename.coComp_paths]
  | .symm π, ρ, σ => by simp only [PEq.rename, PEq.subst, PEq.rename_subst π ρ σ]
  | .trans π π', ρ, σ => by
      simp only [PEq.rename, PEq.subst, PEq.rename_subst π ρ σ, PEq.rename_subst π' ρ σ]
  | .sel π a, ρ, σ => by simp only [PEq.rename, PEq.subst, PEq.rename_subst π ρ σ]
  | .member P e i, ρ, σ => by
      simp only [PEq.rename, PEq.subst, PathCo.rename_subst P ρ σ, LeCo.rename_subst e ρ σ]
theorem PathCo.rename_subst : ∀ (X : PathCo s₁) (ρ : Rename s₁ s₂) (σ : CoSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (Rename.coComp ρ σ)
  | .var _, _, _ => rfl
  | .sel P a i, ρ, σ => by simp only [PathCo.rename, PathCo.subst, PathCo.rename_subst P ρ σ]
  | .cast P e, ρ, σ => by
      simp only [PathCo.rename, PathCo.subst, PathCo.rename_subst P ρ σ, LeCo.rename_subst e ρ σ]
  | .alias P₀ π Q, ρ, σ => by
      simp only [PathCo.rename, PathCo.subst, PathCo.rename_subst P₀ ρ σ,
        PEq.rename_subst π ρ σ, PathCo.rename_subst Q ρ σ]
  | .sngl P q π, ρ, σ => by
      simp only [PathCo.rename, PathCo.subst, PathCo.rename_subst P ρ σ, Path.rename_subst,
        Rename.coComp_paths, PEq.rename_subst π ρ σ]
  | .fldI p a Q, ρ, σ => by
      simp only [PathCo.rename, PathCo.subst, Path.rename_subst, Rename.coComp_paths,
        PathCo.rename_subst Q ρ σ]
  | .fold Tel P, ρ, σ => by
      simp only [PathCo.rename, PathCo.subst, Telescope.rename_subst, Rename.coComp_paths,
        Rename.lift_pathComp, PathCo.rename_subst P ρ σ]
  | .unfold P, ρ, σ => by simp only [PathCo.rename, PathCo.subst, PathCo.rename_subst P ρ σ]
  | .both Tel Tel' P Q, ρ, σ => by
      simp only [PathCo.rename, PathCo.subst, Telescope.rename_subst, Rename.coComp_paths,
        Rename.lift_pathComp, PathCo.rename_subst P ρ σ, PathCo.rename_subst Q ρ σ]
theorem LeCo.rename_subst : ∀ (X : LeCo s₁) (ρ : Rename s₁ s₂) (σ : CoSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (Rename.coComp ρ σ)
  | .refl T, ρ, σ => by
      simp only [LeCo.rename, LeCo.subst, Ty.rename_subst, Rename.coComp_paths]
  | .trans e f, ρ, σ => by
      simp only [LeCo.rename, LeCo.subst, LeCo.rename_subst e ρ σ, LeCo.rename_subst f ρ σ]
  | .top T, ρ, σ => by
      simp only [LeCo.rename, LeCo.subst, Ty.rename_subst, Rename.coComp_paths]
  | .bot T, ρ, σ => by
      simp only [LeCo.rename, LeCo.subst, Ty.rename_subst, Rename.coComp_paths]
  | .eqToLe φ, ρ, σ => by simp only [LeCo.rename, LeCo.subst, EqCo.rename_subst φ ρ σ]
  | .pi e f, ρ, σ => by
      simp only [LeCo.rename, LeCo.subst, LeCo.rename_subst e ρ σ,
        LeCo.rename_subst f ρ.lift σ.lift, Rename.lift_coComp]
  | .obj Tel m, ρ, σ => by
      simp only [LeCo.rename, LeCo.subst, Telescope.rename_subst, Rename.coComp_paths,
        Rename.lift_pathComp, Morphism.rename_subst m ρ σ]
  | .pair Tel Tel' e f, ρ, σ => by
      simp only [LeCo.rename, LeCo.subst, Telescope.rename_subst, Rename.coComp_paths,
        Rename.lift_pathComp, LeCo.rename_subst e ρ σ, LeCo.rename_subst f ρ σ]
  | .bound Tel i, ρ, σ => by
      simp only [LeCo.rename, LeCo.subst, Telescope.rename_subst, Rename.coComp_paths,
        Rename.lift_pathComp]
  | .intoBnd e, ρ, σ => by simp only [LeCo.rename, LeCo.subst, LeCo.rename_subst e ρ σ]
  | .member P e i, ρ, σ => by
      simp only [LeCo.rename, LeCo.subst, PathCo.rename_subst P ρ σ, LeCo.rename_subst e ρ σ]
  | .seal p C, ρ, σ => by
      simp only [LeCo.rename, LeCo.subst, Path.rename_subst, Rename.coComp_paths]
theorem EqCo.rename_subst : ∀ (X : EqCo s₁) (ρ : Rename s₁ s₂) (σ : CoSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (Rename.coComp ρ σ)
  | .refl T, ρ, σ => by
      simp only [EqCo.rename, EqCo.subst, Ty.rename_subst, Rename.coComp_paths]
  | .symm φ, ρ, σ => by simp only [EqCo.rename, EqCo.subst, EqCo.rename_subst φ ρ σ]
  | .trans φ ψ, ρ, σ => by
      simp only [EqCo.rename, EqCo.subst, EqCo.rename_subst φ ρ σ, EqCo.rename_subst ψ ρ σ]
  | .defP p A, ρ, σ => by
      simp only [EqCo.rename, EqCo.subst, Path.rename_subst, Rename.coComp_paths]
  | .lift T π, ρ, σ => by
      simp only [EqCo.rename, EqCo.subst, Ty.rename_subst, Rename.coComp_paths,
        Rename.lift_pathComp, PEq.rename_subst π ρ σ]
  | .dom φ, ρ, σ => by simp only [EqCo.rename, EqCo.subst, EqCo.rename_subst φ ρ σ]
  | .cod φ p, ρ, σ => by
      simp only [EqCo.rename, EqCo.subst, EqCo.rename_subst φ ρ σ, Path.rename_subst,
        Rename.coComp_paths]
theorem Morphism.rename_subst : ∀ (X : Morphism s₁) (ρ : Rename s₁ s₂) (σ : CoSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (Rename.coComp ρ σ)
  | .nil, _, _ => rfl
  | .le m pre j post, ρ, σ => by
      simp only [Morphism.rename, Morphism.subst, Morphism.rename_subst m ρ σ,
        Side.rename_subst pre ρ σ, Side.rename_subst post ρ σ]
  | .fld m j sd, ρ, σ => by
      simp only [Morphism.rename, Morphism.subst, Morphism.rename_subst m ρ σ,
        Side.rename_subst sd ρ σ]
  | .alias m j, ρ, σ => by
      simp only [Morphism.rename, Morphism.subst, Morphism.rename_subst m ρ σ]
  | .is m e, ρ, σ => by
      simp only [Morphism.rename, Morphism.subst, Morphism.rename_subst m ρ σ,
        LeCo.rename_subst e ρ σ]
theorem Side.rename_subst : ∀ (X : Side s₁) (ρ : Rename s₁ s₂) (σ : CoSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (Rename.coComp ρ σ)
  | .none, _, _ => rfl
  | .some e, ρ, σ => by simp only [Side.rename, Side.subst, LeCo.rename_subst e ρ σ]
  | .bot X, ρ, σ => by
      simp only [Side.rename, Side.subst, Ty.rename_subst, Rename.coComp_paths,
        Rename.lift_pathComp]
  | .top X, ρ, σ => by
      simp only [Side.rename, Side.subst, Ty.rename_subst, Rename.coComp_paths,
        Rename.lift_pathComp]
end

mutual
theorem Tm.rename_subst : ∀ (X : Tm s₁) (ρ : Rename s₁ s₂) (σ : CoSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (Rename.coComp ρ σ)
  | .path P, ρ, σ => by simp only [Tm.rename, Tm.subst, PathCo.rename_subst]
  | .val v, ρ, σ => by simp only [Tm.rename, Tm.subst, Value.rename_subst v ρ σ]
  | .app P Q, ρ, σ => by simp only [Tm.rename, Tm.subst, PathCo.rename_subst]
  | .lett t u, ρ, σ => by
      simp only [Tm.rename, Tm.subst, Tm.rename_subst t ρ σ, Tm.rename_subst u ρ.lift σ.lift,
        Rename.lift_coComp]
  | .cast t e, ρ, σ => by
      simp only [Tm.rename, Tm.subst, Tm.rename_subst t ρ σ, LeCo.rename_subst]
theorem Value.rename_subst : ∀ (X : Value s₁) (ρ : Rename s₁ s₂) (σ : CoSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (Rename.coComp ρ σ)
  | .lam S t, ρ, σ => by
      simp only [Value.rename, Value.subst, Ty.rename_subst, Rename.coComp_paths,
        Tm.rename_subst t ρ.lift σ.lift, Rename.lift_coComp]
  | .obj Tel ds, ρ, σ => by
      simp only [Value.rename, Value.subst, Telescope.rename_subst, Rename.coComp_paths,
        Rename.lift_pathComp, Defs.rename_subst ds ρ.lift σ.lift, Rename.lift_coComp]
  | .cast v e, ρ, σ => by
      simp only [Value.rename, Value.subst, Value.rename_subst v ρ σ, LeCo.rename_subst]
theorem Defs.rename_subst : ∀ (X : Defs s₁) (ρ : Rename s₁ s₂) (σ : CoSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (Rename.coComp ρ σ)
  | .nil, _, _ => rfl
  | .typ ds A U, ρ, σ => by
      simp only [Defs.rename, Defs.subst, Defs.rename_subst ds ρ σ, Ty.rename_subst,
        Rename.coComp_paths]
  | .fld ds a rhs, ρ, σ => by
      simp only [Defs.rename, Defs.subst, Defs.rename_subst ds ρ σ, Rhs.rename_subst rhs ρ σ]
  | .cls ds C U, ρ, σ => by
      simp only [Defs.rename, Defs.subst, Defs.rename_subst ds ρ σ, Ty.rename_subst,
        Rename.coComp_paths]
theorem Rhs.rename_subst : ∀ (X : Rhs s₁) (ρ : Rename s₁ s₂) (σ : CoSubst s₂ s₃),
    (X.rename ρ).subst σ = X.subst (Rename.coComp ρ σ)
  | .path P, ρ, σ => by simp only [Rhs.rename, Rhs.subst, PathCo.rename_subst]
  | .fn v, ρ, σ => by simp only [Rhs.rename, Rhs.subst, Value.rename_subst v ρ σ]
  | .nest Tel ds, ρ, σ => by
      simp only [Rhs.rename, Rhs.subst, Telescope.rename_subst, Rename.coComp_paths,
        Rename.lift_pathComp, Defs.rename_subst ds ρ σ]
end

/-! ## Evidence and term families: `subst_rename` -/

mutual
theorem PEq.subst_rename : ∀ (X : PEq s₁) (σ : CoSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .refl p, σ, ρ => by
      simp only [PEq.subst, PEq.rename, Path.subst_rename, CoSubst.compRename_paths]
  | .symm π, σ, ρ => by simp only [PEq.subst, PEq.rename, PEq.subst_rename π σ ρ]
  | .trans π π', σ, ρ => by
      simp only [PEq.subst, PEq.rename, PEq.subst_rename π σ ρ, PEq.subst_rename π' σ ρ]
  | .sel π a, σ, ρ => by simp only [PEq.subst, PEq.rename, PEq.subst_rename π σ ρ]
  | .member P e i, σ, ρ => by
      simp only [PEq.subst, PEq.rename, PathCo.subst_rename P σ ρ, LeCo.subst_rename e σ ρ]
theorem PathCo.subst_rename : ∀ (X : PathCo s₁) (σ : CoSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .var _, _, _ => rfl
  | .sel P a i, σ, ρ => by simp only [PathCo.subst, PathCo.rename, PathCo.subst_rename P σ ρ]
  | .cast P e, σ, ρ => by
      simp only [PathCo.subst, PathCo.rename, PathCo.subst_rename P σ ρ, LeCo.subst_rename e σ ρ]
  | .alias P₀ π Q, σ, ρ => by
      simp only [PathCo.subst, PathCo.rename, PathCo.subst_rename P₀ σ ρ,
        PEq.subst_rename π σ ρ, PathCo.subst_rename Q σ ρ]
  | .sngl P q π, σ, ρ => by
      simp only [PathCo.subst, PathCo.rename, PathCo.subst_rename P σ ρ, Path.subst_rename,
        CoSubst.compRename_paths, PEq.subst_rename π σ ρ]
  | .fldI p a Q, σ, ρ => by
      simp only [PathCo.subst, PathCo.rename, Path.subst_rename, CoSubst.compRename_paths,
        PathCo.subst_rename Q σ ρ]
  | .fold Tel P, σ, ρ => by
      simp only [PathCo.subst, PathCo.rename, Telescope.subst_rename, CoSubst.compRename_paths,
        PathSubst.lift_compRename, PathCo.subst_rename P σ ρ]
  | .unfold P, σ, ρ => by simp only [PathCo.subst, PathCo.rename, PathCo.subst_rename P σ ρ]
  | .both Tel Tel' P Q, σ, ρ => by
      simp only [PathCo.subst, PathCo.rename, Telescope.subst_rename, CoSubst.compRename_paths,
        PathSubst.lift_compRename, PathCo.subst_rename P σ ρ, PathCo.subst_rename Q σ ρ]
theorem LeCo.subst_rename : ∀ (X : LeCo s₁) (σ : CoSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .refl T, σ, ρ => by
      simp only [LeCo.subst, LeCo.rename, Ty.subst_rename, CoSubst.compRename_paths]
  | .trans e f, σ, ρ => by
      simp only [LeCo.subst, LeCo.rename, LeCo.subst_rename e σ ρ, LeCo.subst_rename f σ ρ]
  | .top T, σ, ρ => by
      simp only [LeCo.subst, LeCo.rename, Ty.subst_rename, CoSubst.compRename_paths]
  | .bot T, σ, ρ => by
      simp only [LeCo.subst, LeCo.rename, Ty.subst_rename, CoSubst.compRename_paths]
  | .eqToLe φ, σ, ρ => by simp only [LeCo.subst, LeCo.rename, EqCo.subst_rename φ σ ρ]
  | .pi e f, σ, ρ => by
      simp only [LeCo.subst, LeCo.rename, LeCo.subst_rename e σ ρ,
        LeCo.subst_rename f σ.lift ρ.lift, CoSubst.compRename_lift]
  | .obj Tel m, σ, ρ => by
      simp only [LeCo.subst, LeCo.rename, Telescope.subst_rename, CoSubst.compRename_paths,
        PathSubst.lift_compRename, Morphism.subst_rename m σ ρ]
  | .pair Tel Tel' e f, σ, ρ => by
      simp only [LeCo.subst, LeCo.rename, Telescope.subst_rename, CoSubst.compRename_paths,
        PathSubst.lift_compRename, LeCo.subst_rename e σ ρ, LeCo.subst_rename f σ ρ]
  | .bound Tel i, σ, ρ => by
      simp only [LeCo.subst, LeCo.rename, Telescope.subst_rename, CoSubst.compRename_paths,
        PathSubst.lift_compRename]
  | .intoBnd e, σ, ρ => by simp only [LeCo.subst, LeCo.rename, LeCo.subst_rename e σ ρ]
  | .member P e i, σ, ρ => by
      simp only [LeCo.subst, LeCo.rename, PathCo.subst_rename P σ ρ, LeCo.subst_rename e σ ρ]
  | .seal p C, σ, ρ => by
      simp only [LeCo.subst, LeCo.rename, Path.subst_rename, CoSubst.compRename_paths]
theorem EqCo.subst_rename : ∀ (X : EqCo s₁) (σ : CoSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .refl T, σ, ρ => by
      simp only [EqCo.subst, EqCo.rename, Ty.subst_rename, CoSubst.compRename_paths]
  | .symm φ, σ, ρ => by simp only [EqCo.subst, EqCo.rename, EqCo.subst_rename φ σ ρ]
  | .trans φ ψ, σ, ρ => by
      simp only [EqCo.subst, EqCo.rename, EqCo.subst_rename φ σ ρ, EqCo.subst_rename ψ σ ρ]
  | .defP p A, σ, ρ => by
      simp only [EqCo.subst, EqCo.rename, Path.subst_rename, CoSubst.compRename_paths]
  | .lift T π, σ, ρ => by
      simp only [EqCo.subst, EqCo.rename, Ty.subst_rename, CoSubst.compRename_paths,
        PathSubst.lift_compRename, PEq.subst_rename π σ ρ]
  | .dom φ, σ, ρ => by simp only [EqCo.subst, EqCo.rename, EqCo.subst_rename φ σ ρ]
  | .cod φ p, σ, ρ => by
      simp only [EqCo.subst, EqCo.rename, EqCo.subst_rename φ σ ρ, Path.subst_rename,
        CoSubst.compRename_paths]
theorem Morphism.subst_rename : ∀ (X : Morphism s₁) (σ : CoSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .nil, _, _ => rfl
  | .le m pre j post, σ, ρ => by
      simp only [Morphism.subst, Morphism.rename, Morphism.subst_rename m σ ρ,
        Side.subst_rename pre σ ρ, Side.subst_rename post σ ρ]
  | .fld m j sd, σ, ρ => by
      simp only [Morphism.subst, Morphism.rename, Morphism.subst_rename m σ ρ,
        Side.subst_rename sd σ ρ]
  | .alias m j, σ, ρ => by
      simp only [Morphism.subst, Morphism.rename, Morphism.subst_rename m σ ρ]
  | .is m e, σ, ρ => by
      simp only [Morphism.subst, Morphism.rename, Morphism.subst_rename m σ ρ,
        LeCo.subst_rename e σ ρ]
theorem Side.subst_rename : ∀ (X : Side s₁) (σ : CoSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .none, _, _ => rfl
  | .some e, σ, ρ => by simp only [Side.subst, Side.rename, LeCo.subst_rename e σ ρ]
  | .bot X, σ, ρ => by
      simp only [Side.subst, Side.rename, Ty.subst_rename, CoSubst.compRename_paths,
        PathSubst.lift_compRename]
  | .top X, σ, ρ => by
      simp only [Side.subst, Side.rename, Ty.subst_rename, CoSubst.compRename_paths,
        PathSubst.lift_compRename]
end

mutual
theorem Tm.subst_rename : ∀ (X : Tm s₁) (σ : CoSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .path P, σ, ρ => by simp only [Tm.subst, Tm.rename, PathCo.subst_rename]
  | .val v, σ, ρ => by simp only [Tm.subst, Tm.rename, Value.subst_rename v σ ρ]
  | .app P Q, σ, ρ => by simp only [Tm.subst, Tm.rename, PathCo.subst_rename]
  | .lett t u, σ, ρ => by
      simp only [Tm.subst, Tm.rename, Tm.subst_rename t σ ρ, Tm.subst_rename u σ.lift ρ.lift,
        CoSubst.compRename_lift]
  | .cast t e, σ, ρ => by
      simp only [Tm.subst, Tm.rename, Tm.subst_rename t σ ρ, LeCo.subst_rename]
theorem Value.subst_rename : ∀ (X : Value s₁) (σ : CoSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .lam S t, σ, ρ => by
      simp only [Value.subst, Value.rename, Ty.subst_rename, CoSubst.compRename_paths,
        Tm.subst_rename t σ.lift ρ.lift, CoSubst.compRename_lift]
  | .obj Tel ds, σ, ρ => by
      simp only [Value.subst, Value.rename, Telescope.subst_rename, CoSubst.compRename_paths,
        PathSubst.lift_compRename, Defs.subst_rename ds σ.lift ρ.lift, CoSubst.compRename_lift]
  | .cast v e, σ, ρ => by
      simp only [Value.subst, Value.rename, Value.subst_rename v σ ρ, LeCo.subst_rename]
theorem Defs.subst_rename : ∀ (X : Defs s₁) (σ : CoSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .nil, _, _ => rfl
  | .typ ds A U, σ, ρ => by
      simp only [Defs.subst, Defs.rename, Defs.subst_rename ds σ ρ, Ty.subst_rename,
        CoSubst.compRename_paths]
  | .fld ds a rhs, σ, ρ => by
      simp only [Defs.subst, Defs.rename, Defs.subst_rename ds σ ρ, Rhs.subst_rename rhs σ ρ]
  | .cls ds C U, σ, ρ => by
      simp only [Defs.subst, Defs.rename, Defs.subst_rename ds σ ρ, Ty.subst_rename,
        CoSubst.compRename_paths]
theorem Rhs.subst_rename : ∀ (X : Rhs s₁) (σ : CoSubst s₁ s₂) (ρ : Rename s₂ s₃),
    (X.subst σ).rename ρ = X.subst (σ.compRename ρ)
  | .path P, σ, ρ => by simp only [Rhs.subst, Rhs.rename, PathCo.subst_rename]
  | .fn v, σ, ρ => by simp only [Rhs.subst, Rhs.rename, Value.subst_rename v σ ρ]
  | .nest Tel ds, σ, ρ => by
      simp only [Rhs.subst, Rhs.rename, Telescope.subst_rename, CoSubst.compRename_paths,
        PathSubst.lift_compRename, Defs.subst_rename ds σ ρ]
end

/-! ## Composing evidence substitutions -/

theorem CoSubst.comp_lift (σ : CoSubst s₁ s₂) (τ : CoSubst s₂ s₃) :
    (σ.comp τ).lift = σ.lift.comp τ.lift :=
  CoSubst.funext' fun x => by
    cases x with
    | here => rfl
    | there y =>
        show ((σ.var y).subst τ).rename Rename.succ = ((σ.var y).rename Rename.succ).subst τ.lift
        rw [PathCo.subst_rename, PathCo.rename_subst, Rename.succ_coComp_lift]

mutual
theorem PEq.subst_subst : ∀ (X : PEq s₁) (σ : CoSubst s₁ s₂) (τ : CoSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .refl p, σ, τ => by simp only [PEq.subst, Path.subst_subst, CoSubst.comp_paths]
  | .symm π, σ, τ => by simp only [PEq.subst, PEq.subst_subst π σ τ]
  | .trans π π', σ, τ => by simp only [PEq.subst, PEq.subst_subst π σ τ, PEq.subst_subst π' σ τ]
  | .sel π a, σ, τ => by simp only [PEq.subst, PEq.subst_subst π σ τ]
  | .member P e i, σ, τ => by
      simp only [PEq.subst, PathCo.subst_subst P σ τ, LeCo.subst_subst e σ τ]
theorem PathCo.subst_subst : ∀ (X : PathCo s₁) (σ : CoSubst s₁ s₂) (τ : CoSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .var _, _, _ => rfl
  | .sel P a i, σ, τ => by simp only [PathCo.subst, PathCo.subst_subst P σ τ]
  | .cast P e, σ, τ => by
      simp only [PathCo.subst, PathCo.subst_subst P σ τ, LeCo.subst_subst e σ τ]
  | .alias P₀ π Q, σ, τ => by
      simp only [PathCo.subst, PathCo.subst_subst P₀ σ τ, PEq.subst_subst π σ τ,
        PathCo.subst_subst Q σ τ]
  | .sngl P q π, σ, τ => by
      simp only [PathCo.subst, PathCo.subst_subst P σ τ, Path.subst_subst, CoSubst.comp_paths,
        PEq.subst_subst π σ τ]
  | .fldI p a Q, σ, τ => by
      simp only [PathCo.subst, Path.subst_subst, CoSubst.comp_paths, PathCo.subst_subst Q σ τ]
  | .fold Tel P, σ, τ => by
      simp only [PathCo.subst, Telescope.subst_subst, CoSubst.comp_paths, PathSubst.comp_lift,
        PathCo.subst_subst P σ τ]
  | .unfold P, σ, τ => by simp only [PathCo.subst, PathCo.subst_subst P σ τ]
  | .both Tel Tel' P Q, σ, τ => by
      simp only [PathCo.subst, Telescope.subst_subst, CoSubst.comp_paths, PathSubst.comp_lift,
        PathCo.subst_subst P σ τ, PathCo.subst_subst Q σ τ]
theorem LeCo.subst_subst : ∀ (X : LeCo s₁) (σ : CoSubst s₁ s₂) (τ : CoSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .refl T, σ, τ => by simp only [LeCo.subst, Ty.subst_subst, CoSubst.comp_paths]
  | .trans e f, σ, τ => by
      simp only [LeCo.subst, LeCo.subst_subst e σ τ, LeCo.subst_subst f σ τ]
  | .top T, σ, τ => by simp only [LeCo.subst, Ty.subst_subst, CoSubst.comp_paths]
  | .bot T, σ, τ => by simp only [LeCo.subst, Ty.subst_subst, CoSubst.comp_paths]
  | .eqToLe φ, σ, τ => by simp only [LeCo.subst, EqCo.subst_subst φ σ τ]
  | .pi e f, σ, τ => by
      simp only [LeCo.subst, LeCo.subst_subst e σ τ, LeCo.subst_subst f σ.lift τ.lift,
        CoSubst.comp_lift]
  | .obj Tel m, σ, τ => by
      simp only [LeCo.subst, Telescope.subst_subst, CoSubst.comp_paths, PathSubst.comp_lift,
        Morphism.subst_subst m σ τ]
  | .pair Tel Tel' e f, σ, τ => by
      simp only [LeCo.subst, Telescope.subst_subst, CoSubst.comp_paths, PathSubst.comp_lift,
        LeCo.subst_subst e σ τ, LeCo.subst_subst f σ τ]
  | .bound Tel i, σ, τ => by
      simp only [LeCo.subst, Telescope.subst_subst, CoSubst.comp_paths, PathSubst.comp_lift]
  | .intoBnd e, σ, τ => by simp only [LeCo.subst, LeCo.subst_subst e σ τ]
  | .member P e i, σ, τ => by
      simp only [LeCo.subst, PathCo.subst_subst P σ τ, LeCo.subst_subst e σ τ]
  | .seal p C, σ, τ => by simp only [LeCo.subst, Path.subst_subst, CoSubst.comp_paths]
theorem EqCo.subst_subst : ∀ (X : EqCo s₁) (σ : CoSubst s₁ s₂) (τ : CoSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .refl T, σ, τ => by simp only [EqCo.subst, Ty.subst_subst, CoSubst.comp_paths]
  | .symm φ, σ, τ => by simp only [EqCo.subst, EqCo.subst_subst φ σ τ]
  | .trans φ ψ, σ, τ => by
      simp only [EqCo.subst, EqCo.subst_subst φ σ τ, EqCo.subst_subst ψ σ τ]
  | .defP p A, σ, τ => by simp only [EqCo.subst, Path.subst_subst, CoSubst.comp_paths]
  | .lift T π, σ, τ => by
      simp only [EqCo.subst, Ty.subst_subst, CoSubst.comp_paths, PathSubst.comp_lift,
        PEq.subst_subst π σ τ]
  | .dom φ, σ, τ => by simp only [EqCo.subst, EqCo.subst_subst φ σ τ]
  | .cod φ p, σ, τ => by
      simp only [EqCo.subst, EqCo.subst_subst φ σ τ, Path.subst_subst, CoSubst.comp_paths]
theorem Morphism.subst_subst : ∀ (X : Morphism s₁) (σ : CoSubst s₁ s₂) (τ : CoSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .nil, _, _ => rfl
  | .le m pre j post, σ, τ => by
      simp only [Morphism.subst, Morphism.subst_subst m σ τ, Side.subst_subst pre σ τ,
        Side.subst_subst post σ τ]
  | .fld m j sd, σ, τ => by
      simp only [Morphism.subst, Morphism.subst_subst m σ τ, Side.subst_subst sd σ τ]
  | .alias m j, σ, τ => by simp only [Morphism.subst, Morphism.subst_subst m σ τ]
  | .is m e, σ, τ => by
      simp only [Morphism.subst, Morphism.subst_subst m σ τ, LeCo.subst_subst e σ τ]
theorem Side.subst_subst : ∀ (X : Side s₁) (σ : CoSubst s₁ s₂) (τ : CoSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .none, _, _ => rfl
  | .some e, σ, τ => by simp only [Side.subst, LeCo.subst_subst e σ τ]
  | .bot X, σ, τ => by
      simp only [Side.subst, Ty.subst_subst, CoSubst.comp_paths, PathSubst.comp_lift]
  | .top X, σ, τ => by
      simp only [Side.subst, Ty.subst_subst, CoSubst.comp_paths, PathSubst.comp_lift]
end

mutual
theorem Tm.subst_subst : ∀ (X : Tm s₁) (σ : CoSubst s₁ s₂) (τ : CoSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .path P, σ, τ => by simp only [Tm.subst, PathCo.subst_subst]
  | .val v, σ, τ => by simp only [Tm.subst, Value.subst_subst v σ τ]
  | .app P Q, σ, τ => by simp only [Tm.subst, PathCo.subst_subst]
  | .lett t u, σ, τ => by
      simp only [Tm.subst, Tm.subst_subst t σ τ, Tm.subst_subst u σ.lift τ.lift,
        CoSubst.comp_lift]
  | .cast t e, σ, τ => by simp only [Tm.subst, Tm.subst_subst t σ τ, LeCo.subst_subst]
theorem Value.subst_subst : ∀ (X : Value s₁) (σ : CoSubst s₁ s₂) (τ : CoSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .lam S t, σ, τ => by
      simp only [Value.subst, Ty.subst_subst, CoSubst.comp_paths, Tm.subst_subst t σ.lift τ.lift,
        CoSubst.comp_lift]
  | .obj Tel ds, σ, τ => by
      simp only [Value.subst, Telescope.subst_subst, CoSubst.comp_paths, PathSubst.comp_lift,
        Defs.subst_subst ds σ.lift τ.lift, CoSubst.comp_lift]
  | .cast v e, σ, τ => by simp only [Value.subst, Value.subst_subst v σ τ, LeCo.subst_subst]
theorem Defs.subst_subst : ∀ (X : Defs s₁) (σ : CoSubst s₁ s₂) (τ : CoSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .nil, _, _ => rfl
  | .typ ds A U, σ, τ => by
      simp only [Defs.subst, Defs.subst_subst ds σ τ, Ty.subst_subst, CoSubst.comp_paths]
  | .fld ds a rhs, σ, τ => by
      simp only [Defs.subst, Defs.subst_subst ds σ τ, Rhs.subst_subst rhs σ τ]
  | .cls ds C U, σ, τ => by
      simp only [Defs.subst, Defs.subst_subst ds σ τ, Ty.subst_subst, CoSubst.comp_paths]
theorem Rhs.subst_subst : ∀ (X : Rhs s₁) (σ : CoSubst s₁ s₂) (τ : CoSubst s₂ s₃),
    (X.subst σ).subst τ = X.subst (σ.comp τ)
  | .path P, σ, τ => by simp only [Rhs.subst, PathCo.subst_subst]
  | .fn v, σ, τ => by simp only [Rhs.subst, Value.subst_subst v σ τ]
  | .nest Tel ds, σ, τ => by
      simp only [Rhs.subst, Telescope.subst_subst, CoSubst.comp_paths, PathSubst.comp_lift,
        Defs.subst_subst ds σ τ]
end

/-! ## Evidence and term families: the identity, weakening and instantiation by evidence

`subst_id` is `subst_ofRename` at the identity.  `weaken_substCo` is `rename_subst` at
`Rename.succ`, where the instantiation undoes the weakening (`Rename.succ_coComp_one`).
`substCo_subst` is `subst_subst` twice around `CoSubst.one_comp`. -/

theorem PEq.subst_id (X : PEq s) : X.subst CoSubst.id = X :=
  (PEq.subst_ofRename X Rename.id).trans (PEq.rename_id X)
theorem PathCo.subst_id (X : PathCo s) : X.subst CoSubst.id = X :=
  (PathCo.subst_ofRename X Rename.id).trans (PathCo.rename_id X)
theorem LeCo.subst_id (X : LeCo s) : X.subst CoSubst.id = X :=
  (LeCo.subst_ofRename X Rename.id).trans (LeCo.rename_id X)
theorem EqCo.subst_id (X : EqCo s) : X.subst CoSubst.id = X :=
  (EqCo.subst_ofRename X Rename.id).trans (EqCo.rename_id X)
theorem Morphism.subst_id (X : Morphism s) : X.subst CoSubst.id = X :=
  (Morphism.subst_ofRename X Rename.id).trans (Morphism.rename_id X)
theorem Side.subst_id (X : Side s) : X.subst CoSubst.id = X :=
  (Side.subst_ofRename X Rename.id).trans (Side.rename_id X)
theorem Tm.subst_id (X : Tm s) : X.subst CoSubst.id = X :=
  (Tm.subst_ofRename X Rename.id).trans (Tm.rename_id X)
theorem Value.subst_id (X : Value s) : X.subst CoSubst.id = X :=
  (Value.subst_ofRename X Rename.id).trans (Value.rename_id X)
theorem Defs.subst_id (X : Defs s) : X.subst CoSubst.id = X :=
  (Defs.subst_ofRename X Rename.id).trans (Defs.rename_id X)
theorem Rhs.subst_id (X : Rhs s) : X.subst CoSubst.id = X :=
  (Rhs.subst_ofRename X Rename.id).trans (Rhs.rename_id X)

theorem PEq.weaken_substCo (X : PEq s) (Q : PathCo s) : X.weaken.substCo Q = X :=
  (PEq.rename_subst X Rename.succ (CoSubst.one Q)).trans
    ((congrArg (PEq.subst X) (Rename.succ_coComp_one Q)).trans (PEq.subst_id X))
theorem PathCo.weaken_substCo (X : PathCo s) (Q : PathCo s) : X.weaken.substCo Q = X :=
  (PathCo.rename_subst X Rename.succ (CoSubst.one Q)).trans
    ((congrArg (PathCo.subst X) (Rename.succ_coComp_one Q)).trans (PathCo.subst_id X))
theorem LeCo.weaken_substCo (X : LeCo s) (Q : PathCo s) : X.weaken.substCo Q = X :=
  (LeCo.rename_subst X Rename.succ (CoSubst.one Q)).trans
    ((congrArg (LeCo.subst X) (Rename.succ_coComp_one Q)).trans (LeCo.subst_id X))
theorem EqCo.weaken_substCo (X : EqCo s) (Q : PathCo s) : X.weaken.substCo Q = X :=
  (EqCo.rename_subst X Rename.succ (CoSubst.one Q)).trans
    ((congrArg (EqCo.subst X) (Rename.succ_coComp_one Q)).trans (EqCo.subst_id X))
theorem Morphism.weaken_substCo (X : Morphism s) (Q : PathCo s) : X.weaken.substCo Q = X :=
  (Morphism.rename_subst X Rename.succ (CoSubst.one Q)).trans
    ((congrArg (Morphism.subst X) (Rename.succ_coComp_one Q)).trans (Morphism.subst_id X))
theorem Side.weaken_substCo (X : Side s) (Q : PathCo s) : X.weaken.substCo Q = X :=
  (Side.rename_subst X Rename.succ (CoSubst.one Q)).trans
    ((congrArg (Side.subst X) (Rename.succ_coComp_one Q)).trans (Side.subst_id X))
theorem Tm.weaken_substCo (X : Tm s) (Q : PathCo s) : X.weaken.substCo Q = X :=
  (Tm.rename_subst X Rename.succ (CoSubst.one Q)).trans
    ((congrArg (Tm.subst X) (Rename.succ_coComp_one Q)).trans (Tm.subst_id X))
theorem Value.weaken_substCo (X : Value s) (Q : PathCo s) : X.weaken.substCo Q = X :=
  (Value.rename_subst X Rename.succ (CoSubst.one Q)).trans
    ((congrArg (Value.subst X) (Rename.succ_coComp_one Q)).trans (Value.subst_id X))
theorem Defs.weaken_substCo (X : Defs s) (Q : PathCo s) : X.weaken.substCo Q = X :=
  (Defs.rename_subst X Rename.succ (CoSubst.one Q)).trans
    ((congrArg (Defs.subst X) (Rename.succ_coComp_one Q)).trans (Defs.subst_id X))
theorem Rhs.weaken_substCo (X : Rhs s) (Q : PathCo s) : X.weaken.substCo Q = X :=
  (Rhs.rename_subst X Rename.succ (CoSubst.one Q)).trans
    ((congrArg (Rhs.subst X) (Rename.succ_coComp_one Q)).trans (Rhs.subst_id X))

/-- Instantiating `.here` by `Q` and then substituting is substituting under the binder and
then instantiating by the image of `Q`. -/
theorem CoSubst.one_comp (Q : PathCo s₁) (σ : CoSubst s₁ s₂) :
    (CoSubst.one Q).comp σ = σ.lift.comp (CoSubst.one (Q.subst σ)) :=
  CoSubst.funext' fun x => by
    cases x with
    | here => rfl
    | there y => exact (PathCo.weaken_substCo (σ.var y) (Q.subst σ)).symm

theorem PEq.substCo_subst (X : PEq (s₁,x)) (Q : PathCo s₁) (σ : CoSubst s₁ s₂) :
    (X.substCo Q).subst σ = (X.subst σ.lift).substCo (Q.subst σ) := by
  rw [PEq.substCo, PEq.substCo, PEq.subst_subst, PEq.subst_subst, CoSubst.one_comp]
theorem PathCo.substCo_subst (X : PathCo (s₁,x)) (Q : PathCo s₁) (σ : CoSubst s₁ s₂) :
    (X.substCo Q).subst σ = (X.subst σ.lift).substCo (Q.subst σ) := by
  rw [PathCo.substCo, PathCo.substCo, PathCo.subst_subst, PathCo.subst_subst, CoSubst.one_comp]
theorem LeCo.substCo_subst (X : LeCo (s₁,x)) (Q : PathCo s₁) (σ : CoSubst s₁ s₂) :
    (X.substCo Q).subst σ = (X.subst σ.lift).substCo (Q.subst σ) := by
  rw [LeCo.substCo, LeCo.substCo, LeCo.subst_subst, LeCo.subst_subst, CoSubst.one_comp]
theorem EqCo.substCo_subst (X : EqCo (s₁,x)) (Q : PathCo s₁) (σ : CoSubst s₁ s₂) :
    (X.substCo Q).subst σ = (X.subst σ.lift).substCo (Q.subst σ) := by
  rw [EqCo.substCo, EqCo.substCo, EqCo.subst_subst, EqCo.subst_subst, CoSubst.one_comp]
theorem Morphism.substCo_subst (X : Morphism (s₁,x)) (Q : PathCo s₁) (σ : CoSubst s₁ s₂) :
    (X.substCo Q).subst σ = (X.subst σ.lift).substCo (Q.subst σ) := by
  rw [Morphism.substCo, Morphism.substCo, Morphism.subst_subst, Morphism.subst_subst,
    CoSubst.one_comp]
theorem Side.substCo_subst (X : Side (s₁,x)) (Q : PathCo s₁) (σ : CoSubst s₁ s₂) :
    (X.substCo Q).subst σ = (X.subst σ.lift).substCo (Q.subst σ) := by
  rw [Side.substCo, Side.substCo, Side.subst_subst, Side.subst_subst, CoSubst.one_comp]
theorem Tm.substCo_subst (X : Tm (s₁,x)) (Q : PathCo s₁) (σ : CoSubst s₁ s₂) :
    (X.substCo Q).subst σ = (X.subst σ.lift).substCo (Q.subst σ) := by
  rw [Tm.substCo, Tm.substCo, Tm.subst_subst, Tm.subst_subst, CoSubst.one_comp]
theorem Value.substCo_subst (X : Value (s₁,x)) (Q : PathCo s₁) (σ : CoSubst s₁ s₂) :
    (X.substCo Q).subst σ = (X.subst σ.lift).substCo (Q.subst σ) := by
  rw [Value.substCo, Value.substCo, Value.subst_subst, Value.subst_subst, CoSubst.one_comp]
theorem Defs.substCo_subst (X : Defs (s₁,x)) (Q : PathCo s₁) (σ : CoSubst s₁ s₂) :
    (X.substCo Q).subst σ = (X.subst σ.lift).substCo (Q.subst σ) := by
  rw [Defs.substCo, Defs.substCo, Defs.subst_subst, Defs.subst_subst, CoSubst.one_comp]
theorem Rhs.substCo_subst (X : Rhs (s₁,x)) (Q : PathCo s₁) (σ : CoSubst s₁ s₂) :
    (X.substCo Q).subst σ = (X.subst σ.lift).substCo (Q.subst σ) := by
  rw [Rhs.substCo, Rhs.substCo, Rhs.subst_subst, Rhs.subst_subst, CoSubst.one_comp]

/-! ## Singletons, the tag of a value, labels -/

theorem Ty.sngl_rename (q : Path s₁) (ρ : Rename s₁ s₂) :
    (Ty.sngl q).rename ρ = Ty.sngl (q.rename ρ) := by
  simp only [Ty.sngl, Ty.rename, Telescope.rename, Pr.rename, Path.weaken_rename]

theorem Ty.sngl_subst (q : Path s₁) (σ : PathSubst s₁ s₂) :
    (Ty.sngl q).subst σ = Ty.sngl (q.subst σ) := by
  simp only [Ty.sngl, Ty.subst, Telescope.subst, Pr.subst, Path.weaken_subst_lift]

theorem Value.isLam_rename : ∀ (v : Value s₁) (ρ : Rename s₁ s₂), (v.rename ρ).isLam = v.isLam
  | .lam _ _, _ => rfl
  | .obj _ _, _ => rfl
  | .cast v _, ρ => Value.isLam_rename v ρ

theorem Value.isLam_subst : ∀ (v : Value s₁) (σ : CoSubst s₁ s₂), (v.subst σ).isLam = v.isLam
  | .lam _ _, _ => rfl
  | .obj _ _, _ => rfl
  | .cast v _, σ => Value.isLam_subst v σ

theorem Defs.labels_rename : ∀ (ds : Defs s₁) (ρ : Rename s₁ s₂),
    (ds.rename ρ).labels = ds.labels
  | .nil, _ => rfl
  | .typ ds A _, ρ => congrArg (A :: ·) (Defs.labels_rename ds ρ)
  | .fld ds a _, ρ => congrArg (a :: ·) (Defs.labels_rename ds ρ)
  | .cls ds C _, ρ => congrArg (C :: ·) (Defs.labels_rename ds ρ)

theorem Defs.labels_subst : ∀ (ds : Defs s₁) (σ : CoSubst s₁ s₂),
    (ds.subst σ).labels = ds.labels
  | .nil, _ => rfl
  | .typ ds A _, σ => congrArg (A :: ·) (Defs.labels_subst ds σ)
  | .fld ds a _, σ => congrArg (a :: ·) (Defs.labels_subst ds σ)
  | .cls ds C _, σ => congrArg (C :: ·) (Defs.labels_subst ds σ)

/-! ## Telescopes: length, append, lookup -/

theorem Telescope.length_rename : ∀ (Tel : Telescope s₁) (ρ : Rename s₁ s₂),
    (Tel.rename ρ).length = Tel.length
  | .nil, _ => rfl
  | .cons Tel _, ρ => congrArg (· + 1) (Telescope.length_rename Tel ρ)

theorem Telescope.length_subst : ∀ (Tel : Telescope s₁) (σ : PathSubst s₁ s₂),
    (Tel.subst σ).length = Tel.length
  | .nil, _ => rfl
  | .cons Tel _, σ => congrArg (· + 1) (Telescope.length_subst Tel σ)

theorem Telescope.append_nil (Tel : Telescope s) : Tel ++ .nil = Tel := rfl

theorem Telescope.append_cons (Tel Tel' : Telescope s) (pr : Pr s) :
    Tel ++ .cons Tel' pr = .cons (Tel ++ Tel') pr := rfl

theorem Telescope.length_append : ∀ (Tel Tel' : Telescope s),
    (Tel ++ Tel').length = Tel.length + Tel'.length
  | _, .nil => rfl
  | Tel, .cons Tel' _ => congrArg (· + 1) (Telescope.length_append Tel Tel')

theorem Telescope.append_rename : ∀ (Tel Tel' : Telescope s₁) (ρ : Rename s₁ s₂),
    (Tel ++ Tel').rename ρ = Tel.rename ρ ++ Tel'.rename ρ
  | _, .nil, _ => rfl
  | Tel, .cons Tel' pr, ρ => by
      simp only [Telescope.append_cons, Telescope.rename, Telescope.append_rename Tel Tel' ρ]

theorem Telescope.append_subst : ∀ (Tel Tel' : Telescope s₁) (σ : PathSubst s₁ s₂),
    (Tel ++ Tel').subst σ = Tel.subst σ ++ Tel'.subst σ
  | _, .nil, _ => rfl
  | Tel, .cons Tel' pr, σ => by
      simp only [Telescope.append_cons, Telescope.subst, Telescope.append_subst Tel Tel' σ]

/-- No proposition sits in the empty telescope.  The index is generalized by an equation. -/
theorem Telescope.At.nil_of_eq {T : Telescope s} {i : Nat} {pr : Pr s} (h : T.At i pr)
    (e : T = .nil) : False := by
  cases h <;> cases e

/-- A proposition of `Tel ▹ pr` is `pr` at the last position or a proposition of `Tel`.  The
index is generalized by an equation. -/
theorem Telescope.At.cons_of_eq {T Tel : Telescope s} {i : Nat} {pr pr' : Pr s}
    (h : T.At i pr') (e : T = .cons Tel pr) : (i = Tel.length ∧ pr' = pr) ∨ Tel.At i pr' := by
  cases h with
  | here =>
      cases e
      exact Or.inl ⟨rfl, rfl⟩
  | there h =>
      cases e
      exact Or.inr h

theorem Telescope.At.cons_iff {Tel : Telescope s} {i : Nat} {pr pr' : Pr s} :
    (Telescope.cons Tel pr).At i pr' ↔ (i = Tel.length ∧ pr' = pr) ∨ Tel.At i pr' :=
  ⟨fun h => Telescope.At.cons_of_eq h rfl, fun h => by
    rcases h with ⟨rfl, rfl⟩ | h
    · exact .here
    · exact .there h⟩

theorem Telescope.At.rename {Tel : Telescope s₁} {i : Nat} {pr : Pr s₁} (h : Tel.At i pr)
    (ρ : Rename s₁ s₂) : (Tel.rename ρ).At i (pr.rename ρ) := by
  induction h with
  | @here Tel pr =>
      show (Telescope.cons (Tel.rename ρ) (pr.rename ρ)).At Tel.length (pr.rename ρ)
      rw [← Telescope.length_rename Tel ρ]
      exact .here
  | there _ ih => exact .there ih

theorem Telescope.At.subst {Tel : Telescope s₁} {i : Nat} {pr : Pr s₁} (h : Tel.At i pr)
    (σ : PathSubst s₁ s₂) : (Tel.subst σ).At i (pr.subst σ) := by
  induction h with
  | @here Tel pr =>
      show (Telescope.cons (Tel.subst σ) (pr.subst σ)).At Tel.length (pr.subst σ)
      rw [← Telescope.length_subst Tel σ]
      exact .here
  | there _ ih => exact .there ih

theorem Telescope.At.of_rename : ∀ (Tel : Telescope s₁) (ρ : Rename s₁ s₂) {i : Nat} {pr' : Pr s₂},
    (Tel.rename ρ).At i pr' → ∃ pr, Tel.At i pr ∧ pr' = pr.rename ρ
  | .nil, _, _, _, h => (Telescope.At.nil_of_eq h rfl).elim
  | .cons Tel pr, ρ, _, _, h => by
      rcases Telescope.At.cons_of_eq h rfl with ⟨rfl, rfl⟩ | h
      · refine ⟨pr, ?_, rfl⟩
        rw [Telescope.length_rename]
        exact .here
      · obtain ⟨pr₀, h₀, rfl⟩ := Telescope.At.of_rename Tel ρ h
        exact ⟨pr₀, .there h₀, rfl⟩

theorem Telescope.At.of_subst : ∀ (Tel : Telescope s₁) (σ : PathSubst s₁ s₂) {i : Nat} {pr' : Pr s₂},
    (Tel.subst σ).At i pr' → ∃ pr, Tel.At i pr ∧ pr' = pr.subst σ
  | .nil, _, _, _, h => (Telescope.At.nil_of_eq h rfl).elim
  | .cons Tel pr, σ, _, _, h => by
      rcases Telescope.At.cons_of_eq h rfl with ⟨rfl, rfl⟩ | h
      · refine ⟨pr, ?_, rfl⟩
        rw [Telescope.length_subst]
        exact .here
      · obtain ⟨pr₀, h₀, rfl⟩ := Telescope.At.of_subst Tel σ h
        exact ⟨pr₀, .there h₀, rfl⟩

theorem Telescope.At.rename_iff {Tel : Telescope s₁} {ρ : Rename s₁ s₂} {i : Nat} {pr' : Pr s₂} :
    (Tel.rename ρ).At i pr' ↔ ∃ pr, Tel.At i pr ∧ pr' = pr.rename ρ :=
  ⟨Telescope.At.of_rename Tel ρ, fun ⟨_, h, e⟩ => e ▸ h.rename ρ⟩

theorem Telescope.At.subst_iff {Tel : Telescope s₁} {σ : PathSubst s₁ s₂} {i : Nat}
    {pr' : Pr s₂} : (Tel.subst σ).At i pr' ↔ ∃ pr, Tel.At i pr ∧ pr' = pr.subst σ :=
  ⟨Telescope.At.of_subst Tel σ, fun ⟨_, h, e⟩ => e ▸ h.subst σ⟩

theorem Telescope.At.append_left {Tel : Telescope s} {i : Nat} {pr : Pr s} (h : Tel.At i pr) :
    ∀ (Tel' : Telescope s), (Tel ++ Tel').At i pr
  | .nil => h
  | .cons Tel' _ => .there (Telescope.At.append_left h Tel')

theorem Telescope.At.append_right (Tel : Telescope s) {j : Nat} {pr : Pr s} :
    ∀ {Tel' : Telescope s}, Tel'.At j pr → (Tel ++ Tel').At (Tel.length + j) pr
  | _, .here (Tel := Tel') => by
      rw [Telescope.append_cons, ← Telescope.length_append]
      exact .here
  | _, .there h => .there (Telescope.At.append_right Tel h)

theorem Telescope.At.of_append (Tel : Telescope s) : ∀ (Tel' : Telescope s) {i : Nat} {pr : Pr s},
    (Tel ++ Tel').At i pr → Tel.At i pr ∨ ∃ j, i = Tel.length + j ∧ Tel'.At j pr
  | .nil, _, _, h => Or.inl h
  | .cons Tel' pr', _, _, h => by
      rcases Telescope.At.cons_of_eq h (Telescope.append_cons Tel Tel' pr') with ⟨rfl, rfl⟩ | h
      · exact Or.inr ⟨Tel'.length, Telescope.length_append Tel Tel', .here⟩
      · rcases Telescope.At.of_append Tel Tel' h with h₀ | ⟨j, rfl, hj⟩
        · exact Or.inl h₀
        · exact Or.inr ⟨j, rfl, .there hj⟩

theorem Telescope.At.append_iff {Tel Tel' : Telescope s} {i : Nat} {pr : Pr s} :
    (Tel ++ Tel').At i pr ↔ Tel.At i pr ∨ ∃ j, i = Tel.length + j ∧ Tel'.At j pr :=
  ⟨Telescope.At.of_append Tel Tel', fun h => by
    rcases h with h | ⟨j, rfl, h⟩
    · exact h.append_left Tel'
    · exact Telescope.At.append_right Tel h⟩

theorem Telescope.At.single_iff {pr pr' : Pr s} {i : Nat} :
    (Telescope.cons .nil pr).At i pr' ↔ i = 0 ∧ pr' = pr :=
  ⟨fun h => by
    rcases Telescope.At.cons_of_eq h rfl with h | h
    · exact h
    · exact (Telescope.At.nil_of_eq h rfl).elim,
   fun ⟨hi, hp⟩ => by
    subst hi
    subst hp
    exact .here⟩

end Nominal.FCn
