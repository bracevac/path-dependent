import Coercions.FCdot.Syntax

/-!
# Renaming algebra for FCdot

The standard functorial laws for renaming (`rename_id`, `rename_comp`) on every
syntactic family, the interaction of `Atom.root` with renaming and
substitution, and the facts relating substitutions to renamings that the
typing metatheory needs.

Each family is a mutual inductive, so the proofs come in `mutual` blocks of
structurally recursive theorems that mirror the `rename` definitions.
-/

namespace FCdot

/-! ## `rename_id` for types, propositions, telescopes -/

mutual

@[simp] theorem Ty.rename_id {s : Sig} (T : Ty s) : T.rename Rename.id = T := by
  match T with
  | .top => simp [Ty.rename]
  | .bot => simp [Ty.rename]
  | .sel x ℓ => simp [Ty.rename]
  | .pi S T => simp [Ty.rename, Rename.lift_id, Ty.rename_id S, Ty.rename_id T]
  | .obj Tel => simp [Ty.rename, Rename.lift_id, Telescope.rename_id Tel]

@[simp] theorem Proposition.rename_id {s : Sig} (P : Proposition s) :
    P.rename Rename.id = P := by
  match P with
  | .le S T => simp [Proposition.rename, Ty.rename_id S, Ty.rename_id T]
  | .eq S T => simp [Proposition.rename, Ty.rename_id S, Ty.rename_id T]
  | .has ℓ => simp [Proposition.rename]

@[simp] theorem Telescope.rename_id {s : Sig} (Tel : Telescope s) :
    Tel.rename Rename.id = Tel := by
  match Tel with
  | .nil => simp [Telescope.rename]
  | .cons Tel P => simp [Telescope.rename, Telescope.rename_id Tel, Proposition.rename_id P]

end

/-! ## `rename_comp` for types, propositions, telescopes -/

mutual

@[simp] theorem Ty.rename_comp {s1 s2 s3 : Sig} (T : Ty s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (T.rename ρ).rename ρ' = T.rename (ρ.comp ρ') := by
  match T with
  | .top => simp [Ty.rename]
  | .bot => simp [Ty.rename]
  | .sel x ℓ => simp [Ty.rename]
  | .pi S T =>
      simp [Ty.rename, Rename.lift_comp, Ty.rename_comp S, Ty.rename_comp T]
  | .obj Tel =>
      simp [Ty.rename, Rename.lift_comp, Telescope.rename_comp Tel]

@[simp] theorem Proposition.rename_comp {s1 s2 s3 : Sig} (P : Proposition s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (P.rename ρ).rename ρ' = P.rename (ρ.comp ρ') := by
  match P with
  | .le S T => simp [Proposition.rename, Ty.rename_comp S, Ty.rename_comp T]
  | .eq S T => simp [Proposition.rename, Ty.rename_comp S, Ty.rename_comp T]
  | .has ℓ => simp [Proposition.rename]

@[simp] theorem Telescope.rename_comp {s1 s2 s3 : Sig} (Tel : Telescope s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (Tel.rename ρ).rename ρ' = Tel.rename (ρ.comp ρ') := by
  match Tel with
  | .nil => simp [Telescope.rename]
  | .cons Tel P =>
      simp [Telescope.rename, Telescope.rename_comp Tel, Proposition.rename_comp P]

end

/-! ## `rename_id` for evidence and atoms -/

mutual

@[simp] theorem LeCo.rename_id {s : Sig} (e : LeCo s) : e.rename Rename.id = e := by
  match e with
  | .refl T => simp [LeCo.rename]
  | .trans e f => simp [LeCo.rename, LeCo.rename_id e, LeCo.rename_id f]
  | .top T => simp [LeCo.rename]
  | .bot T => simp [LeCo.rename]
  | .eqToLe φ => simp [LeCo.rename, EqCo.rename_id φ]
  | .pi e f => simp [LeCo.rename, Rename.lift_id, LeCo.rename_id e, LeCo.rename_id f]
  | .obj Tel m => simp [LeCo.rename, Morphism.rename_id m, Telescope.rename_id Tel]
  | .member a e i => simp [LeCo.rename, Atom.rename_id a, LeCo.rename_id e]

@[simp] theorem EqCo.rename_id {s : Sig} (φ : EqCo s) : φ.rename Rename.id = φ := by
  match φ with
  | .refl T => simp [EqCo.rename]
  | .symm φ => simp [EqCo.rename, EqCo.rename_id φ]
  | .trans φ ψ => simp [EqCo.rename, EqCo.rename_id φ, EqCo.rename_id ψ]
  | .def x ℓ => simp [EqCo.rename]
  | .member a e i => simp [EqCo.rename, Atom.rename_id a, LeCo.rename_id e]

@[simp] theorem Has.rename_id {s : Sig} (h : Has s) : h.rename Rename.id = h := by
  match h with
  | .member a e i => simp [Has.rename, Atom.rename_id a, LeCo.rename_id e]
  | .field ℓ => simp [Has.rename]

@[simp] theorem Morphism.rename_id {s : Sig} (m : Morphism s) : m.rename Rename.id = m := by
  match m with
  | .nil => simp [Morphism.rename]
  | .le m e => simp [Morphism.rename, Morphism.rename_id m, LeCo.rename_id e]
  | .eq m φ => simp [Morphism.rename, Morphism.rename_id m, EqCo.rename_id φ]
  | .has m j => simp [Morphism.rename, Morphism.rename_id m]

@[simp] theorem Atom.rename_id {s : Sig} (a : Atom s) : a.rename Rename.id = a := by
  match a with
  | .var x => simp [Atom.rename]
  | .cast a e => simp [Atom.rename, Atom.rename_id a, LeCo.rename_id e]
  | .foldSelf Tel a => simp [Atom.rename, Rename.lift_id, Atom.rename_id a, Telescope.rename_id Tel]
  | .unfoldSelf a => simp [Atom.rename, Atom.rename_id a]

end

/-! ## `rename_comp` for evidence and atoms -/

mutual

@[simp] theorem LeCo.rename_comp {s1 s2 s3 : Sig} (e : LeCo s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (e.rename ρ).rename ρ' = e.rename (ρ.comp ρ') := by
  match e with
  | .refl T => simp [LeCo.rename]
  | .trans e f => simp [LeCo.rename, LeCo.rename_comp e, LeCo.rename_comp f]
  | .top T => simp [LeCo.rename]
  | .bot T => simp [LeCo.rename]
  | .eqToLe φ => simp [LeCo.rename, EqCo.rename_comp φ]
  | .pi e f =>
      simp [LeCo.rename, Rename.lift_comp, LeCo.rename_comp e, LeCo.rename_comp f]
  | .obj Tel m => simp [LeCo.rename, Morphism.rename_comp m, Telescope.rename_comp Tel]
  | .member a e i => simp [LeCo.rename, Atom.rename_comp a, LeCo.rename_comp e]

@[simp] theorem EqCo.rename_comp {s1 s2 s3 : Sig} (φ : EqCo s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (φ.rename ρ).rename ρ' = φ.rename (ρ.comp ρ') := by
  match φ with
  | .refl T => simp [EqCo.rename]
  | .symm φ => simp [EqCo.rename, EqCo.rename_comp φ]
  | .trans φ ψ => simp [EqCo.rename, EqCo.rename_comp φ, EqCo.rename_comp ψ]
  | .def x ℓ => simp [EqCo.rename]
  | .member a e i => simp [EqCo.rename, Atom.rename_comp a, LeCo.rename_comp e]

@[simp] theorem Has.rename_comp {s1 s2 s3 : Sig} (h : Has s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (h.rename ρ).rename ρ' = h.rename (ρ.comp ρ') := by
  match h with
  | .member a e i => simp [Has.rename, Atom.rename_comp a, LeCo.rename_comp e]
  | .field ℓ => simp [Has.rename]

@[simp] theorem Morphism.rename_comp {s1 s2 s3 : Sig} (m : Morphism s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (m.rename ρ).rename ρ' = m.rename (ρ.comp ρ') := by
  match m with
  | .nil => simp [Morphism.rename]
  | .le m e => simp [Morphism.rename, Morphism.rename_comp m, LeCo.rename_comp e]
  | .eq m φ => simp [Morphism.rename, Morphism.rename_comp m, EqCo.rename_comp φ]
  | .has m j => simp [Morphism.rename, Morphism.rename_comp m]

@[simp] theorem Atom.rename_comp {s1 s2 s3 : Sig} (a : Atom s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (a.rename ρ).rename ρ' = a.rename (ρ.comp ρ') := by
  match a with
  | .var x => simp [Atom.rename]
  | .cast a e => simp [Atom.rename, Atom.rename_comp a, LeCo.rename_comp e]
  | .foldSelf Tel a => simp [Atom.rename, Rename.lift_comp, Atom.rename_comp a, Telescope.rename_comp Tel]
  | .unfoldSelf a => simp [Atom.rename, Atom.rename_comp a]

end

/-! ## `rename_id` for terms, values, witnesses, fields -/

mutual

@[simp] theorem Tm.rename_id {s : Sig} (t : Tm s) : t.rename Rename.id = t := by
  match t with
  | .atom a => simp [Tm.rename]
  | .val v => simp [Tm.rename, Value.rename_id v]
  | .app a b => simp [Tm.rename]
  | .proj a ℓ h => simp [Tm.rename, Has.rename_id h]
  | .let t u => simp [Tm.rename, Rename.lift_id, Tm.rename_id t, Tm.rename_id u]
  | .cast t e => simp [Tm.rename, Tm.rename_id t]

@[simp] theorem Value.rename_id {s : Sig} (v : Value s) : v.rename Rename.id = v := by
  match v with
  | .lam S t => simp [Value.rename, Rename.lift_id, Tm.rename_id t]
  | .obj W F =>
      simp [Value.rename, Rename.lift_id, Witnesses.rename_id W, Fields.rename_id F]
  | .cast v e => simp [Value.rename, Value.rename_id v]

@[simp] theorem Witnesses.rename_id {s : Sig} (W : Witnesses s) : W.rename Rename.id = W := by
  match W with
  | .nil => simp [Witnesses.rename]
  | .cons W ℓ T => simp [Witnesses.rename, Witnesses.rename_id W]

@[simp] theorem Fields.rename_id {s : Sig} (F : Fields s) : F.rename Rename.id = F := by
  match F with
  | .nil => simp [Fields.rename]
  | .cons F ℓ t => simp [Fields.rename, Fields.rename_id F, Tm.rename_id t]

end

/-! ## `rename_comp` for terms, values, witnesses, fields -/

mutual

@[simp] theorem Tm.rename_comp {s1 s2 s3 : Sig} (t : Tm s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (t.rename ρ).rename ρ' = t.rename (ρ.comp ρ') := by
  match t with
  | .atom a => simp [Tm.rename]
  | .val v => simp [Tm.rename, Value.rename_comp v]
  | .app a b => simp [Tm.rename]
  | .proj a ℓ h => simp [Tm.rename, Has.rename_comp h]
  | .let t u =>
      simp [Tm.rename, Rename.lift_comp, Tm.rename_comp t, Tm.rename_comp u]
  | .cast t e => simp [Tm.rename, Tm.rename_comp t]

@[simp] theorem Value.rename_comp {s1 s2 s3 : Sig} (v : Value s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (v.rename ρ).rename ρ' = v.rename (ρ.comp ρ') := by
  match v with
  | .lam S t => simp [Value.rename, Rename.lift_comp, Tm.rename_comp t]
  | .obj W F =>
      simp [Value.rename, Rename.lift_comp, Witnesses.rename_comp W, Fields.rename_comp F]
  | .cast v e => simp [Value.rename, Value.rename_comp v]

@[simp] theorem Witnesses.rename_comp {s1 s2 s3 : Sig} (W : Witnesses s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (W.rename ρ).rename ρ' = W.rename (ρ.comp ρ') := by
  match W with
  | .nil => simp [Witnesses.rename]
  | .cons W ℓ T => simp [Witnesses.rename, Witnesses.rename_comp W]

@[simp] theorem Fields.rename_comp {s1 s2 s3 : Sig} (F : Fields s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (F.rename ρ).rename ρ' = F.rename (ρ.comp ρ') := by
  match F with
  | .nil => simp [Fields.rename]
  | .cons F ℓ t => simp [Fields.rename, Fields.rename_comp F, Tm.rename_comp t]

end

/-! ## Roots -/

@[simp] theorem Atom.root_rename {s1 s2 : Sig} (a : Atom s1) (ρ : Rename s1 s2) :
    (a.rename ρ).root = ρ.var a.root := by
  match a with
  | .var x => simp [Atom.rename, Atom.root]
  | .cast a e => simp [Atom.rename, Atom.root, Atom.root_rename a]
  | .foldSelf Tel a => simp [Atom.rename, Atom.root, Atom.root_rename a]
  | .unfoldSelf a => simp [Atom.rename, Atom.root, Atom.root_rename a]

namespace Subst

theorem funext' {s1 s2 : Sig} {σ τ : Subst s1 s2}
    (h : ∀ (x : BVar s1 .var), σ.var x = τ.var x) : σ = τ := by
  cases σ; cases τ
  simp only [Subst.mk.injEq]
  funext x
  exact h x

theorem root_var {s1 s2 : Sig} (σ : Subst s1 s2) (x : BVar s1 .var) :
    σ.root.var x = (σ.var x).root := rfl

@[simp] theorem ofRename_root {s1 s2 : Sig} (ρ : Rename s1 s2) :
    (Subst.ofRename ρ).root = ρ := by
  apply Rename.funext'
  intro k x
  cases k
  simp [Subst.root, Subst.ofRename, Atom.root]

@[simp] theorem ofRename_lift {s1 s2 : Sig} (ρ : Rename s1 s2) :
    (Subst.ofRename ρ).lift = Subst.ofRename ρ.lift := by
  apply Subst.funext'
  intro x
  cases x <;> simp [Subst.lift, Subst.ofRename, Atom.weaken, Atom.rename]

@[simp] theorem lift_root {s1 s2 : Sig} (σ : Subst s1 s2) :
    σ.lift.root = σ.root.lift := by
  apply Rename.funext'
  intro k x
  cases k
  cases x with
  | here => simp [Subst.root, Subst.lift, Atom.root]
  | there x => simp [Subst.root, Subst.lift, Atom.weaken]

@[simp] theorem single_root {s : Sig} (a : Atom s) :
    (Subst.single a).root = Rename.subst a.root := by
  apply Rename.funext'
  intro k x
  cases k
  cases x <;> simp [Subst.root, Subst.single, Atom.root]

end Subst

@[simp] theorem Atom.root_subst {s1 s2 : Sig} (a : Atom s1) (σ : Subst s1 s2) :
    (a.subst σ).root = σ.root.var a.root := by
  match a with
  | .var x => simp [Atom.subst, Atom.root, Subst.root_var]
  | .cast a e => simp [Atom.subst, Atom.root, Atom.root_subst a]
  | .foldSelf Tel a => simp [Atom.subst, Atom.root, Atom.root_subst a]
  | .unfoldSelf a => simp [Atom.subst, Atom.root, Atom.root_subst a]

/-! ## Substitution by a renaming -/

mutual

@[simp] theorem LeCo.subst_ofRename {s1 s2 : Sig} (e : LeCo s1) (ρ : Rename s1 s2) :
    e.subst (Subst.ofRename ρ) = e.rename ρ := by
  match e with
  | .refl T => simp [LeCo.subst, LeCo.rename]
  | .trans e f => simp [LeCo.subst, LeCo.rename, LeCo.subst_ofRename e, LeCo.subst_ofRename f]
  | .top T => simp [LeCo.subst, LeCo.rename]
  | .bot T => simp [LeCo.subst, LeCo.rename]
  | .eqToLe φ => simp [LeCo.subst, LeCo.rename, EqCo.subst_ofRename φ]
  | .pi e f => simp [LeCo.subst, LeCo.rename, LeCo.subst_ofRename e, LeCo.subst_ofRename f]
  | .obj Tel m => simp [LeCo.subst, LeCo.rename, Morphism.subst_ofRename m, Subst.ofRename_root]
  | .member a e i => simp [LeCo.subst, LeCo.rename, Atom.subst_ofRename a, LeCo.subst_ofRename e]

@[simp] theorem EqCo.subst_ofRename {s1 s2 : Sig} (φ : EqCo s1) (ρ : Rename s1 s2) :
    φ.subst (Subst.ofRename ρ) = φ.rename ρ := by
  match φ with
  | .refl T => simp [EqCo.subst, EqCo.rename]
  | .symm φ => simp [EqCo.subst, EqCo.rename, EqCo.subst_ofRename φ]
  | .trans φ ψ => simp [EqCo.subst, EqCo.rename, EqCo.subst_ofRename φ, EqCo.subst_ofRename ψ]
  | .def x ℓ => simp [EqCo.subst, EqCo.rename]
  | .member a e i => simp [EqCo.subst, EqCo.rename, Atom.subst_ofRename a, LeCo.subst_ofRename e]

@[simp] theorem Has.subst_ofRename {s1 s2 : Sig} (h : Has s1) (ρ : Rename s1 s2) :
    h.subst (Subst.ofRename ρ) = h.rename ρ := by
  match h with
  | .member a e i => simp [Has.subst, Has.rename, Atom.subst_ofRename a, LeCo.subst_ofRename e]
  | .field ℓ => simp [Has.subst, Has.rename]

@[simp] theorem Morphism.subst_ofRename {s1 s2 : Sig} (m : Morphism s1) (ρ : Rename s1 s2) :
    m.subst (Subst.ofRename ρ) = m.rename ρ := by
  match m with
  | .nil => simp [Morphism.subst, Morphism.rename]
  | .le m e => simp [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m, LeCo.subst_ofRename e]
  | .eq m φ => simp [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m, EqCo.subst_ofRename φ]
  | .has m j => simp [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m]

@[simp] theorem Atom.subst_ofRename {s1 s2 : Sig} (a : Atom s1) (ρ : Rename s1 s2) :
    a.subst (Subst.ofRename ρ) = a.rename ρ := by
  match a with
  | .var x => simp [Atom.subst, Atom.rename, Subst.ofRename]
  | .cast a e => simp [Atom.subst, Atom.rename, Atom.subst_ofRename a, LeCo.subst_ofRename e]
  | .foldSelf Tel a => simp [Atom.subst, Atom.rename, Atom.subst_ofRename a, Subst.ofRename_root]
  | .unfoldSelf a => simp [Atom.subst, Atom.rename, Atom.subst_ofRename a]

end

mutual

@[simp] theorem Tm.subst_ofRename {s1 s2 : Sig} (t : Tm s1) (ρ : Rename s1 s2) :
    t.subst (Subst.ofRename ρ) = t.rename ρ := by
  match t with
  | .atom a => simp [Tm.subst, Tm.rename]
  | .val v => simp [Tm.subst, Tm.rename, Value.subst_ofRename v]
  | .app a b => simp [Tm.subst, Tm.rename]
  | .proj a ℓ h => simp [Tm.subst, Tm.rename, Has.subst_ofRename h]
  | .let t u => simp [Tm.subst, Tm.rename, Tm.subst_ofRename t, Tm.subst_ofRename u]
  | .cast t e => simp [Tm.subst, Tm.rename, Tm.subst_ofRename t, LeCo.subst_ofRename e]

@[simp] theorem Value.subst_ofRename {s1 s2 : Sig} (v : Value s1) (ρ : Rename s1 s2) :
    v.subst (Subst.ofRename ρ) = v.rename ρ := by
  match v with
  | .lam S t => simp [Value.subst, Value.rename, Tm.subst_ofRename t]
  | .obj W F =>
      simp [Value.subst, Value.rename, Fields.subst_ofRename F]
  | .cast v e => simp [Value.subst, Value.rename, Value.subst_ofRename v, LeCo.subst_ofRename e]

@[simp] theorem Fields.subst_ofRename {s1 s2 : Sig} (F : Fields s1) (ρ : Rename s1 s2) :
    F.subst (Subst.ofRename ρ) = F.rename ρ := by
  match F with
  | .nil => simp [Fields.subst, Fields.rename]
  | .cons F ℓ t =>
      simp [Fields.subst, Fields.rename, Fields.subst_ofRename F, Tm.subst_ofRename t]

end

/-! ## Weakening then instantiating -/

@[simp] theorem Ty.rename_subst_weaken {s : Sig} {k : Kind} (T : Ty s) (y : BVar s k) :
    (T.weaken (k := k))⟦y⟧ = T := by
  simp [Ty.weaken, Ty.substVar, Rename.succ_subst]

@[simp] theorem Proposition.rename_subst_weaken {s : Sig} {k : Kind}
    (P : Proposition s) (y : BVar s k) :
    (P.weaken (k := k))⟦y⟧ = P := by
  simp [Proposition.weaken, Proposition.substVar, Rename.succ_subst]

@[simp] theorem Telescope.rename_subst_weaken {s : Sig} {k : Kind}
    (Tel : Telescope s) (y : BVar s k) :
    (Tel.weaken (k := k))⟦y⟧ = Tel := by
  simp [Telescope.weaken, Telescope.substVar, Rename.succ_subst]

/-! ## `subst` against `lift` -/

theorem Rename.subst_comp {s1 s2 : Sig} {k : Kind} (y : BVar s1 k) (ρ : Rename s1 s2) :
    (Rename.subst y).comp ρ = ρ.lift.comp (Rename.subst (ρ.var y)) := by
  apply Rename.funext'
  intro k x
  cases x <;> rfl

theorem Ty.substVar_rename {s1 s2 : Sig} {k : Kind} (T : Ty (s1,,k))
    (y : BVar s1 k) (ρ : Rename s1 s2) :
    (T⟦y⟧).rename ρ = (T.rename ρ.lift)⟦ρ.var y⟧ := by
  simp only [Ty.substVar, Ty.rename_comp, Rename.subst_comp]

theorem Proposition.substVar_rename {s1 s2 : Sig} {k : Kind} (P : Proposition (s1,,k))
    (y : BVar s1 k) (ρ : Rename s1 s2) :
    (P⟦y⟧).rename ρ = (P.rename ρ.lift)⟦ρ.var y⟧ := by
  simp only [Proposition.substVar, Proposition.rename_comp, Rename.subst_comp]

theorem Telescope.substVar_rename {s1 s2 : Sig} {k : Kind} (Tel : Telescope (s1,,k))
    (y : BVar s1 k) (ρ : Rename s1 s2) :
    (Tel⟦y⟧).rename ρ = (Tel.rename ρ.lift)⟦ρ.var y⟧ := by
  simp only [Telescope.substVar, Telescope.rename_comp, Rename.subst_comp]

/-! ## `weaken` against `lift` -/

theorem Ty.weaken_rename {s1 s2 : Sig} {k : Kind} (T : Ty s1) (ρ : Rename s1 s2) :
    (T.weaken (k := k)).rename ρ.lift = (T.rename ρ)↑ := by
  simp only [Ty.weaken, Ty.rename_comp, Rename.succ_lift]

theorem Proposition.weaken_rename {s1 s2 : Sig} {k : Kind} (P : Proposition s1)
    (ρ : Rename s1 s2) :
    (P.weaken (k := k)).rename ρ.lift = (P.rename ρ)↑ := by
  simp only [Proposition.weaken, Proposition.rename_comp, Rename.succ_lift]

theorem Telescope.weaken_rename {s1 s2 : Sig} {k : Kind} (Tel : Telescope s1)
    (ρ : Rename s1 s2) :
    (Tel.weaken (k := k)).rename ρ.lift = (Tel.rename ρ)↑ := by
  simp only [Telescope.weaken, Telescope.rename_comp, Rename.succ_lift]

theorem LeCo.weaken_rename {s1 s2 : Sig} {k : Kind} (e : LeCo s1) (ρ : Rename s1 s2) :
    (e.weaken (k := k)).rename ρ.lift = (e.rename ρ)↑ := by
  simp only [LeCo.weaken, LeCo.rename_comp, Rename.succ_lift]

theorem Tm.weaken_rename {s1 s2 : Sig} {k : Kind} (t : Tm s1) (ρ : Rename s1 s2) :
    (t.weaken (k := k)).rename ρ.lift = (t.rename ρ)↑ := by
  simp only [Tm.weaken, Tm.rename_comp, Rename.succ_lift]

theorem Atom.weaken_rename {s1 s2 : Sig} {k : Kind} (a : Atom s1) (ρ : Rename s1 s2) :
    (a.weaken (k := k)).rename ρ.lift = (a.rename ρ)↑ := by
  simp only [Atom.weaken, Atom.rename_comp, Rename.succ_lift]

theorem Value.weaken_rename {s1 s2 : Sig} {k : Kind} (v : Value s1) (ρ : Rename s1 s2) :
    (v.weaken (k := k)).rename ρ.lift = (v.rename ρ)↑ := by
  simp only [Value.weaken, Value.rename_comp, Rename.succ_lift]

/-! ## Telescope lookup is stable under renaming -/

@[simp] theorem Telescope.length_rename {s1 s2 : Sig} :
    ∀ (Tel : Telescope s1) (ρ : Rename s1 s2), (Tel.rename ρ).length = Tel.length
  | .nil, _ => rfl
  | .cons Tel P, ρ => by
      simp [Telescope.rename, Telescope.length, Telescope.length_rename Tel ρ]

theorem Telescope.At.rename {s1 s2 : Sig} {Tel : Telescope s1} {i : Nat}
    {P : Proposition s1} (h : Tel.At i P) (ρ : Rename s1 s2) :
    (Tel.rename ρ).At i (P.rename ρ) := by
  induction h with
  | @here Tel P =>
      rw [← Telescope.length_rename Tel ρ]
      exact Telescope.At.here
  | there _ ih => exact Telescope.At.there ih

/-! ## Witness lookup is stable under renaming -/

theorem Witnesses.get_rename {s1 s2 : Sig} :
    ∀ (W : Witnesses s1) (l : Label) (ρ : Rename s1 s2),
      (W.rename ρ).get l = (W.get l).rename ρ
  | .nil, _, _ => rfl
  | .cons W l' T, l, ρ => by
      by_cases hl : l = l' <;>
        simp [Witnesses.rename, Witnesses.get, hl, Witnesses.get_rename W l ρ]

/-! ## The precise telescope of a literal is stable under renaming -/

theorem Witnesses.eqEntriesOf_rename {s1 s2 : Sig} (self : BVar s1 .var) (W₀ : Witnesses s1)
    (ρ : Rename s1 s2) :
    ∀ W : Witnesses s1,
      (W₀.rename ρ).eqEntriesOf (ρ.var self) (W.rename ρ) = (W₀.eqEntriesOf self W).rename ρ
  | .nil => by simp [Witnesses.rename, Witnesses.eqEntriesOf, Telescope.rename]
  | .cons W ℓ T => by
      simp [Witnesses.rename, Witnesses.eqEntriesOf, Telescope.rename, Proposition.rename,
        Ty.rename, Witnesses.eqEntriesOf_rename self W₀ ρ W, Witnesses.get_rename]

@[simp] theorem Witnesses.eqEntries_rename {s1 s2 : Sig} (W : Witnesses (s1,x)) (ρ : Rename s1 s2) :
    (W.rename ρ.lift).eqEntries = W.eqEntries.rename ρ.lift :=
  Witnesses.eqEntriesOf_rename .here W ρ.lift W

@[simp] theorem Telescope.hasEntries_rename {s1 s2 : Sig} :
    ∀ (Tel : Telescope s1) (ls : List Label) (ρ : Rename s1 s2),
      (Tel.hasEntries ls).rename ρ = (Tel.rename ρ).hasEntries ls
  | _, [], _ => rfl
  | Tel, l :: ls, ρ => by
      simp [Telescope.hasEntries, Telescope.hasEntries_rename (Tel.cons (.has l)) ls ρ,
        Telescope.rename, Proposition.rename]

theorem Telescope.ofLiteral_rename {s1 s2 : Sig} (W : Witnesses (s1,x)) (ls : List Label)
    (ρ : Rename s1 s2) :
    (Telescope.ofLiteral W ls).rename ρ.lift = Telescope.ofLiteral (W.rename ρ.lift) ls := by
  simp [Telescope.ofLiteral]

end FCdot
