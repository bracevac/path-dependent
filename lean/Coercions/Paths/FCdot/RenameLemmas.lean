import Coercions.Paths.FCdot.Syntax

namespace Paths

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

/-! ## Renaming of paths

The one clause `Path.sel` is an induction step where the base had a leaf, so
every law of the renaming algebra gains an induction on paths. -/

@[simp] theorem Path.rename_var {s1 s2 : Sig} (x : BVar s1 .var) (ρ : Rename s1 s2) :
    (Path.var x).rename ρ = .var (ρ.var x) := rfl

@[simp] theorem Path.rename_sel {s1 s2 : Sig} (p : Path s1) (ℓ : Label) (ρ : Rename s1 s2) :
    (Path.sel p ℓ).rename ρ = .sel (p.rename ρ) ℓ := rfl

@[simp] theorem Path.rename_id {s : Sig} (p : Path s) : p.rename Rename.id = p := by
  induction p with
  | var x => rfl
  | sel p ℓ ih => exact congrArg (Path.sel · ℓ) ih

@[simp] theorem Path.rename_comp {s1 s2 s3 : Sig} (p : Path s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (p.rename ρ).rename ρ' = p.rename (ρ.comp ρ') := by
  induction p with
  | var x => rfl
  | sel p ℓ ih => exact congrArg (Path.sel · ℓ) ih

/-! ## `rename_id` for types, propositions, telescopes -/

mutual

@[simp] theorem Ty.rename_id {s : Sig} (T : Ty s) : T.rename Rename.id = T := by
  match T with
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
  | .bnd T => simp [Proposition.rename, Ty.rename_id T]
  | .hasVal ℓ => simp [Proposition.rename]
  | .alias q => simp [Proposition.rename, Path.rename_id q]

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
  | .bnd T => simp [Proposition.rename, Ty.rename_comp T]
  | .hasVal ℓ => simp [Proposition.rename]
  | .alias q => simp [Proposition.rename, Path.rename_comp q]

@[simp] theorem Telescope.rename_comp {s1 s2 s3 : Sig} (Tel : Telescope s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (Tel.rename ρ).rename ρ' = Tel.rename (ρ.comp ρ') := by
  match Tel with
  | .nil => simp [Telescope.rename]
  | .cons Tel P =>
      simp [Telescope.rename, Telescope.rename_comp Tel, Proposition.rename_comp P]

end

/-! ## Witnesses

Witnesses mention types only, and the `node` constructor of `PathCo` carries
them, so their two renaming laws come before the evidence's. -/

@[simp] theorem Witnesses.rename_id {s : Sig} (W : Witnesses s) : W.rename Rename.id = W := by
  match W with
  | .nil => simp [Witnesses.rename]
  | .cons W ℓ T => simp [Witnesses.rename, Witnesses.rename_id W]

@[simp] theorem Witnesses.rename_comp {s1 s2 s3 : Sig} (W : Witnesses s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (W.rename ρ).rename ρ' = W.rename (ρ.comp ρ') := by
  match W with
  | .nil => simp [Witnesses.rename]
  | .cons W ℓ T => simp [Witnesses.rename, Witnesses.rename_comp W]

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
  | .obj Tel m => simp [LeCo.rename, Rename.lift_id, Morphism.rename_id m, Telescope.rename_id Tel]
  | .pair Tel₁ Tel₂ e f =>
      simp [LeCo.rename, Rename.lift_id, Telescope.rename_id Tel₁, Telescope.rename_id Tel₂,
        LeCo.rename_id e, LeCo.rename_id f]
  | .bound Tel i => simp [LeCo.rename, Rename.lift_id, Telescope.rename_id Tel]
  | .intoBnd e => simp [LeCo.rename, LeCo.rename_id e]
  | .member a e i => simp [LeCo.rename, Atom.rename_id a, LeCo.rename_id e]
  | .memberP P e i => simp [LeCo.rename, PathCo.rename_id P, LeCo.rename_id e]

@[simp] theorem EqCo.rename_id {s : Sig} (φ : EqCo s) : φ.rename Rename.id = φ := by
  match φ with
  | .refl T => simp [EqCo.rename]
  | .symm φ => simp [EqCo.rename, EqCo.rename_id φ]
  | .trans φ ψ => simp [EqCo.rename, EqCo.rename_id φ, EqCo.rename_id ψ]
  | .def x ℓ => simp [EqCo.rename]
  | .defP p ℓ => simp [EqCo.rename]
  | .member a e i => simp [EqCo.rename, Atom.rename_id a, LeCo.rename_id e]
  | .memberP P e i => simp [EqCo.rename, PathCo.rename_id P, LeCo.rename_id e]

@[simp] theorem Has.rename_id {s : Sig} (h : Has s) : h.rename Rename.id = h := by
  match h with
  | .member a e i => simp [Has.rename, Atom.rename_id a, LeCo.rename_id e]
  | .memberP P e i => simp [Has.rename, PathCo.rename_id P, LeCo.rename_id e]
  | .field ℓ => simp [Has.rename]

@[simp] theorem Side.rename_id {s : Sig} (σ : Side s) : σ.rename Rename.id = σ := by
  match σ with
  | .none => simp [Side.rename]
  | .some e => simp [Side.rename, LeCo.rename_id e]
  | .bot X => simp [Side.rename, Rename.lift_id, Ty.rename_id]
  | .top X => simp [Side.rename, Rename.lift_id, Ty.rename_id]

@[simp] theorem Morphism.rename_id {s : Sig} (m : Morphism s) : m.rename Rename.id = m := by
  match m with
  | .nil => simp [Morphism.rename]
  | .le m pre h post =>
      simp [Morphism.rename, Morphism.rename_id m, Side.rename_id pre, Side.rename_id post]
  | .eq m j b => simp [Morphism.rename, Morphism.rename_id m]
  | .has m j => simp [Morphism.rename, Morphism.rename_id m]
  | .bnd m e => simp [Morphism.rename, Morphism.rename_id m, LeCo.rename_id e]
  | .hasVal m j => simp [Morphism.rename, Morphism.rename_id m]
  | .hasOfVal m j => simp [Morphism.rename, Morphism.rename_id m]
  | .aliasCopy m j => simp [Morphism.rename, Morphism.rename_id m]

@[simp] theorem Atom.rename_id {s : Sig} (a : Atom s) : a.rename Rename.id = a := by
  match a with
  | .var x => simp [Atom.rename]
  | .cast a e => simp [Atom.rename, Atom.rename_id a, LeCo.rename_id e]
  | .foldSelf Tel a => simp [Atom.rename, Rename.lift_id, Atom.rename_id a, Telescope.rename_id Tel]
  | .unfoldSelf a => simp [Atom.rename, Atom.rename_id a]
  | .both Tel₁ Tel₂ a b =>
      simp [Atom.rename, Rename.lift_id, Telescope.rename_id Tel₁, Telescope.rename_id Tel₂,
        Atom.rename_id a, Atom.rename_id b]
  | .sngl a q α => simp [Atom.rename, Atom.rename_id a, AliasCo.rename_id α]

@[simp] theorem PathCo.rename_id {s : Sig} (P : PathCo s) : P.rename Rename.id = P := by
  match P with
  | .var x => simp [PathCo.rename]
  | .sel P a i => simp [PathCo.rename, PathCo.rename_id P]
  | .cast P e => simp [PathCo.rename, PathCo.rename_id P, LeCo.rename_id e]
  | .alias α p P =>
      simp [PathCo.rename, AliasCo.rename_id α, PathCo.rename_id P]
  | .foldSelf Tel P =>
      simp [PathCo.rename, Rename.lift_id, Telescope.rename_id Tel, PathCo.rename_id P]
  | .unfoldSelf P => simp [PathCo.rename, PathCo.rename_id P]
  | .both Tel₁ Tel₂ P Q =>
      simp [PathCo.rename, Rename.lift_id, Telescope.rename_id Tel₁, Telescope.rename_id Tel₂,
        PathCo.rename_id P, PathCo.rename_id Q]
  | .sngl P q α => simp [PathCo.rename, PathCo.rename_id P, AliasCo.rename_id α]
  | .node p W ls vls => simp [PathCo.rename, Rename.lift_id]

@[simp] theorem AliasCo.rename_id {s : Sig} (α : AliasCo s) : α.rename Rename.id = α := by
  match α with
  | .refl p => simp [AliasCo.rename]
  | .symm α => simp [AliasCo.rename, AliasCo.rename_id α]
  | .trans α β => simp [AliasCo.rename, AliasCo.rename_id α, AliasCo.rename_id β]
  | .sel α a => simp [AliasCo.rename, AliasCo.rename_id α]
  | .member P e i => simp [AliasCo.rename, PathCo.rename_id P, LeCo.rename_id e]

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
  | .obj Tel m =>
      simp [LeCo.rename, Rename.lift_comp, Morphism.rename_comp m, Telescope.rename_comp Tel]
  | .pair Tel₁ Tel₂ e f =>
      simp [LeCo.rename, Rename.lift_comp, Telescope.rename_comp Tel₁, Telescope.rename_comp Tel₂,
        LeCo.rename_comp e, LeCo.rename_comp f]
  | .bound Tel i => simp [LeCo.rename, Rename.lift_comp, Telescope.rename_comp Tel]
  | .intoBnd e => simp [LeCo.rename, LeCo.rename_comp e]
  | .member a e i => simp [LeCo.rename, Atom.rename_comp a, LeCo.rename_comp e]
  | .memberP P e i => simp [LeCo.rename, PathCo.rename_comp P, LeCo.rename_comp e]

@[simp] theorem EqCo.rename_comp {s1 s2 s3 : Sig} (φ : EqCo s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (φ.rename ρ).rename ρ' = φ.rename (ρ.comp ρ') := by
  match φ with
  | .refl T => simp [EqCo.rename]
  | .symm φ => simp [EqCo.rename, EqCo.rename_comp φ]
  | .trans φ ψ => simp [EqCo.rename, EqCo.rename_comp φ, EqCo.rename_comp ψ]
  | .def x ℓ => simp [EqCo.rename]
  | .defP p ℓ => simp [EqCo.rename, Path.rename_comp]
  | .member a e i => simp [EqCo.rename, Atom.rename_comp a, LeCo.rename_comp e]
  | .memberP P e i => simp [EqCo.rename, PathCo.rename_comp P, LeCo.rename_comp e]

@[simp] theorem Has.rename_comp {s1 s2 s3 : Sig} (h : Has s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (h.rename ρ).rename ρ' = h.rename (ρ.comp ρ') := by
  match h with
  | .member a e i => simp [Has.rename, Atom.rename_comp a, LeCo.rename_comp e]
  | .memberP P e i => simp [Has.rename, PathCo.rename_comp P, LeCo.rename_comp e]
  | .field ℓ => simp [Has.rename]

@[simp] theorem Side.rename_comp {s1 s2 s3 : Sig} (σ : Side s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (σ.rename ρ).rename ρ' = σ.rename (ρ.comp ρ') := by
  match σ with
  | .none => simp [Side.rename]
  | .some e => simp [Side.rename, LeCo.rename_comp e]
  | .bot X => simp [Side.rename, Rename.lift_comp, Ty.rename_comp]
  | .top X => simp [Side.rename, Rename.lift_comp, Ty.rename_comp]

@[simp] theorem Morphism.rename_comp {s1 s2 s3 : Sig} (m : Morphism s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (m.rename ρ).rename ρ' = m.rename (ρ.comp ρ') := by
  match m with
  | .nil => simp [Morphism.rename]
  | .le m pre h post =>
      simp [Morphism.rename, Morphism.rename_comp m, Side.rename_comp pre, Side.rename_comp post]
  | .eq m j b => simp [Morphism.rename, Morphism.rename_comp m]
  | .has m j => simp [Morphism.rename, Morphism.rename_comp m]
  | .bnd m e => simp [Morphism.rename, Morphism.rename_comp m, LeCo.rename_comp e]
  | .hasVal m j => simp [Morphism.rename, Morphism.rename_comp m]
  | .hasOfVal m j => simp [Morphism.rename, Morphism.rename_comp m]
  | .aliasCopy m j => simp [Morphism.rename, Morphism.rename_comp m]

@[simp] theorem Atom.rename_comp {s1 s2 s3 : Sig} (a : Atom s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (a.rename ρ).rename ρ' = a.rename (ρ.comp ρ') := by
  match a with
  | .var x => simp [Atom.rename]
  | .cast a e => simp [Atom.rename, Atom.rename_comp a, LeCo.rename_comp e]
  | .foldSelf Tel a => simp [Atom.rename, Rename.lift_comp, Atom.rename_comp a, Telescope.rename_comp Tel]
  | .unfoldSelf a => simp [Atom.rename, Atom.rename_comp a]
  | .both Tel₁ Tel₂ a b =>
      simp [Atom.rename, Rename.lift_comp, Telescope.rename_comp Tel₁, Telescope.rename_comp Tel₂,
        Atom.rename_comp a, Atom.rename_comp b]
  | .sngl a q α =>
      simp [Atom.rename, Atom.rename_comp a, AliasCo.rename_comp α, Path.rename_comp]

@[simp] theorem PathCo.rename_comp {s1 s2 s3 : Sig} (P : PathCo s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (P.rename ρ).rename ρ' = P.rename (ρ.comp ρ') := by
  match P with
  | .var x => simp [PathCo.rename]
  | .sel P a i => simp [PathCo.rename, PathCo.rename_comp P]
  | .cast P e => simp [PathCo.rename, PathCo.rename_comp P, LeCo.rename_comp e]
  | .alias α p P =>
      simp [PathCo.rename, AliasCo.rename_comp α, PathCo.rename_comp P, Path.rename_comp]
  | .foldSelf Tel P =>
      simp [PathCo.rename, Rename.lift_comp, Telescope.rename_comp Tel, PathCo.rename_comp P]
  | .unfoldSelf P => simp [PathCo.rename, PathCo.rename_comp P]
  | .both Tel₁ Tel₂ P Q =>
      simp [PathCo.rename, Rename.lift_comp, Telescope.rename_comp Tel₁,
        Telescope.rename_comp Tel₂, PathCo.rename_comp P, PathCo.rename_comp Q]
  | .sngl P q α =>
      simp [PathCo.rename, PathCo.rename_comp P, AliasCo.rename_comp α, Path.rename_comp]
  | .node p W ls vls => simp [PathCo.rename, Rename.lift_comp, Path.rename_comp]

@[simp] theorem AliasCo.rename_comp {s1 s2 s3 : Sig} (α : AliasCo s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (α.rename ρ).rename ρ' = α.rename (ρ.comp ρ') := by
  match α with
  | .refl p => simp [AliasCo.rename, Path.rename_comp]
  | .symm α => simp [AliasCo.rename, AliasCo.rename_comp α]
  | .trans α β => simp [AliasCo.rename, AliasCo.rename_comp α, AliasCo.rename_comp β]
  | .sel α a => simp [AliasCo.rename, AliasCo.rename_comp α]
  | .member P e i => simp [AliasCo.rename, PathCo.rename_comp P, LeCo.rename_comp e]

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
  | .both Tel₁ Tel₂ a b => simp [Atom.rename, Atom.root, Atom.root_rename a]
  | .sngl a q α => simp [Atom.rename, Atom.root, Atom.root_rename a]

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
  | .both Tel₁ Tel₂ a b => simp [Atom.subst, Atom.root, Atom.root_subst a]
  | .sngl a q α => simp [Atom.subst, Atom.root, Atom.root_subst a]

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
  | .pair Tel₁ Tel₂ e f =>
      simp [LeCo.subst, LeCo.rename, LeCo.subst_ofRename e, LeCo.subst_ofRename f,
        Subst.ofRename_root]
  | .bound Tel i => simp [LeCo.subst, LeCo.rename, Subst.ofRename_root]
  | .intoBnd e => simp [LeCo.subst, LeCo.rename, LeCo.subst_ofRename e]
  | .member a e i => simp [LeCo.subst, LeCo.rename, Atom.subst_ofRename a, LeCo.subst_ofRename e]
  | .memberP P e i =>
      simp [LeCo.subst, LeCo.rename, PathCo.subst_ofRename P, LeCo.subst_ofRename e]

@[simp] theorem EqCo.subst_ofRename {s1 s2 : Sig} (φ : EqCo s1) (ρ : Rename s1 s2) :
    φ.subst (Subst.ofRename ρ) = φ.rename ρ := by
  match φ with
  | .refl T => simp [EqCo.subst, EqCo.rename]
  | .symm φ => simp [EqCo.subst, EqCo.rename, EqCo.subst_ofRename φ]
  | .trans φ ψ => simp [EqCo.subst, EqCo.rename, EqCo.subst_ofRename φ, EqCo.subst_ofRename ψ]
  | .def x ℓ => simp [EqCo.subst, EqCo.rename]
  | .defP p ℓ => simp [EqCo.subst, EqCo.rename, Subst.ofRename_root]
  | .member a e i => simp [EqCo.subst, EqCo.rename, Atom.subst_ofRename a, LeCo.subst_ofRename e]
  | .memberP P e i =>
      simp [EqCo.subst, EqCo.rename, PathCo.subst_ofRename P, LeCo.subst_ofRename e]

@[simp] theorem Has.subst_ofRename {s1 s2 : Sig} (h : Has s1) (ρ : Rename s1 s2) :
    h.subst (Subst.ofRename ρ) = h.rename ρ := by
  match h with
  | .member a e i => simp [Has.subst, Has.rename, Atom.subst_ofRename a, LeCo.subst_ofRename e]
  | .memberP P e i =>
      simp [Has.subst, Has.rename, PathCo.subst_ofRename P, LeCo.subst_ofRename e]
  | .field ℓ => simp [Has.subst, Has.rename]

@[simp] theorem Side.subst_ofRename {s1 s2 : Sig} (σ : Side s1) (ρ : Rename s1 s2) :
    σ.subst (Subst.ofRename ρ) = σ.rename ρ := by
  match σ with
  | .none => simp [Side.subst, Side.rename]
  | .some e => simp [Side.subst, Side.rename, LeCo.subst_ofRename e]
  | .bot X => simp [Side.subst, Side.rename, Subst.ofRename_root]
  | .top X => simp [Side.subst, Side.rename, Subst.ofRename_root]

@[simp] theorem Morphism.subst_ofRename {s1 s2 : Sig} (m : Morphism s1) (ρ : Rename s1 s2) :
    m.subst (Subst.ofRename ρ) = m.rename ρ := by
  match m with
  | .nil => simp [Morphism.subst, Morphism.rename]
  | .le m pre h post =>
      simp [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m, Side.subst_ofRename pre,
        Side.subst_ofRename post]
  | .eq m j b => simp [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m]
  | .has m j => simp [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m]
  | .bnd m e =>
      simp [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m, LeCo.subst_ofRename e]
  | .hasVal m j => simp [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m]
  | .hasOfVal m j => simp [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m]
  | .aliasCopy m j => simp [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m]

@[simp] theorem Atom.subst_ofRename {s1 s2 : Sig} (a : Atom s1) (ρ : Rename s1 s2) :
    a.subst (Subst.ofRename ρ) = a.rename ρ := by
  match a with
  | .var x => simp [Atom.subst, Atom.rename, Subst.ofRename]
  | .cast a e => simp [Atom.subst, Atom.rename, Atom.subst_ofRename a, LeCo.subst_ofRename e]
  | .foldSelf Tel a => simp [Atom.subst, Atom.rename, Atom.subst_ofRename a, Subst.ofRename_root]
  | .unfoldSelf a => simp [Atom.subst, Atom.rename, Atom.subst_ofRename a]
  | .both Tel₁ Tel₂ a b =>
      simp [Atom.subst, Atom.rename, Atom.subst_ofRename a, Atom.subst_ofRename b,
        Subst.ofRename_root]
  | .sngl a q α =>
      simp [Atom.subst, Atom.rename, Atom.subst_ofRename a, AliasCo.subst_ofRename α,
        Subst.ofRename_root]

@[simp] theorem PathCo.subst_ofRename {s1 s2 : Sig} (P : PathCo s1) (ρ : Rename s1 s2) :
    P.subst (Subst.ofRename ρ) = P.rename ρ := by
  match P with
  | .var x => simp [PathCo.subst, PathCo.rename, Subst.ofRename, Atom.toPathCo]
  | .sel P a i => simp [PathCo.subst, PathCo.rename, PathCo.subst_ofRename P]
  | .cast P e =>
      simp [PathCo.subst, PathCo.rename, PathCo.subst_ofRename P, LeCo.subst_ofRename e]
  | .alias α p P =>
      simp [PathCo.subst, PathCo.rename, AliasCo.subst_ofRename α, PathCo.subst_ofRename P,
        Subst.ofRename_root]
  | .foldSelf Tel P =>
      simp [PathCo.subst, PathCo.rename, PathCo.subst_ofRename P, Subst.ofRename_root]
  | .unfoldSelf P => simp [PathCo.subst, PathCo.rename, PathCo.subst_ofRename P]
  | .both Tel₁ Tel₂ P Q =>
      simp [PathCo.subst, PathCo.rename, PathCo.subst_ofRename P, PathCo.subst_ofRename Q,
        Subst.ofRename_root]
  | .sngl P q α =>
      simp [PathCo.subst, PathCo.rename, PathCo.subst_ofRename P, AliasCo.subst_ofRename α,
        Subst.ofRename_root]
  | .node p W ls vls => simp [PathCo.subst, PathCo.rename, Subst.ofRename_root]

@[simp] theorem AliasCo.subst_ofRename {s1 s2 : Sig} (α : AliasCo s1) (ρ : Rename s1 s2) :
    α.subst (Subst.ofRename ρ) = α.rename ρ := by
  match α with
  | .refl p => simp [AliasCo.subst, AliasCo.rename, Subst.ofRename_root]
  | .symm α => simp [AliasCo.subst, AliasCo.rename, AliasCo.subst_ofRename α]
  | .trans α β =>
      simp [AliasCo.subst, AliasCo.rename, AliasCo.subst_ofRename α, AliasCo.subst_ofRename β]
  | .sel α a => simp [AliasCo.subst, AliasCo.rename, AliasCo.subst_ofRename α]
  | .member P e i =>
      simp [AliasCo.subst, AliasCo.rename, PathCo.subst_ofRename P, LeCo.subst_ofRename e]

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

/-! ## The substitution layer for `substPath`

`Ty.substVar` is a renaming, `Ty.substPath` is a genuine substitution, and the
two live side by side.  This section is the substitution layer: the two
composition laws, one per order of a renaming and a path substitution, and the
commutation of `substPath` with renaming that follows from them.
`substPath_var` is the bridge back to the renaming layer. -/

@[simp] theorem Path.subst_var {s1 s2 : Sig} (x : BVar s1 .var) (σ : PathSubst s1 s2) :
    (Path.var x).subst σ = σ.var x := rfl

@[simp] theorem Path.subst_sel {s1 s2 : Sig} (p : Path s1) (ℓ : Label) (σ : PathSubst s1 s2) :
    (Path.sel p ℓ).subst σ = .sel (p.subst σ) ℓ := rfl

theorem Path.weaken_rename {s1 s2 : Sig} {k : Kind} (p : Path s1) (ρ : Rename s1 s2) :
    (p.weaken (k := k)).rename ρ.lift = (p.rename ρ).weaken := by
  simp only [Path.weaken, Path.rename_comp, Rename.succ_lift]

theorem PathSubst.lift_compRename {s1 s2 s3 : Sig} (σ : PathSubst s1 s2) (ρ : Rename s2 s3) :
    (σ.compRename ρ).lift = σ.lift.compRename ρ.lift := by
  apply PathSubst.funext'
  intro x
  cases x with
  | here => rfl
  | there y =>
      simp only [PathSubst.lift, PathSubst.compRename]
      exact (Path.weaken_rename (σ.var y) ρ).symm

theorem Rename.lift_pathComp {s1 s2 s3 : Sig} (ρ : Rename s1 s2) (σ : PathSubst s2 s3) :
    (ρ.pathComp σ).lift = ρ.lift.pathComp σ.lift := by
  apply PathSubst.funext'
  intro x
  cases x <;> rfl

theorem Path.subst_rename {s1 s2 s3 : Sig} (p : Path s1) (σ : PathSubst s1 s2)
    (ρ : Rename s2 s3) : (p.subst σ).rename ρ = p.subst (σ.compRename ρ) := by
  induction p with
  | var x => rfl
  | sel p ℓ ih => exact congrArg (Path.sel · ℓ) ih

theorem Path.rename_subst {s1 s2 s3 : Sig} (p : Path s1) (ρ : Rename s1 s2)
    (σ : PathSubst s2 s3) : (p.rename ρ).subst σ = p.subst (ρ.pathComp σ) := by
  induction p with
  | var x => rfl
  | sel p ℓ ih => exact congrArg (Path.sel · ℓ) ih

mutual

theorem Ty.subst_rename {s1 s2 s3 : Sig} :
    ∀ (T : Ty s1) (σ : PathSubst s1 s2) (ρ : Rename s2 s3),
      (T.subst σ).rename ρ = T.subst (σ.compRename ρ)
  | .bot, _, _ => rfl
  | .sel p ℓ, σ, ρ => by simp only [Ty.subst, Ty.rename, Path.subst_rename]
  | .pi S T, σ, ρ => by
      simp only [Ty.subst, Ty.rename, Ty.subst_rename S σ ρ, Ty.subst_rename T σ.lift ρ.lift,
        PathSubst.lift_compRename]
  | .obj Tel, σ, ρ => by
      simp only [Ty.subst, Ty.rename, Telescope.subst_rename Tel σ.lift ρ.lift,
        PathSubst.lift_compRename]

theorem Proposition.subst_rename {s1 s2 s3 : Sig} :
    ∀ (P : Proposition s1) (σ : PathSubst s1 s2) (ρ : Rename s2 s3),
      (P.subst σ).rename ρ = P.subst (σ.compRename ρ)
  | .le S T, σ, ρ => by
      simp only [Proposition.subst, Proposition.rename, Ty.subst_rename S σ ρ,
        Ty.subst_rename T σ ρ]
  | .eq S T, σ, ρ => by
      simp only [Proposition.subst, Proposition.rename, Ty.subst_rename S σ ρ,
        Ty.subst_rename T σ ρ]
  | .has ℓ, _, _ => rfl
  | .bnd T, σ, ρ => by
      simp only [Proposition.subst, Proposition.rename, Ty.subst_rename T σ ρ]
  | .hasVal ℓ, _, _ => rfl
  | .alias q, σ, ρ => by
      simp only [Proposition.subst, Proposition.rename, Path.subst_rename q σ ρ]

theorem Telescope.subst_rename {s1 s2 s3 : Sig} :
    ∀ (Tel : Telescope s1) (σ : PathSubst s1 s2) (ρ : Rename s2 s3),
      (Tel.subst σ).rename ρ = Tel.subst (σ.compRename ρ)
  | .nil, _, _ => rfl
  | .cons Tel P, σ, ρ => by
      simp only [Telescope.subst, Telescope.rename, Telescope.subst_rename Tel σ ρ,
        Proposition.subst_rename P σ ρ]

end

mutual

theorem Ty.rename_subst {s1 s2 s3 : Sig} :
    ∀ (T : Ty s1) (ρ : Rename s1 s2) (σ : PathSubst s2 s3),
      (T.rename ρ).subst σ = T.subst (ρ.pathComp σ)
  | .bot, _, _ => rfl
  | .sel p ℓ, ρ, σ => by simp only [Ty.subst, Ty.rename, Path.rename_subst]
  | .pi S T, ρ, σ => by
      simp only [Ty.subst, Ty.rename, Ty.rename_subst S ρ σ, Ty.rename_subst T ρ.lift σ.lift,
        Rename.lift_pathComp]
  | .obj Tel, ρ, σ => by
      simp only [Ty.subst, Ty.rename, Telescope.rename_subst Tel ρ.lift σ.lift,
        Rename.lift_pathComp]

theorem Proposition.rename_subst {s1 s2 s3 : Sig} :
    ∀ (P : Proposition s1) (ρ : Rename s1 s2) (σ : PathSubst s2 s3),
      (P.rename ρ).subst σ = P.subst (ρ.pathComp σ)
  | .le S T, ρ, σ => by
      simp only [Proposition.subst, Proposition.rename, Ty.rename_subst S ρ σ,
        Ty.rename_subst T ρ σ]
  | .eq S T, ρ, σ => by
      simp only [Proposition.subst, Proposition.rename, Ty.rename_subst S ρ σ,
        Ty.rename_subst T ρ σ]
  | .has ℓ, _, _ => rfl
  | .bnd T, ρ, σ => by
      simp only [Proposition.subst, Proposition.rename, Ty.rename_subst T ρ σ]
  | .hasVal ℓ, _, _ => rfl
  | .alias q, ρ, σ => by
      simp only [Proposition.subst, Proposition.rename, Path.rename_subst q ρ σ]

theorem Telescope.rename_subst {s1 s2 s3 : Sig} :
    ∀ (Tel : Telescope s1) (ρ : Rename s1 s2) (σ : PathSubst s2 s3),
      (Tel.rename ρ).subst σ = Tel.subst (ρ.pathComp σ)
  | .nil, _, _ => rfl
  | .cons Tel P, ρ, σ => by
      simp only [Telescope.subst, Telescope.rename, Telescope.rename_subst Tel ρ σ,
        Proposition.rename_subst P ρ σ]

end

/-- Renaming a one-binder path substitution: the two composition laws meet
here, and the commutation of `substPath` with renaming follows. -/
theorem PathSubst.one_compRename {s1 s2 : Sig} (q : Path s1) (ρ : Rename s1 s2) :
    (PathSubst.one q).compRename ρ = ρ.lift.pathComp (PathSubst.one (q.rename ρ)) := by
  apply PathSubst.funext'
  intro x
  cases x <;> rfl

theorem Path.substPath_rename {s1 s2 : Sig} (p : Path (s1,x)) (q : Path s1) (ρ : Rename s1 s2) :
    (p.substPath q).rename ρ = (p.rename ρ.lift).substPath (q.rename ρ) := by
  rw [← Path.subst_one, ← Path.subst_one, Path.subst_rename, Path.rename_subst,
    PathSubst.one_compRename]

theorem Ty.substPath_rename {s1 s2 : Sig} (T : Ty (s1,x)) (q : Path s1) (ρ : Rename s1 s2) :
    (T.substPath q).rename ρ = (T.rename ρ.lift).substPath (q.rename ρ) := by
  rw [Ty.substPath, Ty.substPath, Ty.subst_rename, Ty.rename_subst, PathSubst.one_compRename]

theorem Proposition.substPath_rename {s1 s2 : Sig} (P : Proposition (s1,x)) (q : Path s1)
    (ρ : Rename s1 s2) :
    (P.substPath q).rename ρ = (P.rename ρ.lift).substPath (q.rename ρ) := by
  rw [Proposition.substPath, Proposition.substPath, Proposition.subst_rename,
    Proposition.rename_subst, PathSubst.one_compRename]

theorem Telescope.substPath_rename {s1 s2 : Sig} (Tel : Telescope (s1,x)) (q : Path s1)
    (ρ : Rename s1 s2) :
    (Tel.substPath q).rename ρ = (Tel.rename ρ.lift).substPath (q.rename ρ) := by
  rw [Telescope.substPath, Telescope.substPath, Telescope.subst_rename, Telescope.rename_subst,
    PathSubst.one_compRename]

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

/-! ## Concatenation commutes with renaming -/

@[simp] theorem Telescope.append_nil {s : Sig} (Tel : Telescope s) : Tel ++ .nil = Tel := rfl

@[simp] theorem Telescope.append_cons {s : Sig} (Tel Tel' : Telescope s) (P : Proposition s) :
    Tel ++ (Tel' ▹ P) = (Tel ++ Tel') ▹ P := rfl

@[simp] theorem Telescope.append_rename {s1 s2 : Sig} :
    ∀ (Tel Tel' : Telescope s1) (ρ : Rename s1 s2),
      (Tel ++ Tel').rename ρ = Tel.rename ρ ++ Tel'.rename ρ
  | _, .nil, _ => rfl
  | Tel, .cons Tel' P, ρ => by
      simp [Telescope.append_cons, Telescope.rename, Telescope.append_rename Tel Tel' ρ]

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

@[simp] theorem Telescope.hasValEntries_rename {s1 s2 : Sig} :
    ∀ (Tel : Telescope s1) (ls : List Label) (ρ : Rename s1 s2),
      (Tel.hasValEntries ls).rename ρ = (Tel.rename ρ).hasValEntries ls
  | _, [], _ => rfl
  | Tel, l :: ls, ρ => by
      simp [Telescope.hasValEntries, Telescope.hasValEntries_rename (Tel.cons (.hasVal l)) ls ρ,
        Telescope.rename, Proposition.rename]

theorem Telescope.ofLiteral_rename {s1 s2 : Sig} (W : Witnesses (s1,x))
    (ls vls : List Label) (ρ : Rename s1 s2) :
    (Telescope.ofLiteral W ls vls).rename ρ.lift
      = Telescope.ofLiteral (W.rename ρ.lift) ls vls := by
  simp [Telescope.ofLiteral]

/-! ## Instantiating weakened syntax, injectivity of renaming -/


theorem Ty.weaken_substVar (T : Ty s) (r : BVar s .var) :
    (T.weaken (k := .var))⟦r⟧ = T := by
  simp only [Ty.weaken, Ty.substVar, Ty.rename_comp]
  rw [show (Rename.succ.comp (Rename.subst r) : Rename s s) = Rename.id from
    Rename.funext' (by intro k y; cases k; rfl)]
  exact Ty.rename_id T

theorem Proposition.weaken_substVar (P : Proposition s) (r : BVar s .var) :
    (P.weaken (k := .var))⟦r⟧ = P := by
  simp only [Proposition.weaken, Proposition.substVar, Proposition.rename_comp]
  rw [show (Rename.succ.comp (Rename.subst r) : Rename s s) = Rename.id from
    Rename.funext' (by intro k y; cases k; rfl)]
  exact Proposition.rename_id P

/-! ### Injectivity of renaming -/

def Rename.Injective (ρ : Rename s1 s2) : Prop :=
  ∀ {k} (x y : BVar s1 k), ρ.var x = ρ.var y → x = y

theorem Rename.Injective.lift {ρ : Rename s1 s2} (h : ρ.Injective) {k : Kind} :
    (ρ.lift (k := k)).Injective := by
  intro k' x y hxy
  cases x <;> cases y <;> simp at hxy
  · rfl
  · rw [h _ _ hxy]

theorem Rename.succ_injective {s : Sig} {k : Kind} : (Rename.succ (s := s) (k := k)).Injective := by
  intro k' x y hxy
  simpa using hxy

theorem Path.rename_inj {s1 s2 : Sig} : ∀ (p p' : Path s1) (ρ : Rename s1 s2),
    ρ.Injective → p.rename ρ = p'.rename ρ → p = p'
  | .var x, .var y, ρ, hρ, h => by
      simp only [Path.rename_var, Path.var.injEq] at h ⊢
      exact hρ _ _ h
  | .var _, .sel _ _, _, _, h => by simp at h
  | .sel _ _, .var _, _, _, h => by simp at h
  | .sel p ℓ, .sel p' ℓ', ρ, hρ, h => by
      simp only [Path.rename_sel, Path.sel.injEq] at h ⊢
      exact ⟨Path.rename_inj p p' ρ hρ h.1, h.2⟩

mutual

theorem Ty.rename_inj {s1 s2 : Sig} (T T' : Ty s1) (ρ : Rename s1 s2) (hρ : ρ.Injective)
    (h : T.rename ρ = T'.rename ρ) : T = T' := by
  match T with
  | .bot => cases T' <;> simp [Ty.rename] at h ⊢
  | .sel p ℓ =>
      cases T' <;> simp [Ty.rename] at h ⊢
      exact ⟨Path.rename_inj p _ ρ hρ h.1, h.2⟩
  | .pi S T =>
      cases T' <;> simp [Ty.rename] at h ⊢
      exact ⟨Ty.rename_inj S _ ρ hρ h.1, Ty.rename_inj T _ ρ.lift hρ.lift h.2⟩
  | .obj Tel =>
      cases T' <;> simp [Ty.rename] at h ⊢
      exact Telescope.rename_inj Tel _ ρ.lift hρ.lift h

theorem Proposition.rename_inj {s1 s2 : Sig} (P P' : Proposition s1) (ρ : Rename s1 s2)
    (hρ : ρ.Injective) (h : P.rename ρ = P'.rename ρ) : P = P' := by
  match P with
  | .le S T =>
      cases P' <;> simp [Proposition.rename] at h ⊢
      exact ⟨Ty.rename_inj S _ ρ hρ h.1, Ty.rename_inj T _ ρ hρ h.2⟩
  | .eq S T =>
      cases P' <;> simp [Proposition.rename] at h ⊢
      exact ⟨Ty.rename_inj S _ ρ hρ h.1, Ty.rename_inj T _ ρ hρ h.2⟩
  | .has ℓ => cases P' <;> simp [Proposition.rename] at h ⊢ <;> exact h
  | .hasVal ℓ => cases P' <;> simp [Proposition.rename] at h ⊢ <;> exact h
  | .alias q =>
      cases P' <;> simp [Proposition.rename] at h ⊢
      exact Path.rename_inj q _ ρ hρ h
  | .bnd T =>
      cases P' <;> simp [Proposition.rename] at h ⊢
      exact Ty.rename_inj T _ ρ hρ h

theorem Telescope.rename_inj {s1 s2 : Sig} (Tel Tel' : Telescope s1) (ρ : Rename s1 s2)
    (hρ : ρ.Injective) (h : Tel.rename ρ = Tel'.rename ρ) : Tel = Tel' := by
  match Tel with
  | .nil => cases Tel' <;> simp [Telescope.rename] at h ⊢
  | .cons Tel P =>
      cases Tel' <;> simp [Telescope.rename] at h ⊢
      exact ⟨Telescope.rename_inj Tel _ ρ hρ h.1, Proposition.rename_inj P _ ρ hρ h.2⟩

end

theorem Telescope.weaken_inj {Tel₁ Tel₂ : Telescope s} {k : Kind}
    (h : (Tel₁.weaken (k := k)) = Tel₂↑) : Tel₁ = Tel₂ :=
  Telescope.rename_inj _ _ _ Rename.succ_injective h

@[simp] theorem Telescope.weaken_nil {s : Sig} {k : Kind} :
    (Telescope.nil (s := s)).weaken (k := k) = .nil := rfl

@[simp] theorem Telescope.weaken_cons (Tel : Telescope s) (P : Proposition s) {k : Kind} :
    (Tel.cons P).weaken (k := k) = Tel↑.cons P↑ := rfl

@[simp] theorem Proposition.weaken_le (S T : Ty s) {k : Kind} :
    (Proposition.le S T).weaken (k := k) = .le S↑ T↑ := rfl

@[simp] theorem Proposition.weaken_eq (S T : Ty s) {k : Kind} :
    (Proposition.eq S T).weaken (k := k) = .eq S↑ T↑ := rfl

@[simp] theorem Proposition.weaken_has (ℓ : Label) {k : Kind} :
    (Proposition.has (s := s) ℓ).weaken (k := k) = .has ℓ := rfl

@[simp] theorem Proposition.weaken_hasVal (ℓ : Label) {k : Kind} :
    (Proposition.hasVal (s := s) ℓ).weaken (k := k) = .hasVal ℓ := rfl

@[simp] theorem Proposition.weaken_alias (q : Path s) {k : Kind} :
    (Proposition.alias q).weaken (k := k) = .alias (q.weaken) := rfl

@[simp] theorem Proposition.weaken_bnd (T : Ty s) {k : Kind} :
    (Proposition.bnd T).weaken (k := k) = .bnd T↑ := rfl

theorem Telescope.weaken_substVar (Tel : Telescope s) (r : BVar s .var) :
    (Tel.weaken (k := .var))⟦r⟧ = Tel := by
  simp only [Telescope.weaken, Telescope.substVar, Telescope.rename_comp]
  rw [show (Rename.succ.comp (Rename.subst r) : Rename s s) = Rename.id from
    Rename.funext' (by intro k y; cases k; rfl)]
  exact Telescope.rename_id Tel

/-- Instantiating a self-substituted, weakened proposition at any root gives
the original instantiation. -/
theorem Proposition.substVar_weaken_substVar (P : Proposition (s,x)) (r r' : BVar s .var) :
    ((P⟦r⟧).weaken (k := .var))⟦r'⟧ = P⟦r⟧ := by
  rw [Proposition.weaken_substVar]

theorem Telescope.At.weaken {Tel : Telescope s} {i : Nat} {P : Proposition s}
    (h : Tel.At i P) : (Tel.weaken (k := .var)).At i (P↑) := by
  induction h with
  | here => simp only [Telescope.weaken, Telescope.rename]; rw [← Telescope.length_rename]; exact .here
  | there _ ih => exact .there ih

/-! ### Instantiating weakened syntax by a path

The twins of `Ty.weaken_substVar` and its family, one layer over.  At a
variable path each is the `substVar` lemma, by `Ty.substPath_var`. -/

/-- A one-binder path substitution undoes a weakening. -/
theorem PathSubst.succ_pathComp_one {s : Sig} (q : Path s) :
    (Rename.succ (k := .var)).pathComp (PathSubst.one q) = PathSubst.ofRename Rename.id := by
  apply PathSubst.funext'
  intro x
  rfl

theorem Ty.weaken_substPath (T : Ty s) (q : Path s) :
    (T.weaken (k := .var)).substPath q = T := by
  rw [Ty.substPath, Ty.weaken, Ty.rename_subst, PathSubst.succ_pathComp_one, Ty.subst_ofRename]
  exact Ty.rename_id T

theorem Proposition.weaken_substPath (P : Proposition s) (q : Path s) :
    (P.weaken (k := .var)).substPath q = P := by
  rw [Proposition.substPath, Proposition.weaken, Proposition.rename_subst,
    PathSubst.succ_pathComp_one, Proposition.subst_ofRename]
  exact Proposition.rename_id P

theorem Telescope.weaken_substPath (Tel : Telescope s) (q : Path s) :
    (Tel.weaken (k := .var)).substPath q = Tel := by
  rw [Telescope.substPath, Telescope.weaken, Telescope.rename_subst,
    PathSubst.succ_pathComp_one, Telescope.subst_ofRename]
  exact Telescope.rename_id Tel

/-- The singleton object type of a path renames as its path does. -/
@[simp] theorem Ty.snglOf_rename {s1 s2 : Sig} (q : Path s1) (ρ : Rename s1 s2) :
    (Ty.snglOf q).rename ρ = Ty.snglOf (q.rename ρ) := by
  simp [Ty.snglOf, Ty.rename, Telescope.rename, Proposition.rename, Path.weaken_rename]

theorem Path.weaken_substPath (p : Path s) (q : Path s) :
    (p.weaken (k := .var)).substPath q = p := by
  rw [← Path.subst_one, Path.weaken, Path.rename_subst, PathSubst.succ_pathComp_one,
    Path.subst_ofRename]
  exact Path.rename_id p

/-- The singleton object type determines its path. -/
theorem Ty.snglOf_inj {s : Sig} {p q : Path s} (h : Ty.snglOf p = Ty.snglOf q) : p = q := by
  simp only [Ty.snglOf, Ty.obj.injEq, Telescope.cons.injEq, Proposition.alias.injEq,
    true_and] at h
  have h2 := congrArg (fun r : Path (s,x) => r.substPath p) h
  simpa [Path.weaken_substPath] using h2


/-- Instantiating a self-substituted, weakened proposition at any path gives
the original instantiation. -/
theorem Proposition.substPath_weaken_substPath (P : Proposition (s,x)) (q q' : Path s) :
    ((P.substPath q).weaken (k := .var)).substPath q' = P.substPath q := by
  rw [Proposition.weaken_substPath]

@[simp] theorem Telescope.length_subst {s1 s2 : Sig} :
    ∀ (Tel : Telescope s1) (σ : PathSubst s1 s2), (Tel.subst σ).length = Tel.length
  | .nil, _ => rfl
  | .cons Tel P, σ => by
      simp [Telescope.subst, Telescope.length, Telescope.length_subst Tel σ]

@[simp] theorem Telescope.length_substPath {s : Sig} (Tel : Telescope (s,x)) (q : Path s) :
    (Tel.substPath q).length = Tel.length := Telescope.length_subst Tel _

theorem Telescope.At.substPath {Tel : Telescope (s,x)} {i : Nat} {P : Proposition (s,x)}
    (h : Tel.At i P) (q : Path s) : (Tel.substPath q).At i (P.substPath q) := by
  induction h with
  | @here Tel P =>
      rw [Telescope.substPath_cons, ← Telescope.length_substPath Tel q]
      exact Telescope.At.here
  | there _ ih => exact Telescope.At.there ih

theorem Telescope.At.substPath_inv : {Tel : Telescope (s,x)} → {q : Path s} → {i : Nat} →
    {P : Proposition s} → (Tel.substPath q).At i P → ∃ P₀, Tel.At i P₀ ∧ P = P₀.substPath q
  | .nil, _, _, _, h => by rw [Telescope.substPath_nil] at h; cases h
  | .cons Tel Q, q, i, P, h => by
      rw [Telescope.substPath_cons] at h
      cases h with
      | here => exact ⟨Q, by rw [Telescope.length_substPath]; exact .here, rfl⟩
      | there h' =>
          obtain ⟨P₀, hP₀, rfl⟩ := Telescope.At.substPath_inv h'
          exact ⟨P₀, .there hP₀, rfl⟩

@[simp] theorem Telescope.append_substPath {s : Sig} :
    ∀ (Tel Tel' : Telescope (s,x)) (q : Path s),
      (Tel ++ Tel').substPath q = Tel.substPath q ++ Tel'.substPath q
  | _, .nil, _ => rfl
  | Tel, .cons Tel' P, q => by
      simp [Telescope.append_cons, Telescope.substPath_cons,
        Telescope.append_substPath Tel Tel' q]

theorem Telescope.At.rename_inv : {Tel : Telescope s1} → {ρ : Rename s1 s2} → {i : Nat} →
    {P : Proposition s2} → (Tel.rename ρ).At i P → ∃ P₀, Tel.At i P₀ ∧ P = P₀.rename ρ
  | .nil, _, _, _, h => by simp [Telescope.rename] at h; cases h
  | .cons Tel Q, ρ, i, P, h => by
      simp only [Telescope.rename] at h
      cases h with
      | here => exact ⟨Q, by rw [Telescope.length_rename]; exact .here, rfl⟩
      | there h' =>
          obtain ⟨P₀, hP₀, rfl⟩ := Telescope.At.rename_inv h'
          exact ⟨P₀, .there hP₀, rfl⟩

/-! ## The block layer

Witnesses and blocks carry the same two layers as types: a renaming layer and
a path-substitution layer, with the commutation between them.  This is what
lets the block of a stored value be weakened through the context spine. -/

@[simp] theorem Witnesses.subst_ofRename {s1 s2 : Sig} :
    ∀ (W : Witnesses s1) (ρ : Rename s1 s2),
      W.subst (PathSubst.ofRename ρ) = W.rename ρ
  | .nil, _ => rfl
  | .cons W ℓ T, ρ => by
      simp [Witnesses.subst, Witnesses.rename, Witnesses.subst_ofRename W ρ, Ty.subst_ofRename]

/-- Witness lookup commutes with a path substitution. -/
theorem Witnesses.get_subst {s1 s2 : Sig} :
    ∀ (W : Witnesses s1) (ℓ : Label) (σ : PathSubst s1 s2),
      (W.subst σ).get ℓ = (W.get ℓ).subst σ
  | .nil, _, _ => rfl
  | .cons W ℓ' T, ℓ, σ => by
      by_cases h : ℓ = ℓ'
      · simp [Witnesses.subst, Witnesses.get, h]
      · simp [Witnesses.subst, Witnesses.get, h, Witnesses.get_subst W ℓ σ]

theorem Witnesses.subst_rename {s1 s2 s3 : Sig} :
    ∀ (W : Witnesses s1) (σ : PathSubst s1 s2) (ρ : Rename s2 s3),
      (W.subst σ).rename ρ = W.subst (σ.compRename ρ)
  | .nil, _, _ => rfl
  | .cons W ℓ T, σ, ρ => by
      simp only [Witnesses.subst, Witnesses.rename, Witnesses.subst_rename W σ ρ,
        Ty.subst_rename T σ ρ]

theorem Witnesses.rename_subst {s1 s2 s3 : Sig} :
    ∀ (W : Witnesses s1) (ρ : Rename s1 s2) (σ : PathSubst s2 s3),
      (W.rename ρ).subst σ = W.subst (ρ.pathComp σ)
  | .nil, _, _ => rfl
  | .cons W ℓ T, ρ, σ => by
      simp only [Witnesses.subst, Witnesses.rename, Witnesses.rename_subst W ρ σ,
        Ty.rename_subst T ρ σ]

theorem Witnesses.substPath_rename {s1 s2 : Sig} (W : Witnesses (s1,x)) (q : Path s1)
    (ρ : Rename s1 s2) :
    (W.substPath q).rename ρ = (W.rename ρ.lift).substPath (q.rename ρ) := by
  rw [Witnesses.substPath, Witnesses.substPath, Witnesses.subst_rename,
    Witnesses.rename_subst, PathSubst.one_compRename]

/-- Substituting a variable path is the renaming `Rename.subst`. -/
@[simp] theorem Witnesses.substPath_var {s : Sig} (W : Witnesses (s,x)) (y : BVar s .var) :
    W.substPath (.var y) = W.rename (Rename.subst y) := by
  rw [Witnesses.substPath, PathSubst.one_var, Witnesses.subst_ofRename]

mutual

theorem Block.subst_rename {s1 s2 s3 : Sig} :
    ∀ (B : Block s1) (σ : PathSubst s1 s2) (ρ : Rename s2 s3),
      (B.subst σ).rename ρ = B.subst (σ.compRename ρ)
  | .obj W ls vls ch, σ, ρ => by
      simp only [Block.subst, Block.rename, Witnesses.subst_rename W σ ρ,
        Children.subst_rename ch σ ρ]
  | .fwd q, σ, ρ => by
      simp only [Block.subst, Block.rename, Path.subst_rename]

theorem Children.subst_rename {s1 s2 s3 : Sig} :
    ∀ (ch : Children s1) (σ : PathSubst s1 s2) (ρ : Rename s2 s3),
      (ch.subst σ).rename ρ = ch.subst (σ.compRename ρ)
  | .nil, _, _ => rfl
  | .cons ch ℓ B, σ, ρ => by
      simp only [Children.subst, Children.rename, Children.subst_rename ch σ ρ,
        Block.subst_rename B σ ρ]

end

mutual

theorem Block.rename_subst {s1 s2 s3 : Sig} :
    ∀ (B : Block s1) (ρ : Rename s1 s2) (σ : PathSubst s2 s3),
      (B.rename ρ).subst σ = B.subst (ρ.pathComp σ)
  | .obj W ls vls ch, ρ, σ => by
      simp only [Block.subst, Block.rename, Witnesses.rename_subst W ρ σ,
        Children.rename_subst ch ρ σ]
  | .fwd q, ρ, σ => by
      simp only [Block.subst, Block.rename, Path.rename_subst]

theorem Children.rename_subst {s1 s2 s3 : Sig} :
    ∀ (ch : Children s1) (ρ : Rename s1 s2) (σ : PathSubst s2 s3),
      (ch.rename ρ).subst σ = ch.subst (ρ.pathComp σ)
  | .nil, _, _ => rfl
  | .cons ch ℓ B, ρ, σ => by
      simp only [Children.subst, Children.rename, Children.rename_subst ch ρ σ,
        Block.rename_subst B ρ σ]

end

theorem Block.substPath_rename {s1 s2 : Sig} (B : Block (s1,x)) (q : Path s1)
    (ρ : Rename s1 s2) :
    (B.substPath q).rename ρ = (B.rename ρ.lift).substPath (q.rename ρ) := by
  rw [Block.substPath, Block.substPath, Block.subst_rename, Block.rename_subst,
    PathSubst.one_compRename]

theorem Children.substPath_rename {s1 s2 : Sig} (ch : Children (s1,x)) (q : Path s1)
    (ρ : Rename s1 s2) :
    (ch.substPath q).rename ρ = (ch.rename ρ.lift).substPath (q.rename ρ) := by
  rw [Children.substPath, Children.substPath, Children.subst_rename, Children.rename_subst,
    PathSubst.one_compRename]

mutual

@[simp] theorem Block.subst_ofRename {s1 s2 : Sig} :
    ∀ (B : Block s1) (ρ : Rename s1 s2), B.subst (PathSubst.ofRename ρ) = B.rename ρ
  | .obj W ls vls ch, ρ => by
      simp only [Block.subst, Block.rename, Witnesses.subst_ofRename,
        Children.subst_ofRename ch ρ]
  | .fwd q, ρ => by simp only [Block.subst, Block.rename, Path.subst_ofRename]

@[simp] theorem Children.subst_ofRename {s1 s2 : Sig} :
    ∀ (ch : Children s1) (ρ : Rename s1 s2), ch.subst (PathSubst.ofRename ρ) = ch.rename ρ
  | .nil, _ => rfl
  | .cons ch ℓ B, ρ => by
      simp only [Children.subst, Children.rename, Children.subst_ofRename ch ρ,
        Block.subst_ofRename B ρ]

end

mutual

@[simp] theorem Block.rename_id {s : Sig} : ∀ B : Block s, B.rename Rename.id = B
  | .obj W ls vls ch => by
      simp [Block.rename, Witnesses.rename_id W, Children.rename_id ch]
  | .fwd q => by simp [Block.rename]

@[simp] theorem Children.rename_id {s : Sig} : ∀ ch : Children s, ch.rename Rename.id = ch
  | .nil => rfl
  | .cons ch a B => by simp [Children.rename, Children.rename_id ch, Block.rename_id B]

end

mutual

@[simp] theorem Block.rename_comp {s1 s2 s3 : Sig} :
    ∀ (B : Block s1) (ρ : Rename s1 s2) (ρ' : Rename s2 s3),
      (B.rename ρ).rename ρ' = B.rename (ρ.comp ρ')
  | .obj W ls vls ch, ρ, ρ' => by
      simp only [Block.rename, Witnesses.rename_comp, Children.rename_comp ch ρ ρ']
  | .fwd q, ρ, ρ' => by simp only [Block.rename, Path.rename_comp]

@[simp] theorem Children.rename_comp {s1 s2 s3 : Sig} :
    ∀ (ch : Children s1) (ρ : Rename s1 s2) (ρ' : Rename s2 s3),
      (ch.rename ρ).rename ρ' = ch.rename (ρ.comp ρ')
  | .nil, _, _ => rfl
  | .cons ch a B, ρ, ρ' => by
      simp only [Children.rename, Children.rename_comp ch ρ ρ', Block.rename_comp B ρ ρ']

end

mutual

@[simp] theorem Block.fwdCount_rename {s1 s2 : Sig} :
    ∀ (B : Block s1) (ρ : Rename s1 s2), (B.rename ρ).fwdCount = B.fwdCount
  | .obj W ls vls ch, ρ => by
      simp only [Block.rename, Block.fwdCount, Children.fwdCount_rename ch ρ]
  | .fwd q, _ => rfl

@[simp] theorem Children.fwdCount_rename {s1 s2 : Sig} :
    ∀ (ch : Children s1) (ρ : Rename s1 s2), (ch.rename ρ).fwdCount = ch.fwdCount
  | .nil, _ => rfl
  | .cons ch a B, ρ => by
      simp only [Children.rename, Children.fwdCount, Children.fwdCount_rename ch ρ,
        Block.fwdCount_rename B ρ]

end

theorem Children.at?_rename {s1 s2 : Sig} : ∀ (ch : Children s1) (ρ : Rename s1 s2) (a : Label),
    (ch.rename ρ).at? a = (ch.at? a).map (Block.rename · ρ)
  | .nil, _, _ => rfl
  | .cons ch a' b, ρ, a => by
      by_cases h : a = a' <;>
        simp [Children.rename, Children.at?, h, Children.at?_rename ch ρ a]

/-- Substituting a variable path is a renaming, as it is on types. -/
@[simp] theorem Block.substPath_var {s : Sig} (B : Block (s,x)) (y : BVar s .var) :
    B.substPath (.var y) = B.rename (Rename.subst y) := by
  rw [Block.substPath, PathSubst.one_var, Block.subst_ofRename]

@[simp] theorem Children.substPath_var {s : Sig} (ch : Children (s,x)) (y : BVar s .var) :
    ch.substPath (.var y) = ch.rename (Rename.subst y) := by
  rw [Children.substPath, PathSubst.one_var, Children.subst_ofRename]

/-! ## The block builder against renaming -/

mutual
@[simp] theorem LeCo.tableOnly_rename : ∀ (e : LeCo s1) (ρ : Rename s1 s2),
    (e.rename ρ).tableOnly = e.tableOnly
  | .refl _, _ => rfl
  | .trans e f, ρ => by
      simp [LeCo.rename, LeCo.tableOnly, LeCo.tableOnly_rename e ρ, LeCo.tableOnly_rename f ρ]
  | .top _, _ => rfl
  | .bot _, _ => rfl
  | .eqToLe φ, ρ => by simp [LeCo.rename, LeCo.tableOnly, EqCo.tableOnly_rename φ ρ]
  | .pi _ _, _ => rfl
  | .obj _ m, ρ => by simp [LeCo.rename, LeCo.tableOnly, Morphism.tableOnly_rename m ρ]
  | .pair _ _ e f, ρ => by
      simp [LeCo.rename, LeCo.tableOnly, LeCo.tableOnly_rename e ρ, LeCo.tableOnly_rename f ρ]
  | .bound _ _, _ => rfl
  | .intoBnd e, ρ => by simp [LeCo.rename, LeCo.tableOnly, LeCo.tableOnly_rename e ρ]
  | .member _ _ _, _ => rfl
  | .memberP _ _ _, _ => rfl

theorem EqCo.tableOnly_rename : ∀ (φ : EqCo s1) (ρ : Rename s1 s2),
    (φ.rename ρ).tableOnly = φ.tableOnly
  | .refl _, _ => rfl
  | .symm φ, ρ => by simp [EqCo.rename, EqCo.tableOnly, EqCo.tableOnly_rename φ ρ]
  | .trans φ ψ, ρ => by
      simp [EqCo.rename, EqCo.tableOnly, EqCo.tableOnly_rename φ ρ, EqCo.tableOnly_rename ψ ρ]
  | .def _ _, _ => rfl
  | .defP _ _, _ => rfl
  | .member _ _ _, _ => rfl
  | .memberP _ _ _, _ => rfl

theorem Side.tableOnly_rename : ∀ (p : Side s1) (ρ : Rename s1 s2),
    (p.rename ρ).tableOnly = p.tableOnly
  | .none, _ => rfl
  | .some e, ρ => by simp [Side.rename, Side.tableOnly, LeCo.tableOnly_rename e ρ]
  | .bot _, _ => rfl
  | .top _, _ => rfl

theorem Morphism.tableOnly_rename : ∀ (m : Morphism s1) (ρ : Rename s1 s2),
    (m.rename ρ).tableOnly = m.tableOnly
  | .nil, _ => rfl
  | .le m pre _ post, ρ => by
      simp [Morphism.rename, Morphism.tableOnly, Morphism.tableOnly_rename m ρ,
        Side.tableOnly_rename pre ρ, Side.tableOnly_rename post ρ]
  | .eq m _ _, ρ => by simp [Morphism.rename, Morphism.tableOnly, Morphism.tableOnly_rename m ρ]
  | .has m _, ρ => by simp [Morphism.rename, Morphism.tableOnly, Morphism.tableOnly_rename m ρ]
  | .bnd m e, ρ => by
      simp [Morphism.rename, Morphism.tableOnly, Morphism.tableOnly_rename m ρ,
        LeCo.tableOnly_rename e ρ]
  | .hasVal m _, ρ => by simp [Morphism.rename, Morphism.tableOnly, Morphism.tableOnly_rename m ρ]
  | .hasOfVal m _, ρ => by
      simp [Morphism.rename, Morphism.tableOnly, Morphism.tableOnly_rename m ρ]
  | .aliasCopy m _, ρ => by
      simp [Morphism.rename, Morphism.tableOnly, Morphism.tableOnly_rename m ρ]
end

@[simp] theorem Value.isStableLit_rename {s1 s2 : Sig} :
    ∀ (v : Value s1) (ρ : Rename s1 s2), (v.rename ρ).isStableLit = v.isStableLit
  | .obj _ _, _ => rfl
  | .lam _ _, _ => rfl
  | .cast v e, ρ => by
      simp [Value.rename, Value.isStableLit, Value.isStableLit_rename v ρ, LeCo.tableOnly_rename]

@[simp] theorem Value.isObjLit_rename {s1 s2 : Sig} :
    ∀ (v : Value s1) (ρ : Rename s1 s2), (v.rename ρ).isObjLit = v.isObjLit
  | .obj _ _, _ => rfl
  | .lam _ _, _ => rfl
  | .cast v _, ρ => Value.isObjLit_rename v ρ

@[simp] theorem Tm.isStable_rename {s1 s2 : Sig} :
    ∀ (t : Tm s1) (ρ : Rename s1 s2), (t.rename ρ).isStable = t.isStable
  | .atom _, _ => rfl
  | .val v, ρ => Value.isStableLit_rename v ρ
  | .cast t e, ρ => by
      simp [Tm.rename, Tm.isStable, Tm.isStable_rename t ρ, LeCo.tableOnly_rename]
  | .app _ _, _ => rfl
  | .proj _ _ _, _ => rfl
  | .let _ _, _ => rfl

@[simp] theorem Fields.valLabels_rename {s1 s2 : Sig} :
    ∀ (F : Fields s1) (ρ : Rename s1 s2), (F.rename ρ).valLabels = F.valLabels
  | .nil, _ => rfl
  | .cons F ℓ t, ρ => by
      have ht : (t.rename ρ).isStable = t.isStable := Tm.isStable_rename t ρ
      simp [Fields.rename, Fields.valLabels, ht, Fields.valLabels_rename F ρ]

@[simp] theorem Fields.labels_rename {s1 s2 : Sig} :
    ∀ (F : Fields s1) (ρ : Rename s1 s2), (F.rename ρ).labels = F.labels
  | .nil, _ => rfl
  | .cons F ℓ t, ρ => by
      simp [Fields.rename, Fields.labels, Fields.labels_rename F ρ]

mutual

theorem Value.blockSelf_rename {s1 s2 : Sig} :
    ∀ (v : Value s1) (ρ : Rename s1 s2),
      (v.rename ρ).blockSelf = v.blockSelf.rename ρ.lift
  | .lam _ _, _ => rfl
  | .cast v _, ρ => Value.blockSelf_rename v ρ
  | .obj W F, ρ => by
      have hch : (F.rename ρ.lift).children (.var .here)
          = (F.children (.var .here)).rename ρ.lift := by
        have h := Fields.children_rename F (.var .here) ρ.lift
        simpa [Path.rename] using h
      simp only [Value.rename, Value.blockSelf, Block.rename, Fields.labels_rename,
        Fields.valLabels_rename, hch]

theorem Fields.children_rename {s1 s2 : Sig} :
    ∀ (F : Fields s1) (p : Path s1) (ρ : Rename s1 s2),
      (F.rename ρ).children (p.rename ρ) = (F.children p).rename ρ
  | .nil, _, _ => rfl
  | .cons F ℓ t, p, ρ => by
      have ht := Tm.childAt_rename t (.sel p ℓ) ρ
      have hF := Fields.children_rename F p ρ
      show (Fields.rename (.cons F ℓ t) ρ).children (p.rename ρ) = _
      simp only [Fields.rename, Fields.children]
      show (match ((t.rename ρ).childAt (.sel (p.rename ρ) ℓ)) with
            | some b => Children.cons ((F.rename ρ).children (p.rename ρ)) ℓ b
            | none => ((F.rename ρ).children (p.rename ρ)).dropLabel ℓ)
        = Children.rename (match t.childAt (.sel p ℓ) with
            | some b => .cons (F.children p) ℓ b
            | none => (F.children p).dropLabel ℓ) ρ
      have hp : Path.sel (p.rename ρ) ℓ = (Path.sel p ℓ).rename ρ := rfl
      rw [hp, ht, hF]
      cases t.childAt (.sel p ℓ) with
      | none => exact Children.dropLabel_rename _ ρ ℓ
      | some b => rfl

theorem Tm.childAt_rename {s1 s2 : Sig} :
    ∀ (t : Tm s1) (p : Path s1) (ρ : Rename s1 s2),
      (t.rename ρ).childAt (p.rename ρ) = (t.childAt p).map (Block.rename · ρ)
  | .val v, p, ρ => by
      simp only [Tm.rename, Tm.childAt, Value.isStableLit_rename]
      cases v.isStableLit with
      | false => rfl
      | true =>
          simp only [if_true, Option.map_some]
          rw [Value.blockSelf_rename v ρ, Block.substPath_rename]
  | .atom a, p, ρ => by
      simp [Tm.rename, Tm.childAt, Block.rename, Path.rename, Atom.root_rename]
  | .cast t e, p, ρ => by
      simp only [Tm.rename, Tm.childAt, Tm.isStable_rename, LeCo.tableOnly_rename]
      split
      · rfl
      · exact Tm.childAt_rename t p ρ
  | .app _ _, _, _ => rfl
  | .proj _ _ _, _, _ => rfl
  | .let _ _, _, _ => rfl

end

/-- The children of a literal's fields at the self path, against a renaming. -/
@[simp] theorem Fields.children_self_rename {s1 s2 : Sig} (F : Fields (s1,x))
    (ρ : Rename s1 s2) :
    (F.rename ρ.lift).children (.var .here) = (F.children (.var .here)).rename ρ.lift := by
  simpa [Path.rename] using Fields.children_rename F (.var .here) ρ.lift

theorem Value.blocksAt_rename {s1 s2 : Sig} (v : Value s1) (p : Path s1) (ρ : Rename s1 s2) :
    (v.rename ρ).blocksAt (p.rename ρ) = (v.blocksAt p).rename ρ := by
  rw [Value.blocksAt, Value.blocksAt, Value.blockSelf_rename, Block.substPath_rename]

/-- The block of a stored value, weakened through one context binder. -/
@[simp] theorem Value.blocksAt_weaken {s : Sig} (v : Value s) (y : BVar s .var) :
    (v.weaken (k := .var)).blocksAt (.var (.there y)) = (v.blocksAt (.var y)).weaken := by
  have h := Value.blocksAt_rename v (.var y) (Rename.succ (s := s) (k := .var))
  simpa [Value.weaken, Block.weaken, Path.rename] using h

end FCdot

end Paths
