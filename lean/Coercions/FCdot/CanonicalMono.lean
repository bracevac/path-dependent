import Coercions.FCdot.RenameLemmas
import Coercions.FCdot.Canonical

/-!
# Fuel monotonicity and the algebra of forms, views and environments

Two independent developments that the metatheory of `Canonical.lean` needs.

* The normalizer is fuel-indexed; adding fuel never destroys a success.  The
  one delicate point is that `closedAtomForm` consults `storeEnv n σ`, and
  `storeEnv` is itself fuel-indexed with a `getD []` fallback, so more fuel
  may *change* the store environment.  Monotonicity is therefore proved
  relative to `StoreEnvStable σ n`, which says that the store environment
  has already stabilised below `n`.

* The algebraic laws of environments (atoms, views, the induced closing
  substitution), of views (`nth?` against append and renaming) and of forms
  (`combine` against `id`/`bot`/`top` and renaming).  The renaming law for
  `combine` needs the two commutations of renaming with substitution, which
  are proved here in the style of `RenameLemmas.lean`.

* The decomposition of a chain application along a concatenation of chains,
  `applyChain_append`, which the canonical-forms argument needs in order to
  split an object coercion built by `Form.combine`.
-/

namespace FCdot

/-! ## Composition of a substitution with a renaming -/

/-- Substitute, then rename. -/
def Subst.compRename (τ : Subst s1 s2) (ρ : Rename s2 s3) : Subst s1 s3 where
  var := fun x => (τ.var x).rename ρ

/-- Rename, then substitute. -/
def Rename.compSubst (ρ : Rename s1 s2) (τ : Subst s2 s3) : Subst s1 s3 where
  var := fun x => τ.var (ρ.var x)

@[simp] theorem Subst.compRename_var (τ : Subst s1 s2) (ρ : Rename s2 s3) (x : BVar s1 .var) :
    (τ.compRename ρ).var x = (τ.var x).rename ρ := rfl

@[simp] theorem Rename.compSubst_var (ρ : Rename s1 s2) (τ : Subst s2 s3) (x : BVar s1 .var) :
    (ρ.compSubst τ).var x = τ.var (ρ.var x) := rfl

@[simp] theorem Subst.compRename_root (τ : Subst s1 s2) (ρ : Rename s2 s3) :
    (τ.compRename ρ).root = τ.root.comp ρ := by
  apply Rename.funext'
  intro k x
  cases k
  simp [Subst.root_var, Subst.compRename]

@[simp] theorem Rename.compSubst_root (ρ : Rename s1 s2) (τ : Subst s2 s3) :
    (ρ.compSubst τ).root = ρ.comp τ.root := by
  apply Rename.funext'
  intro k x
  cases k
  simp [Subst.root_var, Rename.compSubst]

@[simp] theorem Subst.compRename_lift (τ : Subst s1 s2) (ρ : Rename s2 s3) :
    (τ.compRename ρ).lift = τ.lift.compRename ρ.lift := by
  apply Subst.funext'
  intro x
  cases x with
  | here => simp [Subst.lift, Subst.compRename, Atom.rename]
  | there y =>
      simp only [Subst.lift, Subst.compRename, Atom.weaken, Atom.rename_comp]
      rw [Rename.succ_lift]

@[simp] theorem Rename.compSubst_lift (ρ : Rename s1 s2) (τ : Subst s2 s3) :
    (ρ.compSubst τ).lift = ρ.lift.compSubst τ.lift := by
  apply Subst.funext'
  intro x
  cases x with
  | here => simp [Subst.lift, Rename.compSubst]
  | there y => simp [Subst.lift, Rename.compSubst]

/-! ## Renaming after substitution -/

mutual

theorem LeCo.rename_subst {s1 s2 s3 : Sig} (e : LeCo s1) (τ : Subst s1 s2) (ρ : Rename s2 s3) :
    (e.subst τ).rename ρ = e.subst (τ.compRename ρ) := by
  match e with
  | .refl T => simp [LeCo.subst, LeCo.rename]
  | .trans e f => simp [LeCo.subst, LeCo.rename, LeCo.rename_subst e, LeCo.rename_subst f]
  | .top T => simp [LeCo.subst, LeCo.rename]
  | .bot T => simp [LeCo.subst, LeCo.rename]
  | .eqToLe φ => simp [LeCo.subst, LeCo.rename, EqCo.rename_subst φ]
  | .pi e f => simp [LeCo.subst, LeCo.rename, LeCo.rename_subst e, LeCo.rename_subst f]
  | .obj Tel m =>
      simp [LeCo.subst, LeCo.rename, Morphism.rename_subst m, Rename.lift_comp]
  | .member a e i =>
      simp [LeCo.subst, LeCo.rename, Atom.rename_subst a, LeCo.rename_subst e]

theorem EqCo.rename_subst {s1 s2 s3 : Sig} (φ : EqCo s1) (τ : Subst s1 s2) (ρ : Rename s2 s3) :
    (φ.subst τ).rename ρ = φ.subst (τ.compRename ρ) := by
  match φ with
  | .refl T => simp [EqCo.subst, EqCo.rename]
  | .symm φ => simp [EqCo.subst, EqCo.rename, EqCo.rename_subst φ]
  | .trans φ ψ => simp [EqCo.subst, EqCo.rename, EqCo.rename_subst φ, EqCo.rename_subst ψ]
  | .def x ℓ => simp [EqCo.subst, EqCo.rename]
  | .member a e i =>
      simp [EqCo.subst, EqCo.rename, Atom.rename_subst a, LeCo.rename_subst e]

theorem Has.rename_subst {s1 s2 s3 : Sig} (h : Has s1) (τ : Subst s1 s2) (ρ : Rename s2 s3) :
    (h.subst τ).rename ρ = h.subst (τ.compRename ρ) := by
  match h with
  | .member a e i => simp [Has.subst, Has.rename, Atom.rename_subst a, LeCo.rename_subst e]
  | .field ℓ => simp [Has.subst, Has.rename]

theorem Morphism.rename_subst {s1 s2 s3 : Sig} (m : Morphism s1) (τ : Subst s1 s2)
    (ρ : Rename s2 s3) :
    (m.subst τ).rename ρ = m.subst (τ.compRename ρ) := by
  match m with
  | .nil => simp [Morphism.subst, Morphism.rename]
  | .le m e => simp [Morphism.subst, Morphism.rename, Morphism.rename_subst m, LeCo.rename_subst e]
  | .eq m φ => simp [Morphism.subst, Morphism.rename, Morphism.rename_subst m, EqCo.rename_subst φ]
  | .has m h => simp [Morphism.subst, Morphism.rename, Morphism.rename_subst m, Has.rename_subst h]

theorem Atom.rename_subst {s1 s2 s3 : Sig} (a : Atom s1) (τ : Subst s1 s2) (ρ : Rename s2 s3) :
    (a.subst τ).rename ρ = a.subst (τ.compRename ρ) := by
  match a with
  | .var x => simp [Atom.subst, Subst.compRename]
  | .cast a e => simp [Atom.subst, Atom.rename, Atom.rename_subst a, LeCo.rename_subst e]
  | .foldSelf Tel a =>
      simp [Atom.subst, Atom.rename, Atom.rename_subst a, Rename.lift_comp]
  | .unfoldSelf a => simp [Atom.subst, Atom.rename, Atom.rename_subst a]

end

/-! ## Substitution after renaming -/

mutual

theorem LeCo.subst_rename {s1 s2 s3 : Sig} (e : LeCo s1) (ρ : Rename s1 s2) (τ : Subst s2 s3) :
    (e.rename ρ).subst τ = e.subst (ρ.compSubst τ) := by
  match e with
  | .refl T => simp [LeCo.subst, LeCo.rename]
  | .trans e f => simp [LeCo.subst, LeCo.rename, LeCo.subst_rename e, LeCo.subst_rename f]
  | .top T => simp [LeCo.subst, LeCo.rename]
  | .bot T => simp [LeCo.subst, LeCo.rename]
  | .eqToLe φ => simp [LeCo.subst, LeCo.rename, EqCo.subst_rename φ]
  | .pi e f => simp [LeCo.subst, LeCo.rename, LeCo.subst_rename e, LeCo.subst_rename f]
  | .obj Tel m =>
      simp [LeCo.subst, LeCo.rename, Morphism.subst_rename m, Rename.lift_comp]
  | .member a e i =>
      simp [LeCo.subst, LeCo.rename, Atom.subst_rename a, LeCo.subst_rename e]

theorem EqCo.subst_rename {s1 s2 s3 : Sig} (φ : EqCo s1) (ρ : Rename s1 s2) (τ : Subst s2 s3) :
    (φ.rename ρ).subst τ = φ.subst (ρ.compSubst τ) := by
  match φ with
  | .refl T => simp [EqCo.subst, EqCo.rename]
  | .symm φ => simp [EqCo.subst, EqCo.rename, EqCo.subst_rename φ]
  | .trans φ ψ => simp [EqCo.subst, EqCo.rename, EqCo.subst_rename φ, EqCo.subst_rename ψ]
  | .def x ℓ => simp [EqCo.subst, EqCo.rename]
  | .member a e i =>
      simp [EqCo.subst, EqCo.rename, Atom.subst_rename a, LeCo.subst_rename e]

theorem Has.subst_rename {s1 s2 s3 : Sig} (h : Has s1) (ρ : Rename s1 s2) (τ : Subst s2 s3) :
    (h.rename ρ).subst τ = h.subst (ρ.compSubst τ) := by
  match h with
  | .member a e i => simp [Has.subst, Has.rename, Atom.subst_rename a, LeCo.subst_rename e]
  | .field ℓ => simp [Has.subst, Has.rename]

theorem Morphism.subst_rename {s1 s2 s3 : Sig} (m : Morphism s1) (ρ : Rename s1 s2)
    (τ : Subst s2 s3) :
    (m.rename ρ).subst τ = m.subst (ρ.compSubst τ) := by
  match m with
  | .nil => simp [Morphism.subst, Morphism.rename]
  | .le m e => simp [Morphism.subst, Morphism.rename, Morphism.subst_rename m, LeCo.subst_rename e]
  | .eq m φ => simp [Morphism.subst, Morphism.rename, Morphism.subst_rename m, EqCo.subst_rename φ]
  | .has m h => simp [Morphism.subst, Morphism.rename, Morphism.subst_rename m, Has.subst_rename h]

theorem Atom.subst_rename {s1 s2 s3 : Sig} (a : Atom s1) (ρ : Rename s1 s2) (τ : Subst s2 s3) :
    (a.rename ρ).subst τ = a.subst (ρ.compSubst τ) := by
  match a with
  | .var x => simp [Atom.subst, Atom.rename, Rename.compSubst]
  | .cast a e => simp [Atom.subst, Atom.rename, Atom.subst_rename a, LeCo.subst_rename e]
  | .foldSelf Tel a =>
      simp [Atom.subst, Atom.rename, Atom.subst_rename a, Rename.lift_comp]
  | .unfoldSelf a => simp [Atom.subst, Atom.rename, Atom.subst_rename a]

end

/-- Weakening is undone by instantiating the new binder. -/
@[simp] theorem Atom.weaken_subst_single {s : Sig} (b a : Atom s) :
    (b.weaken (k := .var)).subst (Subst.single a) = b := by
  rw [Atom.weaken, Atom.subst_rename]
  have : Rename.succ.compSubst (Subst.single a) = Subst.ofRename (Rename.id (s := s)) := by
    apply Subst.funext'
    intro x
    simp [Rename.compSubst, Subst.single, Subst.ofRename]
  rw [this, Atom.subst_ofRename, Atom.rename_id]

/-! ## Environment algebra -/

namespace Env

@[simp] theorem atom_cons_here {s s' : Sig} (η : Env s s') (a : Atom s) (V : View s) :
    (η.cons a V).atom .here = a := by simp [Env.atom]

@[simp] theorem atom_cons_there {s s' : Sig} (η : Env s s') (a : Atom s) (V : View s)
    (y : BVar s' .var) : (η.cons a V).atom (.there y) = η.atom y := by simp [Env.atom]

@[simp] theorem view_cons_here {s s' : Sig} (η : Env s s') (a : Atom s) (V : View s) :
    (η.cons a V).view .here = V := by simp [Env.view]

@[simp] theorem view_cons_there {s s' : Sig} (η : Env s s') (a : Atom s) (V : View s)
    (y : BVar s' .var) : (η.cons a V).view (.there y) = η.view y := by simp [Env.view]

@[simp] theorem toSubst_var {s s' : Sig} (η : Env s s') (y : BVar s' .var) :
    η.toSubst.var y = η.atom y := rfl

theorem atom_rename {s s₂ : Sig} : ∀ {s' : Sig} (η : Env s s') (ρ : Rename s s₂)
    (y : BVar s' .var), (η.rename ρ).atom y = (η.atom y).rename ρ
  | _, .cons _ _ _, _, .here => by simp [Env.rename]
  | _, .cons η _ _, ρ, .there y => by simp [Env.rename, atom_rename η ρ y]

theorem view_rename {s s₂ : Sig} : ∀ {s' : Sig} (η : Env s s') (ρ : Rename s s₂)
    (y : BVar s' .var), (η.rename ρ).view y = PropForm.renameList (η.view y) ρ
  | _, .cons _ _ _, _, .here => by simp [Env.rename]
  | _, .cons η _ _, ρ, .there y => by simp [Env.rename, view_rename η ρ y]

theorem toSubst_rename {s s₂ s' : Sig} (η : Env s s') (ρ : Rename s s₂) :
    (η.rename ρ).toSubst = η.toSubst.compRename ρ := by
  apply Subst.funext'
  intro y
  simp [Env.atom_rename]

@[simp] theorem toSubst_cons_here {s s' : Sig} (η : Env s s') (a : Atom s) (V : View s) :
    (η.cons a V).toSubst.var .here = a := rfl

@[simp] theorem toSubst_cons_there {s s' : Sig} (η : Env s s') (a : Atom s) (V : View s)
    (y : BVar s' .var) : (η.cons a V).toSubst.var (.there y) = η.toSubst.var y := rfl

/-- The closing substitution of an extended environment factors through the
lift of the old one: extending by `a` is instantiating the new binder by `a`. -/
theorem cons_toSubst_lift {s s' : Sig} (η : Env s s') (a : Atom s) (V : View s)
    (y : BVar (s',x) .var) :
    (η.cons a V).toSubst.var y = ((η.toSubst.lift).var y).subst (Subst.single a) := by
  cases y with
  | here => simp [Subst.lift, Subst.single, Atom.subst]
  | there y => simp [Subst.lift]

theorem root_cons {s s' : Sig} (η : Env s s') (a : Atom s) (V : View s) :
    (η.cons a V).toSubst.root = η.toSubst.root.lift.comp (Rename.subst a.root) := by
  apply Rename.funext'
  intro k y
  cases k
  cases y with
  | here => simp [Subst.root_var]
  | there y => simp [Subst.root_var]

end Env

/-! ## The store environment -/

theorem emptyEnv_atom : ∀ {s : Sig} (σ : Store s) (y : BVar s .var),
    (emptyEnv σ).atom y = .var y
  | _, .cons _ _, .here => by simp [emptyEnv]
  | _, .cons σ _, .there y => by
      simp [emptyEnv, Env.weaken, Env.atom_rename, emptyEnv_atom σ y, Atom.rename]

theorem storeEnv_atom {s : Sig} (n : Nat) (σ : Store s) (y : BVar s .var) :
    (storeEnv n σ).atom y = .var y := by
  induction n generalizing s with
  | zero =>
      cases σ with
      | nil => nomatch y
      | cons σ v => rw [show storeEnv 0 (Store.cons σ v) = emptyEnv (.cons σ v) from rfl]
                    exact emptyEnv_atom _ y
  | succ n ih =>
      cases σ with
      | nil => nomatch y
      | cons σ v =>
          cases y with
          | here => simp [storeEnv]
          | there y => simp [storeEnv, Env.weaken, Env.atom_rename, ih, Atom.rename]

@[simp] theorem Env.toSubst_storeEnv_var {s : Sig} (n : Nat) (σ : Store s) (y : BVar s .var) :
    (storeEnv n σ).toSubst.var y = .var y := storeEnv_atom n σ y

theorem storeEnv_toSubst_root {s : Sig} (n : Nat) (σ : Store s) :
    (storeEnv n σ).toSubst.root = Rename.id := by
  apply Rename.funext'
  intro k y
  cases k
  simp [Subst.root_var, storeEnv_atom, Atom.root]

/-! ## Views -/

theorem View.nth?_lt_length {s : Sig} : ∀ (V : View s) (i : Nat) (P : PropForm s),
    View.nth? V i = some P → i < V.length
  | [], i, P, h => by simp [View.nth?] at h
  | _ :: V, 0, P, _ => by simp
  | _ :: V, i + 1, P, h => by
      have := View.nth?_lt_length V i P (by simpa [View.nth?] using h)
      simpa using Nat.succ_lt_succ this

theorem View.nth?_append_left {s : Sig} : ∀ (V W : View s) (i : Nat), i < V.length →
    View.nth? (V ++ W) i = View.nth? V i
  | [], _, i, h => by simp at h
  | _ :: V, W, 0, _ => by simp [View.nth?]
  | _ :: V, W, i + 1, h => by
      simp only [List.cons_append, View.nth?]
      exact View.nth?_append_left V W i (by simpa using Nat.lt_of_succ_lt_succ (by simpa using h))

theorem View.nth?_append_right {s : Sig} : ∀ (V : View s) (P : PropForm s),
    View.nth? (V ++ [P]) V.length = some P
  | [], P => by simp [View.nth?]
  | Q :: V, P => by
      simp only [List.cons_append, List.length_cons, View.nth?]
      exact View.nth?_append_right V P

@[simp] theorem PropForm.renameList_length {s s₂ : Sig} : ∀ (V : View s) (ρ : Rename s s₂),
    (PropForm.renameList V ρ).length = V.length
  | [], _ => by simp [PropForm.renameList]
  | _ :: V, ρ => by simp [PropForm.renameList, PropForm.renameList_length V ρ]

@[simp] theorem PropForm.renameList_append {s s₂ : Sig} : ∀ (V W : View s) (ρ : Rename s s₂),
    PropForm.renameList (V ++ W) ρ = PropForm.renameList V ρ ++ PropForm.renameList W ρ
  | [], _, _ => by simp [PropForm.renameList]
  | P :: V, W, ρ => by simp [PropForm.renameList, PropForm.renameList_append V W ρ]

theorem PropForm.renameList_nth? {s s₂ : Sig} : ∀ (V : View s) (ρ : Rename s s₂) (i : Nat),
    View.nth? (PropForm.renameList V ρ) i = (View.nth? V i).map (fun P => P.rename ρ)
  | [], _, _ => by simp [PropForm.renameList, View.nth?]
  | _ :: V, ρ, 0 => by simp [PropForm.renameList, View.nth?]
  | _ :: V, ρ, i + 1 => by
      simp [PropForm.renameList, View.nth?, PropForm.renameList_nth? V ρ i]

/-! ## Combining forms -/

@[simp] theorem Form.combine_id_left {s : Sig} (F : Form s) :
    (Form.id : Form s).combine F = F := by
  cases F <;> simp [Form.combine]

@[simp] theorem Form.combine_id_right {s : Sig} (F : Form s) :
    F.combine .id = F := by
  cases F <;> simp [Form.combine]

@[simp] theorem Form.combine_bot {s : Sig} (G : Form s) :
    (Form.bot : Form s).combine G = .bot := by
  cases G <;> simp [Form.combine]

theorem Form.combine_top {s : Sig} (F : Form s) (h : F ≠ .bot) :
    F.combine .top = .top := by
  cases F <;> simp_all [Form.combine]

@[simp] theorem ChainStep.renameList_append {s s₂ : Sig} :
    ∀ (cs ds : List (ChainStep s)) (ρ : Rename s s₂),
      ChainStep.renameList (cs ++ ds) ρ = ChainStep.renameList cs ρ ++ ChainStep.renameList ds ρ
  | [], _, _ => by simp [ChainStep.renameList]
  | c :: cs, ds, ρ => by simp [ChainStep.renameList, ChainStep.renameList_append cs ds ρ]

/-- Renaming commutes with the self-cast substitution used by `Form.combine`. -/
theorem LeCo.selfCast_rename {s s₂ : Sig} (c : LeCo (s,x)) (d : LeCo s) (ρ : Rename s s₂) :
    (c.subst (Subst.selfCast d.weaken)).rename ρ.lift
      = (c.rename ρ.lift).subst (Subst.selfCast (d.rename ρ).weaken) := by
  rw [LeCo.rename_subst, LeCo.subst_rename]
  congr 1
  apply Subst.funext'
  intro y
  cases y with
  | here =>
      simp [Subst.compRename, Rename.compSubst, Subst.selfCast, Atom.rename, LeCo.weaken_rename]
  | there y => simp [Subst.compRename, Rename.compSubst, Subst.selfCast, Atom.rename]

theorem Form.rename_combine {s s₂ : Sig} (F G : Form s) (ρ : Rename s s₂) :
    (F.combine G).rename ρ = (F.rename ρ).combine (G.rename ρ) := by
  cases F <;> cases G <;>
    simp [Form.combine, Form.rename, ChainStep.renameList, ChainStep.rename, LeCo.rename,
      EqCo.rename, LeCo.selfCast_rename]

theorem ChainStep.close_rename {s s₂ : Sig} (c : ChainStep s) (ρ : Rename s s₂) :
    (c.rename ρ).close = c.close.rename ρ := by
  cases c with
  | conv φ => simp [ChainStep.rename, ChainStep.close, LeCo.rename]
  | clos s' Tel m η =>
      simp [ChainStep.rename, ChainStep.close, LeCo.rename, Morphism.rename_subst,
        Env.toSubst_rename, Rename.lift_comp]

/-! ## Morphisms -/

/-- Number of propositions a morphism provides evidence for. -/
def Morphism.length : Morphism s → Nat
  | .nil => 0
  | .le m _ => m.length + 1
  | .eq m _ => m.length + 1
  | .has m _ => m.length + 1

@[simp] theorem Morphism.length_subst {s1 s2 : Sig} :
    ∀ (m : Morphism s1) (τ : Subst s1 s2), (m.subst τ).length = m.length
  | .nil, _ => rfl
  | .le m _, τ => by simp [Morphism.subst, Morphism.length, Morphism.length_subst m τ]
  | .eq m _, τ => by simp [Morphism.subst, Morphism.length, Morphism.length_subst m τ]
  | .has m _, τ => by simp [Morphism.subst, Morphism.length, Morphism.length_subst m τ]

@[simp] theorem Morphism.length_rename {s1 s2 : Sig} :
    ∀ (m : Morphism s1) (ρ : Rename s1 s2), (m.rename ρ).length = m.length
  | .nil, _ => rfl
  | .le m _, ρ => by simp [Morphism.rename, Morphism.length, Morphism.length_rename m ρ]
  | .eq m _, ρ => by simp [Morphism.rename, Morphism.length, Morphism.length_rename m ρ]
  | .has m _, ρ => by simp [Morphism.rename, Morphism.length, Morphism.length_rename m ρ]

theorem morphismView_length {s : Sig} (σ : Store s) : ∀ (n : Nat) {s' : Sig}
    (η : Env s (s',x)) (m : Morphism (s',x)) (V : View s),
    morphismView σ n η m = some V → V.length = m.length
  | 0, _, _, _, _, h => by simp [morphismView] at h
  | n + 1, s', η, m, V, h => by
      cases m with
      | nil => simp [morphismView] at h; simp [← h, Morphism.length]
      | le m e =>
          cases hm : morphismView σ n η m with
          | none => simp [morphismView, hm] at h
          | some V0 =>
              cases he : hnf σ n η e with
              | none => simp [morphismView, hm, he] at h
              | some F =>
                  simp [morphismView, hm, he] at h
                  simp [← h, Morphism.length, morphismView_length σ n η m V0 hm]
      | eq m φ =>
          cases hm : morphismView σ n η m with
          | none => simp [morphismView, hm] at h
          | some V0 =>
              simp [morphismView, hm] at h
              simp [← h, Morphism.length, morphismView_length σ n η m V0 hm]
      | has m hh =>
          cases hm : morphismView σ n η m with
          | none => simp [morphismView, hm] at h
          | some V0 =>
              cases hv : hasView σ n η .here hh with
              | none => simp [morphismView, hm, hv] at h
              | some p =>
                  simp [morphismView, hm, hv] at h
                  simp [← h, Morphism.length, morphismView_length σ n η m V0 hm]

/-! ## Fuel monotonicity

Every function of the normalizer keeps its result when given one more unit
of fuel.  Six of the eight are unconditional; `closedAtomForm` and
`atomForm` are not, because `closedAtomForm` normalizes the coercions of a
closed atom under `storeEnv n σ`, and `storeEnv` is itself fuel-indexed
with a `getD []` fallback: with more fuel the *views* it records may grow
from `[]` to the real telescope normal form.  Those two are therefore
proved relative to `StoreEnvStable`, which says that the store environment
has already stabilised below the fuel in question. -/

/-- The store environment does not change any more below fuel `n`. -/
def StoreEnvStable (σ : Store s) (n : Nat) : Prop :=
  ∀ k, k < n → storeEnv (k+1) σ = storeEnv k σ

theorem StoreEnvStable.mono {σ : Store s} {n m : Nat} (h : StoreEnvStable σ m) (hnm : n ≤ m) :
    StoreEnvStable σ n := fun k hk => h k (Nat.lt_of_lt_of_le hk hnm)

/-- One step of stabilisation for a store with one more entry. -/
theorem storeEnv_succ_cons {s : Sig} {σ : Store s} {v : Value s} {n : Nat}
    (hσ : storeEnv (n+1) σ = storeEnv n σ)
    (hE : ∀ (Tel : Telescope (s,x)) (W : Witnesses (s,x)) (E : Morphism (s,x))
            (F : Fields (s,x)), v = .obj Tel W E F →
          morphismView (Store.cons σ v) (n+1)
              (Env.cons (Env.weaken (storeEnv n σ)) (.var .here) []) E
            = morphismView (Store.cons σ v) n
              (Env.cons (Env.weaken (storeEnv n σ)) (.var .here) []) E) :
    storeEnv (n+2) (Store.cons σ v) = storeEnv (n+1) (Store.cons σ v) := by
  simp only [storeEnv, hσ]
  cases v with
  | lam S t => rfl
  | cast v e => rfl
  | obj Tel W E F => simp only [hE Tel W E F rfl]

/-- The six fuel-monotone functions of the normalizer: the sub-cluster
that never consults `storeEnv`. -/
theorem mono_succ {s : Sig} (σ : Store s) (n : Nat) :
    (∀ (s' : Sig) (η : Env s s') (e : LeCo s') (F : Form s),
        hnf σ n η e = some F → hnf σ (n+1) η e = some F)
  ∧ (∀ (s' : Sig) (η : Env s s') (a : Atom s') (r : Atom s × View s),
        atomView σ n η a = some r → atomView σ (n+1) η a = some r)
  ∧ (∀ (F : Form s) (a : Atom s) (V W : View s),
        applyForm σ n F a V = some W → applyForm σ (n+1) F a V = some W)
  ∧ (∀ (cs : List (ChainStep s)) (a : Atom s) (V W : View s),
        applyChain σ n cs a V = some W → applyChain σ (n+1) cs a V = some W)
  ∧ (∀ (s' : Sig) (η : Env s (s',x)) (m : Morphism (s',x)) (W : View s),
        morphismView σ n η m = some W → morphismView σ (n+1) η m = some W)
  ∧ (∀ (s' : Sig) (η : Env s s') (y : BVar s' .var) (hh : Has s') (r : BVar s .var × Label),
        hasView σ n η y hh = some r → hasView σ (n+1) η y hh = some r) := by
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _ _ _ _ h; simp [hnf] at h
      · intro _ _ _ _ h; simp [atomView] at h
      · intro _ _ _ _ h; simp [applyForm] at h
      · intro _ _ _ _ h; simp [applyChain] at h
      · intro _ _ _ _ h; simp [morphismView] at h
      · intro _ _ _ _ _ h; simp [hasView] at h
  | succ n ih =>
      obtain ⟨ihH, ihAV, ihAF, ihAC, ihMV, ihHV⟩ := ih
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- hnf
        intro s' η e F h
        cases e with
        | refl T => simpa [hnf] using h
        | top T => simpa [hnf] using h
        | bot T => simpa [hnf] using h
        | eqToLe φ => simpa [hnf] using h
        | pi d c => simpa [hnf] using h
        | obj Tel m => simpa [hnf] using h
        | trans e f =>
            cases he : hnf σ n η e with
            | none => simp [hnf, he] at h
            | some F1 =>
                cases hf : hnf σ n η f with
                | none => simp [hnf, he, hf] at h
                | some G1 =>
                    simpa [hnf, he, hf, ihH _ _ _ _ he, ihH _ _ _ _ hf] using h
        | member a e i =>
            cases he : hnf σ n η e with
            | none => simp [hnf, he] at h
            | some F1 =>
                cases hav : atomView σ n η a with
                | none => simp [hnf, he, hav] at h
                | some p =>
                    obtain ⟨a', V⟩ := p
                    cases hap : applyForm σ n F1 a' V with
                    | none => simp [hnf, he, hav, hap] at h
                    | some V' =>
                        simpa [hnf, he, hav, hap, ihH _ _ _ _ he, ihAV _ _ _ _ hav,
                          ihAF _ _ _ _ hap] using h
      · -- atomView
        intro s' η a r h
        cases a with
        | var y => simpa [atomView] using h
        | cast a e =>
            cases hav : atomView σ n η a with
            | none => simp [atomView, hav] at h
            | some p =>
                obtain ⟨a', V⟩ := p
                cases he : hnf σ n η e with
                | none => simp [atomView, hav, he] at h
                | some F1 =>
                    cases hap : applyForm σ n F1 a' V with
                    | none => simp [atomView, hav, he, hap] at h
                    | some V' =>
                        simpa [atomView, hav, he, hap, ihAV _ _ _ _ hav, ihH _ _ _ _ he,
                          ihAF _ _ _ _ hap] using h
        | foldSelf Tel a =>
            cases hav : atomView σ n η a with
            | none => simp [atomView, hav] at h
            | some p =>
                obtain ⟨a', V⟩ := p
                simpa [atomView, hav, ihAV _ _ _ _ hav] using h
        | unfoldSelf a =>
            cases hav : atomView σ n η a with
            | none => simp [atomView, hav] at h
            | some p =>
                obtain ⟨a', V⟩ := p
                simpa [atomView, hav, ihAV _ _ _ _ hav] using h
      · -- applyForm
        intro F a V W h
        cases F with
        | bot => simpa [applyForm] using h
        | top => simpa [applyForm] using h
        | pi d c => simpa [applyForm] using h
        | id => simpa [applyForm] using h
        | eqv φ => simpa [applyForm] using h
        | obj cs =>
            have h' : applyChain σ n cs a V = some W := by simpa [applyForm] using h
            simpa [applyForm] using ihAC _ _ _ _ h'
      · -- applyChain
        intro cs a V W h
        cases cs with
        | nil => simpa [applyChain] using h
        | cons c cs =>
            cases c with
            | conv φ =>
                have h' : applyChain σ n cs (.cast a (.eqToLe φ)) V = some W := by
                  simpa [applyChain] using h
                simpa [applyChain] using ihAC _ _ _ _ h'
            | clos s'' Tel m η =>
                cases hm : morphismView σ n (η.cons a V) m with
                | none => simp [applyChain, hm] at h
                | some V' =>
                    have h' : applyChain σ n cs
                        (.cast a (.obj (Tel.rename η.toSubst.root.lift)
                          (m.subst η.toSubst.lift))) V' = some W := by
                      simpa [applyChain, hm] using h
                    simpa [applyChain, hm, ihMV _ _ _ _ hm] using ihAC _ _ _ _ h'
      · -- morphismView
        intro s' η m W h
        cases m with
        | nil => simpa [morphismView] using h
        | le m e =>
            cases hm : morphismView σ n η m with
            | none => simp [morphismView, hm] at h
            | some V0 =>
                cases he : hnf σ n η e with
                | none => simp [morphismView, hm, he] at h
                | some F1 =>
                    simpa [morphismView, hm, he, ihMV _ _ _ _ hm, ihH _ _ _ _ he] using h
        | eq m φ =>
            cases hm : morphismView σ n η m with
            | none => simp [morphismView, hm] at h
            | some V0 => simpa [morphismView, hm, ihMV _ _ _ _ hm] using h
        | has m hh =>
            cases hm : morphismView σ n η m with
            | none => simp [morphismView, hm] at h
            | some V0 =>
                cases hv : hasView σ n η .here hh with
                | none => simp [morphismView, hm, hv] at h
                | some p =>
                    simpa [morphismView, hm, hv, ihMV _ _ _ _ hm, ihHV _ _ _ _ _ hv] using h
      · -- hasView
        intro s' η y hh r h
        cases hh with
        | field ℓ => simpa [hasView] using h
        | member a e i =>
            cases he : hnf σ n η e with
            | none => simp [hasView, he] at h
            | some F1 =>
                cases hav : atomView σ n η a with
                | none => simp [hasView, he, hav] at h
                | some p =>
                    obtain ⟨a', V⟩ := p
                    cases hap : applyForm σ n F1 a' V with
                    | none => simp [hasView, he, hav, hap] at h
                    | some V' =>
                        simpa [hasView, he, hav, hap, ihH _ _ _ _ he, ihAV _ _ _ _ hav,
                          ihAF _ _ _ _ hap] using h

theorem hnf_succ {s s' : Sig} {σ : Store s} {n : Nat} {η : Env s s'} {e : LeCo s'} {F : Form s}
    (h : hnf σ n η e = some F) : hnf σ (n+1) η e = some F :=
  (mono_succ σ n).1 _ _ _ _ h

theorem atomView_succ {s s' : Sig} {σ : Store s} {n : Nat} {η : Env s s'} {a : Atom s'}
    {r : Atom s × View s} (h : atomView σ n η a = some r) : atomView σ (n+1) η a = some r :=
  (mono_succ σ n).2.1 _ _ _ _ h

theorem applyForm_succ {s : Sig} {σ : Store s} {n : Nat} {F : Form s} {a : Atom s} {V W : View s}
    (h : applyForm σ n F a V = some W) : applyForm σ (n+1) F a V = some W :=
  (mono_succ σ n).2.2.1 _ _ _ _ h

theorem applyChain_succ {s : Sig} {σ : Store s} {n : Nat} {cs : List (ChainStep s)} {a : Atom s}
    {V W : View s} (h : applyChain σ n cs a V = some W) : applyChain σ (n+1) cs a V = some W :=
  (mono_succ σ n).2.2.2.1 _ _ _ _ h

theorem morphismView_succ {s s' : Sig} {σ : Store s} {n : Nat} {η : Env s (s',x)}
    {m : Morphism (s',x)} {W : View s} (h : morphismView σ n η m = some W) :
    morphismView σ (n+1) η m = some W :=
  (mono_succ σ n).2.2.2.2.1 _ _ _ _ h

theorem hasView_succ {s s' : Sig} {σ : Store s} {n : Nat} {η : Env s s'} {y : BVar s' .var}
    {hh : Has s'} {r : BVar s .var × Label} (h : hasView σ n η y hh = some r) :
    hasView σ (n+1) η y hh = some r :=
  (mono_succ σ n).2.2.2.2.2 _ _ _ _ _ h

/-! ### The two functions that consult the store environment -/

theorem closedAtomForm_succ {s : Sig} {σ : Store s} : ∀ (n : Nat), StoreEnvStable σ n →
    ∀ (a : Atom s) (r : Atom s × Form s),
      closedAtomForm σ n a = some r → closedAtomForm σ (n+1) a = some r
  | 0, _, _, _, h => by simp [closedAtomForm] at h
  | n + 1, hst, a, r, h => by
      have ih := closedAtomForm_succ n (hst.mono (Nat.le_succ n))
      have hs : storeEnv (n+1) σ = storeEnv n σ := hst n (Nat.lt_succ_self n)
      cases a with
      | var x => simpa [closedAtomForm] using h
      | cast a e =>
          cases hc : closedAtomForm σ n a with
          | none => simp [closedAtomForm, hc] at h
          | some p =>
              obtain ⟨a', F1⟩ := p
              cases he : hnf σ n (storeEnv n σ) e with
              | none => simp [closedAtomForm, hc, he] at h
              | some G1 =>
                  have he' : hnf σ (n+1) (storeEnv (n+1) σ) e = some G1 := by
                    rw [hs]; exact hnf_succ he
                  simpa [closedAtomForm, hc, he, ih _ _ hc, he'] using h
      | foldSelf Tel a =>
          cases hc : closedAtomForm σ n a with
          | none => simp [closedAtomForm, hc] at h
          | some p =>
              obtain ⟨a', F1⟩ := p
              simpa [closedAtomForm, hc, ih _ _ hc] using h
      | unfoldSelf a =>
          cases hc : closedAtomForm σ n a with
          | none => simp [closedAtomForm, hc] at h
          | some p =>
              obtain ⟨a', F1⟩ := p
              simpa [closedAtomForm, hc, ih _ _ hc] using h

theorem atomForm_succ {s : Sig} {σ : Store s} : ∀ (n : Nat), StoreEnvStable σ n →
    ∀ (s' : Sig) (η : Env s s') (a : Atom s') (r : Atom s × Form s),
      atomForm σ n η a = some r → atomForm σ (n+1) η a = some r
  | 0, _, _, _, _, _, h => by simp [atomForm] at h
  | n + 1, hst, s', η, a, r, h => by
      have ih := atomForm_succ n (hst.mono (Nat.le_succ n))
      cases a with
      | var y =>
          have h' : closedAtomForm σ n (η.atom y) = some r := by simpa [atomForm] using h
          simpa [atomForm] using closedAtomForm_succ n (hst.mono (Nat.le_succ n)) _ _ h'
      | cast a e =>
          cases hc : atomForm σ n η a with
          | none => simp [atomForm, hc] at h
          | some p =>
              obtain ⟨a', F1⟩ := p
              cases he : hnf σ n η e with
              | none => simp [atomForm, hc, he] at h
              | some G1 =>
                  simpa [atomForm, hc, he, ih _ _ _ _ hc, hnf_succ he] using h
      | foldSelf Tel a =>
          cases hc : atomForm σ n η a with
          | none => simp [atomForm, hc] at h
          | some p =>
              obtain ⟨a', F1⟩ := p
              simpa [atomForm, hc, ih _ _ _ _ hc] using h
      | unfoldSelf a =>
          cases hc : atomForm σ n η a with
          | none => simp [atomForm, hc] at h
          | some p =>
              obtain ⟨a', F1⟩ := p
              simpa [atomForm, hc, ih _ _ _ _ hc] using h

/-! ### Monotonicity in the fuel -/

/-- Any property that survives one more unit of fuel survives any amount. -/
theorem mono_le {P : Nat → Prop} (hmono : ∀ k, P k → P (k+1)) :
    ∀ {n m : Nat}, n ≤ m → P n → P m := by
  intro n m hnm h
  induction m with
  | zero => exact (Nat.le_zero.mp hnm) ▸ h
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le hnm with heq | hlt
      · exact heq ▸ h
      · exact hmono m (ih (Nat.lt_succ_iff.mp hlt))

/-- The same, for the two functions whose monotonicity needs a stable store
environment. -/
theorem mono_le_stable {s : Sig} {σ : Store s} {P : Nat → Prop}
    (hmono : ∀ k, StoreEnvStable σ k → P k → P (k+1)) :
    ∀ {n m : Nat}, n ≤ m → StoreEnvStable σ m → P n → P m := by
  intro n m hnm hst h
  induction m with
  | zero => exact (Nat.le_zero.mp hnm) ▸ h
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le hnm with heq | hlt
      · exact heq ▸ h
      · exact hmono m (hst.mono (Nat.le_succ m))
          (ih (Nat.lt_succ_iff.mp hlt) (hst.mono (Nat.le_succ m)))

theorem hnf_le {s s' : Sig} {σ : Store s} {n m : Nat} {η : Env s s'} {e : LeCo s'} {F : Form s}
    (hnm : n ≤ m) (h : hnf σ n η e = some F) : hnf σ m η e = some F :=
  mono_le (P := fun k => hnf σ k η e = some F) (fun _ hk => hnf_succ hk) hnm h

theorem atomView_le {s s' : Sig} {σ : Store s} {n m : Nat} {η : Env s s'} {a : Atom s'}
    {r : Atom s × View s} (hnm : n ≤ m) (h : atomView σ n η a = some r) :
    atomView σ m η a = some r :=
  mono_le (P := fun k => atomView σ k η a = some r) (fun _ hk => atomView_succ hk) hnm h

theorem applyForm_le {s : Sig} {σ : Store s} {n m : Nat} {F : Form s} {a : Atom s} {V W : View s}
    (hnm : n ≤ m) (h : applyForm σ n F a V = some W) : applyForm σ m F a V = some W :=
  mono_le (P := fun k => applyForm σ k F a V = some W) (fun _ hk => applyForm_succ hk) hnm h

theorem applyChain_le {s : Sig} {σ : Store s} {n m : Nat} {cs : List (ChainStep s)} {a : Atom s}
    {V W : View s} (hnm : n ≤ m) (h : applyChain σ n cs a V = some W) :
    applyChain σ m cs a V = some W :=
  mono_le (P := fun k => applyChain σ k cs a V = some W) (fun _ hk => applyChain_succ hk) hnm h

theorem morphismView_le {s s' : Sig} {σ : Store s} {n m : Nat} {η : Env s (s',x)}
    {mm : Morphism (s',x)} {W : View s} (hnm : n ≤ m) (h : morphismView σ n η mm = some W) :
    morphismView σ m η mm = some W :=
  mono_le (P := fun k => morphismView σ k η mm = some W) (fun _ hk => morphismView_succ hk) hnm h

theorem hasView_le {s s' : Sig} {σ : Store s} {n m : Nat} {η : Env s s'} {y : BVar s' .var}
    {hh : Has s'} {r : BVar s .var × Label} (hnm : n ≤ m) (h : hasView σ n η y hh = some r) :
    hasView σ m η y hh = some r :=
  mono_le (P := fun k => hasView σ k η y hh = some r) (fun _ hk => hasView_succ hk) hnm h

theorem closedAtomForm_le {s : Sig} {σ : Store s} {n m : Nat} {a : Atom s}
    {r : Atom s × Form s} (hnm : n ≤ m) (hst : StoreEnvStable σ m)
    (h : closedAtomForm σ n a = some r) : closedAtomForm σ m a = some r :=
  mono_le_stable (P := fun k => closedAtomForm σ k a = some r)
    (fun k hk hkk => closedAtomForm_succ k hk _ _ hkk) hnm hst h

theorem atomForm_le {s s' : Sig} {σ : Store s} {n m : Nat} {η : Env s s'} {a : Atom s'}
    {r : Atom s × Form s} (hnm : n ≤ m) (hst : StoreEnvStable σ m)
    (h : atomForm σ n η a = some r) : atomForm σ m η a = some r :=
  mono_le_stable (P := fun k => atomForm σ k η a = some r)
    (fun k hk hkk => atomForm_succ k hk _ _ _ _ hkk) hnm hst h

/-! ## Splitting a chain application

`Form.combine` concatenates object chains, so the canonical-forms argument
needs to run a concatenated chain in two halves.  The atom threaded through
the chain is deterministic — each step casts it by that step's closed
coercion — so the join point is named by `ChainStep.chainAtom`. -/

/-- The self atom obtained after casting through every step of a chain. -/
def ChainStep.chainAtom : List (ChainStep s) → Atom s → Atom s
  | [], a => a
  | c :: cs, a => ChainStep.chainAtom cs (.cast a c.close)

@[simp] theorem ChainStep.chainAtom_nil {s : Sig} (a : Atom s) :
    ChainStep.chainAtom [] a = a := rfl

@[simp] theorem ChainStep.chainAtom_cons {s : Sig} (c : ChainStep s) (cs : List (ChainStep s))
    (a : Atom s) :
    ChainStep.chainAtom (c :: cs) a = ChainStep.chainAtom cs (.cast a c.close) := rfl

@[simp] theorem applyChain_nil {s : Sig} (σ : Store s) (n : Nat) (a : Atom s) (V : View s) :
    applyChain σ (n+1) [] a V = some V := rfl

@[simp] theorem applyChain_cons_conv {s : Sig} (σ : Store s) (n : Nat) (φ : EqCo s)
    (cs : List (ChainStep s)) (a : Atom s) (V : View s) :
    applyChain σ (n+1) (.conv φ :: cs) a V
      = applyChain σ n cs (.cast a (ChainStep.close (.conv φ))) V := rfl

@[simp] theorem applyChain_cons_clos {s s' : Sig} (σ : Store s) (n : Nat)
    (Tel : Telescope (s',x)) (m : Morphism (s',x)) (η : Env s s')
    (cs : List (ChainStep s)) (a : Atom s) (V : View s) :
    applyChain σ (n+1) (.clos s' Tel m η :: cs) a V
      = (morphismView σ n (η.cons a V) m).bind
          (fun V' => applyChain σ n cs (.cast a (ChainStep.close (.clos s' Tel m η))) V') := rfl

/-- Running a concatenated chain runs the two halves in sequence, through
the atom `chainAtom` names. -/
theorem applyChain_append {s : Sig} {σ : Store s} :
    ∀ (cs₁ : List (ChainStep s)) {n : Nat} {cs₂ : List (ChainStep s)} {a : Atom s}
      {V V'' : View s}, applyChain σ n (cs₁ ++ cs₂) a V = some V'' →
      ∃ (V' : View s) (n₁ n₂ : Nat), applyChain σ n₁ cs₁ a V = some V' ∧
        applyChain σ n₂ cs₂ (ChainStep.chainAtom cs₁ a) V' = some V''
  | [], n, cs₂, a, V, V'', h => ⟨V, 1, n, rfl, by simpa using h⟩
  | c :: cs₁, n, cs₂, a, V, V'', h => by
      rw [List.cons_append] at h
      cases n with
      | zero => simp [applyChain] at h
      | succ n =>
          cases c with
          | conv φ =>
              rw [applyChain_cons_conv] at h
              obtain ⟨V', n₁, n₂, h1, h2⟩ := applyChain_append cs₁ h
              refine ⟨V', n₁ + 1, n₂, ?_, by simpa using h2⟩
              rw [applyChain_cons_conv]
              exact h1
          | clos s' Tel m η =>
              rw [applyChain_cons_clos] at h
              cases hm : morphismView σ n (η.cons a V) m with
              | none => rw [hm] at h; simp at h
              | some W =>
                  rw [hm, Option.bind_some] at h
                  obtain ⟨V', n₁, n₂, h1, h2⟩ := applyChain_append cs₁ h
                  refine ⟨V', n₁ + n + 1, n₂, ?_, by simpa using h2⟩
                  have hm' : morphismView σ (n₁ + n) (η.cons a V) m = some W :=
                    morphismView_le (Nat.le_add_left n n₁) hm
                  rw [applyChain_cons_clos, hm', Option.bind_some]
                  exact applyChain_le (Nat.le_add_right n₁ n) h1

/-- Conversely, two successful halves compose into one run of the
concatenation, at the sum of their fuels (plus slack for the steps). -/
theorem applyChain_append_of {s : Sig} {σ : Store s} :
    ∀ (cs₁ : List (ChainStep s)) {n₁ n₂ : Nat} {cs₂ : List (ChainStep s)} {a : Atom s}
      {V V' V'' : View s}, applyChain σ n₁ cs₁ a V = some V' →
      applyChain σ n₂ cs₂ (ChainStep.chainAtom cs₁ a) V' = some V'' →
      applyChain σ (n₁ + n₂ + cs₁.length) (cs₁ ++ cs₂) a V = some V''
  | [], n₁, n₂, cs₂, a, V, V', V'', h1, h2 => by
      cases n₁ with
      | zero => simp [applyChain] at h1
      | succ n₁ =>
          have hV : V = V' := by simpa using h1
          subst hV
          have h2' : applyChain σ n₂ cs₂ a V = some V'' := by simpa using h2
          have key : applyChain σ (n₁ + 1 + n₂ + 0) cs₂ a V = some V'' :=
            applyChain_le (by omega) h2'
          simpa using key
  | c :: cs₁, n₁, n₂, cs₂, a, V, V', V'', h1, h2 => by
      cases n₁ with
      | zero => simp [applyChain] at h1
      | succ n₁ =>
          have hfuel : n₁ + 1 + n₂ + (c :: cs₁).length
              = (n₁ + n₂ + cs₁.length + 1) + 1 := by
            simp [List.length_cons]; omega
          rw [List.cons_append, hfuel]
          cases c with
          | conv φ =>
              rw [applyChain_cons_conv] at h1
              have key := applyChain_append_of cs₁ h1 (by simpa using h2)
              rw [applyChain_cons_conv]
              exact applyChain_le (by omega) key
          | clos s' Tel m η =>
              rw [applyChain_cons_clos] at h1
              cases hm : morphismView σ n₁ (η.cons a V) m with
              | none => rw [hm] at h1; simp at h1
              | some W =>
                  rw [hm, Option.bind_some] at h1
                  have key := applyChain_append_of cs₁ h1 (by simpa using h2)
                  have hm' : morphismView σ (n₁ + n₂ + cs₁.length + 1) (η.cons a V) m = some W :=
                    morphismView_le (by omega) hm
                  rw [applyChain_cons_clos, hm', Option.bind_some]
                  exact applyChain_le (by omega) key

/-- Both directions at once, quantifying over the fuel. -/
theorem applyChain_append_iff {s : Sig} {σ : Store s} (cs₁ cs₂ : List (ChainStep s))
    (a : Atom s) (V V'' : View s) :
    (∃ n, applyChain σ n (cs₁ ++ cs₂) a V = some V'')
      ↔ (∃ (V' : View s) (n₁ n₂ : Nat), applyChain σ n₁ cs₁ a V = some V' ∧
            applyChain σ n₂ cs₂ (ChainStep.chainAtom cs₁ a) V' = some V'') := by
  constructor
  · rintro ⟨n, h⟩
    exact applyChain_append cs₁ h
  · rintro ⟨V', n₁, n₂, h1, h2⟩
    exact ⟨n₁ + n₂ + cs₁.length, applyChain_append_of cs₁ h1 h2⟩

end FCdot
