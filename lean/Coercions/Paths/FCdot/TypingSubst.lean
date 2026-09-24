import Coercions.Paths.FCdot.TypingRename

namespace Paths

/-!
# Substitution of atoms in FCdot typing derivations

A substitution maps variables to atoms.  Types and evidence see only the
root map `σ.root`, but evidence contains atoms (inside `member`), so the
whole family is transported by `subst`, not by a renaming.  `Subst.Typed Γ σ
Γ'` is the typed-substitution judgement; `Subst.Typed.single` instantiates
the innermost *opaque* binder by an atom of its type.
-/

namespace FCdot

@[simp] theorem Ty.rename_subst_weaken' {s : Sig} {k : Kind} (T : Ty s) (y : BVar s k) :
    (T.weaken (k := k)).rename (Rename.subst y) = T :=
  Ty.rename_subst_weaken T y

@[simp] theorem Telescope.rename_subst_weaken' {s : Sig} {k : Kind}
    (Tel : Telescope s) (y : BVar s k) :
    (Tel.weaken (k := k)).rename (Rename.subst y) = Tel :=
  Telescope.rename_subst_weaken Tel y

@[simp] theorem Fields.labels_subst {s1 s2 : Sig} :
    ∀ (F : Fields s1) (σ : Subst s1 s2), (F.subst σ).labels = F.labels
  | .nil, _ => rfl
  | .cons F l t, σ => by
      simp [Fields.subst, Fields.labels, Fields.labels_subst F σ]

mutual
@[simp] theorem LeCo.tableOnly_subst : ∀ (e : LeCo s1) (σ : Subst s1 s2),
    (e.subst σ).tableOnly = e.tableOnly
  | .refl _, _ => rfl
  | .trans e f, σ => by
      simp [LeCo.subst, LeCo.tableOnly, LeCo.tableOnly_subst e σ, LeCo.tableOnly_subst f σ]
  | .top _, _ => rfl
  | .bot _, _ => rfl
  | .eqToLe φ, σ => by simp [LeCo.subst, LeCo.tableOnly, EqCo.tableOnly_subst φ σ]
  | .pi _ _, _ => rfl
  | .obj _ m, σ => by simp [LeCo.subst, LeCo.tableOnly, Morphism.tableOnly_subst m σ]
  | .pair _ _ e f, σ => by
      simp [LeCo.subst, LeCo.tableOnly, LeCo.tableOnly_subst e σ, LeCo.tableOnly_subst f σ]
  | .bound _ _, _ => rfl
  | .intoBnd e, σ => by simp [LeCo.subst, LeCo.tableOnly, LeCo.tableOnly_subst e σ]
  | .member _ _ _, _ => rfl
  | .memberP _ _ _, _ => rfl

theorem EqCo.tableOnly_subst : ∀ (φ : EqCo s1) (σ : Subst s1 s2),
    (φ.subst σ).tableOnly = φ.tableOnly
  | .refl _, _ => rfl
  | .symm φ, σ => by simp [EqCo.subst, EqCo.tableOnly, EqCo.tableOnly_subst φ σ]
  | .trans φ ψ, σ => by
      simp [EqCo.subst, EqCo.tableOnly, EqCo.tableOnly_subst φ σ, EqCo.tableOnly_subst ψ σ]
  | .def _ _, _ => rfl
  | .defP _ _, _ => rfl
  | .member _ _ _, _ => rfl
  | .memberP _ _ _, _ => rfl

theorem Side.tableOnly_subst : ∀ (p : Side s1) (σ : Subst s1 s2),
    (p.subst σ).tableOnly = p.tableOnly
  | .none, _ => rfl
  | .some e, σ => by simp [Side.subst, Side.tableOnly, LeCo.tableOnly_subst e σ]
  | .bot _, _ => rfl
  | .top _, _ => rfl

theorem Morphism.tableOnly_subst : ∀ (m : Morphism s1) (σ : Subst s1 s2),
    (m.subst σ).tableOnly = m.tableOnly
  | .nil, _ => rfl
  | .le m pre _ post, σ => by
      simp [Morphism.subst, Morphism.tableOnly, Morphism.tableOnly_subst m σ,
        Side.tableOnly_subst pre σ, Side.tableOnly_subst post σ]
  | .eq m _ _, σ => by simp [Morphism.subst, Morphism.tableOnly, Morphism.tableOnly_subst m σ]
  | .has m _, σ => by simp [Morphism.subst, Morphism.tableOnly, Morphism.tableOnly_subst m σ]
  | .bnd m e, σ => by
      simp [Morphism.subst, Morphism.tableOnly, Morphism.tableOnly_subst m σ,
        LeCo.tableOnly_subst e σ]
  | .hasVal m _, σ => by simp [Morphism.subst, Morphism.tableOnly, Morphism.tableOnly_subst m σ]
  | .hasOfVal m _, σ => by
      simp [Morphism.subst, Morphism.tableOnly, Morphism.tableOnly_subst m σ]
  | .aliasCopy m _, σ => by
      simp [Morphism.subst, Morphism.tableOnly, Morphism.tableOnly_subst m σ]
end

@[simp] theorem Value.isStableLit_subst {s1 s2 : Sig} :
    ∀ (v : Value s1) (σ : Subst s1 s2), (v.subst σ).isStableLit = v.isStableLit
  | .obj _ _, _ => rfl
  | .lam _ _, _ => rfl
  | .cast v e, σ => by
      simp [Value.subst, Value.isStableLit, Value.isStableLit_subst v σ, LeCo.tableOnly_subst]

@[simp] theorem Value.isObjLit_subst {s1 s2 : Sig} :
    ∀ (v : Value s1) (σ : Subst s1 s2), (v.subst σ).isObjLit = v.isObjLit
  | .obj _ _, _ => rfl
  | .lam _ _, _ => rfl
  | .cast v _, σ => Value.isObjLit_subst v σ

@[simp] theorem Tm.isStable_subst {s1 s2 : Sig} :
    ∀ (t : Tm s1) (σ : Subst s1 s2), (t.subst σ).isStable = t.isStable
  | .atom _, _ => rfl
  | .val v, σ => Value.isStableLit_subst v σ
  | .cast t e, σ => by
      simp [Tm.subst, Tm.isStable, Tm.isStable_subst t σ, LeCo.tableOnly_subst]
  | .app _ _, _ => rfl
  | .proj _ _ _, _ => rfl
  | .let _ _, _ => rfl

@[simp] theorem Fields.valLabels_subst {s1 s2 : Sig} :
    ∀ (F : Fields s1) (σ : Subst s1 s2), (F.subst σ).valLabels = F.valLabels
  | .nil, _ => rfl
  | .cons F l t, σ => by
      have ht : (t.subst σ).isStable = t.isStable := Tm.isStable_subst t σ
      simp [Fields.subst, Fields.valLabels, ht, Fields.valLabels_subst F σ]

/-! ## The block builder against a substitution

A block reads only types and the roots of atoms, so an atom substitution acts
on a block as the renaming `σ.root`. -/

mutual

theorem Value.blockSelf_subst {s1 s2 : Sig} :
    ∀ (v : Value s1) (σ : Subst s1 s2),
      (v.subst σ).blockSelf = v.blockSelf.rename σ.root.lift
  | .lam _ _, _ => rfl
  | .cast v _, σ => Value.blockSelf_subst v σ
  | .obj W F, σ => by
      have hch : (F.subst σ.lift).children (.var .here)
          = (F.children (.var .here)).rename σ.root.lift := by
        have h := Fields.children_subst F (.var .here) σ.lift
        simpa [Path.rename, Subst.lift_root] using h
      simp only [Value.subst, Value.blockSelf, Block.rename, Fields.labels_subst,
        Fields.valLabels_subst, hch]

theorem Fields.children_subst {s1 s2 : Sig} :
    ∀ (F : Fields s1) (p : Path s1) (σ : Subst s1 s2),
      (F.subst σ).children (p.rename σ.root) = (F.children p).rename σ.root
  | .nil, _, _ => rfl
  | .cons F ℓ t, p, σ => by
      have ht := Tm.childAt_subst t (.sel p ℓ) σ
      have hF := Fields.children_subst F p σ
      show (Fields.subst (.cons F ℓ t) σ).children (p.rename σ.root) = _
      simp only [Fields.subst, Fields.children]
      show (match ((t.subst σ).childAt (.sel (p.rename σ.root) ℓ)) with
            | some b => Children.cons ((F.subst σ).children (p.rename σ.root)) ℓ b
            | none => ((F.subst σ).children (p.rename σ.root)).dropLabel ℓ)
        = Children.rename (match t.childAt (.sel p ℓ) with
            | some b => .cons (F.children p) ℓ b
            | none => (F.children p).dropLabel ℓ) σ.root
      have hp : Path.sel (p.rename σ.root) ℓ = (Path.sel p ℓ).rename σ.root := rfl
      rw [hp, ht, hF]
      cases t.childAt (.sel p ℓ) with
      | none => exact Children.dropLabel_rename _ σ.root ℓ
      | some b => rfl

theorem Tm.childAt_subst {s1 s2 : Sig} :
    ∀ (t : Tm s1) (p : Path s1) (σ : Subst s1 s2),
      (t.subst σ).childAt (p.rename σ.root) = (t.childAt p).map (Block.rename · σ.root)
  | .val v, p, σ => by
      simp only [Tm.subst, Tm.childAt, Value.isStableLit_subst]
      cases v.isStableLit with
      | false => rfl
      | true =>
          simp only [if_true, Option.map_some]
          rw [Value.blockSelf_subst v σ, Block.substPath_rename]
  | .atom a, p, σ => by
      simp [Tm.subst, Tm.childAt, Block.rename, Path.rename, Atom.root_subst]
  | .cast t e, p, σ => by
      simp only [Tm.subst, Tm.childAt, Tm.isStable_subst, LeCo.tableOnly_subst]
      split
      · rfl
      · exact Tm.childAt_subst t p σ
  | .app _ _, _, _ => rfl
  | .proj _ _ _, _, _ => rfl
  | .let _ _, _, _ => rfl

end

@[simp] theorem Fields.children_self_subst {s1 s2 : Sig} (F : Fields (s1,x))
    (σ : Subst s1 s2) :
    (F.subst σ.lift).children (.var .here) = (F.children (.var .here)).rename σ.root.lift := by
  have h := Fields.children_subst F (.var .here) σ.lift
  simpa [Path.rename, Subst.lift_root] using h

/-! ## Typed substitutions -/

/-- `Subst.Typed Γ σ Γ'`: every variable of `Γ` goes to an atom of the
transported type, and definitions and field labels survive along `σ.root`. -/
structure Subst.Typed {s1 s2 : Sig} (Γ : Ctx s1) (σ : Subst s1 s2) (Γ' : Ctx s2) : Prop where
  var : ∀ x, Γ' ⊢ₐ (σ.var x) : ((Γ.lookupTy x).rename σ.root)
  /-- On transparent binders the substitution behaves like a renaming. -/
  ty : ∀ x, Γ.IsTransparent x →
      Γ'.lookupTy (σ.root.var x) = (Γ.lookupTy x).rename σ.root
  transparent : ∀ x, Γ.IsTransparent x → Γ'.IsTransparent (σ.root.var x)
  def_ : ∀ x l W, Γ.lookupDef x l = some W →
      Γ'.lookupDef (σ.root.var x) l = some (W.rename σ.root)
  fields : ∀ x Fs, Γ.lookupFields x = some Fs → Γ'.lookupFields (σ.root.var x) = some Fs
  /-- The whole forest walk is carried along `σ.root`.  This is the field, and
      not the binder table it used to be derived from: the forwarding binder of
      a let over a path has a forwarding node where the atom's root has an
      object node, so its table is not carried while its walk is. -/
  lookupB : ∀ {p : Path s1} {B : Block s1}, Γ.lookupBlock p = some B →
      Γ'.lookupBlock (p.rename σ.root) = some (B.rename σ.root)
  /-- The node walk is carried along `σ.root`, the twin of `lookupB` for the
      walk that follows no forwarding, which the `node` rule reads.  At an
      opaque or a forwarding binder the node walk answers nothing. -/
  nodeB : ∀ {p : Path s1} {B : Block s1}, Γ.nodeBlock p = some B →
      Γ'.nodeBlock (p.rename σ.root) = some (B.rename σ.root)

namespace Subst.Typed

/-- The definition of a block name survives a typed substitution. -/
theorem defP {s1 s2 : Sig} {Γ : Ctx s1} {σ : Subst s1 s2} {Γ' : Ctx s2}
    (h : Subst.Typed Γ σ Γ') {p : Path s1} {l : Label} {W : Ty s1}
    (hd : Γ.lookupDefP p l = some W) :
    Γ'.lookupDefP (p.rename σ.root) l = some (W.rename σ.root) := by
  unfold Ctx.lookupDefP at hd ⊢
  cases hbk : Γ.lookupBlock p with
  | none => rw [hbk] at hd; exact absurd hd (by simp)
  | some B =>
      cases B with
      | fwd r => rw [hbk] at hd; exact absurd hd (by simp)
      | obj W₀ ls vls ch =>
          rw [hbk] at hd
          obtain rfl : W₀.get l = W := by simpa using hd
          simp only [h.lookupB hbk, Block.rename, Witnesses.get_rename]

theorem lift {Γ : Ctx s1} {σ : Subst s1 s2} {Γ' : Ctx s2}
    (h : Subst.Typed Γ σ Γ') (b : Binding s1) :
    Subst.Typed (Γ.cons b) σ.lift (Γ'.cons (b.rename σ.root)) where
  var := by
    intro x
    simp only [Subst.lift_root]
    cases x with
    | here =>
        show Atom.HasType (Γ'.cons (b.rename σ.root)) (.var .here)
          (((Γ.cons b).lookupTy .here).rename σ.root.lift)
        have he : (Γ'.cons (b.rename σ.root)).lookupTy .here
            = ((Γ.cons b).lookupTy .here).rename σ.root.lift := by
          simp [Ty.weaken_rename]
        rw [← he]
        exact .var
    | there y =>
        show Atom.HasType (Γ'.cons (b.rename σ.root)) ((σ.var y)↑)
          (((Γ.cons b).lookupTy (.there y)).rename σ.root.lift)
        rw [Ctx.lookupTy_there, Ty.weaken_rename]
        exact (h.var y).weaken _
  ty := by
    intro x ht
    simp only [Subst.lift_root]
    cases x with
    | here => simp [Ty.weaken_rename]
    | there y =>
        rw [Ctx.isTransparent_there] at ht
        rw [Rename.lift_there, Ctx.lookupTy_there, Ctx.lookupTy_there, h.ty y ht,
          Ty.weaken_rename]
  transparent := by
    intro x ht
    simp only [Subst.lift_root]
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at ht
        | transparent T B =>
            cases B with
            | fwd q => simp [Ctx.IsTransparent] at ht
            | obj W' Fs' Vs' ch' => simp [Block.rename]
    | there y =>
        rw [Ctx.isTransparent_there] at ht
        rw [Rename.lift_there, Ctx.isTransparent_there]
        exact h.transparent y ht
  def_ := by
    intro x l W hW
    simp only [Subst.lift_root]
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hW
        | transparent T B =>
            cases B with
            | fwd q => simp at hW
            | obj W' Fs' Vs' ch' =>
                have hWe : W = W'.get l := by simpa using hW.symm
                subst hWe
                simp only [Rename.lift_here, Binding.rename_transparent, Block.rename,
                  Ctx.lookupDef_here_transparent, Witnesses.get_rename]
    | there y =>
        rw [Ctx.lookupDef_there] at hW
        rw [Rename.lift_there, Ctx.lookupDef_there]
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            simp [Ty.weaken_rename]
  fields := by
    intro x Fs hFs
    simp only [Subst.lift_root]
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hFs
        | transparent T B =>
            cases B with
            | fwd q => simp at hFs
            | obj W' Fs' Vs' ch' => simpa [Block.rename] using hFs
    | there y =>
        rw [Ctx.lookupFields_there] at hFs
        rw [Rename.lift_there, Ctx.lookupFields_there]
        exact h.fields y Fs hFs
  lookupB := by
    have hsl : (Rename.succ.comp σ.root.lift : Rename s1 (s2,x))
        = σ.root.comp Rename.succ :=
      Rename.funext' (by intro k z; cases k; rfl)
    intro p B hp
    simp only [Subst.lift_root]
    refine Ctx.lookupBlock_cons_map Γ b (Γ'.cons (b.rename σ.root)) σ.root.lift ?_ ?_
      (Γ.cons b).aliasBudget p B hp
    · intro B₀ C hx hC
      cases b with
      | «opaque» T => simp at hx
      | transparent T B1 =>
          rw [Ctx.blockAt_here_transparent] at hx
          obtain rfl : B1 = B₀ := by simpa using hx
          rw [Rename.lift_here, Ctx.lookupBlock_var_eq, Binding.rename_transparent,
            Ctx.blockAt_here_transparent]
          exact hC
    · intro y B hy
      rw [Rename.lift_there]
      have hw := Ctx.lookupBlock_weaken Γ' (b.rename σ.root) (h.lookupB hy)
      simp only [Path.weaken, Path.rename, Rename.succ_var] at hw
      rw [hw]
      simp only [Block.weaken, Block.rename_comp, hsl]
  nodeB := by
    have hsl : (Rename.succ.comp σ.root.lift : Rename s1 (s2,x))
        = σ.root.comp Rename.succ :=
      Rename.funext' (by intro k z; cases k; rfl)
    intro p B hp
    simp only [Subst.lift_root]
    refine Ctx.nodeBlock_cons_map Γ b (Γ'.cons (b.rename σ.root)) σ.root.lift ?_ ?_ p B hp
    · intro B₀ hx
      rw [Rename.lift_here]
      cases b with
      | «opaque» T => simp [Ctx.nodeBlock, Ctx.blockPass] at hx
      | transparent T B1 =>
          cases B1 with
          | fwd q => simp [Ctx.nodeBlock, Ctx.blockPass] at hx
          | obj W ls vls ch =>
              simp only [Ctx.nodeBlock, Ctx.blockPass, Ctx.blockAt_here_transparent] at hx
              obtain rfl := Option.some.inj hx
              simp [Ctx.nodeBlock, Ctx.blockPass, Block.rename]
    · intro y B hy
      rw [Rename.lift_there]
      have hw := Ctx.nodeBlock_weaken Γ' (b.rename σ.root) (h.nodeB hy)
      simp only [Path.weaken, Path.rename, Rename.succ_var] at hw
      rw [hw]
      simp only [Block.weaken, Block.rename_comp, hsl]

theorem ofRename {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2} (h : Ctx.Ren Γ ρ Γ') :
    Subst.Typed Γ (Subst.ofRename ρ) Γ' where
  var := by
    intro x
    show Γ' ⊢ₐ (.var (ρ.var x)) : _
    rw [Subst.ofRename_root, ← h.ty x]
    exact .var
  ty := by
    intro x _
    simpa using h.ty x
  transparent := by
    intro x ht
    simpa using h.transparent ht
  def_ := by
    intro x l W hW
    simpa using h.def_ x l W hW
  fields := by
    intro x Fs hFs
    simpa using h.fields x Fs hFs
  lookupB := by
    intro p B hp
    have := Ctx.lookupBlock_rename h.blocks hp
    simpa using this
  nodeB := by
    intro p B hp
    have := Ctx.nodeBlock_rename h.blocks hp
    simpa using this

/-- Instantiating the innermost *opaque* binder by an atom of its type. -/
theorem single {Γ : Ctx s} {T : Ty s} {a : Atom s} (ha : Γ ⊢ₐ a : T) :
    Subst.Typed (Γ.cons (.opaque T)) (Subst.single a) Γ where
  var := by
    intro x
    cases x with
    | here =>
        show Γ ⊢ₐ a : (((Γ.cons (.opaque T)).lookupTy .here).rename (Subst.single a).root)
        simpa [Binding.ty] using ha
    | there y =>
        show Γ ⊢ₐ .var y : _
        simpa using Atom.HasType.var (Γ := Γ) (x := y)
  ty := by
    intro x ht
    cases x with
    | here => simp at ht
    | there y => simp [Subst.single_root]
  transparent := by
    intro x ht
    cases x with
    | here => simp at ht
    | there y =>
        rw [Ctx.isTransparent_there] at ht
        simpa [Subst.single_root] using ht
  def_ := by
    intro x l W hW
    cases x with
    | here => simp at hW
    | there y =>
        rw [Ctx.lookupDef_there] at hW
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            simpa [Subst.single_root] using hd
  fields := by
    intro x Fs hFs
    cases x with
    | here => simp at hFs
    | there y =>
        rw [Ctx.lookupFields_there] at hFs
        simpa [Subst.single_root] using hFs
  lookupB := by
    refine Ctx.lookupBlock_rename ?_
    intro x B hB
    cases x with
    | here => simp at hB
    | there y =>
        rw [Ctx.blockAt_there] at hB
        obtain ⟨B0, hB0, rfl⟩ := Option.map_eq_some_iff.mp hB
        have hid : (Rename.succ.comp (Rename.subst a.root) : Rename s s) = Rename.id :=
          Rename.funext' (by intro k z; cases k; rfl)
        simp only [Subst.single_root, Rename.subst_there, hB0, Block.weaken,
          Block.rename_comp, hid, Block.rename_id]
  nodeB := by
    refine Ctx.nodeBlock_rename ?_
    intro x B hB
    cases x with
    | here => simp at hB
    | there y =>
        rw [Ctx.blockAt_there] at hB
        obtain ⟨B0, hB0, rfl⟩ := Option.map_eq_some_iff.mp hB
        have hid : (Rename.succ.comp (Rename.subst a.root) : Rename s s) = Rename.id :=
          Rename.funext' (by intro k z; cases k; rfl)
        simp only [Subst.single_root, Rename.subst_there, hB0, Block.weaken,
          Block.rename_comp, hid, Block.rename_id]

/-- Instantiating the innermost *forwarding* binder of a let over a path by an
atom typed at the singleton.  The block field is the canonical fact of P1.8:
over a typed store an atom at `μ [≈ q↑]` is rooted at the block of `q`.  It is
the only thing the store typing is used for, and `FormsTyped.sngl` is what
`preservation` hands over. -/
theorem singleFwd {Γ : Ctx s} {q : Path s} {a : Atom s}
    (hb : Γ.lookupBlock (.var a.root) = Γ.lookupBlock q) (ha : Γ ⊢ₐ a : Ty.snglOf q) :
    Subst.Typed (Γ.cons (Binding.fwdAt q)) (Subst.single a) Γ where
  var := by
    intro x
    cases x with
    | here =>
        show Γ ⊢ₐ a : (((Γ.cons (Binding.fwdAt q)).lookupTy .here).rename
          (Subst.single a).root)
        simpa [Binding.fwdAt, Binding.ty, Subst.single_root, Ty.substVar,
          Ty.weaken_substVar] using ha
    | there y =>
        show Γ ⊢ₐ .var y : _
        simpa using Atom.HasType.var (Γ := Γ) (x := y)
  ty := by
    intro x ht
    cases x with
    | here => exact absurd ht (Ctx.fwdAt_not_transparent Γ q)
    | there y => simp [Subst.single_root]
  transparent := by
    intro x ht
    cases x with
    | here => exact absurd ht (Ctx.fwdAt_not_transparent Γ q)
    | there y =>
        rw [Ctx.isTransparent_there] at ht
        simpa [Subst.single_root] using ht
  def_ := by
    intro x l W hW
    cases x with
    | here => simp [Binding.fwdAt] at hW
    | there y =>
        rw [Ctx.lookupDef_there] at hW
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            simpa [Subst.single_root] using hd
  fields := by
    intro x Fs hFs
    cases x with
    | here => simp [Binding.fwdAt] at hFs
    | there y =>
        rw [Ctx.lookupFields_there] at hFs
        simpa [Subst.single_root] using hFs
  lookupB := by
    intro p B hp
    refine Ctx.lookupBlock_cons_map Γ (Binding.fwdAt q) Γ (Subst.single a).root ?_ ?_
      (Γ.cons (Binding.fwdAt q)).aliasBudget p B hp
    · intro B₀ C hx hC
      obtain rfl : (Block.fwd q.weaken) = B₀ := by
        simpa [Binding.fwdAt] using hx
      simp only [Subst.single_root, Rename.subst_here]
      simp only [Block.rename, Path.weaken, Path.rename_comp, Ctx.follow,
        Subst.single_root] at hC
      rw [show (Rename.succ.comp (Rename.subst a.root) : Rename s s) = Rename.id from
        Rename.funext' (by intro k z; cases k; rfl), Path.rename_id] at hC
      rw [hb]
      exact hC
    · intro y B hy
      simp only [Subst.single_root, Rename.subst_there]
      rw [hy]
      simp only [Block.weaken, Block.rename_comp,
        show (Rename.succ.comp (Rename.subst a.root) : Rename s s) = Rename.id from
          Rename.funext' (by intro k z; cases k; rfl), Block.rename_id]
  nodeB := by
    intro p B hp
    refine Ctx.nodeBlock_cons_map Γ (Binding.fwdAt q) Γ (Subst.single a).root ?_ ?_ p B hp
    · intro B₀ hx
      simp [Ctx.nodeBlock, Ctx.blockPass, Binding.fwdAt] at hx
    · intro y B hy
      simp only [Subst.single_root, Rename.subst_there]
      rw [hy]
      simp only [Block.weaken, Block.rename_comp,
        show (Rename.succ.comp (Rename.subst a.root) : Rename s s) = Rename.id from
          Rename.funext' (by intro k z; cases k; rfl), Block.rename_id]

end Subst.Typed

/-! ## Evidence and atoms -/

mutual

theorem LeCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {e : LeCo s1} {S T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ e : S ≤ T) :
    Γ' ⊢ (e.subst σ) : (S.rename σ.root) ≤ (T.rename σ.root) := by
  match h with
  | .refl => exact .refl
  | .trans he hf => exact .trans (he.subst hσ) (hf.subst hσ)
  | .top => exact .top
  | .bot => exact .bot
  | .eqToLe hφ => exact .eqToLe (hφ.subst hσ)
  | .pi he hf =>
      have hf' := hf.subst (hσ.lift _)
      simp only [Subst.lift_root, Binding.rename_opaque] at hf'
      exact .pi (he.subst hσ) hf'
  | .obj hm => exact .obj (hm.subst hσ)
  | .pair he hf =>
      have := LeCo.HasType.pair (he.subst hσ) (hf.subst hσ)
      simpa [LeCo.subst, Ty.rename, Telescope.append_rename] using this
  | .bound hAt =>
      exact .bound (by
        simpa [Proposition.rename, Ty.weaken_rename] using hAt.rename σ.root.lift)
  | .intoBnd he =>
      have := LeCo.HasType.intoBnd (he.subst hσ)
      simpa [LeCo.subst, Ty.rename, Telescope.rename, Proposition.rename,
        Ty.weaken_rename] using this
  | @LeCo.HasType.member _ _ a S e Tel i S' T' ha he hAt =>
      have := LeCo.HasType.member (a := a.subst σ) (ha.subst hσ)
        (by simpa [Ty.rename] using he.subst hσ) (hAt.rename σ.root.lift)
      simpa [LeCo.subst, Ty.substVar_rename] using this
  | @LeCo.HasType.memberP _ _ P S e Tel i S' T' hP he hAt =>
      have := LeCo.HasType.memberP (P := P.subst σ) (hP.subst hσ)
        (by simpa [Ty.rename] using he.subst hσ) (hAt.rename σ.root.lift)
      simpa [LeCo.subst, Ty.substPath_rename, PathCo.path_subst] using this

theorem EqCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {φ : EqCo s1} {S T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ φ : S ≡ T) :
    Γ' ⊢ (φ.subst σ) : (S.rename σ.root) ≡ (T.rename σ.root) := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.subst hσ)
  | .trans hφ hψ => exact .trans (hφ.subst hσ) (hψ.subst hσ)
  | .def hd => exact .def (hσ.def_ _ _ _ hd)
  | .defP hd =>
      have := EqCo.HasType.defP (hσ.defP hd)
      simpa [EqCo.subst, Ty.rename] using this
  | @EqCo.HasType.member _ _ a S e Tel i S' T' ha he hAt =>
      have := EqCo.HasType.member (a := a.subst σ) (ha.subst hσ)
        (by simpa [Ty.rename] using he.subst hσ) (hAt.rename σ.root.lift)
      simpa [EqCo.subst, Ty.substVar_rename] using this
  | @EqCo.HasType.memberP _ _ P S e Tel i S' T' hP he hAt =>
      have := EqCo.HasType.memberP (P := P.subst σ) (hP.subst hσ)
        (by simpa [Ty.rename] using he.subst hσ) (hAt.rename σ.root.lift)
      simpa [EqCo.subst, Ty.substPath_rename, PathCo.path_subst] using this

theorem Has.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {hh : Has s1} {p : Path s1} {l : Label}
    (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ hh : p ∋ l) :
    Γ' ⊢ (hh.subst σ) : (p.rename σ.root) ∋ l := by
  match h with
  | @Has.HasType.member _ _ a S e Tel i l ha he hAt =>
      have := Has.HasType.member (a := a.subst σ) (ha.subst hσ)
        (by simpa [Ty.rename] using he.subst hσ) (hAt.rename σ.root.lift)
      simpa [Has.subst, Path.rename] using this
  | @Has.HasType.memberP _ _ P S e Tel i l hP he hAt =>
      have := Has.HasType.memberP (P := P.subst σ) (hP.subst hσ)
        (by simpa [Ty.rename] using he.subst hσ) (hAt.rename σ.root.lift)
      simpa [Has.subst, PathCo.path_subst] using this
  | .field hf hm => exact .field (hσ.fields _ _ hf) hm

theorem Side.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {sd : Side s1} {X Y : Ty (s1,x)} (hσ : Subst.Typed Γ σ Γ') (h : Side.HasType Γ sd X Y) :
    Side.HasType Γ' (sd.subst σ) (X.rename σ.root.lift) (Y.rename σ.root.lift) := by
  match h with
  | .none => exact .none
  | .bot => exact .bot
  | .top => exact .top
  | .some he =>
      have := Side.HasType.some (he.subst hσ)
      simpa [Side.subst, Ty.weaken_rename] using this

theorem Morphism.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {σ : Subst s1 s2} {src : Telescope (s1,x)} {m : Morphism s1} {Tel : Telescope (s1,x)}
    (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ m : src ⇒ Tel) :
    Γ' ⊢ (m.subst σ) : (src.rename σ.root.lift) ⇒ (Tel.rename σ.root.lift) := by
  match h with
  | .nil => exact .nil
  | .le hm hAt hpre hpost =>
      exact .le (hm.subst hσ) (by simpa [Proposition.rename] using hAt.rename σ.root.lift)
        (hpre.subst hσ) (hpost.subst hσ)
  | .leEq hm hAt hpre hpost =>
      exact .leEq (hm.subst hσ) (by simpa [Proposition.rename] using hAt.rename σ.root.lift)
        (hpre.subst hσ) (hpost.subst hσ)
  | .leEqSym hm hAt hpre hpost =>
      exact .leEqSym (hm.subst hσ) (by simpa [Proposition.rename] using hAt.rename σ.root.lift)
        (hpre.subst hσ) (hpost.subst hσ)
  | .eq hm hAt =>
      exact .eq (hm.subst hσ) (by simpa [Proposition.rename] using hAt.rename σ.root.lift)
  | .eqSym hm hAt =>
      exact .eqSym (hm.subst hσ) (by simpa [Proposition.rename] using hAt.rename σ.root.lift)
  | .has hm hAt =>
      exact .has (hm.subst hσ) (by simpa [Proposition.rename] using hAt.rename σ.root.lift)
  | .bnd hm he =>
      have := Morphism.HasType.bnd (hm.subst hσ) (by simpa [Ty.rename] using he.subst hσ)
      simpa [Morphism.subst, Telescope.rename, Proposition.rename, Ty.weaken_rename] using this
  | .hasVal hm hAt =>
      exact .hasVal (hm.subst hσ) (by simpa [Proposition.rename] using hAt.rename σ.root.lift)
  | .hasOfVal hm hAt =>
      exact .hasOfVal (hm.subst hσ) (by simpa [Proposition.rename] using hAt.rename σ.root.lift)
  | .aliasCopy hm hAt =>
      exact .aliasCopy (hm.subst hσ) (by simpa [Proposition.rename] using hAt.rename σ.root.lift)

theorem Atom.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {a : Atom s1} {T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ₐ a : T) :
    Γ' ⊢ₐ (a.subst σ) : (T.rename σ.root) := by
  match h with
  | @Atom.HasType.var _ _ x => exact hσ.var x
  | .cast ha he => exact .cast (ha.subst hσ) (he.subst hσ)
  | @Atom.HasType.unfoldSelf _ _ a Tel ha =>
      have := Atom.HasType.unfoldSelf (Tel := Tel.rename σ.root.lift) (a := a.subst σ)
        (by simpa [Ty.rename] using ha.subst hσ)
      simpa [Atom.subst, Ty.rename, Telescope.weaken_rename,
        Telescope.substVar_rename] using this
  | @Atom.HasType.foldSelf _ _ a Tel ha =>
      have ha' := ha.subst hσ
      simp only [Ty.rename, Telescope.weaken_rename, Telescope.substVar_rename] at ha'
      have := Atom.HasType.foldSelf (Tel := Tel.rename σ.root.lift) (a := a.subst σ)
        (by rw [Atom.root_subst]; exact ha')
      simpa [Atom.subst, Ty.rename] using this
  | .both ha hb hr =>
      have := Atom.HasType.both (ha.subst hσ) (hb.subst hσ)
        (by simp [Atom.root_subst, hr])
      simpa [Atom.subst, Ty.rename, Telescope.append_rename] using this
  | .sngl ha hα =>
      have := Atom.HasType.sngl (ha.subst hσ)
        (by simpa [Path.rename, Atom.root_subst] using hα.subst hσ)
      simpa [Atom.subst] using this

theorem PathCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {P : PathCo s1} {T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ᵖ P : T) :
    Γ' ⊢ᵖ (P.subst σ) : (T.rename σ.root) := by
  match h with
  | @PathCo.HasType.var _ _ x => exact PathCo.HasType.ofAtom (hσ.var x)
  | @PathCo.HasType.sel _ _ P Tel i a hP hAt =>
      have := PathCo.HasType.sel (P := P.subst σ) (a := a)
        (by simpa [Ty.rename] using hP.subst hσ)
        (by simpa [Proposition.rename] using hAt.rename σ.root.lift)
      simpa [PathCo.subst, Ty.rename, PathCo.path_subst] using this
  | .cast hP he => exact .cast (hP.subst hσ) (he.subst hσ)
  | .alias hα hP =>
      exact .alias (by simpa [PathCo.path_subst] using hα.subst hσ) (hP.subst hσ)
  | @PathCo.HasType.unfoldSelf _ _ P Tel hP =>
      have := PathCo.HasType.unfoldSelf (Tel := Tel.rename σ.root.lift) (P := P.subst σ)
        (by simpa [Ty.rename] using hP.subst hσ)
      simpa [PathCo.subst, Ty.rename, PathCo.path_subst, Telescope.weaken_rename,
        Telescope.substPath_rename] using this
  | @PathCo.HasType.foldSelf _ _ P Tel hP =>
      have hP' := hP.subst hσ
      simp only [Ty.rename, Telescope.weaken_rename, Telescope.substPath_rename] at hP'
      have := PathCo.HasType.foldSelf (Tel := Tel.rename σ.root.lift) (P := P.subst σ)
        (by simpa [PathCo.path_subst] using hP')
      simpa [PathCo.subst, Ty.rename] using this
  | .both hP hQ hr =>
      have := PathCo.HasType.both (hP.subst hσ) (hQ.subst hσ)
        (by simp [PathCo.path_subst, hr])
      simpa [PathCo.subst, Ty.rename, Telescope.append_rename] using this
  | .sngl hP hα =>
      have := PathCo.HasType.sngl (hP.subst hσ)
        (by simpa [PathCo.path_subst] using hα.subst hσ)
      simpa [PathCo.subst] using this
  | @PathCo.HasType.node _ _ p W ls vls ch hs hn =>
      have hn' := hσ.nodeB hn
      simp only [Block.rename, Witnesses.substPath_rename] at hn'
      have := PathCo.HasType.node (Γ := Γ') (by rw [Path.isSel_rename]; exact hs) hn'
      simpa [PathCo.subst, Ty.rename, Telescope.ofLiteral_rename] using this

theorem AliasCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {α : AliasCo s1} {p q : Path s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ α : p ≋ q) :
    Γ' ⊢ (α.subst σ) : (p.rename σ.root) ≋ (q.rename σ.root) := by
  match h with
  | .refl => exact .refl
  | .symm hα => exact .symm (hα.subst hσ)
  | .trans hα hβ => exact .trans (hα.subst hσ) (hβ.subst hσ)
  | @AliasCo.HasType.sel _ _ α p q a hα =>
      have := AliasCo.HasType.sel (a := a) (hα.subst hσ)
      simpa [AliasCo.subst, Path.rename] using this
  | @AliasCo.HasType.member _ _ P S e Tel i q hP he hAt =>
      have := AliasCo.HasType.member (P := P.subst σ) (hP.subst hσ)
        (by simpa [Ty.rename] using he.subst hσ)
        (by simpa [Proposition.rename] using hAt.rename σ.root.lift)
      simpa [AliasCo.subst, PathCo.path_subst, Path.substPath_rename] using this

end

/-! ## Terms, values, fields -/

mutual

theorem Tm.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {t : Tm s1} {T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ t : T) :
    Γ' ⊢ (t.subst σ) : (T.rename σ.root) := by
  match h with
  | .atom ha => exact .atom (ha.subst hσ)
  | .val hv => exact .val (hv.subst hσ)
  | @Tm.HasType.app _ _ a S T b ha hb =>
      have := Tm.HasType.app (b := b.subst σ)
        (by simpa [Ty.rename] using ha.subst hσ) (hb.subst hσ)
      simpa [Tm.subst, Ty.substVar_rename] using this
  | @Tm.HasType.proj _ _ a S hh l ha hhh =>
      have := Tm.HasType.proj (a := a.subst σ) (ha.subst hσ)
        (by rw [Atom.root_subst]; exact hhh.subst hσ)
      simpa [Tm.subst, Ty.rename] using this
  | .let ht hu =>
      refine .let (ht.subst hσ) ?_
      have := hu.subst (hσ.lift _)
      simpa [Ty.weaken_rename] using this
  | .letPath ht hu =>
      refine .letPath (by simpa using ht.subst hσ) ?_
      have := hu.subst (hσ.lift (Binding.fwdAt _))
      simpa [Ty.weaken_rename] using this
  | .cast ht he => exact .cast (ht.subst hσ) (he.subst hσ)

theorem Value.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {v : Value s1} {T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ᵥ v : T) :
    Γ' ⊢ᵥ (v.subst σ) : (T.rename σ.root) := by
  match h with
  | .lam ht =>
      have := ht.subst (hσ.lift _)
      simpa [Value.subst, Ty.rename] using Value.HasType.lam (by simpa using this)
  | @Value.HasType.obj _ F0 _ W0 hF =>
      have hF' := Fields.HasType.subst (hσ.lift _) hF
      have := Value.HasType.obj (Γ := Γ') (W := W0.rename σ.root.lift) (F := F0.subst σ.lift)
        (by simpa [Binding.rename, Ty.rename, Telescope.ofLiteral_rename, Block.rename,
          Fields.children_self_subst] using hF')
      simpa [Value.subst, Ty.rename, Telescope.ofLiteral_rename] using this
  | .cast hv he => exact .cast (hv.subst hσ) (he.subst hσ)

theorem Fields.HasType.subst {s1 s2 : Sig} {Γ : Ctx (s1,x)} {Γ' : Ctx (s2,x)}
    {σ : Subst s1 s2} {F : Fields (s1,x)}
    (hσ : Subst.Typed Γ σ.lift Γ') (h : Γ ⊢ᶠ F) :
    Γ' ⊢ᶠ (F.subst σ.lift) := by
  match h with
  | .nil => exact .nil
  | .cons hF ht =>
      refine .cons (hF.subst hσ) ?_
      have := ht.subst hσ
      simpa [Ty.rename] using this

end

/-! ## Instantiating the innermost opaque binder -/

theorem Atom.HasType.substAtom {Γ : Ctx s} {T : Ty s} {b : Atom (s,x)} {U : Ty (s,x)}
    {a : Atom s} (hb : (Γ.cons (.opaque T)) ⊢ₐ b : U) (ha : Γ ⊢ₐ a : T) :
    Γ ⊢ₐ b.subst (Subst.single a) : (U⟦a.root⟧) := by
  have := hb.subst (Subst.Typed.single ha)
  simpa [Ty.substVar] using this

theorem Tm.HasType.substAtom {Γ : Ctx s} {T : Ty s} {u : Tm (s,x)} {U : Ty (s,x)}
    {a : Atom s} (hu : (Γ.cons (.opaque T)) ⊢ u : U) (ha : Γ ⊢ₐ a : T) :
    Γ ⊢ u.substAtom a : (U⟦a.root⟧) := by
  have := hu.subst (Subst.Typed.single ha)
  simpa [Tm.substAtom, Ty.substVar] using this

theorem Value.HasType.substAtom {Γ : Ctx s} {T : Ty s} {v : Value (s,x)} {U : Ty (s,x)}
    {a : Atom s} (hv : (Γ.cons (.opaque T)) ⊢ᵥ v : U) (ha : Γ ⊢ₐ a : T) :
    Γ ⊢ᵥ v.subst (Subst.single a) : (U⟦a.root⟧) := by
  have := hv.subst (Subst.Typed.single ha)
  simpa [Ty.substVar] using this

/-! ## Instantiating the forwarding binder of a let over a path

The substitution lemma the `rename` step of the machine needs under a
`letPath` frame.  The hypothesis `hb` is the canonical fact of P1.8, which a
typed store gives and which `preservation` reads off `FormsTyped.sngl`.  The
version with the incoming type free is refuted (`forwarding_subst_false`). -/

theorem substAtom_fwd {Γ : Ctx s} {q : Path s} {u : Tm (s,x)} {U : Ty (s,x)} {a : Atom s}
    (hb : Γ.lookupBlock (.var a.root) = Γ.lookupBlock q)
    (hu : Γ.cons (Binding.fwdAt q) ⊢ u : U) (ha : Γ ⊢ₐ a : Ty.snglOf q) :
    Γ ⊢ u.substAtom a : (U⟦a.root⟧) := by
  have := hu.subst (Subst.Typed.singleFwd hb ha)
  simpa [Tm.substAtom, Ty.substVar] using this

end FCdot

end Paths
