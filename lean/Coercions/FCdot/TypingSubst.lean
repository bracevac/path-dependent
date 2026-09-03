import Coercions.FCdot.TypingRename

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

/-! ## Typed substitutions -/

/-- `Subst.Typed Γ σ Γ'`: every variable of `Γ` goes to an atom of the
transported type, and definitions and field labels survive along `σ.root`. -/
structure Subst.Typed {s1 s2 : Sig} (Γ : Ctx s1) (σ : Subst s1 s2) (Γ' : Ctx s2) : Prop where
  var : ∀ x, Atom.HasType Γ' (σ.var x) ((Γ.lookupTy x).rename σ.root)
  /-- On transparent binders the substitution behaves like a renaming. -/
  ty : ∀ x, Γ.IsTransparent x →
      Γ'.lookupTy (σ.root.var x) = (Γ.lookupTy x).rename σ.root
  transparent : ∀ x, Γ.IsTransparent x → Γ'.IsTransparent (σ.root.var x)
  def_ : ∀ x l W, Γ.lookupDef x l = some W →
      Γ'.lookupDef (σ.root.var x) l = some (W.rename σ.root)
  fields : ∀ x Fs, Γ.lookupFields x = some Fs → Γ'.lookupFields (σ.root.var x) = some Fs

namespace Subst.Typed

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
        show Atom.HasType (Γ'.cons (b.rename σ.root)) ((σ.var y).weaken)
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
        | transparent T W' Fs => simp
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
        | transparent T W' Fs =>
            have hWe : W = W'.get l := by simpa using hW.symm
            subst hWe
            simp only [Rename.lift_here, Binding.rename_transparent,
              Ctx.lookupDef_here_transparent, Witnesses.get_rename]
    | there y =>
        rw [Ctx.lookupDef_there] at hW
        rw [Rename.lift_there, Ctx.lookupDef_there]
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0.weaken := by simpa using hW.symm
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
        | transparent T W' Fs' => simpa using hFs
    | there y =>
        rw [Ctx.lookupFields_there] at hFs
        rw [Rename.lift_there, Ctx.lookupFields_there]
        exact h.fields y Fs hFs

theorem ofRename {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2} (h : Ctx.Ren Γ ρ Γ') :
    Subst.Typed Γ (Subst.ofRename ρ) Γ' where
  var := by
    intro x
    show Atom.HasType Γ' (.var (ρ.var x)) _
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

/-- Instantiating the innermost *opaque* binder by an atom of its type. -/
theorem single {Γ : Ctx s} {T : Ty s} {a : Atom s} (ha : Atom.HasType Γ a T) :
    Subst.Typed (Γ.cons (.opaque T)) (Subst.single a) Γ where
  var := by
    intro x
    cases x with
    | here =>
        show Atom.HasType Γ a (((Γ.cons (.opaque T)).lookupTy .here).rename (Subst.single a).root)
        simpa [Binding.ty] using ha
    | there y =>
        show Atom.HasType Γ (.var y) _
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
            have hWe : W = W0.weaken := by simpa using hW.symm
            subst hWe
            simpa [Subst.single_root] using hd
  fields := by
    intro x Fs hFs
    cases x with
    | here => simp at hFs
    | there y =>
        rw [Ctx.lookupFields_there] at hFs
        simpa [Subst.single_root] using hFs

end Subst.Typed

/-! ## Evidence and atoms -/

mutual

theorem LeCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {e : LeCo s1} {S T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : LeCo.HasType Γ e S T) :
    LeCo.HasType Γ' (e.subst σ) (S.rename σ.root) (T.rename σ.root) := by
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
  | .obj hm =>
      have hm' := Morphism.HasType.subst (hσ.lift _) hm
      simp only [Binding.rename_opaque, Ty.rename] at hm'
      exact .obj hm'
  | @LeCo.HasType.member _ _ a S e Tel i S' T' ha he hAt =>
      have := LeCo.HasType.member (a := a.subst σ) (ha.subst hσ)
        (by simpa [Ty.rename] using he.subst hσ) (hAt.rename σ.root.lift)
      simpa [LeCo.subst, Ty.substVar_rename] using this

theorem EqCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {φ : EqCo s1} {S T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : EqCo.HasType Γ φ S T) :
    EqCo.HasType Γ' (φ.subst σ) (S.rename σ.root) (T.rename σ.root) := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.subst hσ)
  | .trans hφ hψ => exact .trans (hφ.subst hσ) (hψ.subst hσ)
  | .def hd => exact .def (hσ.def_ _ _ _ hd)
  | @EqCo.HasType.member _ _ a S e Tel i S' T' ha he hAt =>
      have := EqCo.HasType.member (a := a.subst σ) (ha.subst hσ)
        (by simpa [Ty.rename] using he.subst hσ) (hAt.rename σ.root.lift)
      simpa [EqCo.subst, Ty.substVar_rename] using this

theorem Has.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {hh : Has s1} {x : BVar s1 .var} {l : Label}
    (hσ : Subst.Typed Γ σ Γ') (h : Has.HasType Γ hh x l) :
    Has.HasType Γ' (hh.subst σ) (σ.root.var x) l := by
  match h with
  | @Has.HasType.member _ _ a S e Tel i l ha he hAt =>
      have := Has.HasType.member (a := a.subst σ) (ha.subst hσ)
        (by simpa [Ty.rename] using he.subst hσ) (hAt.rename σ.root.lift)
      simpa [Has.subst] using this
  | .field hf hm => exact .field (hσ.fields _ _ hf) hm

theorem Morphism.HasType.subst {s1 s2 : Sig} {Γ : Ctx (s1,x)} {Γ' : Ctx (s2,x)}
    {σ : Subst s1 s2} {m : Morphism (s1,x)} {Tel : Telescope (s1,x)}
    (hσ : Subst.Typed Γ σ.lift Γ') (h : Morphism.HasType Γ m Tel) :
    Morphism.HasType Γ' (m.subst σ.lift) (Tel.rename σ.root.lift) := by
  match h with
  | .nil => exact .nil
  | .le hm he =>
      have := he.subst hσ
      simp only [Subst.lift_root] at this
      exact .le (hm.subst hσ) this
  | .eq hm hφ =>
      have := hφ.subst hσ
      simp only [Subst.lift_root] at this
      exact .eq (hm.subst hσ) this
  | .has hm hh =>
      have := hh.subst hσ
      simp only [Subst.lift_root, Rename.lift_here] at this
      exact .has (hm.subst hσ) this

theorem Atom.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {a : Atom s1} {T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Atom.HasType Γ a T) :
    Atom.HasType Γ' (a.subst σ) (T.rename σ.root) := by
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

end

/-! ## Terms, values, fields -/

mutual

theorem Tm.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {t : Tm s1} {T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Tm.HasType Γ t T) :
    Tm.HasType Γ' (t.subst σ) (T.rename σ.root) := by
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
  | .cast ht he => exact .cast (ht.subst hσ) (he.subst hσ)

theorem Value.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {v : Value s1} {T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Value.HasType Γ v T) :
    Value.HasType Γ' (v.subst σ) (T.rename σ.root) := by
  match h with
  | .lam ht =>
      have := ht.subst (hσ.lift _)
      simpa [Value.subst, Ty.rename] using Value.HasType.lam (by simpa using this)
  | .obj hG hE hF =>
      refine .obj (Witnesses.Guarded.rename σ.root hG) ?_ ?_
      · have := Morphism.HasType.subst (hσ.lift _) hE
        simpa using this
      · have := Fields.HasType.subst (hσ.lift _) hF
        simpa [Ty.rename] using this
  | .cast hv he => exact .cast (hv.subst hσ) (he.subst hσ)

theorem Fields.HasType.subst {s1 s2 : Sig} {Γ : Ctx (s1,x)} {Γ' : Ctx (s2,x)}
    {σ : Subst s1 s2} {F : Fields (s1,x)}
    (hσ : Subst.Typed Γ σ.lift Γ') (h : Fields.HasType Γ F) :
    Fields.HasType Γ' (F.subst σ.lift) := by
  match h with
  | .nil => exact .nil
  | .cons hF ht =>
      refine .cons (hF.subst hσ) ?_
      have := ht.subst hσ
      simpa [Ty.rename] using this

end

/-! ## Instantiating the innermost opaque binder -/

theorem Atom.HasType.substAtom {Γ : Ctx s} {T : Ty s} {b : Atom (s,x)} {U : Ty (s,x)}
    {a : Atom s} (hb : Atom.HasType (Γ.cons (.opaque T)) b U) (ha : Atom.HasType Γ a T) :
    Atom.HasType Γ (b.subst (Subst.single a)) (U.substVar a.root) := by
  have := hb.subst (Subst.Typed.single ha)
  simpa [Ty.substVar] using this

theorem Tm.HasType.substAtom {Γ : Ctx s} {T : Ty s} {u : Tm (s,x)} {U : Ty (s,x)}
    {a : Atom s} (hu : Tm.HasType (Γ.cons (.opaque T)) u U) (ha : Atom.HasType Γ a T) :
    Tm.HasType Γ (u.substAtom a) (U.substVar a.root) := by
  have := hu.subst (Subst.Typed.single ha)
  simpa [Tm.substAtom, Ty.substVar] using this

theorem Value.HasType.substAtom {Γ : Ctx s} {T : Ty s} {v : Value (s,x)} {U : Ty (s,x)}
    {a : Atom s} (hv : Value.HasType (Γ.cons (.opaque T)) v U) (ha : Atom.HasType Γ a T) :
    Value.HasType Γ (v.subst (Subst.single a)) (U.substVar a.root) := by
  have := hv.subst (Subst.Typed.single ha)
  simpa [Ty.substVar] using this

end FCdot
