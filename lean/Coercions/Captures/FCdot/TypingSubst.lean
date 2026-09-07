import Coercions.Captures.FCdot.TypingRename

namespace Captures

/-!
# Substitution of atoms in FCdot typing derivations

A substitution maps variables to atoms.  Types and evidence see only the
root map `σ.root`, but evidence contains atoms (inside `member`), so the
whole family is transported by `subst`, not by a renaming.  `Subst.Typed Γ σ
Γ'` is the typed-substitution judgement; `Subst.Typed.single` instantiates
the innermost *opaque* binder by an atom of its type.
-/

namespace FCdot

@[simp] theorem CaptureSet.rename_subst_weaken' {s : Sig} {k : Kind}
    (C : CaptureSet s) (y : BVar s k) :
    CaptureSet.rename (C.weaken (k := k)) (Rename.subst y) = C :=
  CaptureSet.rename_subst_weaken C y

@[simp] theorem Ty.rename_subst_weaken' {s : Sig} {k : Kind} (T : Ty s) (y : BVar s k) :
    (T.weaken (k := k)).rename (Rename.subst y) = T :=
  Ty.rename_subst_weaken T y

@[simp] theorem Shape.rename_subst_weaken' {s : Sig} {k : Kind} (S : Shape s) (y : BVar s k) :
    (S.weaken (k := k)).rename (Rename.subst y) = S :=
  Shape.rename_subst_weaken S y

@[simp] theorem Telescope.rename_subst_weaken' {s : Sig} {k : Kind}
    (Tel : Telescope s) (y : BVar s k) :
    (Tel.weaken (k := k)).rename (Rename.subst y) = Tel :=
  Telescope.rename_subst_weaken Tel y

@[simp] theorem Fields.labels_subst {s1 s2 : Sig} :
    ∀ (F : Fields s1) (σ : Subst s1 s2), (F.subst σ).labels = F.labels
  | .nil, _ => rfl
  | .cons F l t g, σ => by
      simp [Fields.subst, Fields.labels, Fields.labels_subst F σ]

/-! ## Typed substitutions -/

/-- `Subst.Typed Γ σ Γ'`: every variable of `Γ` goes to an atom of the
transported type, and definitions and field labels survive along `σ.root`. -/
structure Subst.Typed {s1 s2 : Sig} (Γ : Ctx s1) (σ : Subst s1 s2) (Γ' : Ctx s2) : Prop where
  var : ∀ x, Γ' ⊢ₐ (σ.var x) : ((Γ.lookupTy x).rename σ.root)
  /-- On transparent binders the substitution behaves like a renaming. -/
  ty : ∀ x, Γ.IsTransparent x →
      Γ'.lookupTy (σ.root.var x) = (Γ.lookupTy x).rename σ.root
  transparent : ∀ x, Γ.IsTransparent x → Γ'.IsTransparent (σ.root.var x)
  def_ : ∀ x l (W : Shape s1), Γ.lookupDef x l = some W →
      Γ'.lookupDef (σ.root.var x) l = some (W.rename σ.root)
  /-- Capture definitions of transparent binders survive too. -/
  defC : ∀ x l (C : CaptureSet s1), Γ.lookupDefC x l = some C →
      Γ'.lookupDefC (σ.root.var x) l = some (C.rename σ.root)
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
        | transparent T W' Wc' Fs => simp
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
        | transparent T W' Wc' Fs =>
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
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            simp [Shape.weaken_rename]
  defC := by
    intro x l C hC
    simp only [Subst.lift_root]
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hC
        | transparent T W' Wc' Fs =>
            have hCe : C = Wc'.get l := by simpa using hC.symm
            subst hCe
            simp only [Rename.lift_here, Binding.rename_transparent,
              Ctx.lookupDefC_here_transparent, CapWitnesses.get_rename]
    | there y =>
        rw [Ctx.lookupDefC_there] at hC
        rw [Rename.lift_there, Ctx.lookupDefC_there]
        cases hd : Γ.lookupDefC y l with
        | none => rw [hd] at hC; simp at hC
        | some C0 =>
            rw [hd] at hC
            have hCe : C = C0↑ := by simpa using hC.symm
            subst hCe
            rw [h.defC y l C0 hd]
            simp [CaptureSet.weaken_rename]
  fields := by
    intro x Fs hFs
    simp only [Subst.lift_root]
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hFs
        | transparent T W' Wc' Fs' => simpa using hFs
    | there y =>
        rw [Ctx.lookupFields_there] at hFs
        rw [Rename.lift_there, Ctx.lookupFields_there]
        exact h.fields y Fs hFs

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
  defC := by
    intro x l C hC
    simpa using h.defC x l C hC
  fields := by
    intro x Fs hFs
    simpa using h.fields x Fs hFs

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
  defC := by
    intro x l C hC
    cases x with
    | here => simp at hC
    | there y =>
        rw [Ctx.lookupDefC_there] at hC
        cases hd : Γ.lookupDefC y l with
        | none => rw [hd] at hC; simp at hC
        | some C0 =>
            rw [hd] at hC
            have hCe : C = C0↑ := by simpa using hC.symm
            subst hCe
            simpa [Subst.single_root] using hd
  fields := by
    intro x Fs hFs
    cases x with
    | here => simp at hFs
    | there y =>
        rw [Ctx.lookupFields_there] at hFs
        simpa [Subst.single_root] using hFs

/-- Passing under a capture binder: `Subst.liftC` is a typed substitution
whenever `σ` is.  The capture binder carries no term, so the four lookups
step past it by the same kind-generic weakening. -/
theorem liftC {Γ : Ctx s1} {σ : Subst s1 s2} {Γ' : Ctx s2}
    (h : Subst.Typed Γ σ Γ') (b : CapBound s1) :
    Subst.Typed (Γ.consC b) σ.liftC (Γ'.consC (b.rename σ.root)) where
  var := by
    intro x
    simp only [Subst.liftC_root]
    cases x with
    | there y =>
        show Atom.HasType (Γ'.consC (b.rename σ.root)) ((σ.var y)↑)
          (((Γ.consC b).lookupTy (.there y)).rename σ.root.lift)
        rw [Ctx.lookupTy_thereC, Ty.weaken_rename]
        exact (h.var y).weakenC _
  ty := by
    intro x ht
    simp only [Subst.liftC_root]
    cases x with
    | there y =>
        rw [Ctx.isTransparent_thereC] at ht
        rw [Rename.lift_there, Ctx.lookupTy_thereC, Ctx.lookupTy_thereC, h.ty y ht,
          Ty.weaken_rename]
  transparent := by
    intro x ht
    simp only [Subst.liftC_root]
    cases x with
    | there y =>
        rw [Ctx.isTransparent_thereC] at ht
        rw [Rename.lift_there, Ctx.isTransparent_thereC]
        exact h.transparent y ht
  def_ := by
    intro x l W hW
    simp only [Subst.liftC_root]
    cases x with
    | there y =>
        rw [Ctx.lookupDef_thereC] at hW
        rw [Rename.lift_there, Ctx.lookupDef_thereC]
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            simp [Shape.weaken_rename]
  defC := by
    intro x l C hC
    simp only [Subst.liftC_root]
    cases x with
    | there y =>
        rw [Ctx.lookupDefC_thereC] at hC
        rw [Rename.lift_there, Ctx.lookupDefC_thereC]
        cases hd : Γ.lookupDefC y l with
        | none => rw [hd] at hC; simp at hC
        | some C0 =>
            rw [hd] at hC
            have hCe : C = C0↑ := by simpa using hC.symm
            subst hCe
            rw [h.defC y l C0 hd]
            simp [CaptureSet.weaken_rename]
  fields := by
    intro x Fs hFs
    simp only [Subst.liftC_root]
    cases x with
    | there y =>
        rw [Ctx.lookupFields_thereC] at hFs
        rw [Rename.lift_there, Ctx.lookupFields_thereC]
        exact h.fields y Fs hFs

end Subst.Typed

/-! ## Evidence and atoms -/

mutual

/-- The capture family is transported by the substitution.  Types and
evidence see an atom only through its root, so a capture set travels along
the renaming of roots, exactly as in the type sort; the family mentions
atoms (`capvar`, `member`), so it belongs to the mutual recursion. -/
theorem CapCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {f : CapCo s1} {C D : CaptureSet s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ᶜ f : C ⊑ D) :
    Γ' ⊢ᶜ (f.subst σ) : (C.rename σ.root) ⊑ (D.rename σ.root) := by
  match h with
  | .refl => exact .refl
  | .trans hf hg => exact .trans (hf.subst hσ) (hg.subst hσ)
  | .elem hs => exact .elem (hs.rename σ.root)
  | .union hf hg =>
      have := CapCo.HasType.union (hf.subst hσ) (hg.subst hσ)
      simpa [CapCo.subst, CaptureSet.rename] using this
  | @CapCo.HasType.capvar _ _ a S C ha =>
      have := CapCo.HasType.capvar (a := a.subst σ)
        (by simpa [Ty.rename] using Atom.HasType.subst hσ ha)
      simpa [CapCo.subst, CaptureSet.rename, CapAtom.rename, Atom.root_subst] using this
  | @CapCo.HasType.member _ _ a S D e Tel i C₁ C₂ ha he hAt =>
      have := CapCo.HasType.member (a := a.subst σ)
        (by simpa [Ty.rename] using Atom.HasType.subst hσ ha)
        (by simpa [Shape.rename] using he.subst hσ) (hAt.rename σ.root.lift)
      simpa [CapCo.subst, CaptureSet.substVar_rename, Atom.root_subst] using this
  | .eqToLe hφ => exact .eqToLe (hφ.subst hσ)

theorem CapEq.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {φ : CapEq s1} {C D : CaptureSet s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ᶜ φ : C ≡ D) :
    Γ' ⊢ᶜ (φ.subst σ) : (C.rename σ.root) ≡ (D.rename σ.root) := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.subst hσ)
  | .trans hφ hψ => exact .trans (hφ.subst hσ) (hψ.subst hσ)
  | .defC hd =>
      have := CapEq.HasType.defC (hσ.defC _ _ _ hd)
      simpa [CapEq.subst, CaptureSet.rename, CapAtom.rename] using this
  | @CapEq.HasType.member _ _ a S D e Tel i C₁ C₂ ha he hAt =>
      have := CapEq.HasType.member (a := a.subst σ)
        (by simpa [Ty.rename] using Atom.HasType.subst hσ ha)
        (by simpa [Shape.rename] using he.subst hσ) (hAt.rename σ.root.lift)
      simpa [CapEq.subst, CaptureSet.substVar_rename, Atom.root_subst] using this

theorem CapStep.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {st : CapStep s1} {X Y : CaptureSet (s1,x)} (hσ : Subst.Typed Γ σ Γ')
    (h : CapStep.HasType Γ st X Y) :
    CapStep.HasType Γ' (st.subst σ) (X.rename σ.root.lift) (Y.rename σ.root.lift) := by
  match h with
  | .closed hf =>
      have := CapStep.HasType.closed (hf.subst hσ)
      simpa [CapStep.subst, CaptureSet.weaken_rename] using this
  | .incl hs => exact .incl (hs.rename σ.root.lift)

theorem SideC.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {q : SideC s1} {X Y : CaptureSet (s1,x)} (hσ : Subst.Typed Γ σ Γ')
    (h : SideC.HasType Γ q X Y) :
    SideC.HasType Γ' (q.subst σ) (X.rename σ.root.lift) (Y.rename σ.root.lift) := by
  match h with
  | .nil => exact .nil
  | .cons hst hq => exact .cons (hst.subst hσ) (hq.subst hσ)

theorem ShapeCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {e : ShapeCo s1} {S T : Shape s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ˢ e : S ≤ T) :
    Γ' ⊢ˢ (e.subst σ) : (S.rename σ.root) ≤ (T.rename σ.root) := by
  match h with
  | .refl => exact .refl
  | .trans he hf => exact .trans (he.subst hσ) (hf.subst hσ)
  | .top => exact .top
  | .bot => exact .bot
  | .eqToLe hφ => exact .eqToLe (hφ.subst hσ)
  | .pi he hf =>
      have hf' := LeCo.HasType.subst (hσ.lift _) hf
      simp only [Subst.lift_root, Binding.rename_opaque] at hf'
      exact .pi (LeCo.HasType.subst hσ he) hf'
  | .obj hm => exact .obj (hm.subst hσ)
  | .pair he hf =>
      have := ShapeCo.HasType.pair (he.subst hσ) (hf.subst hσ)
      simpa [ShapeCo.subst, Shape.rename, Telescope.append_rename] using this
  | .bound hAt =>
      exact .bound (by
        simpa [Proposition.rename, Shape.weaken_rename] using hAt.rename σ.root.lift)
  | .intoBnd he =>
      have := ShapeCo.HasType.intoBnd (he.subst hσ)
      simpa [ShapeCo.subst, Shape.rename, Telescope.rename, Proposition.rename,
        Shape.weaken_rename] using this
  | @ShapeCo.HasType.member _ _ a S C e Tel i S' T' ha he hAt =>
      have := ShapeCo.HasType.member (a := a.subst σ)
        (by simpa [Ty.rename] using Atom.HasType.subst hσ ha)
        (by simpa [Shape.rename] using he.subst hσ) (hAt.rename σ.root.lift)
      simpa [ShapeCo.subst, Shape.substVar_rename] using this
  | .boxed hd =>
      have := ShapeCo.HasType.boxed (LeCo.HasType.subst hσ hd)
      simpa [ShapeCo.subst, Shape.rename] using this

theorem LeCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {d : LeCo s1} {S T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ d : S ≤ T) :
    Γ' ⊢ (d.subst σ) : (S.rename σ.root) ≤ (T.rename σ.root) := by
  match h with
  | .capt he hf => exact .capt (he.subst hσ) (CapCo.HasType.subst hσ hf)

theorem EqCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {φ : EqCo s1} {S T : Shape s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ φ : S ≡ T) :
    Γ' ⊢ (φ.subst σ) : (S.rename σ.root) ≡ (T.rename σ.root) := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.subst hσ)
  | .trans hφ hψ => exact .trans (hφ.subst hσ) (hψ.subst hσ)
  | .def hd => exact .def (hσ.def_ _ _ _ hd)
  | @EqCo.HasType.member _ _ a S C e Tel i S' T' ha he hAt =>
      have := EqCo.HasType.member (a := a.subst σ)
        (by simpa [Ty.rename] using Atom.HasType.subst hσ ha)
        (by simpa [Shape.rename] using he.subst hσ) (hAt.rename σ.root.lift)
      simpa [EqCo.subst, Shape.substVar_rename] using this

theorem Has.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {hh : Has s1} {x : BVar s1 .var} {l : Label}
    (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ hh : x ∋ l) :
    Γ' ⊢ (hh.subst σ) : (σ.root.var x) ∋ l := by
  match h with
  | @Has.HasType.member _ _ a S C e Tel i l ha he hAt =>
      have := Has.HasType.member (a := a.subst σ)
        (by simpa [Ty.rename] using Atom.HasType.subst hσ ha)
        (by simpa [Shape.rename] using he.subst hσ) (hAt.rename σ.root.lift)
      simpa [Has.subst] using this
  | .field hf hm => exact .field (hσ.fields _ _ hf) hm

theorem Side.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {sd : Side s1} {X Y : Shape (s1,x)} (hσ : Subst.Typed Γ σ Γ') (h : Side.HasType Γ sd X Y) :
    Side.HasType Γ' (sd.subst σ) (X.rename σ.root.lift) (Y.rename σ.root.lift) := by
  match h with
  | .none => exact .none
  | .some he =>
      have := Side.HasType.some (he.subst hσ)
      simpa [Side.subst, Shape.weaken_rename] using this

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
      have := Morphism.HasType.bnd (hm.subst hσ)
        (by simpa [Shape.rename] using he.subst hσ)
      simpa [Morphism.subst, Telescope.rename, Proposition.rename,
        Shape.weaken_rename] using this
  | .leC hm hh hq hq' =>
      exact .leC (hm.subst hσ) (hh.rename σ.root) (hq.subst hσ) (hq'.subst hσ)
  | .eqC hm hAt =>
      exact .eqC (hm.subst hσ) (by simpa [Proposition.rename] using hAt.rename σ.root.lift)
  | .eqSymC hm hAt =>
      exact .eqSymC (hm.subst hσ) (by simpa [Proposition.rename] using hAt.rename σ.root.lift)

theorem Atom.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {a : Atom s1} {T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ₐ a : T) :
    Γ' ⊢ₐ (a.subst σ) : (T.rename σ.root) := by
  match h with
  | @Atom.HasType.var _ _ x => exact hσ.var x
  | .cast ha he => exact .cast (ha.subst hσ) (LeCo.HasType.subst hσ he)
  | @Atom.HasType.unfoldSelf _ _ a C Tel ha =>
      have := Atom.HasType.unfoldSelf (Tel := Tel.rename σ.root.lift) (a := a.subst σ)
        (C := C.rename σ.root) (by simpa [Ty.rename, Shape.rename] using ha.subst hσ)
      simpa [Atom.subst, Ty.rename, Shape.rename, Telescope.weaken_rename,
        Telescope.substVar_rename] using this
  | @Atom.HasType.foldSelf _ _ a C Tel ha =>
      have ha' := ha.subst hσ
      simp only [Ty.rename, Shape.rename, Telescope.weaken_rename,
        Telescope.substVar_rename] at ha'
      have := Atom.HasType.foldSelf (Tel := Tel.rename σ.root.lift) (a := a.subst σ)
        (C := C.rename σ.root) (by rw [Atom.root_subst]; exact ha')
      simpa [Atom.subst, Ty.rename, Shape.rename] using this
  | .both ha hb hr =>
      have := Atom.HasType.both (by simpa [Ty.rename, Shape.rename] using ha.subst hσ)
        (by simpa [Ty.rename, Shape.rename] using hb.subst hσ)
        (by simp [Atom.root_subst, hr])
      simpa [Atom.subst, Ty.rename, Shape.rename, Telescope.append_rename] using this
  | @Atom.HasType.recap _ _ a S C f C' ha hf =>
      have := Atom.HasType.recap (a := a.subst σ) (C' := C'.rename σ.root)
        (by simpa [Ty.rename] using ha.subst hσ)
        (by
          simpa [CaptureSet.rename, CapAtom.rename, Atom.root_subst] using
            CapCo.HasType.subst hσ hf)
      simpa [Atom.subst, Ty.rename] using this

end

/-! ## Terms, values, fields -/

mutual

theorem Tm.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {t : Tm s1} {T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ t : T) :
    Γ' ⊢ (t.subst σ) : (T.rename σ.root) := by
  match h with
  | .atom ha => exact .atom (ha.subst hσ)
  | .val hv => exact .val (hv.subst hσ)
  | @Tm.HasType.app _ _ a C T U b ha hb =>
      have := Tm.HasType.app (b := b.subst σ)
        (by simpa [Ty.rename, Shape.rename] using ha.subst hσ) (hb.subst hσ)
      simpa [Tm.subst, Ty.substVar_rename] using this
  | @Tm.HasType.proj _ _ a T hh l ha hhh =>
      have := Tm.HasType.proj (a := a.subst σ) (ha.subst hσ)
        (by rw [Atom.root_subst]; exact hhh.subst hσ)
      simpa [Tm.subst, Ty.rename, Shape.rename, CaptureSet.rename, CapAtom.rename,
        Atom.root_subst] using this
  | .let ht hu hf =>
      refine .let (ht.subst hσ) ?_ ?_
      · have := hu.subst (hσ.lift _)
        simpa [Ty.weaken_rename] using this
      · have := CapCo.HasType.subst (hσ.lift _) hf
        simpa only [Tm.uses_subst, Subst.lift_root, CaptureSet.weaken_rename] using this
  | .cast ht he => exact .cast (ht.subst hσ) (LeCo.HasType.subst hσ he)
  | .unbox ha hf =>
      have := Tm.HasType.unbox (by simpa [Ty.rename, Shape.rename] using ha.subst hσ)
        (by simpa using CapCo.HasType.subst hσ hf)
      simpa [Tm.subst, Ty.rename] using this

theorem Value.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {v : Value s1} {T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ᵥ v : T) :
    Γ' ⊢ᵥ (v.subst σ) : (T.rename σ.root) := by
  match h with
  | .lam ht hg =>
      have ht' := ht.subst (hσ.lift _)
      have hg' := CapCo.HasType.subst (hσ.lift _) hg
      simp only [Subst.lift_root, Binding.rename_opaque] at ht' hg'
      have := Value.HasType.lam ht'
        (by
          simpa only [Tm.uses_subst, Subst.lift_root,
            CaptureSet.closing_rename] using hg')
      simpa [Value.subst, Ty.rename, Shape.rename] using this
  | @Value.HasType.obj _ A0 F0 _ W0 Wc0 hF =>
      have hF' := Fields.HasType.subst (hσ.lift _) hF
      have := Value.HasType.obj (Γ := Γ') (A := A0.rename σ.root)
        (W := W0.rename σ.root.lift)
        (Wc := Wc0.rename σ.root.lift) (F := F0.subst σ.lift)
        (by
          simpa [Binding.rename, Ty.rename, Shape.rename,
            Telescope.ofLiteral_rename] using hF')
      simpa [Value.subst, Ty.rename, Shape.rename, Telescope.ofLiteral_rename] using this
  | .box ha =>
      have := Value.HasType.box (ha.subst hσ)
      simpa [Value.subst, Ty.rename, Shape.rename, CaptureSet.rename] using this
  | .cast hv he => exact .cast (hv.subst hσ) (LeCo.HasType.subst hσ he)

theorem Fields.HasType.subst {s1 s2 : Sig} {Γ : Ctx (s1,x)} {Γ' : Ctx (s2,x)}
    {σ : Subst s1 s2} {F : Fields (s1,x)} {A : CaptureSet s1}
    (hσ : Subst.Typed Γ σ.lift Γ') (h : Γ ⊢ᶠ[A] F) :
    Γ' ⊢ᶠ[A.rename σ.root] (F.subst σ.lift) := by
  match h with
  | .nil => exact .nil
  | .cons hF ht hg =>
      refine .cons (hF.subst hσ) ?_ ?_
      · have := ht.subst hσ
        simpa [Ty.rename, Shape.rename, CaptureSet.rename, CapAtom.rename] using this
      · have := CapCo.HasType.subst hσ hg
        simpa only [Tm.uses_subst, Subst.lift_root,
          CaptureSet.closing_rename] using this

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

/-- Capture evidence under the instantiation of the innermost opaque binder. -/
theorem CapCo.HasType.substAtom {Γ : Ctx s} {T : Ty s} {f : CapCo (s,x)}
    {C D : CaptureSet (s,x)} {a : Atom s}
    (hf : (Γ.cons (.opaque T)) ⊢ᶜ f : C ⊑ D) (ha : Γ ⊢ₐ a : T) :
    Γ ⊢ᶜ f.subst (Subst.single a) : C⟦a.root⟧ ⊑ D⟦a.root⟧ := by
  have := hf.subst (Subst.Typed.single ha)
  simpa [CaptureSet.substVar] using this

/-- The avoidance evidence of a let body, instantiated at the atom the body is
substituted with.  This is the form `Preservation.lean` needs at the `rename`
step: the declared use set `U'` does not mention the bound variable, so it is
unchanged, and the body's use set is instantiated at the atom's root. -/
theorem CapCo.HasType.letBody_substAtom {Γ : Ctx s} {T : Ty s} {u : Tm (s,x)}
    {U' : CaptureSet s} {f : CapCo (s,x)} {a : Atom s}
    (hf : (Γ.cons (.opaque T)) ⊢ᶜ f : u.uses ⊑ U'↑) (ha : Γ ⊢ₐ a : T) :
    Γ ⊢ᶜ f.subst (Subst.single a) : (u.substAtom a).uses ⊑ U' := by
  have := hf.substAtom ha
  simpa only [Tm.uses_substAtom, CaptureSet.rename_subst_weaken] using this

end FCdot

end Captures
