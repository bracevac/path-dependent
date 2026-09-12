import Coercions.Classifiers.FCdot.TypingRename

namespace Classifiers

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

/-- Weakening then instantiating, for a capture atom.  The type sort has this
for every other syntactic class already. -/
@[simp] theorem CapAtom.rename_subst_weaken {s : Sig} {k : Kind}
    (a : CapAtom s) (y : BVar s k) :
    (a.weaken (k := k)).rename (Rename.subst y) = a := by
  simp [CapAtom.weaken, CapAtom.rename_comp, Rename.succ_subst]

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

/-! ## Substitution twins of the renaming lemmas

`Subst.cvar` returns a capture *atom*, so a substitution is no longer a
renaming and the type sort no longer travels along `σ.root`.  Every lemma of
`RenameLemmas.lean` that the transport of a derivation uses therefore gets a
twin here, stated at `X.subst σ` where the old one read `X.subst σ`.
Two facts make the twins short.  A type or a capture set reads a term
variable only through its root, which is `Subst.core` below, and the two
fusions of `TypingRename.lean` turn a weakening or an instantiation into one
substitution. -/

/-- Substitution on a binding. -/
def Binding.subst : Binding s1 → Subst s1 s2 → Binding s2
  | .opaque T, σ => .opaque (T.subst σ)
  | .transparent T W Wc Fs, σ =>
      .transparent (T.subst σ) (W.subst σ.lift) (Wc.subst σ.lift) Fs

@[simp] theorem Binding.subst_opaque (T : Ty s1) (σ : Subst s1 s2) :
    (Binding.opaque T).subst σ = .opaque (T.subst σ) := rfl

@[simp] theorem Binding.subst_transparent (T : Ty s1) (W : Witnesses (s1,x))
    (Wc : CapWitnesses (s1,x)) (Fs : List Label) (σ : Subst s1 s2) :
    (Binding.transparent T W Wc Fs).subst σ
      = .transparent (T.subst σ) (W.subst σ.lift) (Wc.subst σ.lift) Fs := rfl

@[simp] theorem Binding.ty_subst (b : Binding s1) (σ : Subst s1 s2) :
    (b.subst σ).ty = b.ty.subst σ := by
  cases b <;> rfl

/-! ### The type sort reads a term variable only through its root -/

/-- The part of a substitution the type sort sees: the root map and the
capture map. -/
def Subst.core (σ : Subst s1 s2) : Subst s1 s2 where
  var := fun x => .var (σ.rootVar x)
  cvar := σ.cvar

@[simp] theorem Subst.core_cvar (σ : Subst s1 s2) (κ : BVar s1 .cap) :
    σ.core.cvar κ = σ.cvar κ := rfl

@[simp] theorem Subst.core_rootVar (σ : Subst s1 s2) (x : BVar s1 .var) :
    σ.core.rootVar x = σ.rootVar x := rfl

theorem Subst.lift_core (σ : Subst s1 s2) : σ.lift.core = σ.core.lift := by
  apply Subst.funext'
  · intro x
    cases x with
    | here => rfl
    | there x =>
        simp [Subst.lift, Subst.core, Subst.rootVar, Atom.weaken, Atom.rename,
          Atom.root_rename]
  · intro κ; cases κ with | there κ => rfl

theorem Subst.liftC_core (σ : Subst s1 s2) : σ.liftC.core = σ.core.liftC := by
  apply Subst.funext'
  · intro x
    cases x with
    | there x =>
        simp [Subst.liftC, Subst.core, Subst.rootVar, Atom.weaken, Atom.rename,
          Atom.root_rename]
  · intro κ; cases κ with | here => rfl | there κ => rfl

theorem CapAtom.subst_core (a : CapAtom s1) (σ : Subst s1 s2) :
    a.subst σ = a.subst σ.core := by
  induction a with
  | proj a φ ih => simp [CapAtom.subst, ih]
  | var x | cvar κ | name x ℓ | top => rfl

theorem CaptureSet.subst_core (C : CaptureSet s1) (σ : Subst s1 s2) :
    C.subst σ = C.subst σ.core := by
  simp only [CaptureSet.subst]
  exact List.map_congr_left (fun a _ => CapAtom.subst_core a σ)

mutual

theorem Shape.subst_core (S : Shape s1) (σ : Subst s1 s2) : S.subst σ = S.subst σ.core := by
  match S with
  | .bot => rfl
  | .sel x ℓ => rfl
  | .pi S T =>
      show Shape.pi (S.subst σ.liftC) (T.subst σ.liftC.lift) = _
      rw [Ty.subst_core S σ.liftC, ETy.subst_core T σ.liftC.lift, Subst.liftC_core,
        Subst.lift_core, Subst.liftC_core]
      rfl
  | .obj Tel =>
      show Shape.obj (Tel.subst σ.lift) = _
      rw [Telescope.subst_core Tel σ.lift, Subst.lift_core]
      rfl
  | .box T =>
      show Shape.box (T.subst σ) = _
      rw [Ty.subst_core T σ]
      rfl

theorem Ty.subst_core (T : Ty s1) (σ : Subst s1 s2) : T.subst σ = T.subst σ.core := by
  match T with
  | .capt C S =>
      show Ty.capt (C.subst σ) (S.subst σ) = _
      rw [CaptureSet.subst_core C σ, Shape.subst_core S σ]
      rfl

theorem ETy.subst_core (E : ETy s1) (σ : Subst s1 s2) : E.subst σ = E.subst σ.core := by
  match E with
  | .ty T =>
      show ETy.ty (T.subst σ) = _
      rw [Ty.subst_core T σ]
      rfl
  | .ex C T =>
      show ETy.ex (C.subst σ) (T.subst σ.liftC) = _
      rw [CaptureSet.subst_core C σ, Ty.subst_core T σ.liftC, Subst.liftC_core]
      rfl

theorem Proposition.subst_core (P : Proposition s1) (σ : Subst s1 s2) :
    P.subst σ = P.subst σ.core := by
  match P with
  | .le S T =>
      show Proposition.le (S.subst σ) (T.subst σ) = _
      rw [Shape.subst_core S σ, Shape.subst_core T σ]
      rfl
  | .eq S T =>
      show Proposition.eq (S.subst σ) (T.subst σ) = _
      rw [Shape.subst_core S σ, Shape.subst_core T σ]
      rfl
  | .has ℓ => rfl
  | .bnd T =>
      show Proposition.bnd (T.subst σ) = _
      rw [Shape.subst_core T σ]
      rfl
  | .leC C D =>
      show Proposition.leC (C.subst σ) (D.subst σ) = _
      rw [CaptureSet.subst_core C σ, CaptureSet.subst_core D σ]
      rfl
  | .eqC C D =>
      show Proposition.eqC (C.subst σ) (D.subst σ) = _
      rw [CaptureSet.subst_core C σ, CaptureSet.subst_core D σ]
      rfl
  | .kindC C φ =>
      show Proposition.kindC (C.subst σ) φ = _
      rw [CaptureSet.subst_core C σ]
      rfl

theorem Telescope.subst_core (Tel : Telescope s1) (σ : Subst s1 s2) :
    Tel.subst σ = Tel.subst σ.core := by
  match Tel with
  | .nil => rfl
  | .cons Tel P =>
      show Telescope.cons (Tel.subst σ) (P.subst σ) = _
      rw [Telescope.subst_core Tel σ, Proposition.subst_core P σ]
      rfl

end

theorem Witnesses.subst_core : ∀ (W : Witnesses s1) (σ : Subst s1 s2),
    W.subst σ = W.subst σ.core
  | .nil, _ => rfl
  | .cons W ℓ T, σ => by
      show Witnesses.cons (W.subst σ) ℓ (T.subst σ) = _
      rw [Witnesses.subst_core W σ, Shape.subst_core T σ]
      rfl

theorem CapWitnesses.subst_core : ∀ (W : CapWitnesses s1) (σ : Subst s1 s2),
    W.subst σ = W.subst σ.core
  | .nil, _ => rfl
  | .cons W ℓ C, σ => by
      show CapWitnesses.cons (W.subst σ) ℓ (C.subst σ) = _
      rw [CapWitnesses.subst_core W σ, CaptureSet.subst_core C σ]
      rfl

/-! ### Weakening against lifting -/

theorem Subst.compRename_succ_lift (σ : Subst s1 s2) :
    Subst.compRename (Rename.succ (k := .var)) σ.lift = σ.compRen (Rename.succ (k := .var)) := by
  apply Subst.funext'
  · intro x; rfl
  · intro κ; rfl

theorem Subst.compRename_succ_liftC (σ : Subst s1 s2) :
    Subst.compRename (Rename.succ (k := .cap)) σ.liftC = σ.compRen (Rename.succ (k := .cap)) := by
  apply Subst.funext'
  · intro x; rfl
  · intro κ; rfl

theorem CaptureSet.weaken_subst (C : CaptureSet s1) (σ : Subst s1 s2) :
    (C.weaken (k := .var)).subst σ.lift = (C.subst σ).weaken (k := .var) := by
  show (C.rename Rename.succ).subst σ.lift = (C.subst σ).rename Rename.succ
  rw [CaptureSet.rename_subst, CaptureSet.subst_rename, Subst.compRename_succ_lift]

theorem CaptureSet.weaken_substC (C : CaptureSet s1) (σ : Subst s1 s2) :
    (C.weaken (k := .cap)).subst σ.liftC = (C.subst σ).weaken (k := .cap) := by
  show (C.rename Rename.succ).subst σ.liftC = (C.subst σ).rename Rename.succ
  rw [CaptureSet.rename_subst, CaptureSet.subst_rename, Subst.compRename_succ_liftC]

theorem Shape.weaken_subst (S : Shape s1) (σ : Subst s1 s2) :
    (S.weaken (k := .var)).subst σ.lift = (S.subst σ).weaken (k := .var) := by
  show (S.rename Rename.succ).subst σ.lift = (S.subst σ).rename Rename.succ
  rw [Shape.rename_subst, Shape.subst_rename, Subst.compRename_succ_lift]

theorem Shape.weaken_substC (S : Shape s1) (σ : Subst s1 s2) :
    (S.weaken (k := .cap)).subst σ.liftC = (S.subst σ).weaken (k := .cap) := by
  show (S.rename Rename.succ).subst σ.liftC = (S.subst σ).rename Rename.succ
  rw [Shape.rename_subst, Shape.subst_rename, Subst.compRename_succ_liftC]

theorem Ty.weaken_subst (T : Ty s1) (σ : Subst s1 s2) :
    (T.weaken (k := .var)).subst σ.lift = (T.subst σ).weaken (k := .var) := by
  show (T.rename Rename.succ).subst σ.lift = (T.subst σ).rename Rename.succ
  rw [Ty.rename_subst, Ty.subst_rename, Subst.compRename_succ_lift]

theorem Ty.weaken_substC (T : Ty s1) (σ : Subst s1 s2) :
    (T.weaken (k := .cap)).subst σ.liftC = (T.subst σ).weaken (k := .cap) := by
  show (T.rename Rename.succ).subst σ.liftC = (T.subst σ).rename Rename.succ
  rw [Ty.rename_subst, Ty.subst_rename, Subst.compRename_succ_liftC]

theorem Telescope.weaken_subst (Tel : Telescope s1) (σ : Subst s1 s2) :
    (Tel.weaken (k := .var)).subst σ.lift = (Tel.subst σ).weaken (k := .var) := by
  show (Tel.rename Rename.succ).subst σ.lift = (Tel.subst σ).rename Rename.succ
  rw [Telescope.rename_subst, Telescope.subst_rename, Subst.compRename_succ_lift]

theorem Telescope.weaken_substC (Tel : Telescope s1) (σ : Subst s1 s2) :
    (Tel.weaken (k := .cap)).subst σ.liftC = (Tel.subst σ).weaken (k := .cap) := by
  show (Tel.rename Rename.succ).subst σ.liftC = (Tel.subst σ).rename Rename.succ
  rw [Telescope.rename_subst, Telescope.subst_rename, Subst.compRename_succ_liftC]

theorem ETy.weaken_subst (E : ETy s1) (σ : Subst s1 s2) :
    (E.weaken (k := .var)).subst σ.lift = (E.subst σ)↑ := by
  show (E.rename Rename.succ).subst σ.lift = (E.subst σ).rename Rename.succ
  rw [ETy.rename_subst, ETy.subst_rename, Subst.compRename_succ_lift]

theorem ETy.weaken_substC (E : ETy s1) (σ : Subst s1 s2) :
    (E.weaken (k := .cap)).subst σ.liftC = (E.subst σ)↑ := by
  show (E.rename Rename.succ).subst σ.liftC = (E.subst σ).rename Rename.succ
  rw [ETy.rename_subst, ETy.subst_rename, Subst.compRename_succ_liftC]

/-- The closing set of a lambda body or of a field under a substitution. -/
theorem CaptureSet.closing_subst (A : CaptureSet s1) (σ : Subst s1 s2) :
    (A.weaken (k := .var) ∪ [CapAtom.var (BVar.here : BVar (s1,x) .var)]).subst σ.lift
      = ((A.subst σ).weaken (k := .var) ∪ [CapAtom.var BVar.here]) := by
  rw [CaptureSet.subst_union, CaptureSet.weaken_subst]
  rfl

/-! ### Instantiating a variable -/

theorem CaptureSet.substVar_subst (C : CaptureSet (s1,x)) (y : BVar s1 .var)
    (σ : Subst s1 s2) : (C⟦y⟧).subst σ = (C.subst σ.lift)⟦σ.rootVar y⟧ := by
  show (C.rename (Rename.subst y)).subst σ = (C.subst σ.lift).rename (Rename.subst (σ.rootVar y))
  rw [CaptureSet.rename_subst, CaptureSet.subst_rename,
    CaptureSet.subst_core _ (Subst.compRename (Rename.subst y) σ),
    CaptureSet.subst_core _ (σ.lift.compRen (Rename.subst (σ.rootVar y)))]
  congr 1
  apply Subst.funext'
  · intro x
    cases x with
    | here => rfl
    | there x =>
        simp [Subst.core, Subst.rootVar, Subst.compRename, Subst.compRen, Subst.lift,
          Atom.weaken, Atom.rename_comp, Rename.succ_subst]
  · intro κ
    cases κ with
    | there κ =>
        simp [Subst.core, Subst.compRename, Subst.compRen, Subst.lift,
          CapAtom.rename_comp, Rename.succ_subst]

theorem Shape.substVar_subst (S : Shape (s1,x)) (y : BVar s1 .var)
    (σ : Subst s1 s2) : (S⟦y⟧).subst σ = (S.subst σ.lift)⟦σ.rootVar y⟧ := by
  show (S.rename (Rename.subst y)).subst σ = (S.subst σ.lift).rename (Rename.subst (σ.rootVar y))
  rw [Shape.rename_subst, Shape.subst_rename,
    Shape.subst_core _ (Subst.compRename (Rename.subst y) σ),
    Shape.subst_core _ (σ.lift.compRen (Rename.subst (σ.rootVar y)))]
  congr 1
  apply Subst.funext'
  · intro x
    cases x with
    | here => rfl
    | there x =>
        simp [Subst.core, Subst.rootVar, Subst.compRename, Subst.compRen, Subst.lift,
          Atom.weaken, Atom.rename_comp, Rename.succ_subst]
  · intro κ
    cases κ with
    | there κ =>
        simp [Subst.core, Subst.compRename, Subst.compRen, Subst.lift,
          CapAtom.rename_comp, Rename.succ_subst]

theorem Ty.substVar_subst (T : Ty (s1,x)) (y : BVar s1 .var)
    (σ : Subst s1 s2) : (T⟦y⟧).subst σ = (T.subst σ.lift)⟦σ.rootVar y⟧ := by
  show (T.rename (Rename.subst y)).subst σ = (T.subst σ.lift).rename (Rename.subst (σ.rootVar y))
  rw [Ty.rename_subst, Ty.subst_rename,
    Ty.subst_core _ (Subst.compRename (Rename.subst y) σ),
    Ty.subst_core _ (σ.lift.compRen (Rename.subst (σ.rootVar y)))]
  congr 1
  apply Subst.funext'
  · intro x
    cases x with
    | here => rfl
    | there x =>
        simp [Subst.core, Subst.rootVar, Subst.compRename, Subst.compRen, Subst.lift,
          Atom.weaken, Atom.rename_comp, Rename.succ_subst]
  · intro κ
    cases κ with
    | there κ =>
        simp [Subst.core, Subst.compRename, Subst.compRen, Subst.lift,
          CapAtom.rename_comp, Rename.succ_subst]

theorem Telescope.substVar_subst (Tel : Telescope (s1,x)) (y : BVar s1 .var)
    (σ : Subst s1 s2) : (Tel⟦y⟧).subst σ = (Tel.subst σ.lift)⟦σ.rootVar y⟧ := by
  show (Tel.rename (Rename.subst y)).subst σ
    = (Tel.subst σ.lift).rename (Rename.subst (σ.rootVar y))
  rw [Telescope.rename_subst, Telescope.subst_rename,
    Telescope.subst_core _ (Subst.compRename (Rename.subst y) σ),
    Telescope.subst_core _ (σ.lift.compRen (Rename.subst (σ.rootVar y)))]
  congr 1
  apply Subst.funext'
  · intro x
    cases x with
    | here => rfl
    | there x =>
        simp [Subst.core, Subst.rootVar, Subst.compRename, Subst.compRen, Subst.lift,
          Atom.weaken, Atom.rename_comp, Rename.succ_subst]
  · intro κ
    cases κ with
    | there κ =>
        simp [Subst.core, Subst.compRename, Subst.compRen, Subst.lift,
          CapAtom.rename_comp, Rename.succ_subst]

/-! ### Structure that travels unchanged -/

theorem CaptureSet.Subset.subst {C D : CaptureSet s1} (h : C.Subset D) (σ : Subst s1 s2) :
    (C.subst σ).Subset (D.subst σ) := by
  intro a ha
  simp only [CaptureSet.subst, List.mem_map] at ha ⊢
  obtain ⟨b, hb, hab⟩ := ha
  exact ⟨b, h b hb, hab⟩

@[simp] theorem Telescope.length_subst :
    ∀ (Tel : Telescope s1) (σ : Subst s1 s2), (Tel.subst σ).length = Tel.length
  | .nil, _ => rfl
  | .cons Tel P, σ => by
      show (Tel.subst σ).length + 1 = Tel.length + 1
      rw [Telescope.length_subst Tel σ]

theorem Telescope.At.subst {Tel : Telescope s1} {i : Nat} {P : Proposition s1}
    (h : Tel.At i P) (σ : Subst s1 s2) : (Tel.subst σ).At i (P.subst σ) := by
  induction h with
  | @here Tel P =>
      rw [← Telescope.length_subst Tel σ]
      exact Telescope.At.here
  | there _ ih => exact Telescope.At.there ih

theorem Telescope.HoleAtC.subst {src : Telescope (s1,x)} {h : HoleC}
    {C₁ C₂ : CaptureSet (s1,x)} (hh : src.HoleAtC h C₁ C₂) (σ : Subst s1 s2) :
    (src.subst σ.lift).HoleAtC h (C₁.subst σ.lift) (C₂.subst σ.lift) := by
  cases hh with
  | leC hAt => exact .leC (by simpa [Proposition.subst] using hAt.subst σ.lift)
  | eqC hAt => exact .eqC (by simpa [Proposition.subst] using hAt.subst σ.lift)
  | eqSymC hAt => exact .eqSymC (by simpa [Proposition.subst] using hAt.subst σ.lift)

/-- Reading a kinding hole survives substitution. -/
theorem Telescope.HoleAtK.subst {src : Telescope (s1,x)} {j : Nat}
    {C : CaptureSet (s1,x)} {φ : Cls.Kind} (hh : src.HoleAtK j C φ) (σ : Subst s1 s2) :
    (src.subst σ.lift).HoleAtK j (C.subst σ.lift) φ := by
  cases hh with
  | kindC hAt => exact .kindC (by simpa [Proposition.subst] using hAt.subst σ.lift)

@[simp] theorem Telescope.append_subst :
    ∀ (Tel Tel' : Telescope s1) (σ : Subst s1 s2),
      (Tel ++ Tel').subst σ = Tel.subst σ ++ Tel'.subst σ
  | _, .nil, _ => rfl
  | Tel, .cons Tel' P, σ => by
      show Telescope.cons ((Tel ++ Tel').subst σ) (P.subst σ) = _
      rw [Telescope.append_subst Tel Tel' σ]
      rfl

theorem Witnesses.get_subst :
    ∀ (W : Witnesses s1) (l : Label) (σ : Subst s1 s2),
      (W.subst σ).get l = (W.get l).subst σ
  | .nil, _, _ => rfl
  | .cons W l' T, l, σ => by
      by_cases hl : l = l' <;>
        simp [Witnesses.subst, Witnesses.get, hl, Witnesses.get_subst W l σ]

theorem CapWitnesses.get_subst :
    ∀ (W : CapWitnesses s1) (l : Label) (σ : Subst s1 s2),
      (W.subst σ).get l = (W.get l).subst σ
  | .nil, _, _ => rfl
  | .cons W l' C, l, σ => by
      by_cases hl : l = l' <;>
        simp [CapWitnesses.subst, CapWitnesses.get, hl, CapWitnesses.get_subst W l σ]

theorem Witnesses.eqEntriesOf_subst (self : BVar s1 .var) (W₀ : Witnesses s1)
    (σ : Subst s1 s2) :
    ∀ W : Witnesses s1,
      (W₀.subst σ).eqEntriesOf (σ.rootVar self) (W.subst σ) = (W₀.eqEntriesOf self W).subst σ
  | .nil => rfl
  | .cons W ℓ T => by
      show Telescope.cons ((W₀.subst σ).eqEntriesOf (σ.rootVar self) (W.subst σ))
        (Proposition.eq (Shape.sel (σ.rootVar self) ℓ) ((W₀.subst σ).get ℓ)) = _
      rw [Witnesses.eqEntriesOf_subst self W₀ σ W, Witnesses.get_subst]
      rfl

@[simp] theorem Witnesses.eqEntries_subst (W : Witnesses (s1,x)) (σ : Subst s1 s2) :
    (W.subst σ.lift).eqEntries = W.eqEntries.subst σ.lift :=
  Witnesses.eqEntriesOf_subst .here W σ.lift W

@[simp] theorem Telescope.hasEntries_subst :
    ∀ (Tel : Telescope s1) (ls : List Label) (σ : Subst s1 s2),
      (Tel.hasEntries ls).subst σ = (Tel.subst σ).hasEntries ls
  | _, [], _ => rfl
  | Tel, l :: ls, σ => by
      show ((Tel.cons (.has l)).hasEntries ls).subst σ = _
      rw [Telescope.hasEntries_subst (Tel.cons (.has l)) ls σ]
      rfl

theorem CapWitnesses.eqEntriesOf_subst (self : BVar s1 .var) (W₀ : CapWitnesses s1)
    (σ : Subst s1 s2) (base : Telescope s1) :
    ∀ W : CapWitnesses s1,
      (W₀.subst σ).eqEntriesOf (σ.rootVar self) (base.subst σ) (W.subst σ)
        = (W₀.eqEntriesOf self base W).subst σ
  | .nil => rfl
  | .cons W ℓ C => by
      show Telescope.cons ((W₀.subst σ).eqEntriesOf (σ.rootVar self) (base.subst σ) (W.subst σ))
        (Proposition.eqC [CapAtom.name (σ.rootVar self) ℓ] ((W₀.subst σ).get ℓ)) = _
      rw [CapWitnesses.eqEntriesOf_subst self W₀ σ base W, CapWitnesses.get_subst]
      rfl

@[simp] theorem CapWitnesses.eqEntries_subst (W : CapWitnesses (s1,x))
    (base : Telescope (s1,x)) (σ : Subst s1 s2) :
    (W.subst σ.lift).eqEntries (base.subst σ.lift) = (W.eqEntries base).subst σ.lift :=
  CapWitnesses.eqEntriesOf_subst .here W σ.lift base W

theorem Telescope.ofLiteral_subst (W : Witnesses (s1,x)) (Wc : CapWitnesses (s1,x))
    (ls : List Label) (σ : Subst s1 s2) :
    (Telescope.ofLiteral W Wc ls).subst σ.lift
      = Telescope.ofLiteral (W.subst σ.lift) (Wc.subst σ.lift) ls := by
  simp [Telescope.ofLiteral]

/-! ### Capture bounds, weakenings that a substitution cancels, and the
scope readings under a substitution -/

/-- Substitution on a capture bound. -/
def CapBound.subst : CapBound s1 → Subst s1 s2 → CapBound s2
  | .root, _ => .root
  | .star, _ => .star
  | .upper C, σ => .upper (C.subst σ)
  | .inst C, σ => .inst (C.subst σ)
  | .cls c, _ => .cls c

@[simp] theorem CapBound.isRoot_subst (b : CapBound s1) (σ : Subst s1 s2) :
    (b.subst σ).isRoot = b.isRoot := by cases b <;> rfl

@[simp] theorem CapBound.opaque_subst (b : CapBound s1) (σ : Subst s1 s2) :
    (b.subst σ).opaque = b.opaque := by cases b <;> rfl

theorem CapAtom.weaken_subst (a : CapAtom s1) (σ : Subst s1 s2) :
    (a.weaken (k := .var)).subst σ.lift = (a.subst σ).weaken (k := .var) := by
  show (a.rename Rename.succ).subst σ.lift = (a.subst σ).rename Rename.succ
  rw [CapAtom.rename_subst, CapAtom.subst_rename, Subst.compRename_succ_lift]

theorem CapAtom.weaken_substC (a : CapAtom s1) (σ : Subst s1 s2) :
    (a.weaken (k := .cap)).subst σ.liftC = (a.subst σ).weaken (k := .cap) := by
  show (a.rename Rename.succ).subst σ.liftC = (a.subst σ).rename Rename.succ
  rw [CapAtom.rename_subst, CapAtom.subst_rename, Subst.compRename_succ_liftC]

theorem Witnesses.rename_subst : ∀ (W : Witnesses s1) (ρ : Rename s1 s2) (σ : Subst s2 s3),
    (W.rename ρ).subst σ = W.subst (Subst.compRename ρ σ)
  | .nil, _, _ => rfl
  | .cons W ℓ T, ρ, σ => by
      show Witnesses.cons ((W.rename ρ).subst σ) ℓ ((T.rename ρ).subst σ) = _
      rw [Witnesses.rename_subst W ρ σ, Shape.rename_subst]
      rfl

theorem Witnesses.subst_rename : ∀ (W : Witnesses s1) (σ : Subst s1 s2) (ρ : Rename s2 s3),
    (W.subst σ).rename ρ = W.subst (σ.compRen ρ)
  | .nil, _, _ => rfl
  | .cons W ℓ T, σ, ρ => by
      show Witnesses.cons ((W.subst σ).rename ρ) ℓ ((T.subst σ).rename ρ) = _
      rw [Witnesses.subst_rename W σ ρ, Shape.subst_rename]
      rfl

theorem CapWitnesses.rename_subst :
    ∀ (W : CapWitnesses s1) (ρ : Rename s1 s2) (σ : Subst s2 s3),
      (W.rename ρ).subst σ = W.subst (Subst.compRename ρ σ)
  | .nil, _, _ => rfl
  | .cons W ℓ C, ρ, σ => by
      show CapWitnesses.cons ((W.rename ρ).subst σ) ℓ ((C.rename ρ).subst σ) = _
      rw [CapWitnesses.rename_subst W ρ σ, CaptureSet.rename_subst]
      rfl

theorem CapWitnesses.subst_rename :
    ∀ (W : CapWitnesses s1) (σ : Subst s1 s2) (ρ : Rename s2 s3),
      (W.subst σ).rename ρ = W.subst (σ.compRen ρ)
  | .nil, _, _ => rfl
  | .cons W ℓ C, σ, ρ => by
      show CapWitnesses.cons ((W.subst σ).rename ρ) ℓ ((C.subst σ).rename ρ) = _
      rw [CapWitnesses.subst_rename W σ ρ, CaptureSet.subst_rename]
      rfl

/-! #### A weakening that an instantiation cancels -/

theorem Subst.compRename_succ_single (a : Atom s) :
    Subst.compRename Rename.succ (Subst.single a) = Subst.ofRename Rename.id := by
  apply Subst.funext' <;> intro y <;> cases y <;> rfl

theorem Subst.compRename_succ_singleC (a : CapAtom s) :
    Subst.compRename Rename.succ (Subst.singleC a) = Subst.ofRename Rename.id := by
  apply Subst.funext' <;> intro y <;> cases y <;> rfl

@[simp] theorem CapAtom.weaken_subst_single (a : CapAtom s) (b : Atom s) :
    (a.weaken (k := .var)).subst (Subst.single b) = a := by
  show (a.rename Rename.succ).subst (Subst.single b) = a
  rw [CapAtom.rename_subst, Subst.compRename_succ_single, CapAtom.subst_ofRename,
    CapAtom.rename_id]

@[simp] theorem CaptureSet.weaken_subst_single (C : CaptureSet s) (b : Atom s) :
    (C.weaken (k := .var)).subst (Subst.single b) = C := by
  show (C.rename Rename.succ).subst (Subst.single b) = C
  rw [CaptureSet.rename_subst, Subst.compRename_succ_single, CaptureSet.subst_ofRename,
    CaptureSet.rename_id]

@[simp] theorem Shape.weaken_subst_single (S : Shape s) (b : Atom s) :
    (S.weaken (k := .var)).subst (Subst.single b) = S := by
  show (S.rename Rename.succ).subst (Subst.single b) = S
  rw [Shape.rename_subst, Subst.compRename_succ_single, Shape.subst_ofRename,
    Shape.rename_id]

@[simp] theorem Ty.weaken_subst_single (T : Ty s) (b : Atom s) :
    (T.weaken (k := .var)).subst (Subst.single b) = T := by
  show (T.rename Rename.succ).subst (Subst.single b) = T
  rw [Ty.rename_subst, Subst.compRename_succ_single, Ty.subst_ofRename, Ty.rename_id]

@[simp] theorem Telescope.weaken_subst_single (Tel : Telescope s) (b : Atom s) :
    (Tel.weaken (k := .var)).subst (Subst.single b) = Tel := by
  show (Tel.rename Rename.succ).subst (Subst.single b) = Tel
  rw [Telescope.rename_subst, Subst.compRename_succ_single, Telescope.subst_ofRename,
    Telescope.rename_id]

@[simp] theorem CapAtom.weaken_subst_singleC (a : CapAtom s) (b : CapAtom s) :
    (a.weaken (k := .cap)).subst (Subst.singleC b) = a := by
  show (a.rename Rename.succ).subst (Subst.singleC b) = a
  rw [CapAtom.rename_subst, Subst.compRename_succ_singleC, CapAtom.subst_ofRename,
    CapAtom.rename_id]

@[simp] theorem CaptureSet.weaken_subst_singleC (C : CaptureSet s) (b : CapAtom s) :
    (C.weaken (k := .cap)).subst (Subst.singleC b) = C := by
  show (C.rename Rename.succ).subst (Subst.singleC b) = C
  rw [CaptureSet.rename_subst, Subst.compRename_succ_singleC, CaptureSet.subst_ofRename,
    CaptureSet.rename_id]

@[simp] theorem Shape.weaken_subst_singleC (S : Shape s) (b : CapAtom s) :
    (S.weaken (k := .cap)).subst (Subst.singleC b) = S := by
  show (S.rename Rename.succ).subst (Subst.singleC b) = S
  rw [Shape.rename_subst, Subst.compRename_succ_singleC, Shape.subst_ofRename,
    Shape.rename_id]

@[simp] theorem Ty.weaken_subst_singleC (T : Ty s) (b : CapAtom s) :
    (T.weaken (k := .cap)).subst (Subst.singleC b) = T := by
  show (T.rename Rename.succ).subst (Subst.singleC b) = T
  rw [Ty.rename_subst, Subst.compRename_succ_singleC, Ty.subst_ofRename, Ty.rename_id]

/-! #### The scope readings under a substitution -/

theorem Subst.compRename_succLift_liftC (σ : Subst s1 s2) :
    Subst.compRename (Rename.lift (k := .cap) (Rename.succ (k := .cap))) σ.liftC.liftC
      = σ.liftC.compRen (Rename.lift (k := .cap) (Rename.succ (k := .cap))) := by
  apply Subst.funext'
  · intro x
    cases x with
    | there x => simp [Subst.liftC, Subst.compRen, Atom.weaken, Atom.rename_comp,
        Rename.succ_lift]
  · intro κ
    cases κ with
    | here => rfl
    | there κ => simp [Subst.liftC, Subst.compRen, CapAtom.rename_comp, Rename.succ_lift]

theorem Dom.underRoot_subst (T : Dom s1) (σ : Subst s1 s2) :
    (Dom.underRoot T).subst σ.liftC.liftC = Dom.underRoot (T.subst σ.liftC) := by
  show (T.rename Rename.succ.lift).subst σ.liftC.liftC
    = (T.subst σ.liftC).rename Rename.succ.lift
  rw [Ty.rename_subst, Ty.subst_rename, Subst.compRename_succLift_liftC]

theorem Cod.underRoot_subst (E : Cod s1) (σ : Subst s1 s2) :
    (Cod.underRoot E).subst σ.liftC.liftC.lift = Cod.underRoot (E.subst σ.liftC.lift) := by
  show (E.rename Rename.succ.lift.lift).subst σ.liftC.liftC.lift
    = (E.subst σ.liftC.lift).rename Rename.succ.lift.lift
  rw [ETy.rename_subst, ETy.subst_rename, ← Subst.compRename_lift, ← Subst.compRen_lift,
    Subst.compRename_succLift_liftC]

theorem Witnesses.underRoot_subst (W : Witnesses (s1,x)) (σ : Subst s1 s2) :
    (W.rename (Rename.lift (k := .var) (Rename.succ (k := .cap)))).subst σ.liftC.lift
      = (W.subst σ.lift).rename (Rename.lift (k := .var) (Rename.succ (k := .cap))) := by
  rw [Witnesses.rename_subst, Witnesses.subst_rename, ← Subst.compRename_lift,
    ← Subst.compRen_lift, Subst.compRename_succ_liftC]

theorem CapWitnesses.underRoot_subst (W : CapWitnesses (s1,x)) (σ : Subst s1 s2) :
    (W.rename (Rename.lift (k := .var) (Rename.succ (k := .cap)))).subst σ.liftC.lift
      = (W.subst σ.lift).rename (Rename.lift (k := .var) (Rename.succ (k := .cap))) := by
  rw [CapWitnesses.rename_subst, CapWitnesses.subst_rename, ← Subst.compRename_lift,
    ← Subst.compRen_lift, Subst.compRename_succ_liftC]

/-- A context with no root binder puts every atom at the outermost level, so
every level comparison in it holds.  This is `Store.Typed.confined` of B0 read
as a fact about `Ctx.LvlLe`, and it is what makes the entering substitutions
of the stage typed. -/
theorem Ctx.lvlLe_of_root?_none {Γ : Ctx s} (h : Γ.root? = none) (e r : CapAtom s) :
    Γ.LvlLe e r := by
  have he : Γ.lvlAtom e = none := by
    induction e with
    | top => rfl
    | var x => exact Ctx.root?_none Γ x h
    | cvar κ => exact Ctx.root?_none Γ κ h
    | name x l => exact Ctx.root?_none Γ x h
    | proj a φ ih => exact ih
  unfold Ctx.LvlLe Ctx.lvlLeB
  rw [he]
  rfl

/-! ## The three capture facts under one more binder, for a substitution

The six lemmas of `TypingRename.lean` again, with `X.subst σ` where they read
`X.rename ρ`.  They are not instances of the renaming ones: a substitution is
not a renaming, and the only property of the map they use is that it commutes
with a weakening, which is `CapAtom.weaken_subst`. -/

/-- An atom of a term-extended signature is the new binder, a field name on
it, or an older atom weakened. -/
theorem CapAtom.cons_cases (e : CapAtom (s,x)) :
    e = .var .here ∨ (∃ l, e = .name .here l) ∨ (∃ e₀ : CapAtom s, e = e₀.weaken) ∨
      ∃ (e₀ : CapAtom (s,x)) (φ : Cls.Kind), e = e₀ ↾ φ := by
  cases e with
  | top => exact Or.inr (Or.inr (Or.inl ⟨.top, rfl⟩))
  | var x => cases x with
      | here => exact Or.inl rfl
      | there x0 => exact Or.inr (Or.inr (Or.inl ⟨.var x0, rfl⟩))
  | name x l => cases x with
      | here => exact Or.inr (Or.inl ⟨l, rfl⟩)
      | there x0 => exact Or.inr (Or.inr (Or.inl ⟨.name x0 l, rfl⟩))
  | cvar k => cases k with
      | there k0 => exact Or.inr (Or.inr (Or.inl ⟨.cvar k0, rfl⟩))
  | proj e₀ φ => exact Or.inr (Or.inr (Or.inr ⟨e₀, φ, rfl⟩))

/-- And of a capture-extended signature: the new binder, or an older atom
weakened. -/
theorem CapAtom.consC_cases (e : CapAtom (s,c)) :
    e = .cvar .here ∨ (∃ e₀ : CapAtom s, e = e₀.weaken) ∨
      ∃ (e₀ : CapAtom (s,c)) (φ : Cls.Kind), e = e₀ ↾ φ := by
  cases e with
  | top => exact Or.inr (Or.inl ⟨.top, rfl⟩)
  | var x => cases x with
      | there x0 => exact Or.inr (Or.inl ⟨.var x0, rfl⟩)
  | name x l => cases x with
      | there x0 => exact Or.inr (Or.inl ⟨.name x0 l, rfl⟩)
  | cvar k => cases k with
      | here => exact Or.inl rfl
      | there k0 => exact Or.inr (Or.inl ⟨.cvar k0, rfl⟩)
  | proj e₀ φ => exact Or.inr (Or.inr ⟨e₀, φ, rfl⟩)

/-- An atom that is its own base stays its own base under a weakening. -/
theorem CapAtom.base_of_weaken {s : Sig} {k : Kind} {a : CapAtom s}
    (h : (CapAtom.weaken (k := k) a).base = a.weaken) : a.base = a := by
  rw [CapAtom.weaken, CapAtom.base_rename] at h
  exact CapAtom.rename_inj _ _ _ Rename.succ_injective h

/-- A level fact under a substitution holds of every atom as soon as it holds
of the atoms that are their own base.  `Ctx.lvlAtom` reads through every
projection and `CapAtom.subst` is structural on one, so a projection compares
exactly as the atom under it does. -/
theorem Ctx.lvlLe_subst_of_base {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {σ : Subst s1 s2} {r : CapAtom s1} {r' : CapAtom s2}
    (h : ∀ e : CapAtom s1, e.base = e → Γ.LvlLe e r → Γ'.LvlLe (e.subst σ) r') :
    ∀ (e : CapAtom s1), Γ.LvlLe e r → Γ'.LvlLe (e.subst σ) r'
  | .top, hl => h .top rfl hl
  | .var x, hl => h (.var x) rfl hl
  | .cvar κ, hl => h (.cvar κ) rfl hl
  | .name x ℓ, hl => h (.name x ℓ) rfl hl
  | .proj e φ, hl => Ctx.lvlLe_subst_of_base h e hl

theorem Ctx.lvlLe_weaken_step_subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {σ : Subst s1 s2}
    (hLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.subst σ) (r.subst σ))
    {b : Binding s1} (b' : Binding s2) (e₀ r₀ : CapAtom s1) (hr₀ : Γ.IsRoot r₀)
    (he : (Γ.cons b).LvlLe (CapAtom.weaken (k := .var) e₀) (CapAtom.weaken (k := .var) r₀)) :
    (Γ'.cons b').LvlLe (CapAtom.weaken (k := .var) (e₀.subst σ))
      (CapAtom.weaken (k := .var) (r₀.subst σ)) := by
  rw [Ctx.lvlLe_weaken_iff] at he ⊢
  exact hLvl e₀ r₀ hr₀ he

theorem Ctx.lvlLe_here_step_subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {σ : Subst s1 s2}
    (hRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.subst σ))
    (hLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.subst σ) (r.subst σ))
    (hInner : Γ'.LvlLe Γ'.rootAtom (Γ.rootAtom.subst σ))
    (b : Binding s1) (b' : Binding s2) (r₀ : CapAtom s1) (hr₀ : Γ.IsRoot r₀)
    (he : (Γ.cons b).LvlLe (CapAtom.var .here) (CapAtom.weaken (k := .var) r₀)) :
    (Γ'.cons b').LvlLe (CapAtom.var .here)
      (CapAtom.weaken (k := .var) (r₀.subst σ)) := by
  have h1 : (Γ.cons b).LvlLe (CapAtom.weaken (k := .var) Γ.rootAtom)
      (CapAtom.weaken (k := .var) r₀) := by
    unfold Ctx.LvlLe
    rw [Ctx.lvlLeB_congr_left (Γ.cons b) (CapAtom.weaken (k := .var) Γ.rootAtom)
      (CapAtom.var .here) _ (Ctx.lvlAtom_cons_here_eq Γ b).symm]
    exact he
  rw [Ctx.lvlLe_weaken_iff] at h1
  have h3 : Γ'.LvlLe Γ'.rootAtom (r₀.subst σ) :=
    Ctx.LvlLe.trans (hRoot _ (Ctx.rootAtom_isRoot Γ)) hInner (hLvl _ _ hr₀ h1)
  have h4 : (Γ'.cons b').LvlLe (CapAtom.weaken (k := .var) Γ'.rootAtom)
      (CapAtom.weaken (k := .var) (r₀.subst σ)) :=
    (Ctx.lvlLe_weaken_iff _ _ _ _).mpr h3
  unfold Ctx.LvlLe
  rw [Ctx.lvlLeB_congr_left (Γ'.cons b') (CapAtom.var .here)
    (CapAtom.weaken (k := .var) Γ'.rootAtom) _ (Ctx.lvlAtom_cons_here_eq Γ' b')]
  exact h4

theorem Ctx.lvlLe_weakenC_step_subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {σ : Subst s1 s2}
    (hLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.subst σ) (r.subst σ))
    {b : CapBound s1} (b' : CapBound s2) (e₀ r₀ : CapAtom s1) (hr₀ : Γ.IsRoot r₀)
    (he : (Γ.consC b).LvlLe (CapAtom.weaken (k := .cap) e₀) (CapAtom.weaken (k := .cap) r₀)) :
    (Γ'.consC b').LvlLe (CapAtom.weaken (k := .cap) (e₀.subst σ))
      (CapAtom.weaken (k := .cap) (r₀.subst σ)) := by
  rw [Ctx.lvlLe_weakenC_iff] at he ⊢
  exact hLvl e₀ r₀ hr₀ he

theorem Ctx.lvlLe_hereC_step_subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {σ : Subst s1 s2}
    (hRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.subst σ))
    (hLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.subst σ) (r.subst σ))
    (hInner : Γ'.LvlLe Γ'.rootAtom (Γ.rootAtom.subst σ))
    (b : CapBound s1) (hb : b.isRoot = false) (b' : CapBound s2) (hb' : b'.isRoot = false)
    (r₀ : CapAtom s1) (hr₀ : Γ.IsRoot r₀)
    (he : (Γ.consC b).LvlLe (CapAtom.cvar .here) (CapAtom.weaken (k := .cap) r₀)) :
    (Γ'.consC b').LvlLe (CapAtom.cvar .here)
      (CapAtom.weaken (k := .cap) (r₀.subst σ)) := by
  have h1 : (Γ.consC b).LvlLe (CapAtom.weaken (k := .cap) Γ.rootAtom)
      (CapAtom.weaken (k := .cap) r₀) := by
    unfold Ctx.LvlLe
    rw [Ctx.lvlLeB_congr_left (Γ.consC b) (CapAtom.weaken (k := .cap) Γ.rootAtom)
      (CapAtom.cvar .here) _ (Ctx.lvlAtom_consC_here_eq Γ b hb).symm]
    exact he
  rw [Ctx.lvlLe_weakenC_iff] at h1
  have h3 : Γ'.LvlLe Γ'.rootAtom (r₀.subst σ) :=
    Ctx.LvlLe.trans (hRoot _ (Ctx.rootAtom_isRoot Γ)) hInner (hLvl _ _ hr₀ h1)
  have h4 : (Γ'.consC b').LvlLe (CapAtom.weaken (k := .cap) Γ'.rootAtom)
      (CapAtom.weaken (k := .cap) (r₀.subst σ)) :=
    (Ctx.lvlLe_weakenC_iff _ _ _ _).mpr h3
  unfold Ctx.LvlLe
  rw [Ctx.lvlLeB_congr_left (Γ'.consC b') (CapAtom.cvar .here)
    (CapAtom.weaken (k := .cap) Γ'.rootAtom) _ (Ctx.lvlAtom_consC_here_eq Γ' b' hb')]
  exact h4

/-! ### The six lemmas -/

theorem Ctx.isRoot_lift_subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    (hRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.subst σ))
    {b : Binding s1} (b' : Binding s2) (r : CapAtom (s1,x))
    (hr : (Γ.cons b).IsRoot r) :
    (Γ'.cons b').IsRoot (r.subst σ.lift) := by
  obtain ⟨r₀, rfl, hr₀⟩ := Ctx.isRoot_cons_cases hr
  unfold Ctx.IsRoot
  rw [CapAtom.weaken_subst, Ctx.isRootB_weaken]
  exact hRoot r₀ hr₀

theorem Ctx.lvlLe_lift_subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    (hRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.subst σ))
    (hLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.subst σ) (r.subst σ))
    (hInner : Γ'.LvlLe Γ'.rootAtom (Γ.rootAtom.subst σ))
    (b : Binding s1) (b' : Binding s2) (e r : CapAtom (s1,x))
    (hr : (Γ.cons b).IsRoot r) (hl : (Γ.cons b).LvlLe e r) :
    (Γ'.cons b').LvlLe (e.subst σ.lift) (r.subst σ.lift) := by
  obtain ⟨r₀, rfl, hr₀⟩ := Ctx.isRoot_cons_cases hr
  rw [CapAtom.weaken_subst]
  revert hl
  refine Ctx.lvlLe_subst_of_base ?_ e
  clear e
  intro e hbase hl
  rcases CapAtom.cons_cases e with rfl | ⟨l, rfl⟩ | ⟨e₀, rfl⟩ | ⟨e₀, φ, rfl⟩
  · exact Ctx.lvlLe_here_step_subst hRoot hLvl hInner b b' r₀ hr₀ hl
  · exact Ctx.lvlLe_here_step_subst hRoot hLvl hInner b b' r₀ hr₀ hl
  · rw [CapAtom.weaken_subst]
    exact Ctx.lvlLe_weaken_step_subst hLvl b' e₀ r₀ hr₀ hl
  · exact absurd hbase (CapAtom.base_ne_proj e₀ e₀ φ)

theorem Ctx.capInner_lift_subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    (hInner : Γ'.LvlLe Γ'.rootAtom (Γ.rootAtom.subst σ)) (b : Binding s1) (b' : Binding s2) :
    (Γ'.cons b').LvlLe (Γ'.cons b').rootAtom (((Γ.cons b).rootAtom).subst σ.lift) := by
  rw [Ctx.rootAtom_cons Γ b, CapAtom.weaken_subst, Ctx.rootAtom_cons Γ' b']
  exact (Ctx.lvlLe_weaken_iff _ _ _ _).mpr hInner

theorem Ctx.isRoot_liftC_subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    (hRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.subst σ))
    (b : CapBound s1) (b' : CapBound s2) (hbb : b'.isRoot = b.isRoot)
    (r : CapAtom (s1,c)) (hr : (Γ.consC b).IsRoot r) :
    (Γ'.consC b').IsRoot (r.subst σ.liftC) := by
  rcases Ctx.isRoot_consC_cases hr with rfl | ⟨r₀, rfl, hr₀⟩
  · have hb : b.isRoot = true := by
      simpa [Ctx.IsRoot, Ctx.isRootB, Ctx.lookupCap] using hr
    show (Γ'.consC b').IsRoot (CapAtom.cvar .here)
    simp [Ctx.IsRoot, Ctx.isRootB, Ctx.lookupCap, hbb, hb]
  · unfold Ctx.IsRoot
    rw [CapAtom.weaken_substC, Ctx.isRootB_weakenC]
    exact hRoot r₀ hr₀

theorem Ctx.lvlLe_liftC_subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    (hRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.subst σ))
    (hLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.subst σ) (r.subst σ))
    (hInner : Γ'.LvlLe Γ'.rootAtom (Γ.rootAtom.subst σ))
    (b : CapBound s1) (b' : CapBound s2) (hbb : b'.isRoot = b.isRoot)
    (e r : CapAtom (s1,c))
    (hr : (Γ.consC b).IsRoot r) (hl : (Γ.consC b).LvlLe e r) :
    (Γ'.consC b').LvlLe (e.subst σ.liftC) (r.subst σ.liftC) := by
  rcases Ctx.isRoot_consC_cases hr with rfl | ⟨r₀, rfl, hr₀⟩
  · exact Ctx.lvlLeB_depth_zero _ _ _ rfl
  · rw [CapAtom.weaken_substC]
    revert hl
    refine Ctx.lvlLe_subst_of_base ?_ e
    clear e
    intro e hbase hl
    rcases CapAtom.consC_cases e with rfl | ⟨e₀, rfl⟩ | ⟨e₀, φ, rfl⟩
    · cases hb : b.isRoot with
      | true => exact absurd hl (Ctx.not_lvlLe_consC_root_here hb r₀)
      | false =>
          exact Ctx.lvlLe_hereC_step_subst hRoot hLvl hInner b hb b' (by rw [hbb]; exact hb)
            r₀ hr₀ hl
    · rw [CapAtom.weaken_substC]
      exact Ctx.lvlLe_weakenC_step_subst hLvl b' e₀ r₀ hr₀ hl
    · exact absurd hbase (CapAtom.base_ne_proj e₀ e₀ φ)

theorem Ctx.capInner_liftC_subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    (hInner : Γ'.LvlLe Γ'.rootAtom (Γ.rootAtom.subst σ)) (b : CapBound s1) (b' : CapBound s2)
    (hbb : b'.isRoot = b.isRoot) :
    (Γ'.consC b').LvlLe (Γ'.consC b').rootAtom (((Γ.consC b).rootAtom).subst σ.liftC) := by
  cases hb : b.isRoot with
  | true =>
      have hb' : b = .root := by cases b <;> simp_all [CapBound.isRoot]
      have hb'' : b' = .root := by
        cases b' <;> simp_all [CapBound.isRoot]
      subst hb'
      subst hb''
      show (Γ'.consC (CapBound.root)).LvlLe (Γ'.consC (CapBound.root)).rootAtom
        (CapAtom.cvar .here)
      have hrt : (Γ'.consC (CapBound.root)).rootAtom = CapAtom.cvar .here := rfl
      rw [hrt]
      exact Ctx.LvlLe.refl_of_root rfl
  | false =>
      have hb' : b'.isRoot = false := by rw [hbb]; exact hb
      rw [Ctx.rootAtom_consC Γ b hb, CapAtom.weaken_substC,
        Ctx.rootAtom_consC Γ' b' hb']
      exact (Ctx.lvlLe_weakenC_iff _ _ _ _).mpr hInner

/-- The level case of a capture append at a root binder, for a substitution:
no `capInner` is needed. -/
theorem Ctx.lvlLe_liftC_root_subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    (hLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.subst σ) (r.subst σ))
    (e r : CapAtom (s1,c))
    (hr : (Γ.consC .root).IsRoot r) (hl : (Γ.consC .root).LvlLe e r) :
    (Γ'.consC .root).LvlLe (e.subst σ.liftC) (r.subst σ.liftC) := by
  rcases Ctx.isRoot_consC_cases hr with rfl | ⟨r₀, rfl, hr₀⟩
  · exact Ctx.lvlLeB_depth_zero _ _ _ rfl
  · rw [CapAtom.weaken_substC]
    revert hl
    refine Ctx.lvlLe_subst_of_base ?_ e
    clear e
    intro e hbase hl
    rcases CapAtom.consC_cases e with rfl | ⟨e₀, rfl⟩ | ⟨e₀, φ, rfl⟩
    · exact absurd hl (Ctx.not_lvlLe_consC_root_here rfl r₀)
    · rw [CapAtom.weaken_substC]
      exact Ctx.lvlLe_weakenC_step_subst hLvl .root e₀ r₀ hr₀ hl
    · exact absurd hbase (CapAtom.base_ne_proj e₀ e₀ φ)


/-! ### Two substitutions in a row, at the type sort

A substitution is not composable with another one at the term sort without
the fusion lemmas of the whole evidence block.  The type sort needs less: it
reads a term variable only through its root, so the composite it sees is
`Subst.compT`, whose term component is a variable again. -/

def Subst.compT (σ : Subst s1 s2) (τ : Subst s2 s3) : Subst s1 s3 where
  var := fun x => .var (τ.rootVar (σ.rootVar x))
  cvar := fun κ => (σ.cvar κ).subst τ

@[simp] theorem Subst.compT_rootVar (σ : Subst s1 s2) (τ : Subst s2 s3) (x : BVar s1 .var) :
    (σ.compT τ).rootVar x = τ.rootVar (σ.rootVar x) := rfl

@[simp] theorem Subst.compT_cvar (σ : Subst s1 s2) (τ : Subst s2 s3) (κ : BVar s1 .cap) :
    (σ.compT τ).cvar κ = (σ.cvar κ).subst τ := rfl

theorem Subst.compT_lift (σ : Subst s1 s2) (τ : Subst s2 s3) :
    (σ.compT τ).lift = σ.lift.compT τ.lift := by
  apply Subst.funext'
  · intro x
    cases x with
    | here => rfl
    | there x =>
        show Classifiers.FCdot.Atom.weaken (Atom.var (τ.rootVar (σ.rootVar x)))
          = Atom.var (τ.lift.rootVar (σ.lift.rootVar (.there x)))
        rw [Subst.lift_rootVar_there, Subst.lift_rootVar_there]
        rfl
  · intro κ
    cases κ with
    | there κ =>
        exact (CapAtom.weaken_subst (σ.cvar κ) τ).symm

theorem Subst.compT_liftC (σ : Subst s1 s2) (τ : Subst s2 s3) :
    (σ.compT τ).liftC = σ.liftC.compT τ.liftC := by
  apply Subst.funext'
  · intro x
    cases x with
    | there x =>
        show Classifiers.FCdot.Atom.weaken (Atom.var (τ.rootVar (σ.rootVar x)))
          = Atom.var (τ.liftC.rootVar (σ.liftC.rootVar (.there x)))
        rw [Subst.liftC_rootVar_there, Subst.liftC_rootVar_there]
        rfl
  · intro κ
    cases κ with
    | here => rfl
    | there κ =>
        exact (CapAtom.weaken_substC (σ.cvar κ) τ).symm

theorem CapAtom.subst_subst (a : CapAtom s1) (σ : Subst s1 s2) (τ : Subst s2 s3) :
    (a.subst σ).subst τ = a.subst (σ.compT τ) := by
  induction a with
  | proj a φ ih => simp [CapAtom.subst, ih]
  | var x | cvar κ | name x ℓ | top => rfl

theorem CaptureSet.subst_subst (C : CaptureSet s1) (σ : Subst s1 s2) (τ : Subst s2 s3) :
    (C.subst σ).subst τ = C.subst (σ.compT τ) := by
  simp only [CaptureSet.subst, List.map_map, Function.comp_def, CapAtom.subst_subst]

mutual

theorem Shape.subst_subst (S : Shape s1) (σ : Subst s1 s2) (τ : Subst s2 s3) :
    (S.subst σ).subst τ = S.subst (σ.compT τ) := by
  match S with
  | .bot => rfl
  | .sel x ℓ => rfl
  | .pi S T =>
      show Shape.pi ((S.subst σ.liftC).subst τ.liftC) ((T.subst σ.liftC.lift).subst τ.liftC.lift)
        = _
      rw [Ty.subst_subst S σ.liftC τ.liftC, ETy.subst_subst T σ.liftC.lift τ.liftC.lift,
        ← Subst.compT_liftC, ← Subst.compT_lift, ← Subst.compT_liftC]
      rfl
  | .obj Tel =>
      show Shape.obj ((Tel.subst σ.lift).subst τ.lift) = _
      rw [Telescope.subst_subst Tel σ.lift τ.lift, ← Subst.compT_lift]
      rfl
  | .box T =>
      show Shape.box ((T.subst σ).subst τ) = _
      rw [Ty.subst_subst T σ τ]
      rfl

theorem Ty.subst_subst (T : Ty s1) (σ : Subst s1 s2) (τ : Subst s2 s3) :
    (T.subst σ).subst τ = T.subst (σ.compT τ) := by
  match T with
  | .capt C S =>
      show Ty.capt ((C.subst σ).subst τ) ((S.subst σ).subst τ) = _
      rw [CaptureSet.subst_subst C σ τ, Shape.subst_subst S σ τ]
      rfl

theorem ETy.subst_subst (E : ETy s1) (σ : Subst s1 s2) (τ : Subst s2 s3) :
    (E.subst σ).subst τ = E.subst (σ.compT τ) := by
  match E with
  | .ty T =>
      show ETy.ty ((T.subst σ).subst τ) = _
      rw [Ty.subst_subst T σ τ]
      rfl
  | .ex C T =>
      show ETy.ex ((C.subst σ).subst τ) ((T.subst σ.liftC).subst τ.liftC) = _
      rw [CaptureSet.subst_subst C σ τ, Ty.subst_subst T σ.liftC τ.liftC,
        ← Subst.compT_liftC]
      rfl

theorem Proposition.subst_subst (P : Proposition s1) (σ : Subst s1 s2) (τ : Subst s2 s3) :
    (P.subst σ).subst τ = P.subst (σ.compT τ) := by
  match P with
  | .le S T =>
      show Proposition.le ((S.subst σ).subst τ) ((T.subst σ).subst τ) = _
      rw [Shape.subst_subst S σ τ, Shape.subst_subst T σ τ]
      rfl
  | .eq S T =>
      show Proposition.eq ((S.subst σ).subst τ) ((T.subst σ).subst τ) = _
      rw [Shape.subst_subst S σ τ, Shape.subst_subst T σ τ]
      rfl
  | .has ℓ => rfl
  | .bnd T =>
      show Proposition.bnd ((T.subst σ).subst τ) = _
      rw [Shape.subst_subst T σ τ]
      rfl
  | .leC C D =>
      show Proposition.leC ((C.subst σ).subst τ) ((D.subst σ).subst τ) = _
      rw [CaptureSet.subst_subst C σ τ, CaptureSet.subst_subst D σ τ]
      rfl
  | .eqC C D =>
      show Proposition.eqC ((C.subst σ).subst τ) ((D.subst σ).subst τ) = _
      rw [CaptureSet.subst_subst C σ τ, CaptureSet.subst_subst D σ τ]
      rfl
  | .kindC C φ =>
      show Proposition.kindC ((C.subst σ).subst τ) φ = _
      rw [CaptureSet.subst_subst C σ τ]
      rfl

theorem Telescope.subst_subst (Tel : Telescope s1) (σ : Subst s1 s2) (τ : Subst s2 s3) :
    (Tel.subst σ).subst τ = Tel.subst (σ.compT τ) := by
  match Tel with
  | .nil => rfl
  | .cons Tel P =>
      show Telescope.cons ((Tel.subst σ).subst τ) ((P.subst σ).subst τ) = _
      rw [Telescope.subst_subst Tel σ τ, Proposition.subst_subst P σ τ]
      rfl

end

/-- The domain premise of the application rule, under a substitution. -/
theorem Ty.singleC_subst (T : Ty (s1,c)) (a : CapAtom s1) (σ : Subst s1 s2) :
    (T.subst (Subst.singleC a)).subst σ
      = (T.subst σ.liftC).subst (Subst.singleC (a.subst σ)) := by
  rw [Ty.subst_subst, Ty.subst_subst]
  congr 1
  apply Subst.funext'
  · intro x
    cases x with
    | there x =>
        show Classifiers.FCdot.Atom.var (σ.rootVar x)
          = Atom.var ((Subst.singleC (a.subst σ)).rootVar (σ.liftC.rootVar (.there x)))
        rw [Subst.liftC_rootVar_there]
        rfl
  · intro κ
    cases κ with
    | here => rfl
    | there κ => exact (CapAtom.weaken_subst_singleC (σ.cvar κ) (a.subst σ)).symm

/-- What an application does to a codomain, under a substitution. -/
theorem Subst.compRename_succ_succ_arg (b : Atom s) :
    Subst.compRename ((Rename.succ (k := .cap)).comp (Rename.succ (k := .var)))
        (Subst.arg b) = Subst.ofRename Rename.id := by
  apply Subst.funext' <;> intro y <;> rfl

@[simp] theorem CapAtom.weaken_weaken_subst_arg (a : CapAtom s) (b : Atom s) :
    ((a.weaken (k := .cap)).weaken (k := .var)).subst (Subst.arg b) = a := by
  show ((a.rename Rename.succ).rename Rename.succ).subst (Subst.arg b) = a
  rw [CapAtom.rename_comp, CapAtom.rename_subst, Subst.compRename_succ_succ_arg,
    CapAtom.subst_ofRename, CapAtom.rename_id]

/-- What an application does to a codomain, under a substitution. -/
theorem Ty.arg_subst (U : Ty ((s1,c),x)) (b : Atom s1) (σ : Subst s1 s2) :
    (U.subst (Subst.arg b)).subst σ
      = (U.subst σ.liftC.lift).subst (Subst.arg (b.subst σ)) := by
  rw [Ty.subst_subst, Ty.subst_subst]
  congr 1
  apply Subst.funext'
  · intro x
    cases x with
    | here =>
        show Classifiers.FCdot.Atom.var (σ.rootVar b.root)
          = Atom.var ((Subst.arg (b.subst σ)).rootVar (σ.liftC.lift.rootVar BVar.here))
        rw [Subst.lift_rootVar_here]
        show Classifiers.FCdot.Atom.var (σ.rootVar b.root) = Atom.var (b.subst σ).root
        rw [Atom.root_subst]
    | there x =>
        cases x with
        | there x =>
            show Classifiers.FCdot.Atom.var (σ.rootVar x)
              = Atom.var ((Subst.arg (b.subst σ)).rootVar
                  (σ.liftC.lift.rootVar (.there (.there x))))
            rw [Subst.lift_rootVar_there, Subst.liftC_rootVar_there]
            rfl
  · intro κ
    cases κ with
    | there κ =>
        cases κ with
        | here =>
            show (CapAtom.var b.root).subst σ = CapAtom.var (b.subst σ).root
            rw [Atom.root_subst]
            rfl
        | there κ => exact (CapAtom.weaken_weaken_subst_arg (σ.cvar κ) (b.subst σ)).symm

/-- The same for an answer codomain. -/
theorem ETy.arg_subst (U : ETy ((s1,c),x)) (b : Atom s1) (σ : Subst s1 s2) :
    (U.subst (Subst.arg b)).subst σ
      = (U.subst σ.liftC.lift).subst (Subst.arg (b.subst σ)) := by
  rw [ETy.subst_subst, ETy.subst_subst]
  congr 1
  apply Subst.funext'
  · intro x
    cases x with
    | here =>
        show Classifiers.FCdot.Atom.var (σ.rootVar b.root)
          = Atom.var ((Subst.arg (b.subst σ)).rootVar (σ.liftC.lift.rootVar BVar.here))
        rw [Subst.lift_rootVar_here]
        show Classifiers.FCdot.Atom.var (σ.rootVar b.root) = Atom.var (b.subst σ).root
        rw [Atom.root_subst]
    | there x =>
        cases x with
        | there x =>
            show Classifiers.FCdot.Atom.var (σ.rootVar x)
              = Atom.var ((Subst.arg (b.subst σ)).rootVar
                  (σ.liftC.lift.rootVar (.there (.there x))))
            rw [Subst.lift_rootVar_there, Subst.liftC_rootVar_there]
            rfl
  · intro κ
    cases κ with
    | there κ =>
        cases κ with
        | here =>
            show (CapAtom.var b.root).subst σ = CapAtom.var (b.subst σ).root
            rw [Atom.root_subst]
            rfl
        | there κ => exact (CapAtom.weaken_weaken_subst_arg (σ.cvar κ) (b.subst σ)).symm

/-- Instantiating the innermost term binder is what `substVar` does, because
the type sort reads an atom only through its root. -/
theorem Subst.single_core (a : Atom s) :
    (Subst.single a).core = Subst.ofRename (Rename.subst a.root) := by
  apply Subst.funext' <;> intro y <;> cases y <;> rfl

@[simp] theorem CaptureSet.subst_single' (C : CaptureSet (s,x)) (a : Atom s) :
    C.subst (Subst.single a) = C⟦a.root⟧ := by
  rw [CaptureSet.subst_core, Subst.single_core, CaptureSet.subst_ofRename]
  rfl

@[simp] theorem Shape.subst_single (S : Shape (s,x)) (a : Atom s) :
    S.subst (Subst.single a) = S⟦a.root⟧ := by
  rw [Shape.subst_core, Subst.single_core, Shape.subst_ofRename]
  rfl

@[simp] theorem Ty.subst_single (T : Ty (s,x)) (a : Atom s) :
    T.subst (Subst.single a) = T⟦a.root⟧ := by
  rw [Ty.subst_core, Subst.single_core, Ty.subst_ofRename]
  rfl

@[simp] theorem Telescope.subst_single (Tel : Telescope (s,x)) (a : Atom s) :
    Tel.subst (Subst.single a) = Tel⟦a.root⟧ := by
  rw [Telescope.subst_core, Subst.single_core, Telescope.subst_ofRename]
  rfl


/-! ### Declared classifiers, set bounds, and projections under a substitution

The three readers the kinding family uses travel with a substitution the way
`Ctx.InstOf` does, flavour-wise on the atom.  The one new demand a
substitution makes is `capProjFree` below: a substitution replaces a capture
variable by a capability, never by a *filtered* capability.  Every
substitution the tree builds does that, and it is what lets the kind an atom
projects by and the base of an atom cross a substitution unchanged. -/

@[simp] theorem CapBound.clsOf?_subst (b : CapBound s1) (σ : Subst s1 s2) :
    (b.subst σ).clsOf? = b.clsOf? := by
  cases b <;> rfl

@[simp] theorem CapBound.setOf?_subst (b : CapBound s1) (σ : Subst s1 s2) :
    (b.subst σ).setOf? = (b.setOf?).map (fun C => C.subst σ) := by
  cases b <;> rfl

/-- An atom that is its own base carries no kind. -/
theorem CapAtom.kindOf_eq_top_of_base {a : CapAtom s} (h : a.base = a) :
    a.kindOf = Cls.Kind.top := by
  cases a with
  | top | var _ | cvar _ | name _ _ => rfl
  | proj a₀ φ => exact absurd h (CapAtom.base_ne_proj a₀ a₀ φ)

/-- Taking the base commutes with a projection-free substitution. -/
theorem CapAtom.base_subst {σ : Subst s1 s2} (hσ : ∀ κ, (σ.cvar κ).base = σ.cvar κ) :
    ∀ a : CapAtom s1, (a.subst σ).base = a.base.subst σ
  | .top => rfl
  | .var x => rfl
  | .name x ℓ => rfl
  | .cvar κ => hσ κ
  | .proj a φ => by
      show (a.subst σ).base = a.base.subst σ
      exact CapAtom.base_subst hσ a

/-- And so does the kind an atom projects by. -/
theorem CapAtom.kindOf_subst {σ : Subst s1 s2} (hσ : ∀ κ, (σ.cvar κ).base = σ.cvar κ) :
    ∀ a : CapAtom s1, (a.subst σ).kindOf = a.kindOf
  | .top => rfl
  | .var x => rfl
  | .name x ℓ => rfl
  | .cvar κ => CapAtom.kindOf_eq_top_of_base (hσ κ)
  | .proj a φ => by
      show φ.interB (a.subst σ).kindOf = φ.interB a.kindOf
      rw [CapAtom.kindOf_subst hσ a]

/-- The smart projection constructor commutes with a projection-free
substitution. -/
theorem CapAtom.projBy_subst {σ : Subst s1 s2} (hσ : ∀ κ, (σ.cvar κ).base = σ.cvar κ)
    (φ : Cls.Kind) : ∀ a : CapAtom s1, (a.projBy φ).subst σ = (a.subst σ).projBy φ
  | .top => rfl
  | .var x => rfl
  | .name x ℓ => rfl
  | .cvar κ => by
      show CapAtom.proj (σ.cvar κ) φ = (σ.cvar κ).projBy φ
      cases hc : σ.cvar κ with
      | top | var _ | cvar _ | name _ _ => rfl
      | proj a₀ ψ =>
          have := hσ κ
          rw [hc] at this
          exact absurd this (CapAtom.base_ne_proj a₀ a₀ ψ)
  | .proj a ψ => rfl

theorem CaptureSet.proj_subst {σ : Subst s1 s2} (hσ : ∀ κ, (σ.cvar κ).base = σ.cvar κ)
    (C : CaptureSet s1) (φ : Cls.Kind) : (C.proj φ).subst σ = (C.subst σ).proj φ := by
  simp only [CaptureSet.proj, CaptureSet.subst, List.map_map, Function.comp_def]
  exact List.map_congr_left (fun a _ => CapAtom.projBy_subst hσ φ a)

/-! ## Typed substitutions -/

/-- `Subst.Typed Γ σ Γ'`: every variable of `Γ` goes to an atom of the
transported type, and definitions and field labels survive along `σ.root`. -/
structure Subst.Typed {s1 s2 : Sig} (Γ : Ctx s1) (σ : Subst s1 s2) (Γ' : Ctx s2) : Prop where
  var : ∀ x, Γ' ⊢ₐ (σ.var x) : ((Γ.lookupTy x).subst σ)
  /-- On transparent binders the substitution behaves like a renaming. -/
  ty : ∀ x, Γ.IsTransparent x →
      Γ'.lookupTy (σ.rootVar x) = (Γ.lookupTy x).subst σ
  transparent : ∀ x, Γ.IsTransparent x → Γ'.IsTransparent (σ.rootVar x)
  def_ : ∀ x l (W : Shape s1), Γ.lookupDef x l = some W →
      Γ'.lookupDef (σ.rootVar x) l = some (W.subst σ)
  /-- Capture definitions of transparent binders survive too. -/
  defC : ∀ x l (C : CaptureSet s1), Γ.lookupDefC x l = some C →
      Γ'.lookupDefC (σ.rootVar x) l = some (C.subst σ)
  fields : ∀ x Fs, Γ.lookupFields x = some Fs → Γ'.lookupFields (σ.rootVar x) = some Fs
  /-- A root goes to a root.  At this stage `Subst.cvar` is still a variable
      map, so a capture atom travels along `σ.root`. -/
  capRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.subst σ)
  /-- A level fact survives. -/
  capLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r →
      Γ'.LvlLe (e.subst σ) (r.subst σ)
  /-- No root is introduced strictly inside the image of the innermost root. -/
  capInner : Γ'.LvlLe Γ'.rootAtom (Γ.rootAtom.subst σ)
  /-- The image of an instance binder is an instance binder of the
      substituted set.  It is what `CapEq.HasType.instC` needs, and it is
      stated flavour-wise on the atom, so that `CapEq.subst` stays
      structural. -/
  capInst : ∀ a C, Γ.InstOf a C → Γ'.InstOf (a.subst σ) (C.subst σ)
  /-- The image of a binder with a declared classifier is a binder with the
      same declared classifier.  `KindCo.HasType.kcls` reads it. -/
  capCls : ∀ a cl, Γ.ClsOf a cl → Γ'.ClsOf (a.subst σ) cl
  /-- The image of a binder standing below a set stands below the substituted
      set.  `KindCo.HasType.kcvar` reads it. -/
  capSet : ∀ a C, Γ.SetOf a C → Γ'.SetOf (a.subst σ) (C.subst σ)
  /-- A capture variable goes to a capability, never to a *filtered*
      capability.  Every substitution the tree builds puts a variable, the
      universal root or another capture binder there, and nothing else, so
      the kind an atom projects by and the base of an atom cross the
      substitution unchanged. -/
  capProjFree : ∀ κ, (σ.cvar κ).base = σ.cvar κ

namespace Subst.Typed

theorem lift {Γ : Ctx s1} {σ : Subst s1 s2} {Γ' : Ctx s2}
    (h : Subst.Typed Γ σ Γ') (b : Binding s1) :
    Subst.Typed (Γ.cons b) σ.lift (Γ'.cons (b.subst σ)) where
  var := by
    intro x
    cases x with
    | here =>
        show Atom.HasType (Γ'.cons (b.subst σ)) (.var .here)
          (((Γ.cons b).lookupTy .here).subst σ.lift)
        have he : (Γ'.cons (b.subst σ)).lookupTy .here
            = ((Γ.cons b).lookupTy .here).subst σ.lift := by
          show ((b.subst σ).ty)↑ = ((b.ty)↑).subst σ.lift
          rw [Binding.ty_subst, Ty.weaken_subst]
        rw [← he]
        exact .var
    | there y =>
        show Atom.HasType (Γ'.cons (b.subst σ)) ((σ.var y)↑)
          (((Γ.cons b).lookupTy (.there y)).subst σ.lift)
        rw [Ctx.lookupTy_there, Ty.weaken_subst]
        exact (h.var y).weaken _
  ty := by
    intro x ht
    cases x with
    | here =>
        show ((b.subst σ).ty)↑ = ((b.ty)↑).subst σ.lift
        rw [Binding.ty_subst, Ty.weaken_subst]
    | there y =>
        rw [Ctx.isTransparent_there] at ht
        rw [Subst.lift_rootVar_there, Ctx.lookupTy_there, Ctx.lookupTy_there,
          Ty.weaken_subst, h.ty y ht]
  transparent := by
    intro x ht
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at ht
        | transparent T W' Wc' Fs => exact Ctx.isTransparent_here_transparent _ _ _ _ _
    | there y =>
        rw [Ctx.isTransparent_there] at ht
        rw [Subst.lift_rootVar_there, Ctx.isTransparent_there]
        exact h.transparent y ht
  def_ := by
    intro x l W hW
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hW
        | transparent T W' Wc' Fs =>
            have hWe : W = W'.get l := by simpa using hW.symm
            subst hWe
            show (Γ'.cons ((Binding.transparent T W' Wc' Fs).subst σ)).lookupDef .here l = _
            simp only [Binding.subst_transparent, Ctx.lookupDef_here_transparent,
              Witnesses.get_subst]
    | there y =>
        rw [Ctx.lookupDef_there] at hW
        rw [Subst.lift_rootVar_there, Ctx.lookupDef_there]
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            simp [Shape.weaken_subst]
  defC := by
    intro x l C hC
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hC
        | transparent T W' Wc' Fs =>
            have hCe : C = Wc'.get l := by simpa using hC.symm
            subst hCe
            show (Γ'.cons ((Binding.transparent T W' Wc' Fs).subst σ)).lookupDefC .here l = _
            simp only [Binding.subst_transparent, Ctx.lookupDefC_here_transparent,
              CapWitnesses.get_subst]
    | there y =>
        rw [Ctx.lookupDefC_there] at hC
        rw [Subst.lift_rootVar_there, Ctx.lookupDefC_there]
        cases hd : Γ.lookupDefC y l with
        | none => rw [hd] at hC; simp at hC
        | some C0 =>
            rw [hd] at hC
            have hCe : C = C0↑ := by simpa using hC.symm
            subst hCe
            rw [h.defC y l C0 hd]
            simp [CaptureSet.weaken_subst]
  fields := by
    intro x Fs hFs
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hFs
        | transparent T W' Wc' Fs' =>
            have he : Fs' = Fs := by simpa using hFs
            subst he
            rfl
    | there y =>
        rw [Ctx.lookupFields_there] at hFs
        rw [Subst.lift_rootVar_there, Ctx.lookupFields_there]
        exact h.fields y Fs hFs
  capInst := fun a C hI => by
    obtain ⟨a₀, C₀, rfl, rfl, h₀⟩ := Ctx.instOf_cons_cases hI
    rw [CapAtom.weaken_subst, CaptureSet.weaken_subst]
    exact (h.capInst a₀ C₀ h₀).weaken (b.subst σ)
  capRoot := fun r hr => Ctx.isRoot_lift_subst h.capRoot (b.subst σ) r hr
  capLvl := fun e r hr hl =>
    Ctx.lvlLe_lift_subst h.capRoot h.capLvl h.capInner b (b.subst σ) e r hr hl
  capInner := Ctx.capInner_lift_subst h.capInner b (b.subst σ)
  capCls := fun a cl hC => by
    obtain ⟨a₀, rfl, h₀⟩ := Ctx.clsOf_cons_cases hC
    rw [CapAtom.weaken_subst]
    exact (h.capCls a₀ cl h₀).weaken (b.subst σ)
  capSet := fun a C hS => by
    obtain ⟨a₀, C₀, rfl, rfl, h₀⟩ := Ctx.setOf_cons_cases hS
    rw [CapAtom.weaken_subst, CaptureSet.weaken_subst]
    exact (h.capSet a₀ C₀ h₀).weaken (b.subst σ)
  capProjFree := by
    intro κ
    cases κ with
    | there κ0 =>
        show ((σ.cvar κ0).rename Rename.succ).base = (σ.cvar κ0).rename Rename.succ
        rw [CapAtom.base_rename, h.capProjFree κ0]

theorem ofRename {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2} (h : Ctx.Ren Γ ρ Γ') :
    Subst.Typed Γ (Subst.ofRename ρ) Γ' where
  var := by
    intro x
    show Γ' ⊢ₐ (.var (ρ.var x)) : _
    rw [Ty.subst_ofRename, ← h.ty x]
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
  capRoot := by
    intro r hr
    rw [CapAtom.subst_ofRename]
    exact h.capRoot r hr
  capLvl := by
    intro e r hr hl
    rw [CapAtom.subst_ofRename, CapAtom.subst_ofRename]
    exact h.capLvl e r hr hl
  capInner := by
    rw [CapAtom.subst_ofRename]
    exact h.capInner
  capInst := by
    intro a C hI
    rw [CapAtom.subst_ofRename, CaptureSet.subst_ofRename]
    exact h.capInst a C hI
  capCls := by
    intro a cl hC
    rw [CapAtom.subst_ofRename]
    exact h.capCls a cl hC
  capSet := by
    intro a C hS
    rw [CapAtom.subst_ofRename, CaptureSet.subst_ofRename]
    exact h.capSet a C hS
  capProjFree := fun _ => rfl

/-- Instantiating the innermost *opaque* binder by an atom of its type. -/
theorem single {Γ : Ctx s} {T : Ty s} {a : Atom s} (ha : Γ ⊢ₐ a : T) :
    Subst.Typed (Γ.cons (.opaque T)) (Subst.single a) Γ where
  var := by
    intro x
    cases x with
    | here =>
        show Γ ⊢ₐ a : (((Γ.cons (.opaque T)).lookupTy .here).subst (Subst.single a))
        show Γ ⊢ₐ a : ((T↑).subst (Subst.single a))
        rw [Ty.weaken_subst_single]
        exact ha
    | there y =>
        show Γ ⊢ₐ .var y : ((Γ.lookupTy y)↑).subst (Subst.single a)
        rw [Ty.weaken_subst_single]
        exact .var
  ty := by
    intro x ht
    cases x with
    | here => simp at ht
    | there y =>
        show Γ.lookupTy y = ((Γ.lookupTy y)↑).subst (Subst.single a)
        rw [Ty.weaken_subst_single]
  transparent := by
    intro x ht
    cases x with
    | here => simp at ht
    | there y =>
        rw [Ctx.isTransparent_there] at ht
        exact ht
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
            show Γ.lookupDef y l = some ((W0↑).subst (Subst.single a))
            rw [Shape.weaken_subst_single]
            exact hd
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
            show Γ.lookupDefC y l = some ((C0↑).subst (Subst.single a))
            rw [CaptureSet.weaken_subst_single]
            exact hd
  fields := by
    intro x Fs hFs
    cases x with
    | here => simp at hFs
    | there y =>
        rw [Ctx.lookupFields_there] at hFs
        exact hFs
  capRoot := by
    intro r hr
    obtain ⟨r₀, rfl, hr₀⟩ := Ctx.isRoot_cons_cases hr
    rw [CapAtom.weaken_subst_single]
    exact hr₀
  capLvl := by
    intro e r hr hl
    obtain ⟨r₀, rfl, hr₀⟩ := Ctx.isRoot_cons_cases hr
    rw [CapAtom.weaken_subst_single]
    have hhere : ∀ x0 : BVar s .var,
        (Γ.cons (Binding.opaque T)).LvlLe (CapAtom.var .here)
          (CapAtom.weaken (k := .var) r₀) → Γ.LvlLe (CapAtom.var x0) r₀ := by
      intro x0 hh
      have h1 : (Γ.cons (Binding.opaque T)).LvlLe (CapAtom.weaken (k := .var) Γ.rootAtom)
          (CapAtom.weaken (k := .var) r₀) := by
        unfold Ctx.LvlLe
        rw [Ctx.lvlLeB_congr_left (Γ.cons (Binding.opaque T))
          (CapAtom.weaken (k := .var) Γ.rootAtom) (CapAtom.var .here) _
          (Ctx.lvlAtom_cons_here_eq Γ (Binding.opaque T)).symm]
        exact hh
      rw [Ctx.lvlLe_weaken_iff] at h1
      exact Ctx.LvlLe.trans (Ctx.rootAtom_isRoot Γ) (Γ.lvl_le_rootAtom_var x0) h1
    revert hl
    refine Ctx.lvlLe_subst_of_base ?_ e
    clear e
    intro e hbase hl
    rcases CapAtom.cons_cases e with rfl | ⟨l, rfl⟩ | ⟨e₀, rfl⟩ | ⟨e₀, φ, rfl⟩
    · exact hhere a.root hl
    · exact hhere a.root hl
    · rw [CapAtom.weaken_subst_single]
      exact (Ctx.lvlLe_weaken_iff Γ (Binding.opaque T) e₀ r₀).mp hl
    · exact absurd hbase (CapAtom.base_ne_proj e₀ e₀ φ)
  capInner := by
    rw [Ctx.rootAtom_cons Γ (Binding.opaque T), CapAtom.weaken_subst_single]
    exact Ctx.LvlLe.refl_of_root (Ctx.rootAtom_isRoot Γ)
  capInst := by
    intro a0 C hI
    obtain ⟨a₀, C₀, rfl, rfl, h₀⟩ := Ctx.instOf_cons_cases hI
    rw [CapAtom.weaken_subst_single, CaptureSet.weaken_subst_single]
    exact h₀
  capCls := by
    intro a0 cl hC
    obtain ⟨a₀, rfl, h₀⟩ := Ctx.clsOf_cons_cases hC
    rw [CapAtom.weaken_subst_single]
    exact h₀
  capSet := by
    intro a0 C hS
    obtain ⟨a₀, C₀, rfl, rfl, h₀⟩ := Ctx.setOf_cons_cases hS
    rw [CapAtom.weaken_subst_single, CaptureSet.weaken_subst_single]
    exact h₀
  capProjFree := by
    intro κ
    cases κ with
    | there κ0 => rfl

/-- Passing under a capture binder that is not a root. -/
theorem liftC {Γ : Ctx s1} {σ : Subst s1 s2} {Γ' : Ctx s2}
    (h : Subst.Typed Γ σ Γ') (b : CapBound s1) (hb : b.isRoot = false) :
    Subst.Typed (Γ.consC b) σ.liftC (Γ'.consC (b.subst σ)) where
  var := by
    intro x
    cases x with
    | there y =>
        show Atom.HasType (Γ'.consC (b.subst σ)) ((σ.var y)↑)
          (((Γ.consC b).lookupTy (.there y)).subst σ.liftC)
        rw [Ctx.lookupTy_thereC, Ty.weaken_substC]
        exact (h.var y).weakenC _ (by rw [CapBound.isRoot_subst]; exact hb)
  ty := by
    intro x ht
    cases x with
    | there y =>
        rw [Ctx.isTransparent_thereC] at ht
        rw [Subst.liftC_rootVar_there, Ctx.lookupTy_thereC, Ctx.lookupTy_thereC,
          Ty.weaken_substC, h.ty y ht]
  transparent := by
    intro x ht
    cases x with
    | there y =>
        rw [Ctx.isTransparent_thereC] at ht
        rw [Subst.liftC_rootVar_there, Ctx.isTransparent_thereC]
        exact h.transparent y ht
  def_ := by
    intro x l W hW
    cases x with
    | there y =>
        rw [Ctx.lookupDef_thereC] at hW
        rw [Subst.liftC_rootVar_there, Ctx.lookupDef_thereC]
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            simp [Shape.weaken_substC]
  defC := by
    intro x l C hC
    cases x with
    | there y =>
        rw [Ctx.lookupDefC_thereC] at hC
        rw [Subst.liftC_rootVar_there, Ctx.lookupDefC_thereC]
        cases hd : Γ.lookupDefC y l with
        | none => rw [hd] at hC; simp at hC
        | some C0 =>
            rw [hd] at hC
            have hCe : C = C0↑ := by simpa using hC.symm
            subst hCe
            rw [h.defC y l C0 hd]
            simp [CaptureSet.weaken_substC]
  fields := by
    intro x Fs hFs
    cases x with
    | there y =>
        rw [Ctx.lookupFields_thereC] at hFs
        rw [Subst.liftC_rootVar_there, Ctx.lookupFields_thereC]
        exact h.fields y Fs hFs
  capRoot := fun r hr =>
    Ctx.isRoot_liftC_subst h.capRoot b (b.subst σ) (CapBound.isRoot_subst b σ) r hr
  capLvl := fun e r hr hl =>
    Ctx.lvlLe_liftC_subst h.capRoot h.capLvl h.capInner b (b.subst σ)
      (CapBound.isRoot_subst b σ) e r hr hl
  capInner := Ctx.capInner_liftC_subst h.capInner b (b.subst σ) (CapBound.isRoot_subst b σ)
  capInst := fun a C hI => by
    rcases Ctx.instOf_consC_cases hI with ⟨C₀, rfl, rfl, hbi⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
    · cases b with
      | root => simp [CapBound.instSet?] at hbi
      | star => simp [CapBound.instSet?] at hbi
      | cls c => simp [CapBound.instSet?] at hbi
      | upper C₁ => simp [CapBound.instSet?] at hbi
      | inst C₁ =>
          have hC : C₁ = C₀ := by simpa [CapBound.instSet?] using hbi
          subst hC
          rw [CaptureSet.weaken_substC]
          rfl
    · rw [CapAtom.weaken_substC, CaptureSet.weaken_substC]
      exact (h.capInst a₀ C₀ h₀).weakenC (b.subst σ)
  capCls := fun a cl hC => by
    rcases Ctx.clsOf_consC_cases hC with ⟨rfl, hbc⟩ | ⟨a₀, rfl, h₀⟩
    · show ((b.subst σ)↑ : CapBound (s2,c)).clsOf? = some cl
      rw [CapBound.clsOf?_weaken, CapBound.clsOf?_subst]
      exact hbc
    · rw [CapAtom.weaken_substC]
      exact (h.capCls a₀ cl h₀).weakenC (b.subst σ)
  capSet := fun a C hS => by
    rcases Ctx.setOf_consC_cases hS with ⟨C₀, rfl, rfl, hbs⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
    · show ((b.subst σ)↑ : CapBound (s2,c)).setOf? = some ((C₀↑).subst σ.liftC)
      rw [CapBound.setOf?_weaken, CapBound.setOf?_subst, hbs, CaptureSet.weaken_substC]
      rfl
    · rw [CapAtom.weaken_substC, CaptureSet.weaken_substC]
      exact (h.capSet a₀ C₀ h₀).weakenC (b.subst σ)
  capProjFree := by
    intro κ
    cases κ with
    | here => rfl
    | there κ0 =>
        show ((σ.cvar κ0).rename Rename.succ).base = (σ.cvar κ0).rename Rename.succ
        rw [CapAtom.base_rename, h.capProjFree κ0]

/-- Passing under the root binder of a scope.  A root binder needs no side
condition: `capInner` is restored by the root itself, and an atom derivation
crosses it by `Atom.HasType.weakenRootC`. -/
theorem consRoot {Γ : Ctx s1} {σ : Subst s1 s2} {Γ' : Ctx s2}
    (h : Subst.Typed Γ σ Γ') :
    Subst.Typed (Γ.consC .root) σ.liftC (Γ'.consC .root) where
  var := by
    intro x
    cases x with
    | there y =>
        show Atom.HasType (Γ'.consC CapBound.root) ((σ.var y)↑)
          (((Γ.consC CapBound.root).lookupTy (.there y)).subst σ.liftC)
        rw [Ctx.lookupTy_thereC, Ty.weaken_substC]
        exact (h.var y).weakenRootC
  ty := by
    intro x ht
    cases x with
    | there y =>
        rw [Ctx.isTransparent_thereC] at ht
        rw [Subst.liftC_rootVar_there, Ctx.lookupTy_thereC, Ctx.lookupTy_thereC,
          Ty.weaken_substC, h.ty y ht]
  transparent := by
    intro x ht
    cases x with
    | there y =>
        rw [Ctx.isTransparent_thereC] at ht
        rw [Subst.liftC_rootVar_there, Ctx.isTransparent_thereC]
        exact h.transparent y ht
  def_ := by
    intro x l W hW
    cases x with
    | there y =>
        rw [Ctx.lookupDef_thereC] at hW
        rw [Subst.liftC_rootVar_there, Ctx.lookupDef_thereC]
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            simp [Shape.weaken_substC]
  defC := by
    intro x l C hC
    cases x with
    | there y =>
        rw [Ctx.lookupDefC_thereC] at hC
        rw [Subst.liftC_rootVar_there, Ctx.lookupDefC_thereC]
        cases hd : Γ.lookupDefC y l with
        | none => rw [hd] at hC; simp at hC
        | some C0 =>
            rw [hd] at hC
            have hCe : C = C0↑ := by simpa using hC.symm
            subst hCe
            rw [h.defC y l C0 hd]
            simp [CaptureSet.weaken_substC]
  fields := by
    intro x Fs hFs
    cases x with
    | there y =>
        rw [Ctx.lookupFields_thereC] at hFs
        rw [Subst.liftC_rootVar_there, Ctx.lookupFields_thereC]
        exact h.fields y Fs hFs
  capRoot := fun r hr => Ctx.isRoot_liftC_subst h.capRoot .root .root rfl r hr
  capLvl := fun e r hr hl => Ctx.lvlLe_liftC_root_subst h.capLvl e r hr hl
  capInner := by
    show (Γ'.consC CapBound.root).LvlLe (Γ'.consC CapBound.root).rootAtom
      (((Γ.consC CapBound.root).rootAtom).subst σ.liftC)
    have hr : (Γ'.consC (CapBound.root)).rootAtom = CapAtom.cvar .here := rfl
    have hr2 : ((Γ.consC (CapBound.root)).rootAtom).subst σ.liftC = CapAtom.cvar .here := rfl
    rw [hr, hr2]
    exact Ctx.LvlLe.refl_of_root rfl
  capInst := fun a C hI => by
    rcases Ctx.instOf_consC_cases hI with ⟨C₀, rfl, rfl, hbi⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
    · simp [CapBound.instSet?] at hbi
    · rw [CapAtom.weaken_substC, CaptureSet.weaken_substC]
      exact (h.capInst a₀ C₀ h₀).weakenC .root
  capCls := fun a cl hC => by
    rcases Ctx.clsOf_consC_cases hC with ⟨rfl, hbc⟩ | ⟨a₀, rfl, h₀⟩
    · simp [CapBound.clsOf?] at hbc
    · rw [CapAtom.weaken_substC]
      exact (h.capCls a₀ cl h₀).weakenC .root
  capSet := fun a C hS => by
    rcases Ctx.setOf_consC_cases hS with ⟨C₀, rfl, rfl, hbs⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
    · simp [CapBound.setOf?] at hbs
    · rw [CapAtom.weaken_substC, CaptureSet.weaken_substC]
      exact (h.capSet a₀ C₀ h₀).weakenC .root
  capProjFree := by
    intro κ
    cases κ with
    | here => rfl
    | there κ0 =>
        show ((σ.cvar κ0).rename Rename.succ).base = (σ.cvar κ0).rename Rename.succ
        rw [CapAtom.base_rename, h.capProjFree κ0]

/-- A typed substitution passes under a scope. -/
theorem scope {Γ : Ctx s1} {σ : Subst s1 s2} {Γ' : Ctx s2} (h : Subst.Typed Γ σ Γ') :
    Subst.Typed Γ.scope σ.liftC.liftC Γ'.scope :=
  (h.consRoot).liftC .star rfl

/-- And under the scope a pack opens.  The instance binder's bound is not a
root, so `Subst.Typed.liftC` applies to it exactly as it does to `.star`. -/
theorem scopeInst {Γ : Ctx s1} {σ : Subst s1 s2} {Γ' : Ctx s2} (h : Subst.Typed Γ σ Γ')
    (C : CaptureSet s1) :
    Subst.Typed (Γ.scopeInst C) σ.liftC.liftC (Γ'.scopeInst (C.subst σ)) := by
  have hb := (h.consRoot).liftC (.inst C↑) rfl
  have hC : (CapBound.inst (C↑ : CaptureSet (s1,c))).subst σ.liftC
      = CapBound.inst ((C.subst σ)↑) := by
    show CapBound.inst ((C↑).subst σ.liftC) = _
    rw [CaptureSet.weaken_substC]
  rw [hC] at hb
  exact hb

/-- And under a lambda body. -/
theorem body {Γ : Ctx s1} {σ : Subst s1 s2} {Γ' : Ctx s2} (h : Subst.Typed Γ σ Γ')
    (T : Dom s1) :
    Subst.Typed (Γ.body T) σ.liftC.liftC.lift (Γ'.body (T.subst σ.liftC)) := by
  unfold Ctx.body
  rw [← Dom.underRoot_subst]
  exact (h.scope).lift _

/-- And under an object body. -/
theorem objBody {Γ : Ctx s1} {σ : Subst s1 s2} {Γ' : Ctx s2} (h : Subst.Typed Γ σ Γ')
    (T : Ty s1) (W : Witnesses (s1,x)) (Wc : CapWitnesses (s1,x)) (ls : List Label) :
    Subst.Typed (Γ.objBody T W Wc ls) σ.liftC.lift
      (Γ'.objBody (T.subst σ) (W.subst σ.lift) (Wc.subst σ.lift) ls) := by
  unfold Ctx.objBody
  rw [← Ty.weaken_substC, ← Witnesses.underRoot_subst, ← CapWitnesses.underRoot_subst]
  exact (h.consRoot).lift _

end Subst.Typed





/-! ## Evidence and atoms -/

mutual

/-- The capture family is transported by the substitution.  Types and
evidence see an atom only through its root, so a capture set travels along
the renaming of roots, exactly as in the type sort; the family mentions
atoms (`capvar`, `member`), so it belongs to the mutual recursion. -/
theorem CapCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {f : CapCo s1} {C D : CaptureSet s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ᶜ f : C ⊑ D) :
    Γ' ⊢ᶜ (f.subst σ) : (C.subst σ) ⊑ (D.subst σ) := by
  match h with
  | .refl => exact .refl
  | .trans hf hg => exact .trans (hf.subst hσ) (hg.subst hσ)
  | .elem hs => exact .elem (hs.subst σ)
  | .union hf hg =>
      have := CapCo.HasType.union (hf.subst hσ) (hg.subst hσ)
      simpa [CapCo.subst, CaptureSet.subst, CaptureSet.subst_union] using this
  | @CapCo.HasType.capvar _ _ a S C ha =>
      have := CapCo.HasType.capvar (a := a.subst σ)
        (by simpa [Ty.subst] using Atom.HasType.subst hσ ha)
      simpa [CapCo.subst, CaptureSet.subst, CaptureSet.subst_union, CapAtom.subst, Atom.root_subst] using this
  | @CapCo.HasType.member _ _ a S D e Tel i C₁ C₂ ha he hAt =>
      have := CapCo.HasType.member (a := a.subst σ)
        (by simpa [Ty.subst] using Atom.HasType.subst hσ ha)
        (by simpa [Shape.subst] using he.subst hσ) (hAt.subst σ.lift)
      simpa [CapCo.subst, CaptureSet.substVar_subst, Subst.rootVar, Atom.root_subst] using this
  | .eqToLe hφ => exact .eqToLe (hφ.subst hσ)
  | .level h₁ h₂ => exact .level (hσ.capRoot _ h₁) (hσ.capLvl _ _ h₁ h₂)
  | @CapCo.HasType.unprojC _ _ C₀ φ₀ =>
      have : Γ' ⊢ᶜ CapCo.unprojC (C₀.subst σ) φ₀
          : (C₀.subst σ).proj φ₀ ⊑ (C₀.subst σ) := .unprojC
      simpa [CapCo.subst, CaptureSet.proj_subst hσ.capProjFree] using this
  | @CapCo.HasType.projC _ _ g₀ C₀ φ₀ hg =>
      have : Γ' ⊢ᶜ CapCo.projC (g₀.subst σ) (C₀.subst σ) φ₀
          : (C₀.subst σ) ⊑ (C₀.subst σ).proj φ₀ := .projC (hg.subst hσ)
      simpa [CapCo.subst, CaptureSet.proj_subst hσ.capProjFree] using this
  | @CapCo.HasType.projMono _ _ f₀ C₀ D₀ ψ₀ hf =>
      have : Γ' ⊢ᶜ CapCo.projMono (f₀.subst σ) ψ₀
          : (C₀.subst σ).proj ψ₀ ⊑ (D₀.subst σ).proj ψ₀ := .projMono (hf.subst hσ)
      simpa [CapCo.subst, CaptureSet.proj_subst hσ.capProjFree] using this

/-- The kinding family is transported by the substitution.  The kind
arguments ride along unchanged, which is Fact 1, and `capProjFree` is what
keeps the kind an atom projects by and the base of an atom in place. -/
theorem KindCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {g : KindCo s1} {C : CaptureSet s1} {φ : Cls.Kind} (hσ : Subst.Typed Γ σ Γ')
    (h : Γ ⊢ᵏ g : C ⊑ᵏ φ) :
    Γ' ⊢ᵏ (g.subst σ) : (C.subst σ) ⊑ᵏ φ := by
  match h with
  | .nil => exact .nil
  | .cons hg hh => exact .cons (hg.subst hσ) (hh.subst hσ)
  | .kproj hk =>
      refine .kproj ?_
      rw [CapAtom.kindOf_subst hσ.capProjFree]
      exact hk
  | @KindCo.HasType.kcls _ _ a₀ φ₀ cl hc hk =>
      refine @KindCo.HasType.kcls _ Γ' (a₀.subst σ) φ₀ cl ?_ ?_
      · rw [CapAtom.base_subst hσ.capProjFree]
        exact hσ.capCls _ _ hc
      · rw [CapAtom.kindOf_subst hσ.capProjFree]
        exact hk
  | .kvar ha hb hg =>
      have ha' := Atom.HasType.subst hσ ha
      have hg' := hg.subst hσ
      simp only [Ty.subst] at ha'
      rw [CaptureSet.proj_subst hσ.capProjFree,
        ← CapAtom.kindOf_subst hσ.capProjFree] at hg'
      refine .kvar ha' ?_ hg'
      rw [CapAtom.base_subst hσ.capProjFree, hb]
      show CapAtom.var (σ.rootVar _) = CapAtom.var _
      rw [Atom.root_subst]
  | .kcvar hb hg =>
      have hg' := hg.subst hσ
      rw [CaptureSet.proj_subst hσ.capProjFree,
        ← CapAtom.kindOf_subst hσ.capProjFree] at hg'
      refine .kcvar ?_ hg'
      rw [CapAtom.base_subst hσ.capProjFree]
      exact hσ.capSet _ _ hb
  | .kmember ha he hAt =>
      have := KindCo.HasType.kmember
        (by simpa [Ty.subst] using Atom.HasType.subst hσ ha)
        (by simpa [Shape.subst] using he.subst hσ)
        (hAt.subst σ)
      simpa [KindCo.subst, CaptureSet.substVar_subst, Subst.rootVar,
        Atom.root_subst] using this
  | @KindCo.HasType.kprojS _ _ g₀ C₀ φ₀ ψ₀ hg =>
      have : Γ' ⊢ᵏ KindCo.kprojS (g₀.subst σ) (C₀.subst σ) ψ₀
          : (C₀.subst σ).proj ψ₀ ⊑ᵏ φ₀ := .kprojS (hg.subst hσ)
      simpa [KindCo.subst, CaptureSet.proj_subst hσ.capProjFree] using this
  | .ksub hg hs => exact .ksub (hg.subst hσ) hs
  | .kle hf hg => exact .kle (hf.subst hσ) (hg.subst hσ)

theorem CapEq.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {φ : CapEq s1} {C D : CaptureSet s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ᶜ φ : C ≡ D) :
    Γ' ⊢ᶜ (φ.subst σ) : (C.subst σ) ≡ (D.subst σ) := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.subst hσ)
  | .trans hφ hψ => exact .trans (hφ.subst hσ) (hψ.subst hσ)
  | .defC hd =>
      have := CapEq.HasType.defC (hσ.defC _ _ _ hd)
      simpa [CapEq.subst, CaptureSet.subst, CaptureSet.subst_union, CapAtom.subst] using this
  | @CapEq.HasType.instC _ _ a C hI =>
      have := CapEq.HasType.instC (hσ.capInst a C hI)
      simpa [CapEq.subst, CaptureSet.subst] using this
  | @CapEq.HasType.member _ _ a S D e Tel i C₁ C₂ ha he hAt =>
      have := CapEq.HasType.member (a := a.subst σ)
        (by simpa [Ty.subst] using Atom.HasType.subst hσ ha)
        (by simpa [Shape.subst] using he.subst hσ) (hAt.subst σ.lift)
      simpa [CapEq.subst, CaptureSet.substVar_subst, Subst.rootVar, Atom.root_subst] using this

theorem CapStep.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {st : CapStep s1} {X Y : CaptureSet (s1,x)} (hσ : Subst.Typed Γ σ Γ')
    (h : CapStep.HasType Γ st X Y) :
    CapStep.HasType Γ' (st.subst σ) (X.subst σ.lift) (Y.subst σ.lift) := by
  match h with
  | .closed hf =>
      have := CapStep.HasType.closed (hf.subst hσ)
      simpa [CapStep.subst, CaptureSet.weaken_subst] using this
  | .incl hs => exact .incl (hs.subst σ.lift)

theorem SideC.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {q : SideC s1} {X Y : CaptureSet (s1,x)} (hσ : Subst.Typed Γ σ Γ')
    (h : SideC.HasType Γ q X Y) :
    SideC.HasType Γ' (q.subst σ) (X.subst σ.lift) (Y.subst σ.lift) := by
  match h with
  | .nil => exact .nil
  | .cons hst hq => exact .cons (hst.subst hσ) (hq.subst hσ)

theorem ShapeCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {e : ShapeCo s1} {S T : Shape s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ˢ e : S ≤ T) :
    Γ' ⊢ˢ (e.subst σ) : (S.subst σ) ≤ (T.subst σ) := by
  match h with
  | .refl => exact .refl
  | .trans he hf => exact .trans (he.subst hσ) (hf.subst hσ)
  | .top => exact .top
  | .bot => exact .bot
  | .eqToLe hφ => exact .eqToLe (hφ.subst hσ)
  | .pi he hf =>
      have he' := LeCo.HasType.subst hσ.scope he
      have hf' := ELeCo.HasType.subst (hσ.body _) hf
      rw [Dom.underRoot_subst, Dom.underRoot_subst] at he'
      rw [Cod.underRoot_subst, Cod.underRoot_subst] at hf'
      simpa only [ShapeCo.subst, Shape.subst] using ShapeCo.HasType.pi he' hf'
  | .obj hm => exact .obj (hm.subst hσ)
  | .pair he hf =>
      have := ShapeCo.HasType.pair (he.subst hσ) (hf.subst hσ)
      simpa [ShapeCo.subst, Shape.subst, Telescope.append_subst] using this
  | .bound hAt =>
      exact .bound (by
        simpa [Proposition.subst, Shape.weaken_subst] using hAt.subst σ.lift)
  | .intoBnd he =>
      have := ShapeCo.HasType.intoBnd (he.subst hσ)
      simpa [ShapeCo.subst, Shape.subst, Telescope.subst, Proposition.subst,
        Shape.weaken_subst] using this
  | @ShapeCo.HasType.member _ _ a S C e Tel i S' T' ha he hAt =>
      have := ShapeCo.HasType.member (a := a.subst σ)
        (by simpa [Ty.subst] using Atom.HasType.subst hσ ha)
        (by simpa [Shape.subst] using he.subst hσ) (hAt.subst σ.lift)
      simpa [ShapeCo.subst, Shape.substVar_subst, Subst.rootVar] using this
  | .boxed hd =>
      have := ShapeCo.HasType.boxed (LeCo.HasType.subst hσ hd)
      simpa [ShapeCo.subst, Shape.subst] using this

theorem LeCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {d : LeCo s1} {S T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ d : S ≤ T) :
    Γ' ⊢ (d.subst σ) : (S.subst σ) ≤ (T.subst σ) := by
  match h with
  | .capt he hf => exact .capt (he.subst hσ) (CapCo.HasType.subst hσ hf)

theorem EqCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {φ : EqCo s1} {S T : Shape s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ φ : S ≡ T) :
    Γ' ⊢ (φ.subst σ) : (S.subst σ) ≡ (T.subst σ) := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.subst hσ)
  | .trans hφ hψ => exact .trans (hφ.subst hσ) (hψ.subst hσ)
  | .def hd => exact .def (hσ.def_ _ _ _ hd)
  | @EqCo.HasType.member _ _ a S C e Tel i S' T' ha he hAt =>
      have := EqCo.HasType.member (a := a.subst σ)
        (by simpa [Ty.subst] using Atom.HasType.subst hσ ha)
        (by simpa [Shape.subst] using he.subst hσ) (hAt.subst σ.lift)
      simpa [EqCo.subst, Shape.substVar_subst, Subst.rootVar] using this

theorem Has.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {hh : Has s1} {x : BVar s1 .var} {l : Label}
    (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ hh : x ∋ l) :
    Γ' ⊢ (hh.subst σ) : (σ.rootVar x) ∋ l := by
  match h with
  | @Has.HasType.member _ _ a S C e Tel i l ha he hAt =>
      have := Has.HasType.member (a := a.subst σ)
        (by simpa [Ty.subst] using Atom.HasType.subst hσ ha)
        (by simpa [Shape.subst] using he.subst hσ) (hAt.subst σ.lift)
      simpa [Has.subst] using this
  | .field hf hm => exact .field (hσ.fields _ _ hf) hm

theorem Side.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {sd : Side s1} {X Y : Shape (s1,x)} (hσ : Subst.Typed Γ σ Γ') (h : Side.HasType Γ sd X Y) :
    Side.HasType Γ' (sd.subst σ) (X.subst σ.lift) (Y.subst σ.lift) := by
  match h with
  | .none => exact .none
  | .some he =>
      have := Side.HasType.some (he.subst hσ)
      simpa [Side.subst, Shape.weaken_subst] using this

theorem Morphism.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {σ : Subst s1 s2} {src : Telescope (s1,x)} {m : Morphism s1} {Tel : Telescope (s1,x)}
    (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ m : src ⇒ Tel) :
    Γ' ⊢ (m.subst σ) : (src.subst σ.lift) ⇒ (Tel.subst σ.lift) := by
  match h with
  | .nil => exact .nil
  | .le hm hAt hpre hpost =>
      exact .le (hm.subst hσ) (by simpa [Proposition.subst] using hAt.subst σ.lift)
        (hpre.subst hσ) (hpost.subst hσ)
  | .leEq hm hAt hpre hpost =>
      exact .leEq (hm.subst hσ) (by simpa [Proposition.subst] using hAt.subst σ.lift)
        (hpre.subst hσ) (hpost.subst hσ)
  | .leEqSym hm hAt hpre hpost =>
      exact .leEqSym (hm.subst hσ) (by simpa [Proposition.subst] using hAt.subst σ.lift)
        (hpre.subst hσ) (hpost.subst hσ)
  | .eq hm hAt =>
      exact .eq (hm.subst hσ) (by simpa [Proposition.subst] using hAt.subst σ.lift)
  | .eqSym hm hAt =>
      exact .eqSym (hm.subst hσ) (by simpa [Proposition.subst] using hAt.subst σ.lift)
  | .has hm hAt =>
      exact .has (hm.subst hσ) (by simpa [Proposition.subst] using hAt.subst σ.lift)
  | .bnd hm he =>
      have := Morphism.HasType.bnd (hm.subst hσ)
        (by simpa [Shape.subst] using he.subst hσ)
      simpa [Morphism.subst, Telescope.subst, Proposition.subst,
        Shape.weaken_subst] using this
  | .leC hm hh hq hq' =>
      exact .leC (hm.subst hσ) (hh.subst σ) (hq.subst hσ) (hq'.subst hσ)
  | .eqC hm hAt =>
      exact .eqC (hm.subst hσ) (by simpa [Proposition.subst] using hAt.subst σ.lift)
  | .eqSymC hm hAt =>
      exact .eqSymC (hm.subst hσ) (by simpa [Proposition.subst] using hAt.subst σ.lift)
  | .kindC hm hAt hq hsub =>
      exact .kindC (hm.subst hσ) (by simpa [Proposition.subst] using hAt.subst σ.lift)
        (hq.subst hσ) hsub
  | .kindCle hm hh hq hq' hg =>
      exact .kindCle (hm.subst hσ) (hh.subst σ) (hq.subst hσ)
        (by simpa [CaptureSet.weaken_subst] using hq'.subst hσ) (hg.subst hσ)

theorem Atom.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {a : Atom s1} {T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ₐ a : T) :
    Γ' ⊢ₐ (a.subst σ) : (T.subst σ) := by
  match h with
  | @Atom.HasType.var _ _ x => exact hσ.var x
  | .cast ha he => exact .cast (ha.subst hσ) (LeCo.HasType.subst hσ he)
  | @Atom.HasType.unfoldSelf _ _ a C Tel ha =>
      have := Atom.HasType.unfoldSelf (Tel := Tel.subst σ.lift) (a := a.subst σ)
        (C := C.subst σ) (by simpa [Ty.subst, Shape.subst] using ha.subst hσ)
      simpa [Atom.subst, Ty.subst, Shape.subst, Telescope.weaken_subst,
        Telescope.substVar_subst, Subst.rootVar] using this
  | @Atom.HasType.foldSelf _ _ a C Tel ha =>
      have ha' := ha.subst hσ
      simp only [Ty.subst, Shape.subst, Telescope.weaken_subst,
        Telescope.substVar_subst, Subst.rootVar] at ha'
      have := Atom.HasType.foldSelf (Tel := Tel.subst σ.lift) (a := a.subst σ)
        (C := C.subst σ) (by rw [Atom.root_subst]; exact ha')
      simpa [Atom.subst, Ty.subst, Shape.subst] using this
  | .both ha hb hr =>
      have := Atom.HasType.both (by simpa [Ty.subst, Shape.subst] using ha.subst hσ)
        (by simpa [Ty.subst, Shape.subst] using hb.subst hσ)
        (by simp [Atom.root_subst, hr])
      simpa [Atom.subst, Ty.subst, Shape.subst, Telescope.append_subst] using this
  | @Atom.HasType.recap _ _ a S C f C' ha hf =>
      have := Atom.HasType.recap (a := a.subst σ) (C' := C'.subst σ)
        (by simpa [Ty.subst] using ha.subst hσ)
        (by
          simpa [CaptureSet.subst, CaptureSet.subst_union, CapAtom.subst, Atom.root_subst] using
            CapCo.HasType.subst hσ hf)
      simpa [Atom.subst, Ty.subst] using this

theorem ELeCo.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {g : ELeCo s1} {E E' : ETy s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ᵉ g : E ≤ E') :
    Γ' ⊢ᵉ (g.subst σ) : (E.subst σ) ≤ (E'.subst σ) := by
  match h with
  | .plain he => exact .plain (LeCo.HasType.subst hσ he)
  | @ELeCo.HasType.pack _ _ T C C₀ hh e T' hc he =>
      have hc' := CapCo.HasType.subst hσ hc
      have he' := LeCo.HasType.subst (hσ.scopeInst C) he
      rw [Ty.weaken_substC, Ty.weaken_substC, Dom.underRoot_subst] at he'
      exact ELeCo.HasType.pack hc' he'
  | @ELeCo.HasType.cong _ _ T T' C₀ C₀' hh e hc he =>
      have hc' := CapCo.HasType.subst hσ hc
      have he' := LeCo.HasType.subst hσ.scope he
      rw [Dom.underRoot_subst, Dom.underRoot_subst] at he'
      exact ELeCo.HasType.cong hc' he'
  | .trans hg hh => exact .trans (hg.subst hσ) (hh.subst hσ)

end

/-- The packed-atom wrapper premises only judgments of the block above. -/
theorem PAtom.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {p : PAtom s1} {E : ETy s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ₚ p : E) :
    Γ' ⊢ₚ (p.subst σ) : (E.subst σ) := by
  match h with
  | .plain ha => exact .plain (Atom.HasType.subst hσ ha)
  | .pack ha hc he =>
      refine PAtom.HasType.pack (Atom.HasType.subst hσ ha) (CapCo.HasType.subst hσ hc) ?_
      have he' := LeCo.HasType.subst (hσ.scopeInst _) he
      rw [Ty.weaken_substC, Ty.weaken_substC, Dom.underRoot_subst] at he'
      exact he'

/-- The set a `letex` body charges its uses to, under a substitution. -/
theorem CaptureSet.letexCharge_subst {s1 s2 : Sig} (U : CaptureSet s1) (σ : Subst s1 s2) :
    ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U))
        ∪ [CapAtom.cvar (BVar.there BVar.here)]).subst σ.liftC.lift
      = ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap)
          (CaptureSet.subst U σ))) ∪ [CapAtom.cvar (BVar.there BVar.here)]) := by
  rw [CaptureSet.subst_union, CaptureSet.weaken_subst, CaptureSet.weaken_substC]
  rfl

/-! ## Terms, values, fields -/

mutual

theorem Tm.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {t : Tm s1} {E : ETy s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ t :ᵉ E) :
    Γ' ⊢ (t.subst σ) :ᵉ (E.subst σ) := by
  match h with
  | .atom ha => exact .atom (PAtom.HasType.subst hσ ha)
  | .val hv => exact .val (hv.subst hσ)
  | .app ha hb =>
      have ha' := ha.subst hσ
      have hb' := hb.subst hσ
      simp only [Ty.subst, Shape.subst] at ha'
      rw [Ty.singleC_subst] at hb'
      simp only [CapAtom.subst, ← Atom.root_subst] at hb'
      have := Tm.HasType.app ha' hb'
      simpa only [Tm.subst, ETy.arg_subst] using this
  | @Tm.HasType.proj _ _ a T hh l ha hhh =>
      have := Tm.HasType.proj (a := a.subst σ) (ha.subst hσ)
        (by rw [Atom.root_subst]; exact hhh.subst hσ)
      simpa [Tm.subst, ETy.subst, Ty.subst, Shape.subst, CaptureSet.subst,
        CaptureSet.subst_union, CapAtom.subst, Atom.root_subst] using this
  | .let ht hu hf =>
      refine .let (ht.subst hσ) ?_ ?_
      · have := hu.subst (hσ.lift _)
        simpa [ETy.weaken_subst] using this
      · have := CapCo.HasType.subst (hσ.lift _) hf
        simpa only [Tm.uses_subst, CaptureSet.weaken_subst] using this
  | .cast ht he => exact .cast (ht.subst hσ) (LeCo.HasType.subst hσ he)
  | .castE ht hg => exact .castE (ht.subst hσ) (ELeCo.HasType.subst hσ hg)
  | .letex ht hc hu hf =>
      have hu' := hu.subst ((hσ.liftC CapBound.star rfl).lift _)
      have hf' := CapCo.HasType.subst ((hσ.liftC CapBound.star rfl).lift _) hf
      rw [ETy.weaken_subst, ETy.weaken_substC] at hu'
      rw [CaptureSet.letexCharge_subst] at hf'
      exact Tm.HasType.letex (ht.subst hσ) (CapCo.HasType.subst hσ hc) hu'
        (by simpa only [Tm.uses_subst] using hf')
  | .unbox ha hf =>
      have := Tm.HasType.unbox (by simpa [Ty.subst, Shape.subst] using ha.subst hσ)
        (by simpa using CapCo.HasType.subst hσ hf)
      simpa [Tm.subst, ETy.subst, Ty.subst] using this

theorem Value.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {v : Value s1} {T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ᵥ v : T) :
    Γ' ⊢ᵥ (v.subst σ) : (T.subst σ) := by
  match h with
  | .lam ht hg =>
      have ht' := ht.subst (hσ.body _)
      have hg' := CapCo.HasType.subst (hσ.body _) hg
      rw [Cod.underRoot_subst] at ht'
      have := Value.HasType.lam ht'
        (by
          simpa only [Tm.uses_subst, CaptureSet.closing_subst,
            CaptureSet.weaken_substC] using hg')
      simpa [Value.subst, Ty.subst, Shape.subst] using this
  | @Value.HasType.obj _ A0 F0 _ W0 Wc0 hF =>
      have hF' := Fields.HasType.subst (σ := σ.liftC) (hσ.objBody _ W0 Wc0 F0.labels) hF
      have := Value.HasType.obj (Γ := Γ') (A := A0.subst σ)
        (W := W0.subst σ.lift)
        (Wc := Wc0.subst σ.lift) (F := F0.subst σ.liftC.lift)
        (by
          simpa only [Ty.subst, Shape.subst, CaptureSet.weaken_substC,
            Telescope.ofLiteral_subst, Fields.labels_subst] using hF')
      simpa [Value.subst, Ty.subst, Shape.subst, Telescope.ofLiteral_subst] using this
  | .box ha =>
      have := Value.HasType.box (ha.subst hσ)
      simpa [Value.subst, Ty.subst, Shape.subst, CaptureSet.subst, CaptureSet.subst_union] using this
  | .cast hv he => exact .cast (hv.subst hσ) (LeCo.HasType.subst hσ he)

theorem Value.HasTypeE.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {v : Value s1} {E : ETy s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ᵥᵉ v : E) :
    Γ' ⊢ᵥᵉ (v.subst σ) : (E.subst σ) := by
  match h with
  | .plain hv => exact .plain (hv.subst hσ)
  | .pack hv hc he =>
      refine Value.HasTypeE.pack (hv.subst hσ) (CapCo.HasType.subst hσ hc) ?_
      have he' := LeCo.HasType.subst (hσ.scopeInst _) he
      rw [Ty.weaken_substC, Ty.weaken_substC, Dom.underRoot_subst] at he'
      exact he'

theorem Fields.HasType.subst {s1 s2 : Sig} {Γ : Ctx (s1,x)} {Γ' : Ctx (s2,x)}
    {σ : Subst s1 s2} {F : Fields (s1,x)} {A : CaptureSet s1}
    (hσ : Subst.Typed Γ σ.lift Γ') (h : Γ ⊢ᶠ[A] F) :
    Γ' ⊢ᶠ[A.subst σ] (F.subst σ.lift) := by
  match h with
  | .nil => exact .nil
  | .cons hF ht hg =>
      refine .cons (hF.subst hσ) ?_ ?_
      · have := ht.subst hσ
        simpa [Ty.subst, Shape.subst, CaptureSet.subst, CaptureSet.subst_union, CapAtom.subst] using this
      · have := CapCo.HasType.subst hσ hg
        simpa only [Tm.uses_subst, CaptureSet.closing_subst] using this

end

/-! ## Instantiating a capture binder, and entering a body

The four typed substitutions of B1.5.  `singleC` instantiates an arrow's
capture binder, `arg` is what an application does to a codomain, and `enter`
and `enterObj` are what a machine step does when it enters a lambda body or
an object body.  The last two ask that the context bind no root, which is
`Store.Typed.rootFree` at every step: a running program is the outermost
scope, so every level comparison in it holds. -/

theorem Subst.compRename_succ_arg (b : Atom s) :
    Subst.compRename Rename.succ (Subst.arg b) = Subst.singleC (CapAtom.var b.root) := by
  apply Subst.funext' <;> intro y <;> cases y <;> rfl

@[simp] theorem Ty.weaken_subst_arg (T : Ty (s,c)) (b : Atom s) :
    (T.weaken (k := .var)).subst (Subst.arg b)
      = T.subst (Subst.singleC (CapAtom.var b.root)) := by
  show (T.rename Rename.succ).subst (Subst.arg b) = _
  rw [Ty.rename_subst, Subst.compRename_succ_arg]

theorem Subst.compRename_succ3_enter (a : Atom s) :
    Subst.compRename
        ((Rename.succ (k := .cap)).comp
          ((Rename.succ (k := .cap)).comp (Rename.succ (k := .var))))
        (Subst.enter a) = Subst.ofRename Rename.id := by
  apply Subst.funext' <;> intro y <;> rfl

theorem Subst.compRename_succ2_enterC (a : Atom s) :
    Subst.compRename ((Rename.succ (k := .cap)).comp (Rename.succ (k := .cap)))
        (Subst.enterC a) = Subst.ofRename Rename.id := by
  apply Subst.funext' <;> intro y <;> rfl

@[simp] theorem Ty.weaken2_subst_enterC (T : Ty s) (a : Atom s) :
    ((T.weaken (k := .cap)).weaken (k := .cap)).subst (Subst.enterC a) = T := by
  show ((T.rename Rename.succ).rename Rename.succ).subst (Subst.enterC a) = T
  rw [Ty.rename_comp, Ty.rename_subst, Subst.compRename_succ2_enterC,
    Ty.subst_ofRename, Ty.rename_id]

@[simp] theorem Shape.weaken2_subst_enterC (S : Shape s) (a : Atom s) :
    ((S.weaken (k := .cap)).weaken (k := .cap)).subst (Subst.enterC a) = S := by
  show ((S.rename Rename.succ).rename Rename.succ).subst (Subst.enterC a) = S
  rw [Shape.rename_comp, Shape.rename_subst, Subst.compRename_succ2_enterC,
    Shape.subst_ofRename, Shape.rename_id]

@[simp] theorem CaptureSet.weaken2_subst_enterC (C : CaptureSet s) (a : Atom s) :
    ((C.weaken (k := .cap)).weaken (k := .cap)).subst (Subst.enterC a) = C := by
  show ((C.rename Rename.succ).rename Rename.succ).subst (Subst.enterC a) = C
  rw [CaptureSet.rename_comp, CaptureSet.rename_subst, Subst.compRename_succ2_enterC,
    CaptureSet.subst_ofRename, CaptureSet.rename_id]

@[simp] theorem CapAtom.weaken2_subst_enterC (e : CapAtom s) (a : Atom s) :
    ((e.weaken (k := .cap)).weaken (k := .cap)).subst (Subst.enterC a) = e := by
  show ((e.rename Rename.succ).rename Rename.succ).subst (Subst.enterC a) = e
  rw [CapAtom.rename_comp, CapAtom.rename_subst, Subst.compRename_succ2_enterC,
    CapAtom.subst_ofRename, CapAtom.rename_id]

theorem Subst.compRename_succ2_enterObj (y : BVar s .var) :
    Subst.compRename ((Rename.succ (k := .cap)).comp (Rename.succ (k := .var)))
        (Subst.enterObj y) = Subst.ofRename Rename.id := by
  apply Subst.funext' <;> intro z <;> rfl

@[simp] theorem Ty.weaken3_subst_enter (T : Ty s) (a : Atom s) :
    (((T.weaken (k := .cap)).weaken (k := .cap)).weaken (k := .var)).subst (Subst.enter a)
      = T := by
  show (((T.rename Rename.succ).rename Rename.succ).rename Rename.succ).subst
    (Subst.enter a) = T
  rw [Ty.rename_comp, Ty.rename_comp, Ty.rename_subst, Subst.compRename_succ3_enter,
    Ty.subst_ofRename, Ty.rename_id]

@[simp] theorem Shape.weaken3_subst_enter (S : Shape s) (a : Atom s) :
    (((S.weaken (k := .cap)).weaken (k := .cap)).weaken (k := .var)).subst (Subst.enter a)
      = S := by
  show (((S.rename Rename.succ).rename Rename.succ).rename Rename.succ).subst
    (Subst.enter a) = S
  rw [Shape.rename_comp, Shape.rename_comp, Shape.rename_subst,
    Subst.compRename_succ3_enter, Shape.subst_ofRename, Shape.rename_id]

@[simp] theorem CaptureSet.weaken3_subst_enter (C : CaptureSet s) (a : Atom s) :
    (((C.weaken (k := .cap)).weaken (k := .cap)).weaken (k := .var)).subst (Subst.enter a)
      = C := by
  show (((C.rename Rename.succ).rename Rename.succ).rename Rename.succ).subst
    (Subst.enter a) = C
  rw [CaptureSet.rename_comp, CaptureSet.rename_comp, CaptureSet.rename_subst,
    Subst.compRename_succ3_enter, CaptureSet.subst_ofRename, CaptureSet.rename_id]

@[simp] theorem Ty.weaken2_subst_enterObj (T : Ty s) (y : BVar s .var) :
    ((T.weaken (k := .cap)).weaken (k := .var)).subst (Subst.enterObj y) = T := by
  show ((T.rename Rename.succ).rename Rename.succ).subst (Subst.enterObj y) = T
  rw [Ty.rename_comp, Ty.rename_subst, Subst.compRename_succ2_enterObj,
    Ty.subst_ofRename, Ty.rename_id]

@[simp] theorem Shape.weaken2_subst_enterObj (S : Shape s) (y : BVar s .var) :
    ((S.weaken (k := .cap)).weaken (k := .var)).subst (Subst.enterObj y) = S := by
  show ((S.rename Rename.succ).rename Rename.succ).subst (Subst.enterObj y) = S
  rw [Shape.rename_comp, Shape.rename_subst, Subst.compRename_succ2_enterObj,
    Shape.subst_ofRename, Shape.rename_id]

@[simp] theorem CaptureSet.weaken2_subst_enterObj (C : CaptureSet s) (y : BVar s .var) :
    ((C.weaken (k := .cap)).weaken (k := .var)).subst (Subst.enterObj y) = C := by
  show ((C.rename Rename.succ).rename Rename.succ).subst (Subst.enterObj y) = C
  rw [CaptureSet.rename_comp, CaptureSet.rename_subst, Subst.compRename_succ2_enterObj,
    CaptureSet.subst_ofRename, CaptureSet.rename_id]

@[simp] theorem CapAtom.weaken3_subst_enter (a : CapAtom s) (b : Atom s) :
    (((a.weaken (k := .cap)).weaken (k := .cap)).weaken (k := .var)).subst (Subst.enter b)
      = a := by
  show (((a.rename Rename.succ).rename Rename.succ).rename Rename.succ).subst
    (Subst.enter b) = a
  rw [CapAtom.rename_comp, CapAtom.rename_comp, CapAtom.rename_subst,
    Subst.compRename_succ3_enter, CapAtom.subst_ofRename, CapAtom.rename_id]

@[simp] theorem CapAtom.weaken2_subst_enterObj (a : CapAtom s) (y : BVar s .var) :
    ((a.weaken (k := .cap)).weaken (k := .var)).subst (Subst.enterObj y) = a := by
  show ((a.rename Rename.succ).rename Rename.succ).subst (Subst.enterObj y) = a
  rw [CapAtom.rename_comp, CapAtom.rename_subst, Subst.compRename_succ2_enterObj,
    CapAtom.subst_ofRename, CapAtom.rename_id]

/-- Entering an object body reads a witness of the class at the receiver:
the class root goes away and the self becomes the receiver. -/
theorem Subst.compRename_succLift_enterObj (y : BVar s .var) :
    Subst.compRename (Rename.lift (k := .var) (Rename.succ (k := .cap)))
        (Subst.enterObj y) = Subst.ofRename (Rename.subst y) := by
  apply Subst.funext' <;> intro z <;> cases z <;> rfl

@[simp] theorem Shape.underRoot_subst_enterObj (S : Shape (s,x)) (y : BVar s .var) :
    (S.rename (Rename.lift (k := .var) (Rename.succ (k := .cap)))).subst (Subst.enterObj y)
      = S⟦y⟧ := by
  rw [Shape.rename_subst, Subst.compRename_succLift_enterObj, Shape.subst_ofRename]
  rfl

@[simp] theorem CaptureSet.underRoot_subst_enterObj (C : CaptureSet (s,x))
    (y : BVar s .var) :
    (C.rename (Rename.lift (k := .var) (Rename.succ (k := .cap)))).subst (Subst.enterObj y)
      = C⟦y⟧ := by
  rw [CaptureSet.rename_subst, Subst.compRename_succLift_enterObj, CaptureSet.subst_ofRename]
  rfl

@[simp] theorem Shape.weaken_weaken_subst_arg (S : Shape s) (b : Atom s) :
    ((S.weaken (k := .cap)).weaken (k := .var)).subst (Subst.arg b) = S := by
  show ((S.rename Rename.succ).rename Rename.succ).subst (Subst.arg b) = S
  rw [Shape.rename_comp, Shape.rename_subst, Subst.compRename_succ_succ_arg,
    Shape.subst_ofRename, Shape.rename_id]

@[simp] theorem CaptureSet.weaken_weaken_subst_arg (C : CaptureSet s) (b : Atom s) :
    ((C.weaken (k := .cap)).weaken (k := .var)).subst (Subst.arg b) = C := by
  show ((C.rename Rename.succ).rename Rename.succ).subst (Subst.arg b) = C
  rw [CaptureSet.rename_comp, CaptureSet.rename_subst, Subst.compRename_succ_succ_arg,
    CaptureSet.subst_ofRename, CaptureSet.rename_id]

@[simp] theorem Ty.weaken_weaken_subst_arg (T : Ty s) (b : Atom s) :
    ((T.weaken (k := .cap)).weaken (k := .var)).subst (Subst.arg b) = T := by
  show ((T.rename Rename.succ).rename Rename.succ).subst (Subst.arg b) = T
  rw [Ty.rename_comp, Ty.rename_subst, Subst.compRename_succ_succ_arg,
    Ty.subst_ofRename, Ty.rename_id]

/-- Instantiate an arrow's capture binder by an atom.  Either the binder is
not a root, or the atom is a root that absorbs every level of `Γ`, which is
what the entering substitutions supply. -/
theorem Subst.Typed.singleC {Γ : Ctx s} {b : CapBound s} (a : CapAtom s)
    (hi : b.instSet? = none) (hc : b.clsOf? = none) (hs : b.setOf? = none)
    (hp : a.base = a)
    (h : b.isRoot = false ∨ (Γ.IsRoot a ∧ ∀ e : CapAtom s, Γ.LvlLe e a)) :
    Subst.Typed (Γ.consC b) (Subst.singleC a) Γ where
  var := by
    intro x
    cases x with
    | there y =>
        show Γ ⊢ₐ .var y : ((Γ.lookupTy y)↑).subst (Subst.singleC a)
        rw [Ty.weaken_subst_singleC]
        exact .var
  ty := by
    intro x _
    cases x with
    | there y =>
        show Γ.lookupTy y = ((Γ.lookupTy y)↑).subst (Subst.singleC a)
        rw [Ty.weaken_subst_singleC]
  transparent := by
    intro x ht
    cases x with
    | there y => rwa [Ctx.isTransparent_thereC] at ht
  def_ := by
    intro x l W hW
    cases x with
    | there y =>
        rw [Ctx.lookupDef_thereC] at hW
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            show Γ.lookupDef y l = some ((W0↑).subst (Subst.singleC a))
            rw [Shape.weaken_subst_singleC]
            exact hd
  defC := by
    intro x l C hC
    cases x with
    | there y =>
        rw [Ctx.lookupDefC_thereC] at hC
        cases hd : Γ.lookupDefC y l with
        | none => rw [hd] at hC; simp at hC
        | some C0 =>
            rw [hd] at hC
            have hCe : C = C0↑ := by simpa using hC.symm
            subst hCe
            show Γ.lookupDefC y l = some ((C0↑).subst (Subst.singleC a))
            rw [CaptureSet.weaken_subst_singleC]
            exact hd
  fields := by
    intro x Fs hFs
    cases x with
    | there y => rwa [Ctx.lookupFields_thereC] at hFs
  capRoot := by
    intro r hr
    rcases Ctx.isRoot_consC_cases hr with rfl | ⟨r₀, rfl, hr₀⟩
    · have hb : b.isRoot = true := by
        simpa [Ctx.IsRoot, Ctx.isRootB, Ctx.lookupCap] using hr
      rcases h with h | ⟨ha, _⟩
      · simp [h] at hb
      · exact ha
    · rw [CapAtom.weaken_subst_singleC]
      exact hr₀
  capLvl := by
    intro e r hr hl
    rcases Ctx.isRoot_consC_cases hr with rfl | ⟨r₀, rfl, hr₀⟩
    · have hb : b.isRoot = true := by
        simpa [Ctx.IsRoot, Ctx.isRootB, Ctx.lookupCap] using hr
      rcases h with h | ⟨_, hall⟩
      · simp [h] at hb
      · exact hall _
    · rw [CapAtom.weaken_subst_singleC]
      revert hl
      refine Ctx.lvlLe_subst_of_base ?_ e
      clear e
      intro e hbase hl
      rcases CapAtom.consC_cases e with rfl | ⟨e₀, rfl⟩ | ⟨e₀, φ, rfl⟩
      · cases hb : b.isRoot with
        | true => exact absurd hl (Ctx.not_lvlLe_consC_root_here hb r₀)
        | false =>
            have h1 : Γ.LvlLe Γ.rootAtom r₀ := by
              have hl2 := hl
              unfold Ctx.LvlLe at hl2
              rw [Ctx.lvlLeB_congr_left (Γ.consC b) (CapAtom.cvar .here)
                (CapAtom.weaken (k := .cap) Γ.rootAtom) _
                (Ctx.lvlAtom_consC_here_eq Γ b hb)] at hl2
              exact (Ctx.lvlLe_weakenC_iff Γ b Γ.rootAtom r₀).mp hl2
            exact Ctx.LvlLe.trans (Ctx.rootAtom_isRoot Γ)
              (Ctx.confined_rootAtom Γ [a] a (by simp)) h1
      · rw [CapAtom.weaken_subst_singleC]
        exact (Ctx.lvlLe_weakenC_iff Γ b e₀ r₀).mp hl
      · exact absurd hbase (CapAtom.base_ne_proj e₀ e₀ φ)
  capInner := by
    cases hb : b.isRoot with
    | true =>
        have hbb : b = .root := by cases b <;> simp_all [CapBound.isRoot]
        subst hbb
        rcases h with h | ⟨_, hall⟩
        · simp [CapBound.isRoot] at h
        · exact hall _
    | false =>
        rw [Ctx.rootAtom_consC Γ b hb, CapAtom.weaken_subst_singleC]
        exact Ctx.LvlLe.refl_of_root (Ctx.rootAtom_isRoot Γ)
  capInst := by
    intro a0 C hI
    rcases Ctx.instOf_consC_cases hI with ⟨C₀, rfl, rfl, hbi⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
    · rw [hi] at hbi; simp at hbi
    · rw [CapAtom.weaken_subst_singleC, CaptureSet.weaken_subst_singleC]
      exact h₀
  capCls := by
    intro a0 cl hC
    rcases Ctx.clsOf_consC_cases hC with ⟨rfl, hbc⟩ | ⟨a₀, rfl, h₀⟩
    · rw [hc] at hbc; simp at hbc
    · rw [CapAtom.weaken_subst_singleC]
      exact h₀
  capSet := by
    intro a0 C hS
    rcases Ctx.setOf_consC_cases hS with ⟨C₀, rfl, rfl, hbs⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
    · rw [hs] at hbs; simp at hbs
    · rw [CapAtom.weaken_subst_singleC, CaptureSet.weaken_subst_singleC]
      exact h₀
  capProjFree := by
    intro κ
    cases κ with
    | here => exact hp
    | there κ0 => rfl


/-- What an application does to a codomain: the parameter goes to the
argument and the arrow's capture binder to the argument's root. -/
theorem Subst.Typed.arg {Γ : Ctx s} {T : Dom s} {b : Atom s}
    (hb : Γ ⊢ₐ b : T.subst (Subst.singleC (CapAtom.var b.root))) :
    Subst.Typed ((Γ.consC .star).cons (.opaque T)) (Subst.arg b) Γ where
  var := by
    intro x
    cases x with
    | here =>
        show Γ ⊢ₐ b : ((T↑).subst (Subst.arg b))
        rw [Ty.weaken_subst_arg]
        exact hb
    | there x =>
        cases x with
        | there y =>
            show Γ ⊢ₐ .var y : (((Γ.lookupTy y)↑)↑).subst (Subst.arg b)
            rw [Ty.weaken_weaken_subst_arg]
            exact .var
  ty := by
    intro x ht
    cases x with
    | here => simp at ht
    | there x =>
        cases x with
        | there y =>
            show Γ.lookupTy y = (((Γ.lookupTy y)↑)↑).subst (Subst.arg b)
            rw [Ty.weaken_weaken_subst_arg]
  transparent := by
    intro x ht
    cases x with
    | here => simp at ht
    | there x =>
        cases x with
        | there y =>
            rw [Ctx.isTransparent_there, Ctx.isTransparent_thereC] at ht
            exact ht
  def_ := by
    intro x l W hW
    cases x with
    | here => simp at hW
    | there x =>
        cases x with
        | there y =>
            rw [Ctx.lookupDef_there, Ctx.lookupDef_thereC] at hW
            cases hd : Γ.lookupDef y l with
            | none => rw [hd] at hW; simp at hW
            | some W0 =>
                rw [hd] at hW
                have hWe : W = (W0↑)↑ := by simpa using hW.symm
                subst hWe
                show Γ.lookupDef y l = some ((((W0↑)↑).subst (Subst.arg b)))
                rw [Shape.weaken_weaken_subst_arg]
                exact hd
  defC := by
    intro x l C hC
    cases x with
    | here => simp at hC
    | there x =>
        cases x with
        | there y =>
            rw [Ctx.lookupDefC_there, Ctx.lookupDefC_thereC] at hC
            cases hd : Γ.lookupDefC y l with
            | none => rw [hd] at hC; simp at hC
            | some C0 =>
                rw [hd] at hC
                have hCe : C = (C0↑)↑ := by simpa using hC.symm
                subst hCe
                show Γ.lookupDefC y l = some ((((C0↑)↑).subst (Subst.arg b)))
                rw [CaptureSet.weaken_weaken_subst_arg]
                exact hd
  fields := by
    intro x Fs hFs
    cases x with
    | here => simp at hFs
    | there x =>
        cases x with
        | there y =>
            rw [Ctx.lookupFields_there, Ctx.lookupFields_thereC] at hFs
            exact hFs
  capRoot := by
    intro r hr
    obtain ⟨r₁, rfl, hr₁⟩ := Ctx.isRoot_cons_cases hr
    rcases Ctx.isRoot_consC_cases hr₁ with rfl | ⟨r₀, rfl, hr₀⟩
    · simp [Ctx.IsRoot, Ctx.isRootB, Ctx.lookupCap, CapBound.weaken, CapBound.rename,
        CapBound.isRoot] at hr₁
    · rw [CapAtom.weaken_weaken_subst_arg]
      exact hr₀
  capLvl := by
    intro e r hr hl
    obtain ⟨r₁, rfl, hr₁⟩ := Ctx.isRoot_cons_cases hr
    rcases Ctx.isRoot_consC_cases hr₁ with rfl | ⟨r₀, rfl, hr₀⟩
    · simp [Ctx.IsRoot, Ctx.isRootB, Ctx.lookupCap, CapBound.weaken, CapBound.rename,
        CapBound.isRoot] at hr₁
    · rw [CapAtom.weaken_weaken_subst_arg]
      have hhere : ((Γ.consC CapBound.star).cons (Binding.opaque T)).LvlLe
          (CapAtom.var .here)
          (CapAtom.weaken (k := .var) (CapAtom.weaken (k := .cap) r₀)) →
          ∀ a : CapAtom s, Γ.LvlLe a r₀ := by
        intro hh a
        have heq := Ctx.lvlAtom_cons_here_eq (Γ.consC CapBound.star) (Binding.opaque T)
        rw [Ctx.rootAtom_consC Γ CapBound.star rfl] at heq
        have h1 : ((Γ.consC CapBound.star).cons (Binding.opaque T)).LvlLe
            (CapAtom.weaken (k := .var) (CapAtom.weaken (k := .cap) Γ.rootAtom))
            (CapAtom.weaken (k := .var) (CapAtom.weaken (k := .cap) r₀)) := by
          unfold Ctx.LvlLe
          rw [Ctx.lvlLeB_congr_left _ _ (CapAtom.var .here) _ heq.symm]
          exact hh
        rw [Ctx.lvlLe_weaken_iff, Ctx.lvlLe_weakenC_iff] at h1
        exact Ctx.LvlLe.trans (Ctx.rootAtom_isRoot Γ)
          (Ctx.confined_rootAtom Γ [a] a (by simp)) h1
      revert hl
      refine Ctx.lvlLe_subst_of_base ?_ e
      clear e
      intro e hbase hl
      rcases CapAtom.cons_cases e with rfl | ⟨l, rfl⟩ | ⟨e₁, rfl⟩ | ⟨e₁, φ, rfl⟩
      · exact hhere hl _
      · exact hhere hl _
      · rcases CapAtom.consC_cases e₁ with rfl | ⟨e₀, rfl⟩ | ⟨e₀, φ, rfl⟩
        · exact hhere hl _
        · rw [CapAtom.weaken_weaken_subst_arg]
          exact (Ctx.lvlLe_weakenC_iff Γ CapBound.star e₀ r₀).mp
            ((Ctx.lvlLe_weaken_iff (Γ.consC CapBound.star) (Binding.opaque T)
              (CapAtom.weaken (k := .cap) e₀) (CapAtom.weaken (k := .cap) r₀)).mp hl)
        · exact absurd (CapAtom.base_of_weaken hbase) (CapAtom.base_ne_proj e₀ e₀ φ)
      · exact absurd hbase (CapAtom.base_ne_proj e₁ e₁ φ)
  capInner := by
    show Γ.LvlLe Γ.rootAtom
      ((((Γ.consC CapBound.star).cons (Binding.opaque T)).rootAtom).subst (Subst.arg b))
    rw [Ctx.rootAtom_cons, Ctx.rootAtom_consC Γ CapBound.star rfl,
      CapAtom.weaken_weaken_subst_arg]
    exact Ctx.LvlLe.refl_of_root (Ctx.rootAtom_isRoot Γ)
  capInst := by
    intro a C hI
    obtain ⟨a₁, C₁, rfl, rfl, h₁⟩ := Ctx.instOf_cons_cases hI
    rcases Ctx.instOf_consC_cases h₁ with ⟨C₀, rfl, rfl, hbi⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
    · simp [CapBound.instSet?] at hbi
    · rw [CapAtom.weaken_weaken_subst_arg, CaptureSet.weaken_weaken_subst_arg]
      exact h₀
  capCls := by
    intro a cl hC
    obtain ⟨a₁, rfl, h₁⟩ := Ctx.clsOf_cons_cases hC
    rcases Ctx.clsOf_consC_cases h₁ with ⟨rfl, hbc⟩ | ⟨a₀, rfl, h₀⟩
    · simp [CapBound.clsOf?] at hbc
    · rw [CapAtom.weaken_weaken_subst_arg]
      exact h₀
  capSet := by
    intro a C hS
    obtain ⟨a₁, C₁, rfl, rfl, h₁⟩ := Ctx.setOf_cons_cases hS
    rcases Ctx.setOf_consC_cases h₁ with ⟨C₀, rfl, rfl, hbs⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
    · simp [CapBound.setOf?] at hbs
    · rw [CapAtom.weaken_weaken_subst_arg, CaptureSet.weaken_weaken_subst_arg]
      exact h₀
  capProjFree := by
    intro κ
    cases κ with
    | there κ0 =>
        cases κ0 with
        | here => rfl
        | there κ1 => rfl


set_option maxHeartbeats 2000000 in
/-- **The hardest lemma of the stage.**  What a step does when it enters a
lambda body: the parameter goes to the argument, the arrow's binder to the
argument's root, and the body root to the universal root.  The context binds
no root, which is `Store.Typed.rootFree` at every machine step, so the root
atoms of the body are `⊤ᶜ` and the body root and no others, both go to `⊤ᶜ`,
and every level fact of the body maps to one that holds because a rootless
context puts every atom at the outermost level. -/
theorem Subst.Typed.enterAux {Γ : Ctx s} {T : Dom s} {b : Atom s}
    (hΓ : Γ.root? = none)
    (hb : Γ ⊢ₐ b : T.subst (Subst.singleC (CapAtom.var b.root))) :
    Subst.Typed (((Γ.consC .root).consC .star).cons (.opaque T.underRoot)) (Subst.enter b) Γ where
  var := by
    intro x
    cases x with
    | here =>
        show Γ ⊢ₐ b : (((Dom.underRoot T)↑).subst (Subst.enter b))
        rw [show ((Dom.underRoot T)↑) = Dom.inBody T from rfl, Dom.inBody_enter]
        exact hb
    | there x =>
        cases x with
        | there x =>
            cases x with
            | there y =>
                show Γ ⊢ₐ .var y : ((((Γ.lookupTy y)↑)↑)↑).subst (Subst.enter b)
                rw [Ty.weaken3_subst_enter]
                exact .var
  ty := by
    intro x ht
    cases x with
    | here => simp [Ctx.body, Ctx.scope] at ht
    | there x =>
        cases x with
        | there x =>
            cases x with
            | there y =>
                show Γ.lookupTy y = ((((Γ.lookupTy y)↑)↑)↑).subst (Subst.enter b)
                rw [Ty.weaken3_subst_enter]
  transparent := by
    intro x ht
    cases x with
    | here => simp [Ctx.body, Ctx.scope] at ht
    | there x =>
        cases x with
        | there x =>
            cases x with
            | there y =>
                rw [Ctx.isTransparent_there, Ctx.isTransparent_thereC,
                  Ctx.isTransparent_thereC] at ht
                exact ht
  def_ := by
    intro x l W hW
    cases x with
    | here => simp [Ctx.body, Ctx.scope] at hW
    | there x =>
        cases x with
        | there x =>
            cases x with
            | there y =>
                rw [Ctx.lookupDef_there, Ctx.lookupDef_thereC, Ctx.lookupDef_thereC] at hW
                cases hd : Γ.lookupDef y l with
                | none => rw [hd] at hW; simp at hW
                | some W0 =>
                    rw [hd] at hW
                    have hWe : W = ((W0↑)↑)↑ := by simpa using hW.symm
                    subst hWe
                    show Γ.lookupDef y l = some ((((W0↑)↑)↑).subst (Subst.enter b))
                    rw [Shape.weaken3_subst_enter]
                    exact hd
  defC := by
    intro x l C hC
    cases x with
    | here => simp [Ctx.body, Ctx.scope] at hC
    | there x =>
        cases x with
        | there x =>
            cases x with
            | there y =>
                rw [Ctx.lookupDefC_there, Ctx.lookupDefC_thereC, Ctx.lookupDefC_thereC] at hC
                cases hd : Γ.lookupDefC y l with
                | none => rw [hd] at hC; simp at hC
                | some C0 =>
                    rw [hd] at hC
                    have hCe : C = ((C0↑)↑)↑ := by simpa using hC.symm
                    subst hCe
                    show Γ.lookupDefC y l = some ((((C0↑)↑)↑).subst (Subst.enter b))
                    rw [CaptureSet.weaken3_subst_enter]
                    exact hd
  fields := by
    intro x Fs hFs
    cases x with
    | here => simp [Ctx.body, Ctx.scope] at hFs
    | there x =>
        cases x with
        | there x =>
            cases x with
            | there y =>
                rw [Ctx.lookupFields_there, Ctx.lookupFields_thereC,
                  Ctx.lookupFields_thereC] at hFs
                exact hFs
  capRoot := by
    intro r hr
    obtain ⟨r₂, rfl, hr₂⟩ := Ctx.isRoot_cons_cases hr
    rcases Ctx.isRoot_consC_cases hr₂ with rfl | ⟨r₁, rfl, hr₁⟩
    · simp [Ctx.IsRoot, Ctx.isRootB, Ctx.lookupCap, CapBound.weaken, CapBound.rename,
        CapBound.isRoot] at hr₂
    · rcases Ctx.isRoot_consC_cases hr₁ with rfl | ⟨r₀, rfl, hr₀⟩
      · rfl
      · rw [CapAtom.weaken3_subst_enter]
        exact hr₀
  capLvl := fun e r _ _ => Ctx.lvlLe_of_root?_none hΓ _ _
  capInner := Ctx.lvlLe_of_root?_none hΓ _ _
  capInst := by
    intro a C hI
    obtain ⟨a₂, C₂, rfl, rfl, h₂⟩ := Ctx.instOf_cons_cases hI
    rcases Ctx.instOf_consC_cases h₂ with ⟨C₁, rfl, rfl, hbi⟩ | ⟨a₁, C₁, rfl, rfl, h₁⟩
    · simp [CapBound.instSet?] at hbi
    · rcases Ctx.instOf_consC_cases h₁ with ⟨C₀, rfl, rfl, hbi⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
      · simp [CapBound.instSet?] at hbi
      · rw [CapAtom.weaken3_subst_enter, CaptureSet.weaken3_subst_enter]
        exact h₀
  capCls := by
    intro a cl hC
    obtain ⟨a₂, rfl, h₂⟩ := Ctx.clsOf_cons_cases hC
    rcases Ctx.clsOf_consC_cases h₂ with ⟨rfl, hbc⟩ | ⟨a₁, rfl, h₁⟩
    · simp [CapBound.clsOf?] at hbc
    · rcases Ctx.clsOf_consC_cases h₁ with ⟨rfl, hbc⟩ | ⟨a₀, rfl, h₀⟩
      · simp [CapBound.clsOf?] at hbc
      · rw [CapAtom.weaken3_subst_enter]
        exact h₀
  capSet := by
    intro a C hS
    obtain ⟨a₂, C₂, rfl, rfl, h₂⟩ := Ctx.setOf_cons_cases hS
    rcases Ctx.setOf_consC_cases h₂ with ⟨C₁, rfl, rfl, hbs⟩ | ⟨a₁, C₁, rfl, rfl, h₁⟩
    · simp [CapBound.setOf?] at hbs
    · rcases Ctx.setOf_consC_cases h₁ with ⟨C₀, rfl, rfl, hbs⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
      · simp [CapBound.setOf?] at hbs
      · rw [CapAtom.weaken3_subst_enter, CaptureSet.weaken3_subst_enter]
        exact h₀
  capProjFree := by
    intro κ
    cases κ with
    | there κ0 =>
        cases κ0 with
        | here => rfl
        | there κ1 =>
            cases κ1 with
            | here => rfl
            | there κ2 => rfl

set_option maxHeartbeats 2000000 in
/-- The same when a projection enters an object body. -/
theorem Subst.Typed.enterObjAux {Γ : Ctx s} {T : Ty s} {W : Witnesses (s,x)}
    {Wc : CapWitnesses (s,x)} {ls : List Label} {y : BVar s .var}
    (hΓ : Γ.root? = none)
    (hy : Γ.lookupTy y = T)
    (hdef : ∀ l, Γ.lookupDef y l = some ((W.get l)⟦y⟧))
    (hdefC : ∀ l, Γ.lookupDefC y l = some ((Wc.get l)⟦y⟧))
    (hfields : Γ.lookupFields y = some ls) :
    Subst.Typed ((Γ.consC .root).cons
      (.transparent T.weaken (W.rename Rename.succ.lift) (Wc.rename Rename.succ.lift) ls))
      (Subst.enterObj y) Γ where
  var := by
    intro x
    cases x with
    | here =>
        show Γ ⊢ₐ .var y : (((T.weaken)↑).subst (Subst.enterObj y))
        rw [Ty.weaken2_subst_enterObj, ← hy]
        exact .var
    | there x =>
        cases x with
        | there z =>
            show Γ ⊢ₐ .var z : (((Γ.lookupTy z)↑)↑).subst (Subst.enterObj y)
            rw [Ty.weaken2_subst_enterObj]
            exact .var
  ty := by
    intro x _
    cases x with
    | here =>
        show Γ.lookupTy y = ((T.weaken)↑).subst (Subst.enterObj y)
        rw [Ty.weaken2_subst_enterObj, hy]
    | there x =>
        cases x with
        | there z =>
            show Γ.lookupTy z = (((Γ.lookupTy z)↑)↑).subst (Subst.enterObj y)
            rw [Ty.weaken2_subst_enterObj]
  transparent := by
    intro x ht
    cases x with
    | here => exact Ctx.IsTransparent.of_lookup hfields
    | there x =>
        cases x with
        | there z =>
            rw [Ctx.isTransparent_there, Ctx.isTransparent_thereC] at ht
            exact ht
  def_ := by
    intro x l W0 hW
    cases x with
    | here =>
        have hWe : W0 = (W.rename Rename.succ.lift).get l := by simpa using hW.symm
        subst hWe
        show Γ.lookupDef y l = some (((W.rename Rename.succ.lift).get l).subst
          (Subst.enterObj y))
        rw [Witnesses.get_rename, Shape.underRoot_subst_enterObj]
        exact hdef l
    | there x =>
        cases x with
        | there z =>
            rw [Ctx.lookupDef_there, Ctx.lookupDef_thereC] at hW
            cases hd : Γ.lookupDef z l with
            | none => rw [hd] at hW; simp at hW
            | some W1 =>
                rw [hd] at hW
                have hWe : W0 = (W1↑)↑ := by simpa using hW.symm
                subst hWe
                show Γ.lookupDef z l = some ((((W1↑)↑).subst (Subst.enterObj y)))
                rw [Shape.weaken2_subst_enterObj]
                exact hd
  defC := by
    intro x l C0 hC
    cases x with
    | here =>
        have hCe : C0 = (Wc.rename Rename.succ.lift).get l := by simpa using hC.symm
        subst hCe
        show Γ.lookupDefC y l = some (((Wc.rename Rename.succ.lift).get l).subst
          (Subst.enterObj y))
        rw [CapWitnesses.get_rename, CaptureSet.underRoot_subst_enterObj]
        exact hdefC l
    | there x =>
        cases x with
        | there z =>
            rw [Ctx.lookupDefC_there, Ctx.lookupDefC_thereC] at hC
            cases hd : Γ.lookupDefC z l with
            | none => rw [hd] at hC; simp at hC
            | some C1 =>
                rw [hd] at hC
                have hCe : C0 = (C1↑)↑ := by simpa using hC.symm
                subst hCe
                show Γ.lookupDefC z l = some ((((C1↑)↑).subst (Subst.enterObj y)))
                rw [CaptureSet.weaken2_subst_enterObj]
                exact hd
  fields := by
    intro x Fs hFs
    cases x with
    | here =>
        have hFe : Fs = ls := by simpa using hFs.symm
        subst hFe
        exact hfields
    | there x =>
        cases x with
        | there z =>
            rw [Ctx.lookupFields_there, Ctx.lookupFields_thereC] at hFs
            exact hFs
  capRoot := by
    intro r hr
    obtain ⟨r₁, rfl, hr₁⟩ := Ctx.isRoot_cons_cases hr
    rcases Ctx.isRoot_consC_cases hr₁ with rfl | ⟨r₀, rfl, hr₀⟩
    · rfl
    · rw [CapAtom.weaken2_subst_enterObj]
      exact hr₀
  capLvl := fun e r _ _ => Ctx.lvlLe_of_root?_none hΓ _ _
  capInner := Ctx.lvlLe_of_root?_none hΓ _ _
  capInst := by
    intro a C hI
    obtain ⟨a₁, C₁, rfl, rfl, h₁⟩ := Ctx.instOf_cons_cases hI
    rcases Ctx.instOf_consC_cases h₁ with ⟨C₀, rfl, rfl, hbi⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
    · simp [CapBound.instSet?] at hbi
    · rw [CapAtom.weaken2_subst_enterObj, CaptureSet.weaken2_subst_enterObj]
      exact h₀
  capCls := by
    intro a cl hC
    obtain ⟨a₁, rfl, h₁⟩ := Ctx.clsOf_cons_cases hC
    rcases Ctx.clsOf_consC_cases h₁ with ⟨rfl, hbc⟩ | ⟨a₀, rfl, h₀⟩
    · simp [CapBound.clsOf?] at hbc
    · rw [CapAtom.weaken2_subst_enterObj]
      exact h₀
  capSet := by
    intro a C hS
    obtain ⟨a₁, C₁, rfl, rfl, h₁⟩ := Ctx.setOf_cons_cases hS
    rcases Ctx.setOf_consC_cases h₁ with ⟨C₀, rfl, rfl, hbs⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
    · simp [CapBound.setOf?] at hbs
    · rw [CapAtom.weaken2_subst_enterObj, CaptureSet.weaken2_subst_enterObj]
      exact h₀
  capProjFree := by
    intro κ
    cases κ with
    | there κ0 =>
        cases κ0 with
        | here => rfl
        | there κ1 => rfl

/-- **The entering substitution**, at the context of B1.1. -/
theorem Subst.Typed.enter {Γ : Ctx s} {T : Dom s} {b : Atom s}
    (hΓ : Γ.root? = none)
    (hb : Γ ⊢ₐ b : T.subst (Subst.singleC (CapAtom.var b.root))) :
    Subst.Typed (Γ.body T) (Subst.enter b) Γ :=
  Subst.Typed.enterAux hΓ hb

/-- The scope half of `Subst.Typed.enter`: what a step does to a coercion of
a `pi` form, which lives in a scope and not in a body.  The two capture
binders of the scope go to the argument's root and to the universal root, and
the argument itself is not needed, because a scope binds no parameter. -/
theorem Subst.Typed.enterCAux {Γ : Ctx s} {b : Atom s} (hΓ : Γ.root? = none) :
    Subst.Typed ((Γ.consC .root).consC .star) (Subst.enterC b) Γ where
  var := by
    intro x
    cases x with
    | there x =>
        cases x with
        | there y =>
            show Γ ⊢ₐ .var y : (((Γ.lookupTy y)↑)↑).subst (Subst.enterC b)
            rw [Ty.weaken2_subst_enterC]
            exact .var
  ty := by
    intro x _
    cases x with
    | there x =>
        cases x with
        | there y =>
            show Γ.lookupTy y = (((Γ.lookupTy y)↑)↑).subst (Subst.enterC b)
            rw [Ty.weaken2_subst_enterC]
  transparent := by
    intro x ht
    cases x with
    | there x =>
        cases x with
        | there y =>
            rw [Ctx.isTransparent_thereC, Ctx.isTransparent_thereC] at ht
            exact ht
  def_ := by
    intro x l W hW
    cases x with
    | there x =>
        cases x with
        | there y =>
            rw [Ctx.lookupDef_thereC, Ctx.lookupDef_thereC] at hW
            cases hd : Γ.lookupDef y l with
            | none => rw [hd] at hW; simp at hW
            | some W0 =>
                rw [hd] at hW
                have hWe : W = (W0↑)↑ := by simpa using hW.symm
                subst hWe
                show Γ.lookupDef y l = some (((W0↑)↑).subst (Subst.enterC b))
                rw [Shape.weaken2_subst_enterC]
                exact hd
  defC := by
    intro x l C hC
    cases x with
    | there x =>
        cases x with
        | there y =>
            rw [Ctx.lookupDefC_thereC, Ctx.lookupDefC_thereC] at hC
            cases hd : Γ.lookupDefC y l with
            | none => rw [hd] at hC; simp at hC
            | some C0 =>
                rw [hd] at hC
                have hCe : C = (C0↑)↑ := by simpa using hC.symm
                subst hCe
                show Γ.lookupDefC y l = some (((C0↑)↑).subst (Subst.enterC b))
                rw [CaptureSet.weaken2_subst_enterC]
                exact hd
  fields := by
    intro x Fs hFs
    cases x with
    | there x =>
        cases x with
        | there y =>
            rw [Ctx.lookupFields_thereC, Ctx.lookupFields_thereC] at hFs
            exact hFs
  capRoot := by
    intro r hr
    rcases Ctx.isRoot_consC_cases hr with rfl | ⟨r₁, rfl, hr₁⟩
    · exact Bool.noConfusion hr
    · rcases Ctx.isRoot_consC_cases hr₁ with rfl | ⟨r₀, rfl, hr₀⟩
      · rfl
      · rw [CapAtom.weaken2_subst_enterC]
        exact hr₀
  capLvl := fun e r _ _ => Ctx.lvlLe_of_root?_none hΓ _ _
  capInner := Ctx.lvlLe_of_root?_none hΓ _ _
  capInst := by
    intro a C hI
    rcases Ctx.instOf_consC_cases hI with ⟨C₁, rfl, rfl, hbi⟩ | ⟨a₁, C₁, rfl, rfl, h₁⟩
    · simp [CapBound.instSet?] at hbi
    · rcases Ctx.instOf_consC_cases h₁ with ⟨C₀, rfl, rfl, hbi⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
      · simp [CapBound.instSet?] at hbi
      · rw [CapAtom.weaken2_subst_enterC, CaptureSet.weaken2_subst_enterC]
        exact h₀
  capCls := by
    intro a cl hC
    rcases Ctx.clsOf_consC_cases hC with ⟨rfl, hbc⟩ | ⟨a₁, rfl, h₁⟩
    · simp [CapBound.clsOf?] at hbc
    · rcases Ctx.clsOf_consC_cases h₁ with ⟨rfl, hbc⟩ | ⟨a₀, rfl, h₀⟩
      · simp [CapBound.clsOf?] at hbc
      · rw [CapAtom.weaken2_subst_enterC]
        exact h₀
  capSet := by
    intro a C hS
    rcases Ctx.setOf_consC_cases hS with ⟨C₁, rfl, rfl, hbs⟩ | ⟨a₁, C₁, rfl, rfl, h₁⟩
    · simp [CapBound.setOf?] at hbs
    · rcases Ctx.setOf_consC_cases h₁ with ⟨C₀, rfl, rfl, hbs⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
      · simp [CapBound.setOf?] at hbs
      · rw [CapAtom.weaken2_subst_enterC, CaptureSet.weaken2_subst_enterC]
        exact h₀
  capProjFree := by
    intro κ
    cases κ with
    | here => rfl
    | there κ0 =>
        cases κ0 with
        | here => rfl
        | there κ1 => rfl

/-- The same at `Ctx.scope`, which is the context the `pi` rule opens. -/
theorem Subst.Typed.enterC {Γ : Ctx s} {b : Atom s} (hΓ : Γ.root? = none) :
    Subst.Typed Γ.scope (Subst.enterC b) Γ :=
  Subst.Typed.enterCAux hΓ

/-! ### Collapsing a pack's scope

`Subst.instRoot` sends the witness binder of a pack's scope to the instance
binder the store gains at the unpack, and the pack's own root to the
universal root, for the reason `Subst.enter` sends a body root to `⊤ᶜ`: a
running program is the outermost scope.  The three cancellations below are
`Ty.weakenC_two_instRoot` at the other sorts, by the same fusion. -/

theorem Subst.compRename_succ_succ_instRoot {s : Sig} :
    Subst.compRename (Rename.succ (k := .cap))
        (Subst.compRename (Rename.succ (k := .cap)) (Subst.instRoot (s := s)))
      = Subst.ofRename (Rename.succ (k := .cap)) := by
  apply Subst.funext' <;> intro y <;> rfl

@[simp] theorem CapAtom.weakenC_two_instRoot (a : CapAtom s) :
    (CapAtom.weaken (k := .cap) (CapAtom.weaken (k := .cap) a)).subst Subst.instRoot
      = CapAtom.weaken (k := .cap) a := by
  show ((a.rename Rename.succ).rename Rename.succ).subst Subst.instRoot = _
  rw [CapAtom.rename_subst, CapAtom.rename_subst, Subst.compRename_succ_succ_instRoot,
    CapAtom.subst_ofRename]
  rfl

@[simp] theorem CaptureSet.weakenC_two_instRoot (C : CaptureSet s) :
    (CaptureSet.weaken (k := .cap) (CaptureSet.weaken (k := .cap) C)).subst Subst.instRoot
      = CaptureSet.weaken (k := .cap) C := by
  show ((C.rename Rename.succ).rename Rename.succ).subst Subst.instRoot = _
  rw [CaptureSet.rename_subst, CaptureSet.rename_subst, Subst.compRename_succ_succ_instRoot,
    CaptureSet.subst_ofRename]
  rfl

@[simp] theorem Shape.weakenC_two_instRoot (S : Shape s) :
    (Shape.weaken (k := .cap) (Shape.weaken (k := .cap) S)).subst Subst.instRoot
      = Shape.weaken (k := .cap) S := by
  show ((S.rename Rename.succ).rename Rename.succ).subst Subst.instRoot = _
  rw [Shape.rename_subst, Shape.rename_subst, Subst.compRename_succ_succ_instRoot,
    Shape.subst_ofRename]
  rfl

/-- **T-B2.2, the instance substitution.**  The root atoms of a pack's scope
are `⊤ᶜ` and the pack's own root and no others, because `hΓ` excludes a root
in `Γ` and the witness binder is an instance; both go to `⊤ᶜ`.  The `var`
field is not vacuous: the scope keeps every term binder of `Γ` two binders
in, and `Subst.instRoot` sends it back one, which is the two-against-one
weakening `Ty.weakenC_two_instRoot`. -/
theorem Subst.Typed.instRoot {Γ : Ctx s} (hΓ : Γ.root? = none) (C : CaptureSet s) :
    Subst.Typed (Γ.scopeInst C) Subst.instRoot (Γ.consC (.inst C)) where
  var := by
    intro x
    cases x with
    | there x =>
        cases x with
        | there y =>
            show (Γ.consC (CapBound.inst C)) ⊢ₐ .var (.there y)
              : (((Γ.lookupTy y)↑)↑).subst Subst.instRoot
            rw [Ty.weakenC_two_instRoot]
            exact .var
  ty := by
    intro x _
    cases x with
    | there x =>
        cases x with
        | there y =>
            show ((Γ.lookupTy y)↑ : Ty (s,c)) = (((Γ.lookupTy y)↑)↑).subst Subst.instRoot
            rw [Ty.weakenC_two_instRoot]
  transparent := by
    intro x ht
    cases x with
    | there x =>
        cases x with
        | there y =>
            unfold Ctx.scopeInst at ht
            rw [Ctx.isTransparent_thereC, Ctx.isTransparent_thereC] at ht
            show (Γ.consC (CapBound.inst C)).IsTransparent (BVar.there y)
            rwa [Ctx.isTransparent_thereC]
  def_ := by
    intro x l W hW
    cases x with
    | there x =>
        cases x with
        | there y =>
            unfold Ctx.scopeInst at hW
            rw [Ctx.lookupDef_thereC, Ctx.lookupDef_thereC] at hW
            cases hd : Γ.lookupDef y l with
            | none => rw [hd] at hW; simp at hW
            | some W0 =>
                rw [hd] at hW
                have hWe : W = (W0↑)↑ := by simpa using hW.symm
                subst hWe
                show (Γ.consC (CapBound.inst C)).lookupDef (.there y) l
                  = some (((W0↑)↑).subst Subst.instRoot)
                rw [Shape.weakenC_two_instRoot, Ctx.lookupDef_thereC, hd]
                rfl
  defC := by
    intro x l C0 hC
    cases x with
    | there x =>
        cases x with
        | there y =>
            unfold Ctx.scopeInst at hC
            rw [Ctx.lookupDefC_thereC, Ctx.lookupDefC_thereC] at hC
            cases hd : Γ.lookupDefC y l with
            | none => rw [hd] at hC; simp at hC
            | some C1 =>
                rw [hd] at hC
                have hCe : C0 = (C1↑)↑ := by simpa using hC.symm
                subst hCe
                show (Γ.consC (CapBound.inst C)).lookupDefC (.there y) l
                  = some (((C1↑)↑).subst Subst.instRoot)
                rw [CaptureSet.weakenC_two_instRoot, Ctx.lookupDefC_thereC, hd]
                rfl
  fields := by
    intro x Fs hFs
    cases x with
    | there x =>
        cases x with
        | there y =>
            unfold Ctx.scopeInst at hFs
            rw [Ctx.lookupFields_thereC, Ctx.lookupFields_thereC] at hFs
            show (Γ.consC (CapBound.inst C)).lookupFields (BVar.there y) = some Fs
            rwa [Ctx.lookupFields_thereC]
  capRoot := by
    intro r hr
    rcases Ctx.isRoot_consC_cases hr with rfl | ⟨r₁, rfl, hr₁⟩
    · exact Bool.noConfusion hr
    · rcases Ctx.isRoot_consC_cases hr₁ with rfl | ⟨r₀, rfl, hr₀⟩
      · rfl
      · rw [CapAtom.weakenC_two_instRoot]
        show (Γ.consC (CapBound.inst C)).isRootB (CapAtom.weaken (k := .cap) r₀) = true
        rw [Ctx.isRootB_weakenC]
        exact hr₀
  capLvl := fun e r _ _ =>
    Ctx.lvlLe_of_root?_none
      (by rw [Ctx.root?_consC_of_not_root Γ (CapBound.inst C) rfl, hΓ]; rfl) _ _
  capInner :=
    Ctx.lvlLe_of_root?_none
      (by rw [Ctx.root?_consC_of_not_root Γ (CapBound.inst C) rfl, hΓ]; rfl) _ _
  capInst := by
    intro a C0 hI
    rcases Ctx.instOf_consC_cases hI with ⟨C₁, rfl, rfl, hbi⟩ | ⟨a₁, C₁, rfl, rfl, h₁⟩
    · have hC : C₁ = C↑ := by simpa [CapBound.instSet?] using hbi.symm
      subst hC
      rw [CaptureSet.weakenC_two_instRoot]
      rfl
    · rcases Ctx.instOf_consC_cases h₁ with ⟨C₀, rfl, rfl, hbi⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
      · simp [CapBound.instSet?] at hbi
      · rw [CapAtom.weakenC_two_instRoot, CaptureSet.weakenC_two_instRoot]
        exact h₀.weakenC (.inst C)
  capCls := by
    intro a cl hC
    rcases Ctx.clsOf_consC_cases hC with ⟨rfl, hbc⟩ | ⟨a₁, rfl, h₁⟩
    · simp [CapBound.clsOf?] at hbc
    · rcases Ctx.clsOf_consC_cases h₁ with ⟨rfl, hbc⟩ | ⟨a₀, rfl, h₀⟩
      · simp [CapBound.clsOf?] at hbc
      · rw [CapAtom.weakenC_two_instRoot]
        exact h₀.weakenC (.inst C)
  capSet := by
    intro a C0 hS
    rcases Ctx.setOf_consC_cases hS with ⟨C₁, rfl, rfl, hbs⟩ | ⟨a₁, C₁, rfl, rfl, h₁⟩
    · have hC : C₁ = C↑ := by simpa [CapBound.setOf?] using hbs.symm
      subst hC
      rw [CaptureSet.weakenC_two_instRoot]
      rfl
    · rcases Ctx.setOf_consC_cases h₁ with ⟨C₀, rfl, rfl, hbs⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
      · simp [CapBound.setOf?] at hbs
      · rw [CapAtom.weakenC_two_instRoot, CaptureSet.weakenC_two_instRoot]
        exact h₀.weakenC (.inst C)
  capProjFree := by
    intro κ
    cases κ with
    | here => rfl
    | there κ0 =>
        cases κ0 with
        | here => rfl
        | there κ1 => rfl

/-- And the entering substitution of a projection. -/
theorem Subst.Typed.enterObj {Γ : Ctx s} {T : Ty s} {W : Witnesses (s,x)}
    {Wc : CapWitnesses (s,x)} {ls : List Label} {y : BVar s .var}
    (hΓ : Γ.root? = none)
    (hy : Γ.lookupTy y = T)
    (hdef : ∀ l, Γ.lookupDef y l = some ((W.get l)⟦y⟧))
    (hdefC : ∀ l, Γ.lookupDefC y l = some ((Wc.get l)⟦y⟧))
    (hfields : Γ.lookupFields y = some ls) :
    Subst.Typed (Γ.objBody T W Wc ls) (Subst.enterObj y) Γ :=
  Subst.Typed.enterObjAux hΓ hy hdef hdefC hfields

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
  simpa [Tm.substAtom, Ty.substVar, ETy.subst] using this

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
  simpa only [Tm.uses_substAtom, CaptureSet.subst, CaptureSet.rename_subst_weaken] using this

/-! ## The self cast, and what a term binding hides from the capture spine

These live here rather than beside `Subst.Typed.selfCast` in
`Preservation.lean`, because `FormAlgebra.lean` reads them and nothing else
of the machine, so it imports this module in place of `Preservation`. -/

/-! ## The two substitution instances the machine uses -/

@[simp] theorem Subst.selfCast_var_there {s : Sig} (E : LeCo (s,x)) (z : BVar s .var) :
    (Subst.selfCast E).var (.there z) = .var (.there z) := rfl

@[simp] theorem Subst.selfCast_cvar_there {s : Sig} (E : LeCo (s,x)) (κ : BVar s .cap) :
    (Subst.selfCast E).cvar (.there κ) = .cvar (.there κ) := rfl

@[simp] theorem Subst.selfCast_rootVar {s : Sig} (E : LeCo (s,x)) (y : BVar (s,x) .var) :
    (Subst.selfCast E).rootVar y = y := by
  cases y <;> rfl

/-- The self cast is invisible to the type sort: it changes a term variable
into a cast around it, and a type reads only the root of that cast.  This is
the substitution reading of `Subst.selfCast_root` of the vanilla line. -/
theorem Subst.selfCast_core {s : Sig} (E : LeCo (s,x)) :
    (Subst.selfCast E).core = Subst.ofRename Rename.id := by
  apply Subst.funext'
  · intro y; cases y <;> rfl
  · intro κ; cases κ with | there y => rfl

@[simp] theorem CapAtom.subst_selfCast {s : Sig} (a : CapAtom (s,x)) (E : LeCo (s,x)) :
    a.subst (Subst.selfCast E) = a := by
  rw [CapAtom.subst_core, Subst.selfCast_core, CapAtom.subst_ofRename, CapAtom.rename_id]

@[simp] theorem CaptureSet.subst_selfCast {s : Sig} (C : CaptureSet (s,x)) (E : LeCo (s,x)) :
    C.subst (Subst.selfCast E) = C := by
  rw [CaptureSet.subst_core, Subst.selfCast_core, CaptureSet.subst_ofRename, CaptureSet.rename_id]

@[simp] theorem Shape.subst_selfCast {s : Sig} (S : Shape (s,x)) (E : LeCo (s,x)) :
    S.subst (Subst.selfCast E) = S := by
  rw [Shape.subst_core, Subst.selfCast_core, Shape.subst_ofRename, Shape.rename_id]

@[simp] theorem Ty.subst_selfCast {s : Sig} (T : Ty (s,x)) (E : LeCo (s,x)) :
    T.subst (Subst.selfCast E) = T := by
  rw [Ty.subst_core, Subst.selfCast_core, Ty.subst_ofRename, Ty.rename_id]

/-- The answer sort reads the self cast exactly as the type sort does: an
answer names a term variable only through its root. -/
@[simp] theorem ETy.subst_selfCast {s : Sig} (A : ETy (s,x)) (E : LeCo (s,x)) :
    A.subst (Subst.selfCast E) = A := by
  rw [ETy.subst_core, Subst.selfCast_core, ETy.subst_ofRename, ETy.rename_id]

/-! ### A term binding is invisible to the capture spine

`Ctx.lookupCap`, `Ctx.root?` and `Ctx.lvl` step past a term binder without
reading it, so two contexts that append different bindings to the same prefix
have the same roots and the same levels.  This is what the self-cast
substitution below needs for its three capture fields, since it changes only
the binding at the self. -/

theorem Ctx.lookupCap_cons_eq (Γ : Ctx s) (b b' : Binding s) :
    ∀ κ : BVar (s,x) .cap, (Γ.cons b).lookupCap κ = (Γ.cons b').lookupCap κ
  | .there _ => rfl

theorem Ctx.lvl_cons_eq (Γ : Ctx s) (b b' : Binding s) {k : Kind} (z : BVar (s,x) k) :
    (Γ.cons b).lvl z = (Γ.cons b').lvl z := by
  cases z <;> rfl

theorem Ctx.lvlAtom_cons_eq (Γ : Ctx s) (b b' : Binding s) (a : CapAtom (s,x)) :
    (Γ.cons b).lvlAtom a = (Γ.cons b').lvlAtom a := by
  induction a with
  | top => rfl
  | var z => exact Ctx.lvl_cons_eq Γ b b' z
  | cvar z => exact Ctx.lvl_cons_eq Γ b b' z
  | name z _ => exact Ctx.lvl_cons_eq Γ b b' z
  | proj a φ ih => exact ih

theorem Ctx.isRootB_cons_eq (Γ : Ctx s) (b b' : Binding s) (a : CapAtom (s,x)) :
    (Γ.cons b).isRootB a = (Γ.cons b').isRootB a := by
  cases a with
  | top => rfl
  | var _ => rfl
  | name _ _ => rfl
  | proj _ _ => rfl
  | cvar κ => exact congrArg CapBound.isRoot (Ctx.lookupCap_cons_eq Γ b b' κ)

theorem Ctx.lvlLeB_cons_eq (Γ : Ctx s) (b b' : Binding s) (e r : CapAtom (s,x)) :
    (Γ.cons b).lvlLeB e r = (Γ.cons b').lvlLeB e r := by
  unfold Ctx.lvlLeB
  rw [Ctx.lvlAtom_cons_eq Γ b b' e]

theorem Ctx.rootAtom_cons_eq (Γ : Ctx s) (b b' : Binding s) :
    (Γ.cons b).rootAtom = (Γ.cons b').rootAtom := rfl

/-- And so do the instance facts, which read the same `lookupCap`.  This is
the `capInst` field of every self-cast substitution instance. -/
theorem Ctx.instOf_cons_eq (Γ : Ctx s) (b b' : Binding s) (a : CapAtom (s,x))
    (C : CaptureSet (s,x)) : (Γ.cons b).InstOf a C ↔ (Γ.cons b').InstOf a C := by
  cases a with
  | top => exact Iff.rfl
  | var _ => exact Iff.rfl
  | name _ _ => exact Iff.rfl
  | proj _ _ => exact Iff.rfl
  | cvar κ =>
      show ((Γ.cons b).lookupCap κ).instSet? = some C ↔ _
      rw [Ctx.lookupCap_cons_eq Γ b b' κ]
      exact Iff.rfl

/-- The declared classifier of a capture binder reads the same `lookupCap`,
so a term binder in front of it makes no difference.  This is the `capCls`
field of every self-cast substitution instance. -/
theorem Ctx.clsOf_cons_eq (Γ : Ctx s) (b b' : Binding s) (a : CapAtom (s,x))
    (cl : Cls.Classifier) : (Γ.cons b).ClsOf a cl ↔ (Γ.cons b').ClsOf a cl := by
  cases a with
  | top => exact Iff.rfl
  | var _ => exact Iff.rfl
  | name _ _ => exact Iff.rfl
  | proj _ _ => exact Iff.rfl
  | cvar κ =>
      show ((Γ.cons b).lookupCap κ).clsOf? = some cl ↔ _
      rw [Ctx.lookupCap_cons_eq Γ b b' κ]
      exact Iff.rfl

/-- And so does the declared set of a capture binder.  This is the `capSet`
field of every self-cast substitution instance. -/
theorem Ctx.setOf_cons_eq (Γ : Ctx s) (b b' : Binding s) (a : CapAtom (s,x))
    (C : CaptureSet (s,x)) : (Γ.cons b).SetOf a C ↔ (Γ.cons b').SetOf a C := by
  cases a with
  | top => exact Iff.rfl
  | var _ => exact Iff.rfl
  | name _ _ => exact Iff.rfl
  | proj _ _ => exact Iff.rfl
  | cvar κ =>
      show ((Γ.cons b).lookupCap κ).setOf? = some C ↔ _
      rw [Ctx.lookupCap_cons_eq Γ b b' κ]
      exact Iff.rfl

end FCdot

end Classifiers
