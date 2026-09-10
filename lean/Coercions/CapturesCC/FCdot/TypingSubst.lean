import Coercions.CapturesCC.FCdot.TypingRename

namespace CapturesCC

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
  cases a <;> rfl

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
      rw [Ty.subst_core S σ.liftC, Ty.subst_core T σ.liftC.lift, Subst.liftC_core,
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
  rw [Ty.rename_subst, Ty.subst_rename, ← Subst.compRename_lift, ← Subst.compRen_lift,
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
    cases e with
    | top => rfl
    | var x => exact Ctx.root?_none Γ x h
    | cvar κ => exact Ctx.root?_none Γ κ h
    | name x l => exact Ctx.root?_none Γ x h
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
    e = .var .here ∨ (∃ l, e = .name .here l) ∨ ∃ e₀ : CapAtom s, e = e₀.weaken := by
  cases e with
  | top => exact Or.inr (Or.inr ⟨.top, rfl⟩)
  | var x => cases x with
      | here => exact Or.inl rfl
      | there x0 => exact Or.inr (Or.inr ⟨.var x0, rfl⟩)
  | name x l => cases x with
      | here => exact Or.inr (Or.inl ⟨l, rfl⟩)
      | there x0 => exact Or.inr (Or.inr ⟨.name x0 l, rfl⟩)
  | cvar k => cases k with
      | there k0 => exact Or.inr (Or.inr ⟨.cvar k0, rfl⟩)

/-- And of a capture-extended signature: the new binder, or an older atom
weakened. -/
theorem CapAtom.consC_cases (e : CapAtom (s,c)) :
    e = .cvar .here ∨ ∃ e₀ : CapAtom s, e = e₀.weaken := by
  cases e with
  | top => exact Or.inr ⟨.top, rfl⟩
  | var x => cases x with
      | there x0 => exact Or.inr ⟨.var x0, rfl⟩
  | name x l => cases x with
      | there x0 => exact Or.inr ⟨.name x0 l, rfl⟩
  | cvar k => cases k with
      | here => exact Or.inl rfl
      | there k0 => exact Or.inr ⟨.cvar k0, rfl⟩

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
  rcases CapAtom.cons_cases e with rfl | ⟨l, rfl⟩ | ⟨e₀, rfl⟩
  · exact Ctx.lvlLe_here_step_subst hRoot hLvl hInner b b' r₀ hr₀ hl
  · exact Ctx.lvlLe_here_step_subst hRoot hLvl hInner b b' r₀ hr₀ hl
  · rw [CapAtom.weaken_subst]
    exact Ctx.lvlLe_weaken_step_subst hLvl b' e₀ r₀ hr₀ hl

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
    rcases CapAtom.consC_cases e with rfl | ⟨e₀, rfl⟩
    · cases hb : b.isRoot with
      | true => exact absurd hl (Ctx.not_lvlLe_consC_root_here hb r₀)
      | false =>
          exact Ctx.lvlLe_hereC_step_subst hRoot hLvl hInner b hb b' (by rw [hbb]; exact hb)
            r₀ hr₀ hl
    · rw [CapAtom.weaken_substC]
      exact Ctx.lvlLe_weakenC_step_subst hLvl b' e₀ r₀ hr₀ hl

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
    rcases CapAtom.consC_cases e with rfl | ⟨e₀, rfl⟩
    · exact absurd hl (Ctx.not_lvlLe_consC_root_here rfl r₀)
    · rw [CapAtom.weaken_substC]
      exact Ctx.lvlLe_weakenC_step_subst hLvl .root e₀ r₀ hr₀ hl


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
        show CapturesCC.FCdot.Atom.weaken (Atom.var (τ.rootVar (σ.rootVar x)))
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
        show CapturesCC.FCdot.Atom.weaken (Atom.var (τ.rootVar (σ.rootVar x)))
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
  cases a <;> rfl

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
      rw [Ty.subst_subst S σ.liftC τ.liftC, Ty.subst_subst T σ.liftC.lift τ.liftC.lift,
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
        show CapturesCC.FCdot.Atom.var (σ.rootVar x)
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
        show CapturesCC.FCdot.Atom.var (σ.rootVar b.root)
          = Atom.var ((Subst.arg (b.subst σ)).rootVar (σ.liftC.lift.rootVar BVar.here))
        rw [Subst.lift_rootVar_here]
        show CapturesCC.FCdot.Atom.var (σ.rootVar b.root) = Atom.var (b.subst σ).root
        rw [Atom.root_subst]
    | there x =>
        cases x with
        | there x =>
            show CapturesCC.FCdot.Atom.var (σ.rootVar x)
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
  capRoot := fun r hr => Ctx.isRoot_lift_subst h.capRoot (b.subst σ) r hr
  capLvl := fun e r hr hl =>
    Ctx.lvlLe_lift_subst h.capRoot h.capLvl h.capInner b (b.subst σ) e r hr hl
  capInner := Ctx.capInner_lift_subst h.capInner b (b.subst σ)

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
    rcases CapAtom.cons_cases e with rfl | ⟨l, rfl⟩ | ⟨e₀, rfl⟩
    · exact hhere a.root hl
    · exact hhere a.root hl
    · rw [CapAtom.weaken_subst_single]
      exact (Ctx.lvlLe_weaken_iff Γ (Binding.opaque T) e₀ r₀).mp hl
  capInner := by
    rw [Ctx.rootAtom_cons Γ (Binding.opaque T), CapAtom.weaken_subst_single]
    exact Ctx.LvlLe.refl_of_root (Ctx.rootAtom_isRoot Γ)

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

/-- A typed substitution passes under a scope. -/
theorem scope {Γ : Ctx s1} {σ : Subst s1 s2} {Γ' : Ctx s2} (h : Subst.Typed Γ σ Γ') :
    Subst.Typed Γ.scope σ.liftC.liftC Γ'.scope :=
  (h.consRoot).liftC .star rfl

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
      have hf' := LeCo.HasType.subst (hσ.body _) hf
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

end

/-! ## Terms, values, fields -/

mutual

theorem Tm.HasType.subst {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {σ : Subst s1 s2}
    {t : Tm s1} {T : Ty s1} (hσ : Subst.Typed Γ σ Γ') (h : Γ ⊢ t : T) :
    Γ' ⊢ (t.subst σ) : (T.subst σ) := by
  match h with
  | .atom ha => exact .atom (ha.subst hσ)
  | .val hv => exact .val (hv.subst hσ)
  | .app ha hb =>
      have ha' := ha.subst hσ
      have hb' := hb.subst hσ
      simp only [Ty.subst, Shape.subst] at ha'
      rw [Ty.singleC_subst] at hb'
      simp only [CapAtom.subst, ← Atom.root_subst] at hb'
      have := Tm.HasType.app ha' hb'
      simpa only [Tm.subst, Ty.arg_subst] using this
  | @Tm.HasType.proj _ _ a T hh l ha hhh =>
      have := Tm.HasType.proj (a := a.subst σ) (ha.subst hσ)
        (by rw [Atom.root_subst]; exact hhh.subst hσ)
      simpa [Tm.subst, Ty.subst, Shape.subst, CaptureSet.subst, CaptureSet.subst_union, CapAtom.subst,
        Atom.root_subst] using this
  | .let ht hu hf =>
      refine .let (ht.subst hσ) ?_ ?_
      · have := hu.subst (hσ.lift _)
        simpa [Ty.weaken_subst] using this
      · have := CapCo.HasType.subst (hσ.lift _) hf
        simpa only [Tm.uses_subst, CaptureSet.weaken_subst] using this
  | .cast ht he => exact .cast (ht.subst hσ) (LeCo.HasType.subst hσ he)
  | .unbox ha hf =>
      have := Tm.HasType.unbox (by simpa [Ty.subst, Shape.subst] using ha.subst hσ)
        (by simpa using CapCo.HasType.subst hσ hf)
      simpa [Tm.subst, Ty.subst] using this

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
      rcases CapAtom.consC_cases e with rfl | ⟨e₀, rfl⟩
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
      rcases CapAtom.cons_cases e with rfl | ⟨l, rfl⟩ | ⟨e₁, rfl⟩
      · exact hhere hl _
      · exact hhere hl _
      · rcases CapAtom.consC_cases e₁ with rfl | ⟨e₀, rfl⟩
        · exact hhere hl _
        · rw [CapAtom.weaken_weaken_subst_arg]
          exact (Ctx.lvlLe_weakenC_iff Γ CapBound.star e₀ r₀).mp
            ((Ctx.lvlLe_weaken_iff (Γ.consC CapBound.star) (Binding.opaque T)
              (CapAtom.weaken (k := .cap) e₀) (CapAtom.weaken (k := .cap) r₀)).mp hl)
  capInner := by
    show Γ.LvlLe Γ.rootAtom
      ((((Γ.consC CapBound.star).cons (Binding.opaque T)).rootAtom).subst (Subst.arg b))
    rw [Ctx.rootAtom_cons, Ctx.rootAtom_consC Γ CapBound.star rfl,
      CapAtom.weaken_weaken_subst_arg]
    exact Ctx.LvlLe.refl_of_root (Ctx.rootAtom_isRoot Γ)


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

/-- The same at `Ctx.scope`, which is the context the `pi` rule opens. -/
theorem Subst.Typed.enterC {Γ : Ctx s} {b : Atom s} (hΓ : Γ.root? = none) :
    Subst.Typed Γ.scope (Subst.enterC b) Γ :=
  Subst.Typed.enterCAux hΓ

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
  simpa only [Tm.uses_substAtom, CaptureSet.subst, CaptureSet.rename_subst_weaken] using this

end FCdot

end CapturesCC
