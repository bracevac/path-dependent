import Coercions.Captures.FCdot.Syntax

namespace Captures

/-!
# Renaming algebra for FCdot

The standard functorial laws for renaming (`rename_id`, `rename_comp`) on every
syntactic family, the interaction of `Atom.root` with renaming and
substitution, and the facts relating substitutions to renamings that the
typing metatheory needs.

Each family is a mutual inductive, so the proofs come in `mutual` blocks of
structurally recursive theorems that mirror the `rename` definitions.  Every
lemma about weakening is stated for an arbitrary binder kind, so that passing
under a capture binder is an instance of passing under a term binder.
-/

namespace FCdot

/-! ## `rename_id` and `rename_comp` for capture atoms and capture sets -/

@[simp] theorem CapAtom.rename_id {s : Sig} (a : CapAtom s) : a.rename Rename.id = a := by
  cases a <;> simp [CapAtom.rename]

@[simp] theorem CapAtom.rename_comp {s1 s2 s3 : Sig} (a : CapAtom s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (a.rename ρ).rename ρ' = a.rename (ρ.comp ρ') := by
  cases a <;> simp [CapAtom.rename]

@[simp] theorem CaptureSet.rename_id {s : Sig} :
    ∀ C : CaptureSet s, C.rename Rename.id = C
  | [] => rfl
  | a :: C => by
      show a.rename Rename.id :: CaptureSet.rename C Rename.id = a :: C
      rw [CapAtom.rename_id, CaptureSet.rename_id C]

@[simp] theorem CaptureSet.rename_comp {s1 s2 s3 : Sig} :
    ∀ (C : CaptureSet s1) (ρ : Rename s1 s2) (ρ' : Rename s2 s3),
      (C.rename ρ).rename ρ' = C.rename (ρ.comp ρ')
  | [], _, _ => rfl
  | a :: C, ρ, ρ' => by
      show (a.rename ρ).rename ρ' :: (CaptureSet.rename C ρ).rename ρ'
        = a.rename (ρ.comp ρ') :: CaptureSet.rename C (ρ.comp ρ')
      rw [CapAtom.rename_comp, CaptureSet.rename_comp C ρ ρ']

/-! ## `rename_id` for shapes, types, propositions, telescopes -/

mutual

@[simp] theorem Shape.rename_id {s : Sig} (S : Shape s) : S.rename Rename.id = S := by
  match S with
  | .bot => simp [Shape.rename]
  | .sel x ℓ => simp [Shape.rename]
  | .pi S T => simp [Shape.rename, Rename.lift_id, Ty.rename_id S, Ty.rename_id T]
  | .obj Tel => simp [Shape.rename, Rename.lift_id, Telescope.rename_id Tel]
  | .box T => simp [Shape.rename, Ty.rename_id T]

@[simp] theorem Ty.rename_id {s : Sig} (T : Ty s) : T.rename Rename.id = T := by
  match T with
  | .capt C S => simp [Ty.rename, CaptureSet.rename_id C, Shape.rename_id S]

@[simp] theorem Proposition.rename_id {s : Sig} (P : Proposition s) :
    P.rename Rename.id = P := by
  match P with
  | .le S T => simp [Proposition.rename, Shape.rename_id S, Shape.rename_id T]
  | .eq S T => simp [Proposition.rename, Shape.rename_id S, Shape.rename_id T]
  | .has ℓ => simp [Proposition.rename]
  | .bnd T => simp [Proposition.rename, Shape.rename_id T]
  | .leC C D => simp [Proposition.rename, CaptureSet.rename_id C, CaptureSet.rename_id D]
  | .eqC C D => simp [Proposition.rename, CaptureSet.rename_id C, CaptureSet.rename_id D]

@[simp] theorem Telescope.rename_id {s : Sig} (Tel : Telescope s) :
    Tel.rename Rename.id = Tel := by
  match Tel with
  | .nil => simp [Telescope.rename]
  | .cons Tel P => simp [Telescope.rename, Telescope.rename_id Tel, Proposition.rename_id P]

end

/-! ## `rename_comp` for shapes, types, propositions, telescopes -/

mutual

@[simp] theorem Shape.rename_comp {s1 s2 s3 : Sig} (S : Shape s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (S.rename ρ).rename ρ' = S.rename (ρ.comp ρ') := by
  match S with
  | .bot => simp [Shape.rename]
  | .sel x ℓ => simp [Shape.rename]
  | .pi S T =>
      simp [Shape.rename, Rename.lift_comp, Ty.rename_comp S, Ty.rename_comp T]
  | .obj Tel =>
      simp [Shape.rename, Rename.lift_comp, Telescope.rename_comp Tel]
  | .box T => simp [Shape.rename, Ty.rename_comp T]

@[simp] theorem Ty.rename_comp {s1 s2 s3 : Sig} (T : Ty s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (T.rename ρ).rename ρ' = T.rename (ρ.comp ρ') := by
  match T with
  | .capt C S => simp [Ty.rename, CaptureSet.rename_comp C, Shape.rename_comp S]

@[simp] theorem Proposition.rename_comp {s1 s2 s3 : Sig} (P : Proposition s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (P.rename ρ).rename ρ' = P.rename (ρ.comp ρ') := by
  match P with
  | .le S T => simp [Proposition.rename, Shape.rename_comp S, Shape.rename_comp T]
  | .eq S T => simp [Proposition.rename, Shape.rename_comp S, Shape.rename_comp T]
  | .has ℓ => simp [Proposition.rename]
  | .bnd T => simp [Proposition.rename, Shape.rename_comp T]
  | .leC C D => simp [Proposition.rename, CaptureSet.rename_comp C, CaptureSet.rename_comp D]
  | .eqC C D => simp [Proposition.rename, CaptureSet.rename_comp C, CaptureSet.rename_comp D]

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

@[simp] theorem ShapeCo.rename_id {s : Sig} (e : ShapeCo s) : e.rename Rename.id = e := by
  match e with
  | .refl T => simp [ShapeCo.rename]
  | .trans e f => simp [ShapeCo.rename, ShapeCo.rename_id e, ShapeCo.rename_id f]
  | .top T => simp [ShapeCo.rename]
  | .bot T => simp [ShapeCo.rename]
  | .eqToLe φ => simp [ShapeCo.rename, EqCo.rename_id φ]
  | .pi e f => simp [ShapeCo.rename, Rename.lift_id, LeCo.rename_id e, LeCo.rename_id f]
  | .obj Tel m =>
      simp [ShapeCo.rename, Rename.lift_id, Morphism.rename_id m, Telescope.rename_id Tel]
  | .pair Tel₁ Tel₂ e f =>
      simp [ShapeCo.rename, Rename.lift_id, Telescope.rename_id Tel₁, Telescope.rename_id Tel₂,
        ShapeCo.rename_id e, ShapeCo.rename_id f]
  | .bound Tel i => simp [ShapeCo.rename, Rename.lift_id, Telescope.rename_id Tel]
  | .intoBnd e => simp [ShapeCo.rename, ShapeCo.rename_id e]
  | .member a e i => simp [ShapeCo.rename, Atom.rename_id a, ShapeCo.rename_id e]
  | .boxed d => simp [ShapeCo.rename, LeCo.rename_id d]

@[simp] theorem CapCo.rename_id {s : Sig} (f : CapCo s) : f.rename Rename.id = f := by
  match f with
  | .refl C => simp [CapCo.rename]
  | .trans f g => simp [CapCo.rename, CapCo.rename_id f, CapCo.rename_id g]
  | .elem C D => simp [CapCo.rename]
  | .union f g => simp [CapCo.rename, CapCo.rename_id f, CapCo.rename_id g]
  | .capvar a => simp [CapCo.rename, Atom.rename_id a]
  | .member a e i => simp [CapCo.rename, Atom.rename_id a, ShapeCo.rename_id e]
  | .eqToLe φ => simp [CapCo.rename, CapEq.rename_id φ]

@[simp] theorem CapEq.rename_id {s : Sig} (φ : CapEq s) : φ.rename Rename.id = φ := by
  match φ with
  | .refl C => simp [CapEq.rename]
  | .symm φ => simp [CapEq.rename, CapEq.rename_id φ]
  | .trans φ ψ => simp [CapEq.rename, CapEq.rename_id φ, CapEq.rename_id ψ]
  | .defC x ℓ => simp [CapEq.rename]
  | .member a e i => simp [CapEq.rename, Atom.rename_id a, ShapeCo.rename_id e]

@[simp] theorem CapStep.rename_id {s : Sig} (st : CapStep s) : st.rename Rename.id = st := by
  match st with
  | .closed f => simp [CapStep.rename, CapCo.rename_id f]
  | .incl C D => simp [CapStep.rename, Rename.lift_id]

@[simp] theorem SideC.rename_id {s : Sig} (q : SideC s) : q.rename Rename.id = q := by
  match q with
  | .nil => simp [SideC.rename]
  | .cons st q => simp [SideC.rename, CapStep.rename_id st, SideC.rename_id q]

@[simp] theorem LeCo.rename_id {s : Sig} (d : LeCo s) : d.rename Rename.id = d := by
  match d with
  | .capt e f => simp [LeCo.rename, ShapeCo.rename_id e, CapCo.rename_id f]

@[simp] theorem EqCo.rename_id {s : Sig} (φ : EqCo s) : φ.rename Rename.id = φ := by
  match φ with
  | .refl T => simp [EqCo.rename]
  | .symm φ => simp [EqCo.rename, EqCo.rename_id φ]
  | .trans φ ψ => simp [EqCo.rename, EqCo.rename_id φ, EqCo.rename_id ψ]
  | .def x ℓ => simp [EqCo.rename]
  | .member a e i => simp [EqCo.rename, Atom.rename_id a, ShapeCo.rename_id e]

@[simp] theorem Has.rename_id {s : Sig} (h : Has s) : h.rename Rename.id = h := by
  match h with
  | .member a e i => simp [Has.rename, Atom.rename_id a, ShapeCo.rename_id e]
  | .field ℓ => simp [Has.rename]

@[simp] theorem Side.rename_id {s : Sig} (σ : Side s) : σ.rename Rename.id = σ := by
  match σ with
  | .none => simp [Side.rename]
  | .some e => simp [Side.rename, ShapeCo.rename_id e]

@[simp] theorem Morphism.rename_id {s : Sig} (m : Morphism s) : m.rename Rename.id = m := by
  match m with
  | .nil => simp [Morphism.rename]
  | .le m pre h post =>
      simp [Morphism.rename, Morphism.rename_id m, Side.rename_id pre, Side.rename_id post]
  | .eq m j b => simp [Morphism.rename, Morphism.rename_id m]
  | .has m j => simp [Morphism.rename, Morphism.rename_id m]
  | .bnd m e => simp [Morphism.rename, Morphism.rename_id m, ShapeCo.rename_id e]
  | .leC m q h q' =>
      simp [Morphism.rename, Morphism.rename_id m, SideC.rename_id q, SideC.rename_id q']
  | .eqC m j b => simp [Morphism.rename, Morphism.rename_id m]

@[simp] theorem Atom.rename_id {s : Sig} (a : Atom s) : a.rename Rename.id = a := by
  match a with
  | .var x => simp [Atom.rename]
  | .cast a e => simp [Atom.rename, Atom.rename_id a, LeCo.rename_id e]
  | .foldSelf Tel a =>
      simp [Atom.rename, Rename.lift_id, Atom.rename_id a, Telescope.rename_id Tel]
  | .unfoldSelf a => simp [Atom.rename, Atom.rename_id a]
  | .both Tel₁ Tel₂ a b =>
      simp [Atom.rename, Rename.lift_id, Telescope.rename_id Tel₁, Telescope.rename_id Tel₂,
        Atom.rename_id a, Atom.rename_id b]
  | .recap a f => simp [Atom.rename, Atom.rename_id a, CapCo.rename_id f]

end

/-! ## `rename_comp` for evidence and atoms -/

mutual

@[simp] theorem ShapeCo.rename_comp {s1 s2 s3 : Sig} (e : ShapeCo s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (e.rename ρ).rename ρ' = e.rename (ρ.comp ρ') := by
  match e with
  | .refl T => simp [ShapeCo.rename]
  | .trans e f => simp [ShapeCo.rename, ShapeCo.rename_comp e, ShapeCo.rename_comp f]
  | .top T => simp [ShapeCo.rename]
  | .bot T => simp [ShapeCo.rename]
  | .eqToLe φ => simp [ShapeCo.rename, EqCo.rename_comp φ]
  | .pi e f =>
      simp [ShapeCo.rename, Rename.lift_comp, LeCo.rename_comp e, LeCo.rename_comp f]
  | .obj Tel m =>
      simp [ShapeCo.rename, Rename.lift_comp, Morphism.rename_comp m, Telescope.rename_comp Tel]
  | .pair Tel₁ Tel₂ e f =>
      simp [ShapeCo.rename, Rename.lift_comp, Telescope.rename_comp Tel₁,
        Telescope.rename_comp Tel₂, ShapeCo.rename_comp e, ShapeCo.rename_comp f]
  | .bound Tel i => simp [ShapeCo.rename, Rename.lift_comp, Telescope.rename_comp Tel]
  | .intoBnd e => simp [ShapeCo.rename, ShapeCo.rename_comp e]
  | .member a e i => simp [ShapeCo.rename, Atom.rename_comp a, ShapeCo.rename_comp e]
  | .boxed d => simp [ShapeCo.rename, LeCo.rename_comp d]

@[simp] theorem CapCo.rename_comp {s1 s2 s3 : Sig} (f : CapCo s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (f.rename ρ).rename ρ' = f.rename (ρ.comp ρ') := by
  match f with
  | .refl C => simp [CapCo.rename]
  | .trans f g => simp [CapCo.rename, CapCo.rename_comp f, CapCo.rename_comp g]
  | .elem C D => simp [CapCo.rename]
  | .union f g => simp [CapCo.rename, CapCo.rename_comp f, CapCo.rename_comp g]
  | .capvar a => simp [CapCo.rename, Atom.rename_comp a]
  | .member a e i => simp [CapCo.rename, Atom.rename_comp a, ShapeCo.rename_comp e]
  | .eqToLe φ => simp [CapCo.rename, CapEq.rename_comp φ]

@[simp] theorem CapEq.rename_comp {s1 s2 s3 : Sig} (φ : CapEq s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (φ.rename ρ).rename ρ' = φ.rename (ρ.comp ρ') := by
  match φ with
  | .refl C => simp [CapEq.rename]
  | .symm φ => simp [CapEq.rename, CapEq.rename_comp φ]
  | .trans φ ψ => simp [CapEq.rename, CapEq.rename_comp φ, CapEq.rename_comp ψ]
  | .defC x ℓ => simp [CapEq.rename]
  | .member a e i => simp [CapEq.rename, Atom.rename_comp a, ShapeCo.rename_comp e]

@[simp] theorem CapStep.rename_comp {s1 s2 s3 : Sig} (st : CapStep s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (st.rename ρ).rename ρ' = st.rename (ρ.comp ρ') := by
  match st with
  | .closed f => simp [CapStep.rename, CapCo.rename_comp f]
  | .incl C D => simp [CapStep.rename, Rename.lift_comp]

@[simp] theorem SideC.rename_comp {s1 s2 s3 : Sig} (q : SideC s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (q.rename ρ).rename ρ' = q.rename (ρ.comp ρ') := by
  match q with
  | .nil => simp [SideC.rename]
  | .cons st q => simp [SideC.rename, CapStep.rename_comp st, SideC.rename_comp q]

@[simp] theorem LeCo.rename_comp {s1 s2 s3 : Sig} (d : LeCo s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (d.rename ρ).rename ρ' = d.rename (ρ.comp ρ') := by
  match d with
  | .capt e f => simp [LeCo.rename, ShapeCo.rename_comp e, CapCo.rename_comp f]

@[simp] theorem EqCo.rename_comp {s1 s2 s3 : Sig} (φ : EqCo s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (φ.rename ρ).rename ρ' = φ.rename (ρ.comp ρ') := by
  match φ with
  | .refl T => simp [EqCo.rename]
  | .symm φ => simp [EqCo.rename, EqCo.rename_comp φ]
  | .trans φ ψ => simp [EqCo.rename, EqCo.rename_comp φ, EqCo.rename_comp ψ]
  | .def x ℓ => simp [EqCo.rename]
  | .member a e i => simp [EqCo.rename, Atom.rename_comp a, ShapeCo.rename_comp e]

@[simp] theorem Has.rename_comp {s1 s2 s3 : Sig} (h : Has s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (h.rename ρ).rename ρ' = h.rename (ρ.comp ρ') := by
  match h with
  | .member a e i => simp [Has.rename, Atom.rename_comp a, ShapeCo.rename_comp e]
  | .field ℓ => simp [Has.rename]

@[simp] theorem Side.rename_comp {s1 s2 s3 : Sig} (σ : Side s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (σ.rename ρ).rename ρ' = σ.rename (ρ.comp ρ') := by
  match σ with
  | .none => simp [Side.rename]
  | .some e => simp [Side.rename, ShapeCo.rename_comp e]

@[simp] theorem Morphism.rename_comp {s1 s2 s3 : Sig} (m : Morphism s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (m.rename ρ).rename ρ' = m.rename (ρ.comp ρ') := by
  match m with
  | .nil => simp [Morphism.rename]
  | .le m pre h post =>
      simp [Morphism.rename, Morphism.rename_comp m, Side.rename_comp pre, Side.rename_comp post]
  | .eq m j b => simp [Morphism.rename, Morphism.rename_comp m]
  | .has m j => simp [Morphism.rename, Morphism.rename_comp m]
  | .bnd m e => simp [Morphism.rename, Morphism.rename_comp m, ShapeCo.rename_comp e]
  | .leC m q h q' =>
      simp [Morphism.rename, Morphism.rename_comp m, SideC.rename_comp q, SideC.rename_comp q']
  | .eqC m j b => simp [Morphism.rename, Morphism.rename_comp m]

@[simp] theorem Atom.rename_comp {s1 s2 s3 : Sig} (a : Atom s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (a.rename ρ).rename ρ' = a.rename (ρ.comp ρ') := by
  match a with
  | .var x => simp [Atom.rename]
  | .cast a e => simp [Atom.rename, Atom.rename_comp a, LeCo.rename_comp e]
  | .foldSelf Tel a =>
      simp [Atom.rename, Rename.lift_comp, Atom.rename_comp a, Telescope.rename_comp Tel]
  | .unfoldSelf a => simp [Atom.rename, Atom.rename_comp a]
  | .both Tel₁ Tel₂ a b =>
      simp [Atom.rename, Rename.lift_comp, Telescope.rename_comp Tel₁, Telescope.rename_comp Tel₂,
        Atom.rename_comp a, Atom.rename_comp b]
  | .recap a f => simp [Atom.rename, Atom.rename_comp a, CapCo.rename_comp f]

end

/-! ## `rename_id` and `rename_comp` for capture witnesses -/

@[simp] theorem CapWitnesses.rename_id {s : Sig} :
    ∀ W : CapWitnesses s, W.rename Rename.id = W
  | .nil => rfl
  | .cons W ℓ C => by
      simp [CapWitnesses.rename, CapWitnesses.rename_id W]

@[simp] theorem CapWitnesses.rename_comp {s1 s2 s3 : Sig} :
    ∀ (W : CapWitnesses s1) (ρ : Rename s1 s2) (ρ' : Rename s2 s3),
      (W.rename ρ).rename ρ' = W.rename (ρ.comp ρ')
  | .nil, _, _ => rfl
  | .cons W ℓ C, ρ, ρ' => by
      simp [CapWitnesses.rename, CapWitnesses.rename_comp W]

/-! ## `rename_id` for terms, values, witnesses, fields -/

mutual

@[simp] theorem Tm.rename_id {s : Sig} (t : Tm s) : t.rename Rename.id = t := by
  match t with
  | .atom a => simp [Tm.rename]
  | .val v => simp [Tm.rename, Value.rename_id v]
  | .app a b => simp [Tm.rename]
  | .proj a ℓ h => simp [Tm.rename, Has.rename_id h]
  | .let t u U f =>
      simp [Tm.rename, Rename.lift_id, Tm.rename_id t, Tm.rename_id u,
        CaptureSet.rename_id U]
  | .cast t e => simp [Tm.rename, Tm.rename_id t]
  | .unbox a U f => simp [Tm.rename, CaptureSet.rename_id U]

@[simp] theorem Value.rename_id {s : Sig} (v : Value s) : v.rename Rename.id = v := by
  match v with
  | .lam A S t g =>
      simp [Value.rename, Rename.lift_id, Tm.rename_id t, CaptureSet.rename_id A]
  | .obj A W Wc F =>
      simp [Value.rename, Rename.lift_id, Witnesses.rename_id W, CapWitnesses.rename_id Wc,
        Fields.rename_id F, CaptureSet.rename_id A]
  | .box a => simp [Value.rename]
  | .cast v e => simp [Value.rename, Value.rename_id v]

@[simp] theorem Witnesses.rename_id {s : Sig} (W : Witnesses s) : W.rename Rename.id = W := by
  match W with
  | .nil => simp [Witnesses.rename]
  | .cons W ℓ T => simp [Witnesses.rename, Witnesses.rename_id W]

@[simp] theorem Fields.rename_id {s : Sig} (F : Fields s) : F.rename Rename.id = F := by
  match F with
  | .nil => simp [Fields.rename]
  | .cons F ℓ t g => simp [Fields.rename, Fields.rename_id F, Tm.rename_id t]

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
  | .let t u U f =>
      simp [Tm.rename, Rename.lift_comp, Tm.rename_comp t, Tm.rename_comp u,
        CaptureSet.rename_comp U]
  | .cast t e => simp [Tm.rename, Tm.rename_comp t]
  | .unbox a U f => simp [Tm.rename, CaptureSet.rename_comp U]

@[simp] theorem Value.rename_comp {s1 s2 s3 : Sig} (v : Value s1)
    (ρ : Rename s1 s2) (ρ' : Rename s2 s3) :
    (v.rename ρ).rename ρ' = v.rename (ρ.comp ρ') := by
  match v with
  | .lam A S t g =>
      simp [Value.rename, Rename.lift_comp, Tm.rename_comp t, CaptureSet.rename_comp A]
  | .obj A W Wc F =>
      simp [Value.rename, Rename.lift_comp, Witnesses.rename_comp W, CapWitnesses.rename_comp Wc,
        Fields.rename_comp F, CaptureSet.rename_comp A]
  | .box a => simp [Value.rename]
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
  | .cons F ℓ t g => simp [Fields.rename, Fields.rename_comp F, Tm.rename_comp t]

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
  | .recap a f => simp [Atom.rename, Atom.root, Atom.root_rename a]

namespace Subst

/-- Extensionality: a substitution is its two components. -/
theorem funext' {s1 s2 : Sig} {σ τ : Subst s1 s2}
    (h : ∀ (x : BVar s1 .var), σ.var x = τ.var x)
    (hc : ∀ (κ : BVar s1 .cap), σ.cvar κ = τ.cvar κ) : σ = τ := by
  cases σ; cases τ
  simp only [Subst.mk.injEq]
  exact ⟨funext h, funext hc⟩

theorem root_var {s1 s2 : Sig} (σ : Subst s1 s2) (x : BVar s1 .var) :
    σ.root.var x = (σ.var x).root := rfl

theorem root_cvar {s1 s2 : Sig} (σ : Subst s1 s2) (κ : BVar s1 .cap) :
    σ.root.var κ = σ.cvar κ := rfl

@[simp] theorem ofRename_root {s1 s2 : Sig} (ρ : Rename s1 s2) :
    (Subst.ofRename ρ).root = ρ := by
  apply Rename.funext'
  intro k x
  cases k <;> rfl

@[simp] theorem ofRename_lift {s1 s2 : Sig} (ρ : Rename s1 s2) :
    (Subst.ofRename ρ).lift = Subst.ofRename ρ.lift := by
  apply Subst.funext'
  · intro x
    cases x <;> simp [Subst.lift, Subst.ofRename, Atom.weaken, Atom.rename]
  · intro κ
    cases κ; rfl

@[simp] theorem ofRename_liftC {s1 s2 : Sig} (ρ : Rename s1 s2) :
    (Subst.ofRename ρ).liftC = Subst.ofRename ρ.lift := by
  apply Subst.funext'
  · intro x
    cases x
    simp [Subst.liftC, Subst.ofRename, Atom.weaken, Atom.rename]
  · intro κ
    cases κ <;> rfl

@[simp] theorem lift_root {s1 s2 : Sig} (σ : Subst s1 s2) :
    σ.lift.root = σ.root.lift := by
  apply Rename.funext'
  intro k x
  cases k
  · cases x with
    | here => simp [Subst.root, Subst.lift, Atom.root]
    | there x => simp [Subst.root, Subst.lift, Atom.weaken]
  · cases x with
    | there x => rfl

@[simp] theorem liftC_root {s1 s2 : Sig} (σ : Subst s1 s2) :
    σ.liftC.root = σ.root.lift := by
  apply Rename.funext'
  intro k x
  cases k
  · cases x with
    | there x => simp [Subst.root, Subst.liftC, Atom.weaken]
  · cases x with
    | here => rfl
    | there x => rfl

@[simp] theorem single_root {s : Sig} (a : Atom s) :
    (Subst.single a).root = Rename.subst a.root := by
  apply Rename.funext'
  intro k x
  cases k
  · cases x <;> simp [Subst.root, Subst.single, Atom.root]
  · cases x with
    | there x => rfl

end Subst

@[simp] theorem Atom.root_subst {s1 s2 : Sig} (a : Atom s1) (σ : Subst s1 s2) :
    (a.subst σ).root = σ.root.var a.root := by
  match a with
  | .var x => simp [Atom.subst, Atom.root, Subst.root_var]
  | .cast a e => simp [Atom.subst, Atom.root, Atom.root_subst a]
  | .foldSelf Tel a => simp [Atom.subst, Atom.root, Atom.root_subst a]
  | .unfoldSelf a => simp [Atom.subst, Atom.root, Atom.root_subst a]
  | .both Tel₁ Tel₂ a b => simp [Atom.subst, Atom.root, Atom.root_subst a]
  | .recap a f => simp [Atom.subst, Atom.root, Atom.root_subst a]

/-! ## Substitution by a renaming -/

mutual

@[simp] theorem ShapeCo.subst_ofRename {s1 s2 : Sig} (e : ShapeCo s1) (ρ : Rename s1 s2) :
    e.subst (Subst.ofRename ρ) = e.rename ρ := by
  match e with
  | .refl T => simp [ShapeCo.subst, ShapeCo.rename]
  | .trans e f =>
      simp [ShapeCo.subst, ShapeCo.rename, ShapeCo.subst_ofRename e, ShapeCo.subst_ofRename f]
  | .top T => simp [ShapeCo.subst, ShapeCo.rename]
  | .bot T => simp [ShapeCo.subst, ShapeCo.rename]
  | .eqToLe φ => simp [ShapeCo.subst, ShapeCo.rename, EqCo.subst_ofRename φ]
  | .pi e f => simp [ShapeCo.subst, ShapeCo.rename, LeCo.subst_ofRename e, LeCo.subst_ofRename f]
  | .obj Tel m =>
      simp [ShapeCo.subst, ShapeCo.rename, Morphism.subst_ofRename m, Subst.ofRename_root]
  | .pair Tel₁ Tel₂ e f =>
      simp [ShapeCo.subst, ShapeCo.rename, ShapeCo.subst_ofRename e, ShapeCo.subst_ofRename f,
        Subst.ofRename_root]
  | .bound Tel i => simp [ShapeCo.subst, ShapeCo.rename, Subst.ofRename_root]
  | .intoBnd e => simp [ShapeCo.subst, ShapeCo.rename, ShapeCo.subst_ofRename e]
  | .member a e i =>
      simp [ShapeCo.subst, ShapeCo.rename, Atom.subst_ofRename a, ShapeCo.subst_ofRename e]
  | .boxed d => simp [ShapeCo.subst, ShapeCo.rename, LeCo.subst_ofRename d]

@[simp] theorem CapCo.subst_ofRename {s1 s2 : Sig} (f : CapCo s1) (ρ : Rename s1 s2) :
    f.subst (Subst.ofRename ρ) = f.rename ρ := by
  match f with
  | .refl C => simp [CapCo.subst, CapCo.rename]
  | .trans f g => simp [CapCo.subst, CapCo.rename, CapCo.subst_ofRename f, CapCo.subst_ofRename g]
  | .elem C D => simp [CapCo.subst, CapCo.rename]
  | .union f g => simp [CapCo.subst, CapCo.rename, CapCo.subst_ofRename f, CapCo.subst_ofRename g]
  | .capvar a => simp [CapCo.subst, CapCo.rename, Atom.subst_ofRename a]
  | .member a e i =>
      simp [CapCo.subst, CapCo.rename, Atom.subst_ofRename a, ShapeCo.subst_ofRename e]
  | .eqToLe φ => simp [CapCo.subst, CapCo.rename, CapEq.subst_ofRename φ]

@[simp] theorem CapEq.subst_ofRename {s1 s2 : Sig} (φ : CapEq s1) (ρ : Rename s1 s2) :
    φ.subst (Subst.ofRename ρ) = φ.rename ρ := by
  match φ with
  | .refl C => simp [CapEq.subst, CapEq.rename]
  | .symm φ => simp [CapEq.subst, CapEq.rename, CapEq.subst_ofRename φ]
  | .trans φ ψ =>
      simp [CapEq.subst, CapEq.rename, CapEq.subst_ofRename φ, CapEq.subst_ofRename ψ]
  | .defC x ℓ => simp [CapEq.subst, CapEq.rename]
  | .member a e i =>
      simp [CapEq.subst, CapEq.rename, Atom.subst_ofRename a, ShapeCo.subst_ofRename e]

@[simp] theorem CapStep.subst_ofRename {s1 s2 : Sig} (st : CapStep s1) (ρ : Rename s1 s2) :
    st.subst (Subst.ofRename ρ) = st.rename ρ := by
  match st with
  | .closed f => simp [CapStep.subst, CapStep.rename, CapCo.subst_ofRename f]
  | .incl C D => simp [CapStep.subst, CapStep.rename]

@[simp] theorem SideC.subst_ofRename {s1 s2 : Sig} (q : SideC s1) (ρ : Rename s1 s2) :
    q.subst (Subst.ofRename ρ) = q.rename ρ := by
  match q with
  | .nil => simp [SideC.subst, SideC.rename]
  | .cons st q => simp [SideC.subst, SideC.rename, CapStep.subst_ofRename st,
      SideC.subst_ofRename q]

@[simp] theorem LeCo.subst_ofRename {s1 s2 : Sig} (d : LeCo s1) (ρ : Rename s1 s2) :
    d.subst (Subst.ofRename ρ) = d.rename ρ := by
  match d with
  | .capt e f => simp [LeCo.subst, LeCo.rename, ShapeCo.subst_ofRename e, CapCo.subst_ofRename f]

@[simp] theorem EqCo.subst_ofRename {s1 s2 : Sig} (φ : EqCo s1) (ρ : Rename s1 s2) :
    φ.subst (Subst.ofRename ρ) = φ.rename ρ := by
  match φ with
  | .refl T => simp [EqCo.subst, EqCo.rename]
  | .symm φ => simp [EqCo.subst, EqCo.rename, EqCo.subst_ofRename φ]
  | .trans φ ψ => simp [EqCo.subst, EqCo.rename, EqCo.subst_ofRename φ, EqCo.subst_ofRename ψ]
  | .def x ℓ => simp [EqCo.subst, EqCo.rename]
  | .member a e i =>
      simp [EqCo.subst, EqCo.rename, Atom.subst_ofRename a, ShapeCo.subst_ofRename e]

@[simp] theorem Has.subst_ofRename {s1 s2 : Sig} (h : Has s1) (ρ : Rename s1 s2) :
    h.subst (Subst.ofRename ρ) = h.rename ρ := by
  match h with
  | .member a e i =>
      simp [Has.subst, Has.rename, Atom.subst_ofRename a, ShapeCo.subst_ofRename e]
  | .field ℓ => simp [Has.subst, Has.rename]

@[simp] theorem Side.subst_ofRename {s1 s2 : Sig} (σ : Side s1) (ρ : Rename s1 s2) :
    σ.subst (Subst.ofRename ρ) = σ.rename ρ := by
  match σ with
  | .none => simp [Side.subst, Side.rename]
  | .some e => simp [Side.subst, Side.rename, ShapeCo.subst_ofRename e]

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
      simp [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m, ShapeCo.subst_ofRename e]
  | .leC m q h q' =>
      simp [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m, SideC.subst_ofRename q,
        SideC.subst_ofRename q']
  | .eqC m j b => simp [Morphism.subst, Morphism.rename, Morphism.subst_ofRename m]

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
  | .recap a f => simp [Atom.subst, Atom.rename, Atom.subst_ofRename a, CapCo.subst_ofRename f]

end

mutual

@[simp] theorem Tm.subst_ofRename {s1 s2 : Sig} (t : Tm s1) (ρ : Rename s1 s2) :
    t.subst (Subst.ofRename ρ) = t.rename ρ := by
  match t with
  | .atom a => simp [Tm.subst, Tm.rename]
  | .val v => simp [Tm.subst, Tm.rename, Value.subst_ofRename v]
  | .app a b => simp [Tm.subst, Tm.rename]
  | .proj a ℓ h => simp [Tm.subst, Tm.rename, Has.subst_ofRename h]
  | .let t u U f =>
      simp [Tm.subst, Tm.rename, Tm.subst_ofRename t, Tm.subst_ofRename u,
        CapCo.subst_ofRename f]
  | .cast t e => simp [Tm.subst, Tm.rename, Tm.subst_ofRename t, LeCo.subst_ofRename e]
  | .unbox a U f =>
      simp [Tm.subst, Tm.rename, Atom.subst_ofRename a, CapCo.subst_ofRename f]

@[simp] theorem Value.subst_ofRename {s1 s2 : Sig} (v : Value s1) (ρ : Rename s1 s2) :
    v.subst (Subst.ofRename ρ) = v.rename ρ := by
  match v with
  | .lam A S t g =>
      simp [Value.subst, Value.rename, Tm.subst_ofRename t, CapCo.subst_ofRename g]
  | .obj A W Wc F =>
      simp [Value.subst, Value.rename, Fields.subst_ofRename F, Subst.ofRename_root]
  | .box a => simp [Value.subst, Value.rename, Atom.subst_ofRename a]
  | .cast v e => simp [Value.subst, Value.rename, Value.subst_ofRename v, LeCo.subst_ofRename e]

@[simp] theorem Fields.subst_ofRename {s1 s2 : Sig} (F : Fields s1) (ρ : Rename s1 s2) :
    F.subst (Subst.ofRename ρ) = F.rename ρ := by
  match F with
  | .nil => simp [Fields.subst, Fields.rename]
  | .cons F ℓ t g =>
      simp [Fields.subst, Fields.rename, Fields.subst_ofRename F, Tm.subst_ofRename t,
        CapCo.subst_ofRename g]

end

/-! ## Weakening then instantiating -/

@[simp] theorem CaptureSet.rename_subst_weaken {s : Sig} {k : Kind}
    (C : CaptureSet s) (y : BVar s k) :
    (C.weaken (k := k))⟦y⟧ = C := by
  simp [CaptureSet.weaken, CaptureSet.substVar, Rename.succ_subst]

@[simp] theorem Shape.rename_subst_weaken {s : Sig} {k : Kind} (S : Shape s) (y : BVar s k) :
    (S.weaken (k := k))⟦y⟧ = S := by
  simp [Shape.weaken, Shape.substVar, Rename.succ_subst]

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

theorem CaptureSet.substVar_rename {s1 s2 : Sig} {k : Kind} (C : CaptureSet (s1,,k))
    (y : BVar s1 k) (ρ : Rename s1 s2) :
    (C⟦y⟧).rename ρ = (C.rename ρ.lift)⟦ρ.var y⟧ := by
  simp only [CaptureSet.substVar, CaptureSet.rename_comp, Rename.subst_comp]

theorem Shape.substVar_rename {s1 s2 : Sig} {k : Kind} (S : Shape (s1,,k))
    (y : BVar s1 k) (ρ : Rename s1 s2) :
    (S⟦y⟧).rename ρ = (S.rename ρ.lift)⟦ρ.var y⟧ := by
  simp only [Shape.substVar, Shape.rename_comp, Rename.subst_comp]

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

theorem CaptureSet.weaken_rename {s1 s2 : Sig} {k : Kind} (C : CaptureSet s1)
    (ρ : Rename s1 s2) :
    (C.weaken (k := k)).rename ρ.lift = (C.rename ρ)↑ := by
  simp only [CaptureSet.weaken, CaptureSet.rename_comp, Rename.succ_lift]

theorem Shape.weaken_rename {s1 s2 : Sig} {k : Kind} (S : Shape s1) (ρ : Rename s1 s2) :
    (S.weaken (k := k)).rename ρ.lift = (S.rename ρ)↑ := by
  simp only [Shape.weaken, Shape.rename_comp, Rename.succ_lift]

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

theorem ShapeCo.weaken_rename {s1 s2 : Sig} {k : Kind} (e : ShapeCo s1) (ρ : Rename s1 s2) :
    (e.weaken (k := k)).rename ρ.lift = (e.rename ρ)↑ := by
  simp only [ShapeCo.weaken, ShapeCo.rename_comp, Rename.succ_lift]

theorem CapCo.weaken_rename {s1 s2 : Sig} {k : Kind} (f : CapCo s1) (ρ : Rename s1 s2) :
    (f.weaken (k := k)).rename ρ.lift = (f.rename ρ)↑ := by
  simp only [CapCo.weaken, CapCo.rename_comp, Rename.succ_lift]

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

theorem CapWitnesses.get_rename {s1 s2 : Sig} :
    ∀ (W : CapWitnesses s1) (l : Label) (ρ : Rename s1 s2),
      (W.rename ρ).get l = (W.get l).rename ρ
  | .nil, _, _ => rfl
  | .cons W l' C, l, ρ => by
      by_cases hl : l = l' <;>
        simp [CapWitnesses.rename, CapWitnesses.get, hl, CapWitnesses.get_rename W l ρ]

/-! ## The precise telescope of a literal is stable under renaming -/

theorem Witnesses.eqEntriesOf_rename {s1 s2 : Sig} (self : BVar s1 .var) (W₀ : Witnesses s1)
    (ρ : Rename s1 s2) :
    ∀ W : Witnesses s1,
      (W₀.rename ρ).eqEntriesOf (ρ.var self) (W.rename ρ) = (W₀.eqEntriesOf self W).rename ρ
  | .nil => by simp [Witnesses.rename, Witnesses.eqEntriesOf, Telescope.rename]
  | .cons W ℓ T => by
      simp [Witnesses.rename, Witnesses.eqEntriesOf, Telescope.rename, Proposition.rename,
        Shape.rename, Witnesses.eqEntriesOf_rename self W₀ ρ W, Witnesses.get_rename]

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

theorem CapWitnesses.eqEntriesOf_rename {s1 s2 : Sig} (self : BVar s1 .var)
    (W₀ : CapWitnesses s1) (ρ : Rename s1 s2) :
    ∀ (base : Telescope s1) (W : CapWitnesses s1),
      (W₀.rename ρ).eqEntriesOf (ρ.var self) (base.rename ρ) (W.rename ρ)
        = (W₀.eqEntriesOf self base W).rename ρ
  | _, .nil => rfl
  | base, .cons W ℓ C => by
      simp [CapWitnesses.rename, CapWitnesses.eqEntriesOf, Telescope.rename, Proposition.rename,
        CaptureSet.rename, CapAtom.rename,
        CapWitnesses.eqEntriesOf_rename self W₀ ρ base W, CapWitnesses.get_rename]

@[simp] theorem CapWitnesses.eqEntries_rename {s1 s2 : Sig} (W : CapWitnesses (s1,x))
    (base : Telescope (s1,x)) (ρ : Rename s1 s2) :
    (W.rename ρ.lift).eqEntries (base.rename ρ.lift) = (W.eqEntries base).rename ρ.lift :=
  CapWitnesses.eqEntriesOf_rename .here W ρ.lift base W

theorem Telescope.ofLiteral_rename {s1 s2 : Sig} (W : Witnesses (s1,x))
    (Wc : CapWitnesses (s1,x)) (ls : List Label) (ρ : Rename s1 s2) :
    (Telescope.ofLiteral W Wc ls).rename ρ.lift
      = Telescope.ofLiteral (W.rename ρ.lift) (Wc.rename ρ.lift) ls := by
  simp [Telescope.ofLiteral]

/-! ## Instantiating weakened syntax, injectivity of renaming -/

theorem Shape.weaken_substVar {k : Kind} (S : Shape s) (r : BVar s k) :
    (S.weaken (k := k))⟦r⟧ = S := by
  simp only [Shape.weaken, Shape.substVar, Shape.rename_comp]
  rw [show (Rename.succ.comp (Rename.subst r) : Rename s s) = Rename.id from
    Rename.funext' (by intro k y; cases k <;> rfl)]
  exact Shape.rename_id S

theorem Ty.weaken_substVar {k : Kind} (T : Ty s) (r : BVar s k) :
    (T.weaken (k := k))⟦r⟧ = T := by
  simp only [Ty.weaken, Ty.substVar, Ty.rename_comp]
  rw [show (Rename.succ.comp (Rename.subst r) : Rename s s) = Rename.id from
    Rename.funext' (by intro k y; cases k <;> rfl)]
  exact Ty.rename_id T

theorem Proposition.weaken_substVar {k : Kind} (P : Proposition s) (r : BVar s k) :
    (P.weaken (k := k))⟦r⟧ = P := by
  simp only [Proposition.weaken, Proposition.substVar, Proposition.rename_comp]
  rw [show (Rename.succ.comp (Rename.subst r) : Rename s s) = Rename.id from
    Rename.funext' (by intro k y; cases k <;> rfl)]
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

theorem CapAtom.rename_inj {s1 s2 : Sig} (a a' : CapAtom s1) (ρ : Rename s1 s2)
    (hρ : ρ.Injective) (h : a.rename ρ = a'.rename ρ) : a = a' := by
  cases a <;> cases a' <;> simp [CapAtom.rename] at h ⊢
  · exact hρ _ _ h
  · exact hρ _ _ h
  · exact ⟨hρ _ _ h.1, h.2⟩

theorem CaptureSet.rename_inj {s1 s2 : Sig} (ρ : Rename s1 s2) (hρ : ρ.Injective) :
    ∀ (C C' : CaptureSet s1), C.rename ρ = C'.rename ρ → C = C'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [CaptureSet.rename] at h
  | _ :: _, [], h => by simp [CaptureSet.rename] at h
  | a :: C, a' :: C', h => by
      simp [CaptureSet.rename] at h ⊢
      exact ⟨CapAtom.rename_inj a a' ρ hρ h.1, CaptureSet.rename_inj ρ hρ C C' h.2⟩

mutual

theorem Shape.rename_inj {s1 s2 : Sig} (S S' : Shape s1) (ρ : Rename s1 s2) (hρ : ρ.Injective)
    (h : S.rename ρ = S'.rename ρ) : S = S' := by
  match S with
  | .bot => cases S' <;> simp [Shape.rename] at h ⊢
  | .sel x ℓ =>
      cases S' <;> simp [Shape.rename] at h ⊢
      exact ⟨hρ _ _ h.1, h.2⟩
  | .pi S T =>
      cases S' <;> simp [Shape.rename] at h ⊢
      exact ⟨Ty.rename_inj S _ ρ hρ h.1, Ty.rename_inj T _ ρ.lift hρ.lift h.2⟩
  | .obj Tel =>
      cases S' <;> simp [Shape.rename] at h ⊢
      exact Telescope.rename_inj Tel _ ρ.lift hρ.lift h
  | .box T =>
      cases S' <;> simp [Shape.rename] at h ⊢
      exact Ty.rename_inj T _ ρ hρ h

theorem Ty.rename_inj {s1 s2 : Sig} (T T' : Ty s1) (ρ : Rename s1 s2) (hρ : ρ.Injective)
    (h : T.rename ρ = T'.rename ρ) : T = T' := by
  match T with
  | .capt C S =>
      cases T' <;> simp [Ty.rename] at h ⊢
      exact ⟨CaptureSet.rename_inj ρ hρ C _ h.1, Shape.rename_inj S _ ρ hρ h.2⟩

theorem Proposition.rename_inj {s1 s2 : Sig} (P P' : Proposition s1) (ρ : Rename s1 s2)
    (hρ : ρ.Injective) (h : P.rename ρ = P'.rename ρ) : P = P' := by
  match P with
  | .le S T =>
      cases P' <;> simp [Proposition.rename] at h ⊢
      exact ⟨Shape.rename_inj S _ ρ hρ h.1, Shape.rename_inj T _ ρ hρ h.2⟩
  | .eq S T =>
      cases P' <;> simp [Proposition.rename] at h ⊢
      exact ⟨Shape.rename_inj S _ ρ hρ h.1, Shape.rename_inj T _ ρ hρ h.2⟩
  | .has ℓ => cases P' <;> simp [Proposition.rename] at h ⊢ <;> exact h
  | .bnd T =>
      cases P' <;> simp [Proposition.rename] at h ⊢
      exact Shape.rename_inj T _ ρ hρ h
  | .leC C D =>
      cases P' <;> simp [Proposition.rename] at h ⊢
      exact ⟨CaptureSet.rename_inj ρ hρ C _ h.1, CaptureSet.rename_inj ρ hρ D _ h.2⟩
  | .eqC C D =>
      cases P' <;> simp [Proposition.rename] at h ⊢
      exact ⟨CaptureSet.rename_inj ρ hρ C _ h.1, CaptureSet.rename_inj ρ hρ D _ h.2⟩

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

@[simp] theorem Proposition.weaken_le (S T : Shape s) {k : Kind} :
    (Proposition.le S T).weaken (k := k) = .le S↑ T↑ := rfl

@[simp] theorem Proposition.weaken_eq (S T : Shape s) {k : Kind} :
    (Proposition.eq S T).weaken (k := k) = .eq S↑ T↑ := rfl

@[simp] theorem Proposition.weaken_has (ℓ : Label) {k : Kind} :
    (Proposition.has (s := s) ℓ).weaken (k := k) = .has ℓ := rfl

@[simp] theorem Proposition.weaken_bnd (T : Shape s) {k : Kind} :
    (Proposition.bnd T).weaken (k := k) = .bnd T↑ := rfl

@[simp] theorem Ty.weaken_capt (C : CaptureSet s) (S : Shape s) {k : Kind} :
    (Ty.capt C S).weaken (k := k) = .capt C↑ S↑ := rfl

theorem Telescope.weaken_substVar {k : Kind} (Tel : Telescope s) (r : BVar s k) :
    (Tel.weaken (k := k))⟦r⟧ = Tel := by
  simp only [Telescope.weaken, Telescope.substVar, Telescope.rename_comp]
  rw [show (Rename.succ.comp (Rename.subst r) : Rename s s) = Rename.id from
    Rename.funext' (by intro k y; cases k <;> rfl)]
  exact Telescope.rename_id Tel

/-- Instantiating a self-substituted, weakened proposition at any root gives
the original instantiation. -/
theorem Proposition.substVar_weaken_substVar {k : Kind} (P : Proposition (s,x))
    (r : BVar s .var) (r' : BVar s k) :
    ((P⟦r⟧).weaken (k := k))⟦r'⟧ = P⟦r⟧ := by
  rw [Proposition.weaken_substVar]

theorem Telescope.At.weaken {Tel : Telescope s} {i : Nat} {P : Proposition s} {k : Kind}
    (h : Tel.At i P) : (Tel.weaken (k := k)).At i (P↑) := by
  induction h with
  | here => simp only [Telescope.weaken, Telescope.rename]; rw [← Telescope.length_rename]; exact .here
  | there _ ih => exact .there ih

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


/-! ## Use sets and the inspected root under renaming and substitution

The use set of a term is a capture set, and it travels with the term: a
renaming renames it, and a substitution renames it by the substitution's
renaming of roots (`Subst.root`, the same reading of a substitution on
capture sets that types and evidence already use).  The inspected root
travels the same way. -/

theorem CaptureSet.rename_union {s1 s2 : Sig} (C D : CaptureSet s1) (ρ : Rename s1 s2) :
    (C ∪ D).rename ρ = C.rename ρ ∪ D.rename ρ := by
  simp [CaptureSet.rename, CaptureSet.union_def]

theorem Tm.uses_rename {s1 s2 : Sig} (t : Tm s1) (ρ : Rename s1 s2) :
    (t.rename ρ).uses = t.uses.rename ρ := by
  match t with
  | .atom a => simp [Tm.rename, CaptureSet.rename, CapAtom.rename]
  | .val v => simp [Tm.rename, CaptureSet.rename]
  | .app a b => simp [Tm.rename, CaptureSet.rename, CapAtom.rename]
  | .proj a ℓ h => simp [Tm.rename, CaptureSet.rename, CapAtom.rename]
  | .let t u U f =>
      simp only [Tm.rename, Tm.uses_let, CaptureSet.rename_union, Tm.uses_rename t]
  | .cast t e => simp only [Tm.rename, Tm.uses_cast, Tm.uses_rename t]
  | .unbox a U f =>
      simp only [Tm.rename, Tm.uses_unbox, CaptureSet.rename_union, Atom.root_rename]
      simp [CaptureSet.rename, CapAtom.rename]

theorem Tm.uses_subst {s1 s2 : Sig} (t : Tm s1) (σ : Subst s1 s2) :
    (t.subst σ).uses = t.uses.rename σ.root := by
  match t with
  | .atom a => simp [Tm.subst, CaptureSet.rename, CapAtom.rename]
  | .val v => simp [Tm.subst, CaptureSet.rename]
  | .app a b => simp [Tm.subst, CaptureSet.rename, CapAtom.rename]
  | .proj a ℓ h => simp [Tm.subst, CaptureSet.rename, CapAtom.rename]
  | .let t u U f =>
      simp only [Tm.subst, Tm.uses_let, CaptureSet.rename_union, Tm.uses_subst t]
  | .cast t e => simp only [Tm.subst, Tm.uses_cast, Tm.uses_subst t]
  | .unbox a U f =>
      simp only [Tm.subst, Tm.uses_unbox, CaptureSet.rename_union, Atom.root_subst]
      simp [CaptureSet.rename, CapAtom.rename]

/-- Instantiating the innermost binder of a term by an atom instantiates its
use set at the atom's root. -/
theorem Tm.uses_substAtom {s : Sig} (t : Tm (s,x)) (a : Atom s) :
    (t.substAtom a).uses = t.uses⟦a.root⟧ := by
  simp [Tm.substAtom, Tm.uses_subst, CaptureSet.substVar]

theorem Tm.inspects_rename {s1 s2 : Sig} (t : Tm s1) (ρ : Rename s1 s2) :
    (t.rename ρ).inspects = t.inspects.map ρ.var := by
  match t with
  | .atom a => simp [Tm.rename]
  | .val v => simp [Tm.rename]
  | .app a b => simp [Tm.rename]
  | .proj a ℓ h => simp [Tm.rename]
  | .let t u U f => simp [Tm.rename]
  | .cast t e => simp [Tm.rename]
  | .unbox a U f => simp [Tm.rename]

theorem Tm.inspects_subst {s1 s2 : Sig} (t : Tm s1) (σ : Subst s1 s2) :
    (t.subst σ).inspects = t.inspects.map σ.root.var := by
  match t with
  | .atom a => simp [Tm.subst]
  | .val v => simp [Tm.subst]
  | .app a b => simp [Tm.subst]
  | .proj a ℓ h => simp [Tm.subst]
  | .let t u U f => simp [Tm.subst]
  | .cast t e => simp [Tm.subst]
  | .unbox a U f => simp [Tm.subst]

end FCdot

end Captures
