import Coercions.CapturesCC.DotToFCdot.TypesLemmas
import Coercions.CapturesCC.FCdot.TypingSubst

namespace CapturesCC

/-!
# Substitution for the type translation

B1 gives the source arrow a capture binder, so the source's `All-E` reads
its argument at the instantiated domain and concludes at the instantiated
codomain, exactly as the target's `app` does.  The translation therefore
needs the substitution twin of `Shape.translate_rename`: the type
translation commutes with substitution, once a source substitution and a
target substitution are known to agree.

Agreement is two conditions.  On a term variable the two must land on the
same variable, which is what the target reads through `Subst.rootVar`.  On a
capture binder the atom the source puts there must translate to the atom the
target puts there; in particular the source substitution may not put `any`
at a capture binder, since `any` has no target atom.  The two substitutions
the rules use, `Subst.singleC` at a variable and `Subst.arg`, both satisfy
it.
-/

namespace FCdot

/-! ## Two target facts a translated telescope needs -/

theorem CaptureSet.subst_name_here {s1 s2 : Sig} (a : Label) (σ : Subst s1 s2) :
    CaptureSet.subst [CapAtom.name (BVar.here : BVar (s1,x) .var) a] σ.lift
      = [CapAtom.name BVar.here a] := rfl

theorem Shape.subst_sel_here {s1 s2 : Sig} (A : Label) (σ : Subst s1 s2) :
    Shape.subst (Shape.sel (BVar.here : BVar (s1,x) .var) A) σ.lift
      = Shape.sel BVar.here A := rfl

/-- The self stays the self under a lifted substitution, with the root
spelled out. -/
@[simp] theorem Subst.lift_var_root_here {s1 s2 : Sig} (σ : Subst s1 s2) :
    (σ.lift.var (BVar.here : BVar (s1,x) .var)).root = BVar.here := rfl

/-- `Telescope.append_subst`, restated against the plain `Telescope.append`
function, as `Telescope.append_rename'` is for renaming. -/
theorem Telescope.append_subst' {s1 s2 : Sig} (Tel Tel' : Telescope s1) (σ : Subst s1 s2) :
    (Tel.append Tel').subst σ = (Tel.subst σ).append (Tel'.subst σ) :=
  Telescope.append_subst Tel Tel' σ

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Agreement -/

/-- A source substitution and a target substitution do the same thing to a
translated type. -/
structure SubstAgree {s1 s2 : Sig} (σ : Subst s1 s2) (σ' : FCdot.Subst s1 s2) : Prop where
  var : ∀ x, σ'.rootVar x = σ.var x
  cvar : ∀ κ, (σ.cvar κ).translate? = some (σ'.cvar κ)

/-- Agreement on a variable, with the root spelled out: `Subst.rootVar` is a
definition and `simp` unfolds it, so this is the form the rewrites match. -/
theorem SubstAgree.var' {s1 s2 : Sig} {σ : Subst s1 s2} {σ' : FCdot.Subst s1 s2}
    (h : SubstAgree σ σ') (x : BVar s1 .var) : (σ'.var x).root = σ.var x := h.var x

theorem SubstAgree.lift {s1 s2 : Sig} {σ : Subst s1 s2} {σ' : FCdot.Subst s1 s2}
    (h : SubstAgree σ σ') : SubstAgree σ.lift σ'.lift where
  var := fun z => by
    cases z with
    | here => rfl
    | there x =>
        rw [FCdot.Subst.lift_rootVar_there]
        show BVar.there (σ'.rootVar x) = BVar.there (σ.var x)
        rw [h.var x]
  cvar := fun z => by
    cases z with
    | there κ =>
        show ((σ.cvar κ).rename Rename.succ).translate?
          = some ((σ'.cvar κ).rename Rename.succ)
        rw [CapAtom.translate_rename, h.cvar κ]
        rfl

theorem SubstAgree.liftC {s1 s2 : Sig} {σ : Subst s1 s2} {σ' : FCdot.Subst s1 s2}
    (h : SubstAgree σ σ') : SubstAgree σ.liftC σ'.liftC where
  var := fun z => by
    cases z with
    | there x =>
        rw [FCdot.Subst.liftC_rootVar_there]
        show BVar.there (σ'.rootVar x) = BVar.there (σ.var x)
        rw [h.var x]
  cvar := fun z => by
    cases z with
    | here => rfl
    | there κ =>
        show ((σ.cvar κ).rename Rename.succ).translate?
          = some ((σ'.cvar κ).rename Rename.succ)
        rw [CapAtom.translate_rename, h.cvar κ]
        rfl

/-- The two substitutions the source's `All-E` uses agree with the target's. -/
theorem SubstAgree.singleC {s : Sig} (y : BVar s .var) :
    SubstAgree (Subst.singleC (CapAtom.var y)) (FCdot.Subst.singleC (FCdot.CapAtom.var y)) where
  var := fun z => by cases z; rfl
  cvar := fun z => by cases z <;> rfl

theorem SubstAgree.arg {s : Sig} (b : FCdot.Atom s) (y : BVar s .var) (hb : b.root = y) :
    SubstAgree (Subst.arg y) (FCdot.Subst.arg b) where
  var := fun z => by
    match z with
    | .here => exact hb
    | .there (.there w) => rfl
  cvar := fun z => by
    match z with
    | .there .here => show some (FCdot.CapAtom.var y) = some (FCdot.CapAtom.var b.root); rw [hb]
    | .there (.there κ) => rfl

/-! ## Capture atoms and capture sets -/

theorem CapAtom.translate_subst {s1 s2 : Sig} {σ : Subst s1 s2} {σ' : FCdot.Subst s1 s2}
    (h : SubstAgree σ σ') :
    ∀ a : CapAtom s1, (a.subst σ).translate? = (a.translate?).map (fun b => b.subst σ')
  | .var x => by
      show some (FCdot.CapAtom.var (σ.var x)) = some (FCdot.CapAtom.var (σ'.rootVar x))
      rw [h.var x]
  | .cvar κ => by
      show (σ.cvar κ).translate? = some (σ'.cvar κ)
      exact h.cvar κ
  | .sel x A => by
      show some (FCdot.CapAtom.name (σ.var x) A) = some (FCdot.CapAtom.name (σ'.rootVar x) A)
      rw [h.var x]
  | .any => rfl

@[simp] theorem CaptureSet.translate_subst {s1 s2 : Sig} {σ : Subst s1 s2}
    {σ' : FCdot.Subst s1 s2} (h : SubstAgree σ σ') (C : CaptureSet s1) :
    (C.subst σ).translate = C.translate.subst σ' := by
  induction C with
  | nil => rfl
  | cons a C ih =>
      cases a with
      | var x =>
          show CaptureSet.translate (CapAtom.var (σ.var x) :: CaptureSet.subst C σ)
            = FCdot.CaptureSet.subst (CaptureSet.translate (CapAtom.var x :: C)) σ'
          rw [CaptureSet.translate_cons_var, CaptureSet.translate_cons_var, ih]
          show FCdot.CapAtom.var (σ.var x) :: _ = FCdot.CapAtom.var (σ'.rootVar x) :: _
          rw [h.var x]
          rfl
      | cvar κ =>
          show CaptureSet.translate ((σ.cvar κ) :: CaptureSet.subst C σ)
            = FCdot.CaptureSet.subst (CaptureSet.translate (CapAtom.cvar κ :: C)) σ'
          rw [CaptureSet.translate_cons (h.cvar κ), CaptureSet.translate_cons_cvar, ih]
          rfl
      | sel x A =>
          show CaptureSet.translate (CapAtom.sel (σ.var x) A :: CaptureSet.subst C σ)
            = FCdot.CaptureSet.subst (CaptureSet.translate (CapAtom.sel x A :: C)) σ'
          rw [CaptureSet.translate_cons_sel, CaptureSet.translate_cons_sel, ih]
          show FCdot.CapAtom.name (σ.var x) A :: _ = FCdot.CapAtom.name (σ'.rootVar x) A :: _
          rw [h.var x]
          rfl
      | any =>
          show CaptureSet.translate (CapAtom.any :: CaptureSet.subst C σ)
            = FCdot.CaptureSet.subst (CaptureSet.translate (CapAtom.any :: C)) σ'
          rw [CaptureSet.translate_cons_any, CaptureSet.translate_cons_any, ih]

/-! ## The fragment tests are invariant -/

theorem Shape.isDecl_subst {s1 s2 : Sig} :
    ∀ (S : Shape s1) (σ : Subst s1 s2), (S.subst σ).isDecl = S.isDecl
  | .top, _ => rfl
  | .bot, _ => rfl
  | .sel _ _, _ => rfl
  | .typ _ _ _, _ => rfl
  | .fld _ _, _ => rfl
  | .cap _ _ _, _ => rfl
  | .box _, _ => rfl
  | .all _ _, _ => rfl
  | .mu S, σ => by simp [Shape.subst, Shape.isDecl, Shape.isDecl_subst S σ.lift]
  | .and S T, σ => by
      simp [Shape.subst, Shape.isDecl, Shape.isDecl_subst S σ, Shape.isDecl_subst T σ]

/-! ## `translate`, `tel` and `telSelf` commute with substitution -/

mutual

theorem Shape.translate_subst {s1 s2 : Sig} {σ : Subst s1 s2} {σ' : FCdot.Subst s1 s2}
    (S : Shape s1) (h : SubstAgree σ σ') :
    (S.subst σ).translate = S.translate.subst σ' := by
  match S with
  | .top => simp [Shape.subst, Shape.translate, FCdot.Shape.subst, FCdot.Telescope.subst]
  | .bot => simp [Shape.subst, Shape.translate, FCdot.Shape.subst]
  | .sel (.var x) A =>
      simp [Shape.subst, Path.subst, Shape.translate, FCdot.Shape.subst, h.var' x]
  | .all (.capt C1 S1) (.capt C2 S2) =>
      simp [Shape.subst, Ty.subst, Shape.translate, FCdot.Shape.subst, FCdot.Ty.subst,
        Shape.translate_subst S1 h.liftC, Shape.translate_subst S2 h.liftC.lift,
        CaptureSet.translate_subst h.liftC, CaptureSet.translate_subst h.liftC.lift]
  | .box (.capt C S0) =>
      simp [Shape.subst, Ty.subst, Shape.translate, FCdot.Shape.subst, FCdot.Ty.subst,
        Shape.translate_subst S0 h, CaptureSet.translate_subst h]
  | .typ A S1 S2 =>
      simp [Shape.subst, Shape.translate, Shape.tel, FCdot.Shape.subst, FCdot.Telescope.subst,
        FCdot.Proposition.subst, FCdot.Subst.lift_rootVar_here, FCdot.Shape.weaken_subst,
        Shape.translate_subst S1 h, Shape.translate_subst S2 h]
  | .fld a (.capt C S0) =>
      simp [Shape.subst, Ty.subst, Shape.translate, Shape.tel, FCdot.Shape.subst,
        FCdot.Telescope.subst, FCdot.Proposition.subst, FCdot.Subst.lift_rootVar_here,
        FCdot.Shape.weaken_subst, FCdot.CaptureSet.subst_name_here,
        FCdot.CaptureSet.weaken_subst, Shape.translate_subst S0 h,
        CaptureSet.translate_subst h]
  | .cap A c1 c2 =>
      simp [Shape.subst, Shape.translate, Shape.tel, FCdot.Shape.subst,
        FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.CaptureSet.subst_name_here, FCdot.CaptureSet.weaken_subst,
        CaptureSet.translate_subst h]
  | .and S1 S2 =>
      simp [Shape.subst, Shape.translate, Shape.tel, FCdot.Shape.subst,
        FCdot.Telescope.append_subst', Shape.tel_subst S1 h, Shape.tel_subst S2 h]
  | .mu S0 =>
      simp [Shape.subst, Shape.translate, FCdot.Shape.subst, Shape.telSelf_subst S0 h]

theorem Shape.tel_subst {s1 s2 : Sig} {σ : Subst s1 s2} {σ' : FCdot.Subst s1 s2}
    (S : Shape s1) (h : SubstAgree σ σ') :
    (S.subst σ).tel = S.tel.subst σ'.lift := by
  match S with
  | .top => simp [Shape.subst, Shape.tel, FCdot.Telescope.subst]
  | .bot =>
      simp [Shape.subst, Shape.tel, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Shape.subst, FCdot.Shape.weaken, FCdot.Shape.rename]
  | .sel (.var y) A =>
      simp [Shape.subst, Path.subst, Shape.tel, FCdot.Telescope.subst,
        FCdot.Proposition.subst, FCdot.Shape.weaken_subst, FCdot.Shape.subst, h.var' y]
  | .all (.capt C1 S1) (.capt C2 S2) =>
      simp [Shape.subst, Ty.subst, Shape.tel, FCdot.Telescope.subst,
        FCdot.Proposition.subst, FCdot.Shape.weaken_subst, FCdot.Shape.subst,
        FCdot.Ty.subst, Shape.translate_subst S1 h.liftC,
        Shape.translate_subst S2 h.liftC.lift, CaptureSet.translate_subst h.liftC,
        CaptureSet.translate_subst h.liftC.lift]
  | .box (.capt C S0) =>
      simp [Shape.subst, Ty.subst, Shape.tel, FCdot.Telescope.subst,
        FCdot.Proposition.subst, FCdot.Shape.weaken_subst, FCdot.Shape.subst,
        FCdot.Ty.subst, Shape.translate_subst S0 h, CaptureSet.translate_subst h]
  | .typ A S1 S2 =>
      simp [Shape.subst, Shape.tel, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Shape.subst, FCdot.Subst.lift_rootVar_here, FCdot.Shape.weaken_subst,
        Shape.translate_subst S1 h, Shape.translate_subst S2 h]
  | .fld a (.capt C S0) =>
      simp [Shape.subst, Ty.subst, Shape.tel, FCdot.Telescope.subst,
        FCdot.Proposition.subst, FCdot.Shape.subst, FCdot.Subst.lift_rootVar_here,
        FCdot.Shape.weaken_subst, FCdot.CaptureSet.subst_name_here,
        FCdot.CaptureSet.weaken_subst, Shape.translate_subst S0 h,
        CaptureSet.translate_subst h]
  | .cap A c1 c2 =>
      simp [Shape.subst, Shape.tel, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.CaptureSet.subst_name_here, FCdot.CaptureSet.weaken_subst,
        CaptureSet.translate_subst h]
  | .and S1 S2 =>
      simp [Shape.subst, Shape.tel, FCdot.Telescope.append_subst',
        Shape.tel_subst S1 h, Shape.tel_subst S2 h]
  | .mu S0 =>
      by_cases hd : S0.isDecl = true
      · simp [Shape.subst, Shape.tel, hd, Shape.isDecl_subst S0 σ.lift,
          Shape.telSelf_subst S0 h]
      · simp [Shape.subst, Shape.tel, hd, Shape.isDecl_subst S0 σ.lift,
          Shape.telSelf_subst S0 h, FCdot.Telescope.subst, FCdot.Proposition.subst,
          FCdot.Shape.weaken_subst, FCdot.Shape.subst]

theorem Shape.telSelf_subst {s1 s2 : Sig} {σ : Subst s1 s2} {σ' : FCdot.Subst s1 s2}
    (S : Shape (s1,x)) (h : SubstAgree σ σ') :
    (S.subst σ.lift).telSelf = S.telSelf.subst σ'.lift := by
  match S with
  | .top => simp [Shape.subst, Shape.telSelf, FCdot.Telescope.subst]
  | .bot =>
      simp [Shape.subst, Shape.telSelf, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Shape.subst]
  | .sel (.var y) A =>
      simp [Shape.subst, Path.subst, Shape.telSelf, FCdot.Telescope.subst,
        FCdot.Proposition.subst, FCdot.Shape.subst, h.lift.var' y]
  | .all (.capt C1 S1) (.capt C2 S2) =>
      simp [Shape.subst, Ty.subst, Shape.telSelf, FCdot.Telescope.subst,
        FCdot.Proposition.subst, FCdot.Shape.subst, FCdot.Ty.subst,
        Shape.translate_subst S1 h.lift.liftC, Shape.translate_subst S2 h.lift.liftC.lift,
        CaptureSet.translate_subst h.lift.liftC, CaptureSet.translate_subst h.lift.liftC.lift]
  | .box (.capt C S0) =>
      simp [Shape.subst, Ty.subst, Shape.telSelf, FCdot.Telescope.subst,
        FCdot.Proposition.subst, FCdot.Shape.subst, FCdot.Ty.subst,
        Shape.translate_subst S0 h.lift, CaptureSet.translate_subst h.lift]
  | .typ A S1 S2 =>
      simp [Shape.subst, Shape.telSelf, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Shape.subst, FCdot.Subst.lift_rootVar_here,
        Shape.translate_subst S1 h.lift, Shape.translate_subst S2 h.lift]
  | .fld a (.capt C S0) =>
      simp [Shape.subst, Ty.subst, Shape.telSelf, FCdot.Telescope.subst,
        FCdot.Proposition.subst, FCdot.Shape.subst, FCdot.Subst.lift_rootVar_here,
        FCdot.CaptureSet.subst_name_here, Shape.translate_subst S0 h.lift,
        CaptureSet.translate_subst h.lift]
  | .cap A c1 c2 =>
      simp [Shape.subst, Shape.telSelf, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.CaptureSet.subst_name_here, CaptureSet.translate_subst h.lift]
  | .and S1 S2 =>
      simp [Shape.subst, Shape.telSelf, FCdot.Telescope.append_subst',
        Shape.telSelf_subst S1 h, Shape.telSelf_subst S2 h]
  | .mu S0 =>
      have h1 : (S0.subst σ.lift.lift).telSelf = (Shape.telSelf S0).subst σ'.lift.lift :=
        Shape.telSelf_subst S0 h.lift
      by_cases hd : S0.isDecl = true
      · have hd' : (S0.subst σ.lift.lift).isDecl = true := by
          rw [Shape.isDecl_subst S0 σ.lift.lift]; exact hd
        simp only [Shape.subst, Shape.telSelf, if_pos hd, if_pos hd']
        rw [h1, FCdot.Telescope.substVar_subst]
        simp [FCdot.Subst.lift_rootVar_here]
      · have hd' : ¬ (S0.subst σ.lift.lift).isDecl = true := by
          rw [Shape.isDecl_subst S0 σ.lift.lift]; exact hd
        simp only [Shape.subst, Shape.telSelf, if_neg hd, if_neg hd']
        simp [FCdot.Telescope.subst, FCdot.Proposition.subst, FCdot.Shape.subst, h1]

end

/-- `⟦T⟧` commutes with substitution: the shape half is
`Shape.translate_subst`, the capture half is `CaptureSet.translate_subst`. -/
theorem Ty.translate_subst {s1 s2 : Sig} {σ : Subst s1 s2} {σ' : FCdot.Subst s1 s2}
    (T : Ty s1) (h : SubstAgree σ σ') : (T.subst σ).translate = T.translate.subst σ' := by
  cases T with
  | capt C S =>
      simp [Ty.subst, Ty.translate, FCdot.Ty.subst, Shape.translate_subst S h,
        CaptureSet.translate_subst h]

/-- The instantiated domain of the source's `All-E`, translated. -/
theorem Ty.translate_singleC {s : Sig} (T : Dom s) (y : BVar s .var) :
    (T.subst (Subst.singleC (CapAtom.var y))).translate
      = T.translate.subst (FCdot.Subst.singleC (FCdot.CapAtom.var y)) :=
  Ty.translate_subst T (SubstAgree.singleC y)

/-- The instantiated codomain of the source's `All-E`, translated.  Only the
root of the target's argument atom is read, which is why any atom with the
right root will do. -/
theorem Ty.translate_arg {s : Sig} (E : Cod s) (b : FCdot.Atom s) (y : BVar s .var)
    (hb : b.root = y) :
    (E.subst (Subst.arg y)).translate = E.translate.subst (FCdot.Subst.arg b) :=
  Ty.translate_subst E (SubstAgree.arg b y hb)

end DotMNF

end CapturesCC
