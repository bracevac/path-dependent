import Coercions.Captures.DotToFCdot.Types
import Coercions.Captures.FCdot.RenameLemmas

namespace Captures

/-!
# Renaming for the type translation (Plan III §8.1, M3)

The type translation `Shape.translate`/`Shape.tel`/`Shape.telSelf`
(`DotToFCdot/Types.lean`) is a mutual recursion mirroring the shape of
`Shape`.  This file proves it commutes with renaming, mirroring
`Coercions.FCdot.RenameLemmas`, and derives the context-lookup facts the
typedness proofs (M3 second half) need.
-/

namespace FCdot

/-! ## `Witnesses.append` and `CapWitnesses.append` commute with renaming -/

theorem Witnesses.append_rename {s1 s2 : Sig} :
    ∀ (W W' : Witnesses s1) (ρ : Rename s1 s2),
      (W.append W').rename ρ = (W.rename ρ).append (W'.rename ρ)
  | _, .nil, _ => rfl
  | W, .cons W' ℓ T, ρ => by
      simp [Witnesses.append, Witnesses.rename, Witnesses.append_rename W W' ρ]

theorem CapWitnesses.append_rename {s1 s2 : Sig} :
    ∀ (W W' : CapWitnesses s1) (ρ : Rename s1 s2),
      (W.append W').rename ρ = (W.rename ρ).append (W'.rename ρ)
  | _, .nil, _ => rfl
  | W, .cons W' ℓ C, ρ => by
      simp [CapWitnesses.append, CapWitnesses.rename, CapWitnesses.append_rename W W' ρ]


/-! ## Small capture-set facts

The capture entries of a field and of a capture member are a singleton name
of the self and a translated capture set; these are the two rewrites their
renaming needs, stated so that `CaptureSet.rename` is never unfolded to a
`List.map`. -/

theorem CaptureSet.rename_name_here {s s' : Sig} (ρ : Rename s s') (l : Label) :
    CaptureSet.rename ([CapAtom.name BVar.here l] : CaptureSet (s,x)) ρ.lift
      = [CapAtom.name BVar.here l] := by
  simp [CaptureSet.rename, CapAtom.rename, Rename.lift_here]

theorem CaptureSet.substVar_name_here' {s : Sig} (l : Label) (r : BVar s .var) :
    CaptureSet.substVar ([CapAtom.name BVar.here l] : CaptureSet (s,x)) r
      = [CapAtom.name r l] := by
  simp [CaptureSet.substVar, CaptureSet.rename, CapAtom.rename]

theorem CaptureSet.weaken_name {s : Sig} {k : Kind} (l : Label) (r : BVar s .var) :
    CaptureSet.weaken (k := k) ([CapAtom.name r l] : CaptureSet s)
      = [CapAtom.name (BVar.there r) l] := rfl

theorem CaptureSet.weaken_substVar' {s : Sig} {k : Kind} (C : CaptureSet s) (r : BVar s k) :
    (C.weaken (k := k)).substVar r = C := by
  simp only [CaptureSet.weaken, CaptureSet.substVar, CaptureSet.rename_comp, Rename.succ_subst,
    CaptureSet.rename_id]

/-- Renaming by `(Rename.succ).lift` (inserting a fresh binder under a binder) and then
instantiating the inserted-under binder by the (now doubly-shifted) old innermost binder is
the identity: the two operations cancel. -/
theorem Rename.succ_lift_subst_here {s : Sig} :
    (Rename.succ (s := s) (k := Kind.var)).lift.comp (Rename.subst (BVar.here (s := s) (k := Kind.var)))
      = Rename.id := by
  apply Rename.funext'
  intro k x
  cases x <;> rfl

theorem Telescope.rename_lift_substVar_succ {s : Sig} (Tel : Telescope (s,x)) :
    (Tel.rename (Rename.succ (k := Kind.var)).lift).substVar BVar.here = Tel := by
  simp only [Telescope.substVar, Telescope.rename_comp, Rename.succ_lift_subst_here,
    Telescope.rename_id]

/-- `Telescope.append_rename`, restated against the plain `Telescope.append` function
(rather than the `++` notation): the definitions of `Shape.tel`/`Shape.telSelf` use
`.append` directly, and `simp`/`rw` do not see through the `Append` instance to match
`++`. -/
theorem Telescope.append_rename' {s1 s2 : Sig} (Tel Tel' : Telescope s1) (ρ : Rename s1 s2) :
    (Tel.append Tel').rename ρ = (Tel.rename ρ).append (Tel'.rename ρ) :=
  Telescope.append_rename Tel Tel' ρ

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Declaration shapes are a syntactic property -/

theorem Shape.isDecl_rename {s s' : Sig} : ∀ (S : Shape s) (ρ : Rename s s'),
    (S.rename ρ).isDecl = S.isDecl
  | .top, _ => rfl
  | .bot, _ => rfl
  | .sel _ _, _ => rfl
  | .typ _ _ _, _ => rfl
  | .fld _ _, _ => rfl
  | .cap _ _ _, _ => rfl
  | .box _, _ => rfl
  | .all _ _, _ => rfl
  | .mu S, ρ => by simp [Shape.rename, Shape.isDecl, Shape.isDecl_rename S ρ.lift]
  | .and S T, ρ => by
      simp [Shape.rename, Shape.isDecl, Shape.isDecl_rename S ρ, Shape.isDecl_rename T ρ]

theorem Shape.isObj_rename {s s' : Sig} : ∀ (S : Shape s) (ρ : Rename s s'),
    (S.rename ρ).isObj = S.isObj
  | .top, _ => rfl
  | .bot, _ => rfl
  | .sel _ _, _ => rfl
  | .typ _ _ _, _ => rfl
  | .fld _ _, _ => rfl
  | .cap _ _ _, _ => rfl
  | .box _, _ => rfl
  | .all _ _, _ => rfl
  | .and _ _, _ => rfl
  | .mu S, ρ => by simp [Shape.rename, Shape.isObj, Shape.isDecl_rename S ρ.lift]

/-! ## Renaming for `translate`, `tel`, `telSelf` -/

mutual

/-- The shape translation commutes with renaming: the vanilla
`Ty.translate_rename`, read at the shape sort. -/
theorem Shape.translate_rename {s s' : Sig} (S : Shape s) (ρ : Rename s s') :
    (S.rename ρ).translate = S.translate.rename ρ := by
  match S with
  | .top => simp [Shape.rename, Shape.translate, FCdot.Shape.rename, FCdot.Telescope.rename]
  | .bot => simp [Shape.rename, Shape.translate, FCdot.Shape.rename]
  | .sel (.var x) A => simp [Shape.rename, Path.rename, Shape.translate, FCdot.Shape.rename]
  | .all (.capt C1 S1) (.capt C2 S2) =>
      simp [Shape.rename, Ty.rename, Shape.translate, FCdot.Shape.rename, FCdot.Ty.rename,
        Shape.translate_rename S1 ρ, Shape.translate_rename S2 ρ.lift]
  | .box (.capt C S0) =>
      simp [Shape.rename, Ty.rename, Shape.translate, FCdot.Shape.rename, FCdot.Ty.rename,
        Shape.translate_rename S0 ρ]
  | .typ A S1 S2 =>
      simp [Shape.rename, Shape.translate, Shape.tel, FCdot.Shape.rename, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Rename.lift_here, FCdot.Shape.weaken_rename,
        Shape.translate_rename S1 ρ, Shape.translate_rename S2 ρ]
  | .fld a (.capt C S0) =>
      simp [Shape.rename, Ty.rename, Shape.translate, Shape.tel, FCdot.Shape.rename,
        FCdot.Telescope.rename, FCdot.Proposition.rename, FCdot.Rename.lift_here,
        FCdot.Shape.weaken_rename, FCdot.CaptureSet.rename_name_here,
        FCdot.CaptureSet.weaken_rename, Shape.translate_rename S0 ρ]
  | .cap A c1 c2 =>
      simp [Shape.rename, Shape.translate, Shape.tel, FCdot.Shape.rename,
        FCdot.Telescope.rename, FCdot.Proposition.rename,
        FCdot.CaptureSet.rename_name_here, FCdot.CaptureSet.weaken_rename]
  | .and S1 S2 =>
      simp [Shape.rename, Shape.translate, Shape.tel, FCdot.Shape.rename,
        FCdot.Telescope.append_rename', Shape.tel_rename S1 ρ, Shape.tel_rename S2 ρ]
  | .mu S0 =>
      simp [Shape.rename, Shape.translate, FCdot.Shape.rename, Shape.telSelf_rename S0 ρ]

theorem Shape.tel_rename {s s' : Sig} (S : Shape s) (ρ : Rename s s') :
    (S.rename ρ).tel = S.tel.rename ρ.lift := by
  match S with
  | .top => simp [Shape.rename, Shape.tel, FCdot.Telescope.rename]
  | .bot =>
      simp [Shape.rename, Shape.tel, FCdot.Telescope.rename, FCdot.Proposition.rename,
        FCdot.Shape.rename, FCdot.Shape.weaken]
  | .sel (.var y) A =>
      simp [Shape.rename, Path.rename, Shape.tel, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Shape.weaken_rename, FCdot.Shape.rename]
  | .all (.capt C1 S1) (.capt C2 S2) =>
      simp [Shape.rename, Ty.rename, Shape.tel, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Shape.weaken_rename, FCdot.Shape.rename,
        FCdot.Ty.rename, Shape.translate_rename S1 ρ, Shape.translate_rename S2 ρ.lift]
  | .box (.capt C S0) =>
      simp [Shape.rename, Ty.rename, Shape.tel, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Shape.weaken_rename, FCdot.Shape.rename,
        FCdot.Ty.rename, Shape.translate_rename S0 ρ]
  | .typ A S1 S2 =>
      simp [Shape.rename, Shape.tel, FCdot.Telescope.rename, FCdot.Proposition.rename,
        FCdot.Shape.rename, FCdot.Rename.lift_here, FCdot.Shape.weaken_rename,
        Shape.translate_rename S1 ρ, Shape.translate_rename S2 ρ]
  | .fld a (.capt C S0) =>
      simp [Shape.rename, Ty.rename, Shape.tel, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Shape.rename, FCdot.Rename.lift_here,
        FCdot.Shape.weaken_rename, FCdot.CaptureSet.rename_name_here,
        FCdot.CaptureSet.weaken_rename, Shape.translate_rename S0 ρ]
  | .cap A c1 c2 =>
      simp [Shape.rename, Shape.tel, FCdot.Telescope.rename, FCdot.Proposition.rename,
        FCdot.CaptureSet.rename_name_here,
        FCdot.CaptureSet.weaken_rename]
  | .and S1 S2 =>
      simp [Shape.rename, Shape.tel, FCdot.Telescope.append_rename',
        Shape.tel_rename S1 ρ, Shape.tel_rename S2 ρ]
  | .mu S0 =>
      by_cases hd : S0.isDecl = true
      · simp [Shape.rename, Shape.tel, hd, Shape.isDecl_rename S0 ρ.lift,
          Shape.telSelf_rename S0 ρ]
      · simp [Shape.rename, Shape.tel, hd, Shape.isDecl_rename S0 ρ.lift,
          Shape.telSelf_rename S0 ρ, FCdot.Telescope.rename, FCdot.Proposition.rename,
          FCdot.Shape.weaken_rename, FCdot.Shape.rename]

theorem Shape.telSelf_rename {s s' : Sig} (S : Shape (s,x)) (ρ : Rename s s') :
    (S.rename ρ.lift).telSelf = S.telSelf.rename ρ.lift := by
  match S with
  | .top => simp [Shape.rename, Shape.telSelf, FCdot.Telescope.rename]
  | .bot =>
      simp [Shape.rename, Shape.telSelf, FCdot.Telescope.rename, FCdot.Proposition.rename,
        FCdot.Shape.rename]
  | .sel (.var y) A =>
      simp [Shape.rename, Path.rename, Shape.telSelf, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Shape.rename]
  | .all (.capt C1 S1) (.capt C2 S2) =>
      simp [Shape.rename, Ty.rename, Shape.telSelf, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Shape.rename, FCdot.Ty.rename,
        Shape.translate_rename S1 ρ.lift, Shape.translate_rename S2 ρ.lift.lift]
  | .box (.capt C S0) =>
      simp [Shape.rename, Ty.rename, Shape.telSelf, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Shape.rename, FCdot.Ty.rename,
        Shape.translate_rename S0 ρ.lift]
  | .typ A S1 S2 =>
      simp [Shape.rename, Shape.telSelf, FCdot.Telescope.rename, FCdot.Proposition.rename,
        FCdot.Shape.rename, FCdot.Rename.lift_here,
        Shape.translate_rename S1 ρ.lift, Shape.translate_rename S2 ρ.lift]
  | .fld a (.capt C S0) =>
      simp [Shape.rename, Ty.rename, Shape.telSelf, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Shape.rename, FCdot.Rename.lift_here,
        FCdot.CaptureSet.rename_name_here, Shape.translate_rename S0 ρ.lift]
  | .cap A c1 c2 =>
      simp [Shape.rename, Shape.telSelf, FCdot.Telescope.rename, FCdot.Proposition.rename,
        FCdot.CaptureSet.rename_name_here]
  | .and S1 S2 =>
      simp [Shape.rename, Shape.telSelf, FCdot.Telescope.append_rename',
        Shape.telSelf_rename S1 ρ, Shape.telSelf_rename S2 ρ]
  | .mu S0 =>
      have h1 : (S0.rename ρ.lift.lift).telSelf = (Shape.telSelf S0).rename ρ.lift.lift :=
        Shape.telSelf_rename S0 ρ.lift
      by_cases hd : S0.isDecl = true
      · have hd' : (S0.rename ρ.lift.lift).isDecl = true := by
          rw [Shape.isDecl_rename S0 ρ.lift.lift]; exact hd
        simp only [Shape.rename, Shape.telSelf, if_pos hd, if_pos hd']
        rw [h1, FCdot.Telescope.substVar_rename]
        simp [FCdot.Rename.lift_here]
      · have hd' : ¬ (S0.rename ρ.lift.lift).isDecl = true := by
          rw [Shape.isDecl_rename S0 ρ.lift.lift]; exact hd
        simp only [Shape.rename, Shape.telSelf, if_neg hd, if_neg hd']
        simp [FCdot.Telescope.rename, FCdot.Proposition.rename, FCdot.Shape.rename, h1]

end

/-- `⟦T⟧` commutes with renaming: the shape half is `Shape.translate_rename`,
the capture half is `CaptureSet.translate_rename`. -/
theorem Ty.translate_rename {s s' : Sig} (T : Ty s) (ρ : Rename s s') :
    (T.rename ρ).translate = T.translate.rename ρ := by
  cases T with
  | capt C S =>
      simp [Ty.rename, Ty.translate, FCdot.Ty.rename, Shape.translate_rename S ρ]

/-! ## `translate` and instantiation of the innermost binder -/

theorem Shape.translate_substVar {s : Sig} (S : Shape (s,x)) (r : BVar s .var) :
    (S.substVar r).translate = S.translate.substVar r :=
  Shape.translate_rename S (Rename.subst r)

theorem Ty.translate_substVar {s : Sig} (T : Ty (s,x)) (r : BVar s .var) :
    (T.substVar r).translate = T.translate.substVar r :=
  Ty.translate_rename T (Rename.subst r)

/-! ## `tel` on a shape equals `telSelf` on its weakening -/

theorem Shape.tel_eq_telSelf_weaken {s : Sig} (S : Shape s) : S.tel = (S.weaken).telSelf := by
  match S with
  | .top => simp [Shape.weaken, Shape.rename, Shape.tel, Shape.telSelf]
  | .bot =>
      simp [Shape.weaken, Shape.rename, Shape.tel, Shape.telSelf,
        FCdot.Shape.rename, FCdot.Shape.weaken]
  | .sel (.var y) A =>
      simp [Shape.weaken, Shape.rename, Path.rename, Shape.tel, Shape.telSelf,
        FCdot.Shape.rename, FCdot.Shape.weaken]
  | .all (.capt C1 S1) (.capt C2 S2) =>
      simp [Shape.weaken, Shape.rename, Ty.rename, Shape.tel, Shape.telSelf,
        FCdot.Shape.rename, FCdot.Shape.weaken, FCdot.Ty.rename,
        Shape.translate_rename S1 FCdot.Rename.succ,
        Shape.translate_rename S2 (FCdot.Rename.succ (k := Kind.var)).lift,
        CaptureSet.translate_rename C1 FCdot.Rename.succ,
        CaptureSet.translate_rename C2 (FCdot.Rename.succ (k := Kind.var)).lift]
  | .box (.capt C S0) =>
      simp [Shape.weaken, Shape.rename, Ty.rename, Shape.tel, Shape.telSelf,
        FCdot.Shape.rename, FCdot.Shape.weaken, FCdot.Ty.rename,
        Shape.translate_rename S0 FCdot.Rename.succ,
        CaptureSet.translate_rename C FCdot.Rename.succ]
  | .typ A S1 S2 =>
      simp [Shape.weaken, Shape.rename, Shape.tel, Shape.telSelf, FCdot.Shape.weaken,
        Shape.translate_rename S1 FCdot.Rename.succ, Shape.translate_rename S2 FCdot.Rename.succ]
  | .fld a (.capt C S0) =>
      simp [Shape.weaken, Shape.rename, Ty.rename, Shape.tel, Shape.telSelf,
        FCdot.Shape.weaken, FCdot.CaptureSet.weaken,
        Shape.translate_rename S0 FCdot.Rename.succ,
        CaptureSet.translate_rename C FCdot.Rename.succ]
  | .cap A c1 c2 =>
      simp [Shape.weaken, Shape.rename, Shape.tel, Shape.telSelf,
        FCdot.CaptureSet.weaken,
        CaptureSet.translate_rename c1 FCdot.Rename.succ,
        CaptureSet.translate_rename c2 FCdot.Rename.succ]
  | .and S1 S2 =>
      simp [Shape.weaken, Shape.rename, Shape.tel, Shape.telSelf,
        Shape.tel_eq_telSelf_weaken S1, Shape.tel_eq_telSelf_weaken S2]
  | .mu S0 =>
      have hw : (Shape.mu S0 : Shape s).weaken
          = Shape.mu (S0.rename (FCdot.Rename.succ (k := Kind.var)).lift) := by
        simp [Shape.weaken, Shape.rename]
      by_cases hd : S0.isDecl = true
      · have hd' : (S0.rename (FCdot.Rename.succ (k := Kind.var)).lift).isDecl = true := by
          rw [Shape.isDecl_rename S0 _]; exact hd
        have htel : (Shape.mu S0 : Shape s).tel = Shape.telSelf S0 := by simp [Shape.tel, hd]
        have htelSelf' :
            (Shape.mu (S0.rename (FCdot.Rename.succ (k := Kind.var)).lift) : Shape (s,x)).telSelf
              = ((S0.rename (FCdot.Rename.succ (k := Kind.var)).lift).telSelf).substVar .here := by
          simp [Shape.telSelf, hd']
        rw [htel, hw, htelSelf']
        rw [Shape.telSelf_rename S0 FCdot.Rename.succ, FCdot.Telescope.rename_lift_substVar_succ]
      · have hd' : ¬ (S0.rename (FCdot.Rename.succ (k := Kind.var)).lift).isDecl = true := by
          rw [Shape.isDecl_rename S0 _]; exact hd
        rw [hw]
        simp [Shape.tel, Shape.telSelf, hd, hd',
          FCdot.Shape.rename, FCdot.Shape.weaken, Shape.telSelf_rename S0 FCdot.Rename.succ]

end DotMNF

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Instantiating both self binders of a declaration agree -/

theorem Shape.tel_substVar {s : Sig} (S : Shape (s,x)) (r : BVar s .var) :
    (((S.substVar r).tel.substVar r).weaken : FCdot.Telescope (s,x)) =
      (S.telSelf.substVar r).weaken := by
  match S with
  | .top =>
      simp [Shape.substVar, Shape.rename, Shape.tel, Shape.telSelf, FCdot.Telescope.rename,
        FCdot.Telescope.weaken, FCdot.Telescope.substVar]
  | .bot =>
      simp [Shape.substVar, Shape.rename, Shape.tel, Shape.telSelf, FCdot.Telescope.rename,
        FCdot.Telescope.weaken, FCdot.Telescope.substVar, FCdot.Proposition.rename,
        FCdot.Shape.rename, FCdot.Shape.weaken]
  | .sel (.var y) A =>
      simp [Shape.substVar, Shape.rename, Path.rename, Shape.tel, Shape.telSelf,
        FCdot.Telescope.rename, FCdot.Telescope.weaken, FCdot.Telescope.substVar,
        FCdot.Proposition.rename, FCdot.Shape.rename, FCdot.Shape.weaken]
  | .all (.capt C1 S1) (.capt C2 S2) =>
      simp [Shape.substVar, Shape.rename, Ty.rename, Shape.tel, Shape.telSelf,
        FCdot.Telescope.rename, FCdot.Telescope.weaken, FCdot.Telescope.substVar,
        FCdot.Proposition.rename, FCdot.Shape.rename, FCdot.Shape.weaken, FCdot.Ty.rename,
        FCdot.Rename.comp_assoc, FCdot.Rename.succ_subst, FCdot.Rename.comp_id,
        ← FCdot.Rename.lift_comp,
        Shape.translate_rename S1 (Rename.subst r),
        Shape.translate_rename S2 (Rename.subst r).lift,
        CaptureSet.translate_rename C1 (Rename.subst r),
        CaptureSet.translate_rename C2 (Rename.subst r).lift]
  | .box (.capt C S0) =>
      simp [Shape.substVar, Shape.rename, Ty.rename, Shape.tel, Shape.telSelf,
        FCdot.Telescope.rename, FCdot.Telescope.weaken, FCdot.Telescope.substVar,
        FCdot.Proposition.rename, FCdot.Shape.rename, FCdot.Shape.weaken, FCdot.Ty.rename,
        FCdot.Rename.comp_assoc, FCdot.Rename.succ_subst, FCdot.Rename.comp_id,
        Shape.translate_rename S0 (Rename.subst r),
        CaptureSet.translate_rename C (Rename.subst r)]
  | .typ A S1 S2 =>
      simp [Shape.substVar, Shape.rename, Shape.tel, Shape.telSelf, FCdot.Telescope.rename,
        FCdot.Telescope.weaken, FCdot.Telescope.substVar, FCdot.Proposition.rename,
        FCdot.Shape.rename, FCdot.Shape.weaken, FCdot.Rename.subst_here,
        FCdot.Rename.comp_assoc, FCdot.Rename.succ_subst, FCdot.Rename.comp_id,
        Shape.translate_rename S1 (Rename.subst r), Shape.translate_rename S2 (Rename.subst r)]
  | .fld a (.capt C S0) =>
      simp [Shape.substVar, Shape.rename, Ty.rename, Shape.tel, Shape.telSelf,
        FCdot.Telescope.rename, FCdot.Telescope.weaken, FCdot.Telescope.substVar,
        FCdot.Proposition.rename, FCdot.Shape.rename, FCdot.Shape.weaken,
        FCdot.CaptureSet.weaken,
        FCdot.Rename.subst_here, FCdot.Rename.comp_assoc, FCdot.Rename.succ_subst,
        FCdot.Rename.comp_id, Shape.translate_rename S0 (Rename.subst r),
        CaptureSet.translate_rename C (Rename.subst r)]
  | .cap A c1 c2 =>
      simp [Shape.substVar, Shape.rename, Shape.tel, Shape.telSelf,
        FCdot.Telescope.rename, FCdot.Telescope.weaken, FCdot.Telescope.substVar,
        FCdot.Proposition.rename,
        FCdot.CaptureSet.weaken,
        FCdot.Rename.comp_assoc, FCdot.Rename.succ_subst,
        FCdot.Rename.comp_id, CaptureSet.translate_rename c1 (Rename.subst r),
        CaptureSet.translate_rename c2 (Rename.subst r)]
  | .and S1 S2 =>
      have hS := Shape.tel_substVar S1 r
      have hT := Shape.tel_substVar S2 r
      simp only [Shape.substVar, FCdot.Telescope.substVar, FCdot.Telescope.weaken,
        FCdot.Telescope.rename_comp] at hS hT
      simp only [Shape.substVar, Shape.rename, Shape.tel, Shape.telSelf,
        FCdot.Telescope.append_rename', FCdot.Telescope.substVar, FCdot.Telescope.weaken,
        FCdot.Telescope.rename_comp]
      rw [hS, hT]
  | .mu S0 =>
      have h1 : (S0.rename (Rename.subst r).lift).telSelf
          = (Shape.telSelf S0).rename (Rename.subst r).lift :=
        Shape.telSelf_rename S0 (Rename.subst r)
      by_cases hd : S0.isDecl = true
      · have hd' : (S0.rename (Rename.subst r).lift).isDecl = true := by
          rw [Shape.isDecl_rename S0 _]; exact hd
        have htel : ((Shape.mu S0 : Shape (s,x)).substVar r).tel
            = Shape.telSelf (S0.rename (Rename.subst r).lift) := by
          simp [Shape.substVar, Shape.rename, Shape.tel, hd']
        have htelSelf : (Shape.mu S0 : Shape (s,x)).telSelf
            = (Shape.telSelf S0).substVar (BVar.here) := by
          simp [Shape.telSelf, hd]
        rw [htel, htelSelf, h1]
        simp only [FCdot.Telescope.substVar, FCdot.Telescope.weaken, FCdot.Telescope.rename_comp,
          FCdot.Rename.subst_comp, FCdot.Rename.subst_here]
      · have hd' : ¬ (S0.rename (Rename.subst r).lift).isDecl = true := by
          rw [Shape.isDecl_rename S0 _]; exact hd
        have htel : ((Shape.mu S0 : Shape (s,x)).substVar r).tel
            = .cons .nil
                (.bnd (FCdot.Shape.obj (Shape.telSelf (S0.rename (Rename.subst r).lift))).weaken) := by
          simp [Shape.substVar, Shape.rename, Shape.tel, hd']
        have htelSelf : (Shape.mu S0 : Shape (s,x)).telSelf
            = .cons .nil (.bnd (FCdot.Shape.obj (Shape.telSelf S0))) := by
          simp [Shape.telSelf, hd]
        rw [htel, htelSelf, h1]
        simp [FCdot.Telescope.substVar, FCdot.Telescope.weaken, FCdot.Telescope.rename,
          FCdot.Proposition.rename, FCdot.Shape.rename, FCdot.Shape.weaken,
          FCdot.Telescope.rename_comp, FCdot.Rename.comp_assoc, FCdot.Rename.succ_subst,
          FCdot.Rename.comp_id, ← FCdot.Rename.lift_comp]

end DotMNF

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Witnesses, field labels, and the literal type -/

theorem Shape.witnesses_rename {s s' : Sig} (S : Shape (s,x)) (ρ : Rename s s') :
    (S.rename ρ.lift).witnesses = S.witnesses.rename ρ.lift := by
  match S with
  | .top => simp [Shape.rename, Shape.witnesses, FCdot.Witnesses.rename]
  | .bot => simp [Shape.rename, Shape.witnesses, FCdot.Witnesses.rename]
  | .sel p A => simp [Shape.rename, Shape.witnesses, FCdot.Witnesses.rename]
  | .all T1 T2 => simp [Shape.rename, Shape.witnesses, FCdot.Witnesses.rename]
  | .box T => simp [Shape.rename, Shape.witnesses, FCdot.Witnesses.rename]
  | .cap A c1 c2 => simp [Shape.rename, Shape.witnesses, FCdot.Witnesses.rename]
  | .typ A S1 S2 =>
      simp [Shape.rename, Shape.witnesses, FCdot.Witnesses.rename,
        Shape.translate_rename S1 ρ.lift]
  | .fld a (.capt C S0) =>
      simp [Shape.rename, Ty.rename, Shape.witnesses, FCdot.Witnesses.rename,
        Shape.translate_rename S0 ρ.lift]
  | .and S1 S2 =>
      simp [Shape.rename, Shape.witnesses, FCdot.Witnesses.append_rename,
        Shape.witnesses_rename S1 ρ, Shape.witnesses_rename S2 ρ]
  | .mu S0 => simp [Shape.rename, Shape.witnesses, FCdot.Witnesses.rename]

theorem Shape.fieldLabels_rename {s s' : Sig} (S : Shape s) (ρ : Rename s s') :
    (S.rename ρ).fieldLabels = S.fieldLabels := by
  match S with
  | .top => simp [Shape.rename, Shape.fieldLabels]
  | .bot => simp [Shape.rename, Shape.fieldLabels]
  | .sel p A => simp [Shape.rename, Shape.fieldLabels]
  | .all T1 T2 => simp [Shape.rename, Shape.fieldLabels]
  | .box T => simp [Shape.rename, Shape.fieldLabels]
  | .cap A c1 c2 => simp [Shape.rename, Shape.fieldLabels]
  | .typ A S1 S2 => simp [Shape.rename, Shape.fieldLabels]
  | .fld a T => simp [Shape.rename, Shape.fieldLabels]
  | .and S1 S2 =>
      simp [Shape.rename, Shape.fieldLabels, Shape.fieldLabels_rename S1 ρ,
        Shape.fieldLabels_rename S2 ρ]
  | .mu S0 => simp [Shape.rename, Shape.fieldLabels]

@[simp] theorem Shape.capWitnesses_rename {s s' : Sig} (S : Shape (s,x)) (ρ : Rename s s') :
    (S.rename ρ.lift).capWitnesses = S.capWitnesses.rename ρ.lift := by
  match S with
  | .top => simp [Shape.rename, Shape.capWitnesses, FCdot.CapWitnesses.rename]
  | .bot => simp [Shape.rename, Shape.capWitnesses, FCdot.CapWitnesses.rename]
  | .sel p A => simp [Shape.rename, Shape.capWitnesses, FCdot.CapWitnesses.rename]
  | .all T1 T2 => simp [Shape.rename, Shape.capWitnesses, FCdot.CapWitnesses.rename]
  | .box T => simp [Shape.rename, Shape.capWitnesses, FCdot.CapWitnesses.rename]
  | .typ A S1 S2 => simp [Shape.rename, Shape.capWitnesses, FCdot.CapWitnesses.rename]
  | .cap A c1 c2 =>
      simp [Shape.rename, Shape.capWitnesses, FCdot.CapWitnesses.rename]
  | .fld a (.capt C S0) =>
      simp [Shape.rename, Ty.rename, Shape.capWitnesses, FCdot.CapWitnesses.rename]
  | .and S1 S2 =>
      simp [Shape.rename, Shape.capWitnesses, FCdot.CapWitnesses.append_rename,
        Shape.capWitnesses_rename S1 ρ, Shape.capWitnesses_rename S2 ρ]
  | .mu S0 => simp [Shape.rename, Shape.capWitnesses, FCdot.CapWitnesses.rename]

theorem Shape.literalShape_rename {s s' : Sig} (S : Shape (s,x)) (ρ : Rename s s') :
    (S.rename ρ.lift).literalShape = S.literalShape.rename ρ := by
  simp only [Shape.literalShape, FCdot.Shape.rename, Shape.witnesses_rename S ρ,
    Shape.fieldLabels_rename (S := S) (ρ := ρ.lift), Shape.capWitnesses_rename S ρ]
  rw [FCdot.Telescope.ofLiteral_rename]

theorem Shape.literalTy_rename {s s' : Sig} (S : Shape (s,x)) (U : CaptureSet s)
    (ρ : Rename s s') :
    (S.rename ρ.lift).literalTy (U.rename ρ) = (S.literalTy U).rename ρ := by
  simp only [Shape.literalTy, FCdot.Ty.rename, Shape.literalShape_rename S ρ,
    CaptureSet.translate_rename U ρ]

end DotMNF

/-! ## Declaration-shaped shapes are preserved by renaming -/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

theorem Shape.Decl.rename : ∀ {s1 s2 : Sig} {S : Shape s1}, Shape.Decl S → ∀ (ρ : Rename s1 s2),
    Shape.Decl (S.rename ρ)
  | _, _, _, .top, _ => .top
  | _, _, _, .typ, _ => .typ
  | _, _, _, .cap, _ => .cap
  | _, _, _, .fld, _ => .fld
  | _, _, _, .mu h, ρ => .mu (Shape.Decl.rename h ρ.lift)
  | _, _, _, .and hS hT, ρ => .and (Shape.Decl.rename hS ρ) (Shape.Decl.rename hT ρ)

theorem Shape.Decl.substVar {s : Sig} {S : Shape (s,x)} (h : Shape.Decl S) (r : BVar s .var) :
    Shape.Decl (S.substVar r) :=
  h.rename (Rename.subst r)

/-! ## Every declaration-shaped shape translates to its telescope -/

/-- A declaration shape is an object shape. -/
theorem Shape.Decl.isObj {s : Sig} {S : Shape s} (h : Shape.Decl S) : S.isObj = true := by
  cases h with
  | top => rfl
  | typ => rfl
  | cap => rfl
  | fld => rfl
  | and => rfl
  | mu h' => exact (Shape.isDecl_iff _).mpr h'

theorem Shape.translate_decl {s : Sig} {S : Shape s} (h : Shape.Decl S) :
    S.translate = .obj S.tel :=
  Shape.translate_isObj h.isObj

/-- The same one layer up: a type whose shape is declaration-shaped
translates to the object type of the shape's telescope, at the translated
capture set. -/
theorem Ty.translate_decl {s : Sig} {S : Shape s} {C : CaptureSet s} (h : Shape.Decl S) :
    (S ^ C).translate = FCdot.Ty.capt C.translate (.obj S.tel) := by
  rw [Ty.translate_capt, Shape.translate_decl h]

end DotMNF

/-! ## Context translation and lookup -/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

theorem Ctx.translate_lookup_cons {s : Sig} (Γ : Ctx s) (T : Ty s) :
    (Γ.cons T).translate.lookupTy .here = T.translate.weaken := rfl

theorem Ctx.translate_lookup_cons_there {s : Sig} (Γ : Ctx s) (T : Ty s) (y : BVar s .var) :
    (Γ.cons T).translate.lookupTy (.there y) = (Γ.translate.lookupTy y).weaken := rfl

theorem Ctx.translate_lookup_consSelf {s : Sig} (Γ : Ctx s) (d : Defs (s,x)) (S : Shape (s,x))
    (U : CaptureSet s) :
    (Γ.consSelf d S U).translate.lookupTy .here = (S.literalTy U).weaken := rfl

theorem Ctx.translate_lookup_consSelf_there {s : Sig} (Γ : Ctx s) (d : Defs (s,x))
    (S : Shape (s,x)) (U : CaptureSet s) (y : BVar s .var) :
    (Γ.consSelf d S U).translate.lookupTy (.there y) = (Γ.translate.lookupTy y).weaken := rfl

theorem Ctx.translate_lookup_consC_there {s : Sig} (Γ : Ctx s) (y : BVar s .var) :
    (Ctx.consC Γ).translate.lookupTy (.there y) = (Γ.translate.lookupTy y).weaken := rfl

end DotMNF

end Captures
