import Coercions.Classifiers.DotToFCdot.Types
import Coercions.Classifiers.FCdot.RenameLemmas
import Coercions.Classifiers.FCdot.Levels

namespace Classifiers

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

/-- The instance set of a weakened capture bound, weakened.  It is
`FCdot.CapBound.instSet?_weaken`, restated here because this file does not
import `FCdot.TypingRename`. -/
theorem CapBound.instSet?_weaken' {s : Sig} {k : Kind} (b : CapBound s) :
    (CapBound.weaken (k := k) b).instSet? = (b.instSet?).map (CaptureSet.weaken (k := k)) := by
  cases b <;> rfl

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
  | .all (.capt C1 S1) (.ty (.capt C2 S2)) =>
      simp [Shape.rename, Ty.rename, ETy.rename, Shape.translate, FCdot.Shape.rename,
        FCdot.Ty.rename, FCdot.ETy.rename,
        Shape.translate_rename S1 ρ.lift, Shape.translate_rename S2 ρ.lift.lift]
  | .all (.capt C1 S1) (.ex C0 (.capt C2 S2)) =>
      simp [Shape.rename, Ty.rename, ETy.rename, Shape.translate, FCdot.Shape.rename,
        FCdot.Ty.rename, FCdot.ETy.rename,
        Shape.translate_rename S1 ρ.lift, Shape.translate_rename S2 ρ.lift.lift.lift]
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
  | .all (.capt C1 S1) (.ty (.capt C2 S2)) =>
      simp [Shape.rename, Ty.rename, ETy.rename, Shape.tel, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Shape.weaken_rename, FCdot.Shape.rename,
        FCdot.Ty.rename, FCdot.ETy.rename,
        Shape.translate_rename S1 ρ.lift, Shape.translate_rename S2 ρ.lift.lift]
  | .all (.capt C1 S1) (.ex C0 (.capt C2 S2)) =>
      simp [Shape.rename, Ty.rename, ETy.rename, Shape.tel, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Shape.weaken_rename, FCdot.Shape.rename,
        FCdot.Ty.rename, FCdot.ETy.rename,
        Shape.translate_rename S1 ρ.lift, Shape.translate_rename S2 ρ.lift.lift.lift]
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
  | .all (.capt C1 S1) (.ty (.capt C2 S2)) =>
      simp [Shape.rename, Ty.rename, ETy.rename, Shape.telSelf, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Shape.rename, FCdot.Ty.rename, FCdot.ETy.rename,
        Shape.translate_rename S1 ρ.lift.lift, Shape.translate_rename S2 ρ.lift.lift.lift]
  | .all (.capt C1 S1) (.ex C0 (.capt C2 S2)) =>
      simp [Shape.rename, Ty.rename, ETy.rename, Shape.telSelf, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Shape.rename, FCdot.Ty.rename, FCdot.ETy.rename,
        Shape.translate_rename S1 ρ.lift.lift,
        Shape.translate_rename S2 ρ.lift.lift.lift.lift]
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

/-- The answer translation commutes with renaming: one clause per
constructor, each from `Ty.translate_rename`. -/
theorem ETy.translate_rename {s s' : Sig} (E : ETy s) (ρ : Rename s s') :
    (E.rename ρ).translate = E.translate.rename ρ := by
  cases E with
  | ty T => simp [ETy.rename, ETy.translate, FCdot.ETy.rename, Ty.translate_rename T ρ]
  | ex C T =>
      simp [ETy.rename, ETy.translate, FCdot.ETy.rename, Ty.translate_rename T ρ.lift]

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
  | .all (.capt C1 S1) (.ty (.capt C2 S2)) =>
      simp [Shape.weaken, Shape.rename, Ty.rename, ETy.rename, Shape.tel, Shape.telSelf,
        FCdot.Shape.rename, FCdot.Shape.weaken, FCdot.Ty.rename, FCdot.ETy.rename,
        Shape.translate_rename S1 (FCdot.Rename.succ (k := Kind.var)).lift,
        Shape.translate_rename S2 (FCdot.Rename.succ (k := Kind.var)).lift.lift,
        CaptureSet.translate_rename C1 (FCdot.Rename.succ (k := Kind.var)).lift,
        CaptureSet.translate_rename C2 (FCdot.Rename.succ (k := Kind.var)).lift.lift]
  | .all (.capt C1 S1) (.ex C0 (.capt C2 S2)) =>
      simp [Shape.weaken, Shape.rename, Ty.rename, ETy.rename, Shape.tel, Shape.telSelf,
        FCdot.Shape.rename, FCdot.Shape.weaken, FCdot.Ty.rename, FCdot.ETy.rename,
        Shape.translate_rename S1 (FCdot.Rename.succ (k := Kind.var)).lift,
        Shape.translate_rename S2 (FCdot.Rename.succ (k := Kind.var)).lift.lift.lift,
        CaptureSet.translate_rename C1 (FCdot.Rename.succ (k := Kind.var)).lift,
        CaptureSet.translate_rename C0 (FCdot.Rename.succ (k := Kind.var)).lift.lift,
        CaptureSet.translate_rename C2 (FCdot.Rename.succ (k := Kind.var)).lift.lift.lift]
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
  | .all (.capt C1 S1) (.ty (.capt C2 S2)) =>
      simp [Shape.substVar, Shape.rename, Ty.rename, ETy.rename, Shape.tel, Shape.telSelf,
        FCdot.Telescope.rename, FCdot.Telescope.weaken, FCdot.Telescope.substVar,
        FCdot.Proposition.rename, FCdot.Shape.rename, FCdot.Shape.weaken, FCdot.Ty.rename,
        FCdot.ETy.rename,
        FCdot.Rename.comp_assoc, FCdot.Rename.succ_subst, FCdot.Rename.comp_id,
        ← FCdot.Rename.lift_comp,
        Shape.translate_rename S1 (Rename.subst r).lift,
        Shape.translate_rename S2 (Rename.subst r).lift.lift,
        CaptureSet.translate_rename C1 (Rename.subst r).lift,
        CaptureSet.translate_rename C2 (Rename.subst r).lift.lift]
  | .all (.capt C1 S1) (.ex C0 (.capt C2 S2)) =>
      simp [Shape.substVar, Shape.rename, Ty.rename, ETy.rename, Shape.tel, Shape.telSelf,
        FCdot.Telescope.rename, FCdot.Telescope.weaken, FCdot.Telescope.substVar,
        FCdot.Proposition.rename, FCdot.Shape.rename, FCdot.Shape.weaken, FCdot.Ty.rename,
        FCdot.ETy.rename,
        FCdot.Rename.comp_assoc, FCdot.Rename.succ_subst, FCdot.Rename.comp_id,
        ← FCdot.Rename.lift_comp,
        Shape.translate_rename S1 (Rename.subst r).lift,
        Shape.translate_rename S2 (Rename.subst r).lift.lift.lift,
        CaptureSet.translate_rename C1 (Rename.subst r).lift,
        CaptureSet.translate_rename C0 (Rename.subst r).lift.lift,
        CaptureSet.translate_rename C2 (Rename.subst r).lift.lift.lift]
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

/-! ## Injectivity of renaming on source shapes

The `obj` rule of B1.7 types a literal's definitions against its declaration
shape read under the class root, so the facts the translation needs about
that shape have to travel back through one renaming.  Renaming a source
shape by an injective renaming is injective, exactly as it is in the target
(`FCdot.Shape.rename_inj`). -/

theorem Path.rename_inj {s1 s2 : Sig} (p p' : Path s1) (ρ : FCdot.Rename s1 s2)
    (hρ : ρ.Injective) (h : p.rename ρ = p'.rename ρ) : p = p' := by
  cases p; cases p'
  simp only [Path.rename, Path.var.injEq] at h ⊢
  exact hρ _ _ h

theorem CapAtom.rename_inj {s1 s2 : Sig} (a a' : CapAtom s1) (ρ : FCdot.Rename s1 s2)
    (hρ : ρ.Injective) (h : a.rename ρ = a'.rename ρ) : a = a' := by
  cases a <;> cases a' <;> simp [CapAtom.rename] at h ⊢
  · exact hρ _ _ h
  · exact hρ _ _ h
  · exact ⟨hρ _ _ h.1, h.2⟩

theorem CaptureSet.rename_inj {s1 s2 : Sig} (ρ : FCdot.Rename s1 s2) (hρ : ρ.Injective) :
    ∀ (C C' : CaptureSet s1), CaptureSet.rename C ρ = CaptureSet.rename C' ρ → C = C'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [CaptureSet.rename] at h
  | _ :: _, [], h => by simp [CaptureSet.rename] at h
  | a :: C, a' :: C', h => by
      simp only [CaptureSet.rename_cons, List.cons.injEq] at h ⊢
      exact ⟨CapAtom.rename_inj a a' ρ hρ h.1, CaptureSet.rename_inj ρ hρ C C' h.2⟩

mutual

theorem Shape.rename_inj {s1 s2 : Sig} (S S' : Shape s1) (ρ : FCdot.Rename s1 s2)
    (hρ : ρ.Injective) (h : S.rename ρ = S'.rename ρ) : S = S' := by
  match S with
  | .top => cases S' <;> simp [Shape.rename] at h ⊢
  | .bot => cases S' <;> simp [Shape.rename] at h ⊢
  | .sel p A =>
      cases S' <;> simp [Shape.rename] at h ⊢
      exact ⟨Path.rename_inj p _ ρ hρ h.1, h.2⟩
  | .typ A S1 S2 =>
      cases S' <;> simp [Shape.rename] at h ⊢
      exact ⟨h.1, Shape.rename_inj S1 _ ρ hρ h.2.1, Shape.rename_inj S2 _ ρ hρ h.2.2⟩
  | .fld a T =>
      cases S' <;> simp [Shape.rename] at h ⊢
      exact ⟨h.1, Ty.rename_inj T _ ρ hρ h.2⟩
  | .cap A c1 c2 =>
      cases S' <;> simp [Shape.rename] at h ⊢
      exact ⟨h.1, CaptureSet.rename_inj ρ hρ c1 _ h.2.1, CaptureSet.rename_inj ρ hρ c2 _ h.2.2⟩
  | .mu S0 =>
      cases S' <;> simp [Shape.rename] at h ⊢
      exact Shape.rename_inj S0 _ ρ.lift hρ.lift h
  | .all T1 T2 =>
      cases S' <;> simp [Shape.rename] at h ⊢
      exact ⟨Ty.rename_inj T1 _ ρ.lift hρ.lift h.1,
        ETy.rename_inj T2 _ ρ.lift.lift
          (FCdot.Rename.Injective.lift (FCdot.Rename.Injective.lift hρ)) h.2⟩
  | .and S1 S2 =>
      cases S' <;> simp [Shape.rename] at h ⊢
      exact ⟨Shape.rename_inj S1 _ ρ hρ h.1, Shape.rename_inj S2 _ ρ hρ h.2⟩
  | .box T =>
      cases S' <;> simp [Shape.rename] at h ⊢
      exact Ty.rename_inj T _ ρ hρ h

theorem Ty.rename_inj {s1 s2 : Sig} (T T' : Ty s1) (ρ : FCdot.Rename s1 s2)
    (hρ : ρ.Injective) (h : T.rename ρ = T'.rename ρ) : T = T' := by
  match T with
  | .capt C S =>
      cases T' <;> simp [Ty.rename] at h ⊢
      exact ⟨CaptureSet.rename_inj ρ hρ C _ h.1, Shape.rename_inj S _ ρ hρ h.2⟩

theorem ETy.rename_inj {s1 s2 : Sig} (E E' : ETy s1) (ρ : FCdot.Rename s1 s2)
    (hρ : ρ.Injective) (h : E.rename ρ = E'.rename ρ) : E = E' := by
  match E with
  | .ty T =>
      cases E' <;> simp [ETy.rename] at h ⊢
      exact Ty.rename_inj T _ ρ hρ h
  | .ex C T =>
      cases E' <;> simp [ETy.rename] at h ⊢
      exact ⟨CaptureSet.rename_inj ρ hρ C _ h.1, Ty.rename_inj T _ ρ.lift hρ.lift h.2⟩

end

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

theorem Ctx.translate_lookup_consRoot_there {s : Sig} (Γ : Ctx s) (y : BVar s .var) :
    (Ctx.consRoot Γ).translate.lookupTy (.there y) = (Γ.translate.lookupTy y).weaken := rfl

/-! ## Instance binders translate to instance binders -/

/-- The set an instance binder stands for is translated pointwise, so a
source instance fact becomes the target instance fact the rule `instC`
reads. -/
theorem Ctx.translate_lookupCapInst {s : Sig} : ∀ (Γ : Ctx s) (κ : BVar s .cap),
    (Γ.translate.lookupCap κ).instSet? = (Γ.instSet? κ).map CaptureSet.translate
  | .cons Γ _, .there κ => by
      show (FCdot.CapBound.weaken (Γ.translate.lookupCap κ)).instSet? = _
      rw [FCdot.CapBound.instSet?_weaken', Ctx.translate_lookupCapInst Γ κ]
      simp [Ctx.instSet?, Option.map_map, Function.comp_def, CaptureSet.translate_weaken]
  | .consSelf Γ _ _ _, .there κ => by
      show (FCdot.CapBound.weaken (Γ.translate.lookupCap κ)).instSet? = _
      rw [FCdot.CapBound.instSet?_weaken', Ctx.translate_lookupCapInst Γ κ]
      simp [Ctx.instSet?, Option.map_map, Function.comp_def, CaptureSet.translate_weaken]
  | .consC Γ, .there κ => by
      show (FCdot.CapBound.weaken (Γ.translate.lookupCap κ)).instSet? = _
      rw [FCdot.CapBound.instSet?_weaken', Ctx.translate_lookupCapInst Γ κ]
      simp [Ctx.instSet?, Option.map_map, Function.comp_def, CaptureSet.translate_weaken]
  | .consC _, .here => rfl
  | .consRoot Γ, .there κ => by
      show (FCdot.CapBound.weaken (Γ.translate.lookupCap κ)).instSet? = _
      rw [FCdot.CapBound.instSet?_weaken', Ctx.translate_lookupCapInst Γ κ]
      simp [Ctx.instSet?, Option.map_map, Function.comp_def, CaptureSet.translate_weaken]
  | .consRoot _, .here => rfl
  | .consInst Γ _, .there κ => by
      show (FCdot.CapBound.weaken (Γ.translate.lookupCap κ)).instSet? = _
      rw [FCdot.CapBound.instSet?_weaken', Ctx.translate_lookupCapInst Γ κ]
      simp [Ctx.instSet?, Option.map_map, Function.comp_def, CaptureSet.translate_weaken]
  | .consInst _ C, .here => by
      show (FCdot.CapBound.weaken (FCdot.CapBound.inst C.translate)).instSet? = _
      simp [FCdot.CapBound.weaken, FCdot.CapBound.rename, FCdot.CapBound.instSet?,
        Ctx.instSet?, CaptureSet.translate_weaken, FCdot.CaptureSet.weaken]

theorem Ctx.translate_instSet? {s : Sig} (Γ : Ctx s) (κ : BVar s .cap) :
    Γ.translate.instSet? (FCdot.CapAtom.cvar κ) = (Γ.instSet? κ).map CaptureSet.translate :=
  Ctx.translate_lookupCapInst Γ κ

/-- The source instance fact, read in the target. -/
theorem Ctx.InstOf.translate {s : Sig} {Γ : Ctx s} {κ : BVar s .cap} {C : CaptureSet s}
    (h : Γ.InstOf κ C) : Γ.translate.InstOf (FCdot.CapAtom.cvar κ) C.translate := by
  show Γ.translate.instSet? (FCdot.CapAtom.cvar κ) = _
  rw [Ctx.translate_instSet?, h]
  rfl

/-! ## The scope contexts translate to the target's scope contexts

The source binds the same binders in the same places, so `Ctx.translate` is
a homomorphism on the three scope contexts of B1.1. -/

theorem Ty.translate_underRoot {s : Sig} (T : Dom s) :
    (Dom.underRoot T).translate = FCdot.Dom.underRoot T.translate :=
  Ty.translate_rename T FCdot.Rename.succ.lift

theorem Ty.translate_underRootCod {s : Sig} (E : Cod s) :
    (Cod.underRoot E).translate = FCdot.Cod.underRoot E.translate :=
  ETy.translate_rename E FCdot.Rename.succ.lift.lift

@[simp] theorem Ctx.translate_scope {s : Sig} (Γ : Ctx s) :
    (Γ.scope).translate = Γ.translate.scope := rfl

/-- The pack's scope translates to the target's pack scope: a root and then
the instance binder at the translated witness. -/
@[simp] theorem Ctx.translate_scopeInst {s : Sig} (Γ : Ctx s) (C : CaptureSet s) :
    (Γ.scopeInst C).translate = Γ.translate.scopeInst C.translate := by
  simp only [Ctx.scopeInst, Ctx.translate, FCdot.Ctx.scopeInst, CaptureSet.translate_weaken]

@[simp] theorem Ctx.translate_body {s : Sig} (Γ : Ctx s) (T : Dom s) :
    (Γ.body T).translate = Γ.translate.body T.translate := by
  simp only [Ctx.body, Ctx.translate, FCdot.Ctx.body, Ctx.translate_scope,
    Ty.translate_underRoot]

/-- The source's object body translates to the target's: the class root
becomes a root capture binder and the self a transparent binder at the
literal's precise type, with the witnesses read under the class root by the
same insertion on both sides. -/
theorem Ctx.translate_objBody {s : Sig} (Γ : Ctx s) (d : Defs ((s,c),x)) (S : Shape (s,x))
    (U : CaptureSet s) :
    (Γ.objBody d S U).translate
      = Γ.translate.objBody (S.literalTy U) S.witnesses S.capWitnesses S.fieldLabels := by
  show FCdot.Ctx.cons (FCdot.Ctx.consC Γ.translate .root)
      (.transparent ((S.rename FCdot.Rename.succ.lift).literalTy (U.rename FCdot.Rename.succ))
        (S.rename FCdot.Rename.succ.lift).witnesses
        (S.rename FCdot.Rename.succ.lift).capWitnesses
        (S.rename FCdot.Rename.succ.lift).fieldLabels) = _
  rw [Shape.literalTy_rename S U FCdot.Rename.succ, Shape.witnesses_rename S FCdot.Rename.succ,
    Shape.capWitnesses_rename S FCdot.Rename.succ,
    Shape.fieldLabels_rename S FCdot.Rename.succ.lift]
  rfl

/-- The shape witnesses and the field labels of a literal are written under
the self alone, so the class root is inserted below them by the same
renaming on both sides. -/
theorem Shape.translate_underRoot {s : Sig} (S : Shape (s,x)) :
    (Shape.underRoot S).translate = S.translate.rename FCdot.Rename.succ.lift :=
  Shape.translate_rename S FCdot.Rename.succ.lift


/-! ## The level spine commutes with the translation

**T-B3.2.**  `Ctx.translate` maps `consRoot` to `.consC _ .root` and every
other capture binder to a non-root capture bound, so the target binder at a
position is a root exactly when the source binder is.  Each of the five is a
recursion on the context with one case per constructor. -/

theorem Ctx.translate_root? : ∀ {s : Sig} (Γ : Ctx s), Γ.translate.root? = Γ.root?
  | _, .nil => rfl
  | _, .cons Γ _ => by
      show (FCdot.Ctx.cons Γ.translate _).root? = _
      rw [FCdot.Ctx.root?, Ctx.root?, Ctx.translate_root? Γ]
  | _, .consSelf Γ _ _ _ => by
      show (FCdot.Ctx.cons Γ.translate _).root? = _
      rw [FCdot.Ctx.root?, Ctx.root?, Ctx.translate_root? Γ]
  | _, .consC Γ => by
      show (FCdot.Ctx.consC Γ.translate .star).root? = _
      rw [FCdot.Ctx.root?_consC_of_not_root _ _ rfl, Ctx.root?, Ctx.translate_root? Γ]
  | _, .consInst Γ C => by
      show (FCdot.Ctx.consC Γ.translate (.inst C.translate)).root? = _
      rw [FCdot.Ctx.root?_consC_of_not_root _ _ rfl, Ctx.root?, Ctx.translate_root? Γ]
  | _, .consRoot Γ => rfl

theorem Ctx.translate_lvl : ∀ {s : Sig} {k : Kind} (Γ : Ctx s) (y : BVar s k),
    Γ.translate.lvl y = Γ.lvl y
  | _, _, .cons Γ _, .here => by
      show (FCdot.Ctx.cons Γ.translate _).lvl .here = _
      rw [FCdot.Ctx.lvl, Ctx.lvl, Ctx.translate_root? Γ]
  | _, _, .consSelf Γ _ _ _, .here => by
      show (FCdot.Ctx.cons Γ.translate _).lvl .here = _
      rw [FCdot.Ctx.lvl, Ctx.lvl, Ctx.translate_root? Γ]
  | _, _, .consC Γ, .here => by
      show (FCdot.Ctx.consC Γ.translate .star).lvl .here = _
      rw [FCdot.Ctx.lvl_consC_here_of_not_root _ _ rfl, Ctx.lvl, Ctx.translate_root? Γ]
  | _, _, .consInst Γ C, .here => by
      show (FCdot.Ctx.consC Γ.translate (.inst C.translate)).lvl .here = _
      rw [FCdot.Ctx.lvl_consC_here_of_not_root _ _ rfl, Ctx.lvl, Ctx.translate_root? Γ]
  | _, _, .consRoot _, .here => rfl
  | _, _, .cons Γ _, .there y => by
      show (FCdot.Ctx.cons Γ.translate _).lvl (.there y) = _
      rw [FCdot.Ctx.lvl, Ctx.lvl, Ctx.translate_lvl Γ y]
  | _, _, .consSelf Γ _ _ _, .there y => by
      show (FCdot.Ctx.cons Γ.translate _).lvl (.there y) = _
      rw [FCdot.Ctx.lvl, Ctx.lvl, Ctx.translate_lvl Γ y]
  | _, _, .consC Γ, .there y => by
      show (FCdot.Ctx.consC Γ.translate .star).lvl (.there y) = _
      rw [FCdot.Ctx.lvl, Ctx.lvl, Ctx.translate_lvl Γ y]
  | _, _, .consInst Γ C, .there y => by
      show (FCdot.Ctx.consC Γ.translate (.inst C.translate)).lvl (.there y) = _
      rw [FCdot.Ctx.lvl, Ctx.lvl, Ctx.translate_lvl Γ y]
  | _, _, .consRoot Γ, .there y => by
      show (FCdot.Ctx.consC Γ.translate .root).lvl (.there y) = _
      rw [FCdot.Ctx.lvl, Ctx.lvl, Ctx.translate_lvl Γ y]

theorem Ctx.translate_rootB : ∀ {s : Sig} (Γ : Ctx s) (κ : BVar s .cap),
    (Γ.translate.lookupCap κ).isRoot = Γ.rootB κ
  | _, .consRoot _, .here => rfl
  | _, .consC _, .here => rfl
  | _, .consInst _ _, .here => rfl
  | _, .cons Γ _, .there κ => by
      show (FCdot.CapBound.weaken (Γ.translate.lookupCap κ)).isRoot = _
      rw [FCdot.CapBound.isRoot_weaken, Ctx.translate_rootB Γ κ]; rfl
  | _, .consSelf Γ _ _ _, .there κ => by
      show (FCdot.CapBound.weaken (Γ.translate.lookupCap κ)).isRoot = _
      rw [FCdot.CapBound.isRoot_weaken, Ctx.translate_rootB Γ κ]; rfl
  | _, .consC Γ, .there κ => by
      show (FCdot.CapBound.weaken (Γ.translate.lookupCap κ)).isRoot = _
      rw [FCdot.CapBound.isRoot_weaken, Ctx.translate_rootB Γ κ]; rfl
  | _, .consInst Γ _, .there κ => by
      show (FCdot.CapBound.weaken (Γ.translate.lookupCap κ)).isRoot = _
      rw [FCdot.CapBound.isRoot_weaken, Ctx.translate_rootB Γ κ]; rfl
  | _, .consRoot Γ, .there κ => by
      show (FCdot.CapBound.weaken (Γ.translate.lookupCap κ)).isRoot = _
      rw [FCdot.CapBound.isRoot_weaken, Ctx.translate_rootB Γ κ]; rfl

theorem Ctx.IsRoot.translate {s : Sig} {Γ : Ctx s} {κ : BVar s .cap}
    (h : Γ.IsRoot (.cvar κ)) : Γ.translate.IsRoot (FCdot.CapAtom.cvar κ) := by
  show (Γ.translate.lookupCap κ).isRoot = true
  rw [Ctx.translate_rootB Γ κ]; exact h

theorem Ctx.LvlLe.translate {s : Sig} {Γ : Ctx s} {e : CapAtom s} {κ : BVar s .cap}
    {e' : FCdot.CapAtom s} (he : e.translate? = some e')
    (h : Γ.LvlLe e (.cvar κ)) :
    Γ.translate.LvlLe e' (FCdot.CapAtom.cvar κ) := by
  cases e with
  | var x =>
      cases he
      show FCdot.depthGe ((Γ.translate.lvl x).map FCdot.BVar.depth) (some κ.depth) = true
      rw [Ctx.translate_lvl Γ x]; exact h
  | cvar ν =>
      cases he
      show FCdot.depthGe ((Γ.translate.lvl ν).map FCdot.BVar.depth) (some κ.depth) = true
      rw [Ctx.translate_lvl Γ ν]; exact h
  | sel x A =>
      cases he
      show FCdot.depthGe ((Γ.translate.lvl x).map FCdot.BVar.depth) (some κ.depth) = true
      rw [Ctx.translate_lvl Γ x]; exact h
  | any => exact absurd h (by simp [Ctx.LvlLe, Ctx.lvlLeB])
  | fresh => exact absurd h (by simp [Ctx.LvlLe, Ctx.lvlLeB])

end DotMNF

end Classifiers
