import Coercions.Paths.DotToFCdot.Types
import Coercions.Paths.FCdot.RenameLemmas
import Coercions.Paths.FCdot.TypingPathSubst

namespace Paths

/-!
# Renaming and path substitution for the type translation (Plan III §8.1, M3, and P2.7)

The type translation `Ty.translate`, `Ty.tel`, `Ty.telSelfAt` (`DotToFCdot/Types.lean`) is a
mutual recursion over the shape of `Ty`.  This file proves that it commutes with path
substitution (`Ty.translate_subst`, `Ty.tel_subst`, `Ty.telSelfAt_subst`), and derives from it
the commutation with renaming, the opening of a body at a path (`Ty.tel_substPath`) and at a
variable (`Ty.tel_substVar`), and the context-lookup facts the typedness proofs need.

The composition law of path substitutions is `FCdot.Telescope.subst_subst` of
`FCdot/TypingPathSubst.lean`, which this module imports for it.
-/

namespace FCdot

/-! ## `Witnesses.append` commutes with renaming -/

theorem Witnesses.append_rename {s1 s2 : Sig} :
    ∀ (W W' : Witnesses s1) (ρ : Rename s1 s2),
      (W.append W').rename ρ = (W.rename ρ).append (W'.rename ρ)
  | _, .nil, _ => rfl
  | W, .cons W' ℓ T, ρ => by
      simp [Witnesses.append, Witnesses.rename, Witnesses.append_rename W W' ρ]

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
(rather than the `++` notation): the definitions of `Ty.tel`/`Ty.telSelf` use `.append`
directly, and `simp`/`rw` do not see through the `Append` instance to match `++`. -/
theorem Telescope.append_rename' {s1 s2 : Sig} (Tel Tel' : Telescope s1) (ρ : Rename s1 s2) :
    (Tel.append Tel').rename ρ = (Tel.rename ρ).append (Tel'.rename ρ) :=
  Telescope.append_rename Tel Tel' ρ

/-- `Telescope.append_subst` against the plain `Telescope.append` function. -/
theorem Telescope.append_subst' {s1 s2 : Sig} (Tel Tel' : Telescope s1) (σ : PathSubst s1 s2) :
    (Tel.append Tel').subst σ = (Tel.subst σ).append (Tel'.subst σ) :=
  Telescope.append_subst Tel Tel' σ

/-- `Telescope.append_substPath` against the plain `Telescope.append` function. -/
theorem Telescope.append_substPath' {s : Sig} (Tel Tel' : Telescope (s,x)) (q : Path s) :
    (Tel.append Tel').substPath q = (Tel.substPath q).append (Tel'.substPath q) :=
  Telescope.append_substPath Tel Tel' q

/-- Instantiating the self at `self` and then substituting is substituting under the self
and then instantiating at the image of `self`, when that image is a variable. -/
theorem Telescope.substVar_subst {s1 s2 : Sig} (Tel : Telescope (s1,x)) (self : BVar s1 .var)
    (self' : BVar s2 .var) (σ : PathSubst s1 s2) (h : σ.var self = .var self') :
    (Tel.substVar self).subst σ = (Tel.subst σ.lift).substVar self' := by
  rw [Telescope.substVar, Telescope.substVar, Telescope.rename_subst, Telescope.subst_rename]
  congr 1
  apply PathSubst.funext'
  intro y
  cases y with
  | here => exact h
  | there y =>
      show σ.var y = ((σ.var y).rename Rename.succ).rename (Rename.subst self')
      rw [Path.rename_comp, Rename.succ_subst, Path.rename_id]

/-- The same when the image of the self is a path: substituting under the self and then
instantiating it at the image of `self` is instantiating at `self` and then substituting. -/
theorem Telescope.subst_lift_substPath {s1 s2 : Sig} (Tel : Telescope (s1,x))
    (self : BVar s1 .var) (σ : PathSubst s1 s2) :
    (Tel.subst σ.lift).substPath (σ.var self) = (Tel.substVar self).subst σ := by
  rw [Telescope.substPath, Telescope.subst_subst, Telescope.substVar, Telescope.rename_subst]
  congr 1
  apply PathSubst.funext'
  intro y
  cases y with
  | here => rfl
  | there y =>
      show ((σ.var y).weaken (k := .var)).subst (PathSubst.one (σ.var self)) = σ.var y
      rw [Path.subst_one, Path.weaken_substPath]

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Declaration shapes are a syntactic property -/

theorem Ty.isDecl_rename {s s' : Sig} : ∀ (T : Ty s) (ρ : Rename s s'),
    (T.rename ρ).isDecl = T.isDecl
  | .top, _ => rfl
  | .bot, _ => rfl
  | .sel _ _, _ => rfl
  | .typ _ _ _, _ => rfl
  | .fld _ _, _ => rfl
  | .vfld _ _, _ => rfl
  | .sngl _, _ => rfl
  | .all _ _, _ => rfl
  | .mu T, ρ => by simp [Ty.rename, Ty.isDecl, Ty.isDecl_rename T ρ.lift]
  | .and S T, ρ => by
      simp [Ty.rename, Ty.isDecl, Ty.isDecl_rename S ρ, Ty.isDecl_rename T ρ]

theorem Ty.isObj_rename {s s' : Sig} : ∀ (T : Ty s) (ρ : Rename s s'),
    (T.rename ρ).isObj = T.isObj
  | .top, _ => rfl
  | .bot, _ => rfl
  | .sel _ _, _ => rfl
  | .typ _ _ _, _ => rfl
  | .fld _ _, _ => rfl
  | .vfld _ _, _ => rfl
  | .sngl _, _ => rfl
  | .all _ _, _ => rfl
  | .and _ _, _ => rfl
  | .mu T, ρ => by simp [Ty.rename, Ty.isObj, Ty.isDecl_rename T ρ.lift]

/-- The shape test does not read paths, so a path substitution keeps it. -/
theorem Ty.isDecl_subst {s1 s2 : Sig} : ∀ (T : Ty s1) (σ : PathSubst s1 s2),
    (T.subst σ).isDecl = T.isDecl
  | .top, _ => rfl
  | .bot, _ => rfl
  | .sel _ _, _ => rfl
  | .typ _ _ _, _ => rfl
  | .fld _ _, _ => rfl
  | .vfld _ _, _ => rfl
  | .sngl _, _ => rfl
  | .all _ _, _ => rfl
  | .mu T, σ => by simp [Ty.subst, Ty.isDecl, Ty.isDecl_subst T σ.lift]
  | .and S T, σ => by
      simp [Ty.subst, Ty.isDecl, Ty.isDecl_subst S σ, Ty.isDecl_subst T σ]

theorem Ty.isObj_subst {s1 s2 : Sig} : ∀ (T : Ty s1) (σ : PathSubst s1 s2),
    (T.subst σ).isObj = T.isObj
  | .top, _ => rfl
  | .bot, _ => rfl
  | .sel _ _, _ => rfl
  | .typ _ _ _, _ => rfl
  | .fld _ _, _ => rfl
  | .vfld _ _, _ => rfl
  | .sngl _, _ => rfl
  | .all _ _, _ => rfl
  | .and _ _, _ => rfl
  | .mu T, σ => by simp [Ty.subst, Ty.isObj, Ty.isDecl_subst T σ.lift]

/-! ## Paths and path substitutions -/

theorem Path.translate_rename {s1 s2 : Sig} (p : Path s1) (ρ : Rename s1 s2) :
    (p.rename ρ).translate = p.translate.rename ρ := by
  induction p with
  | var x => rfl
  | sel p a ih => simp only [Path.rename, Path.translate, FCdot.Path.rename, ih]

/-- A path substitution, translated pointwise. -/
def PathSubst.translate (σ : PathSubst s1 s2) : FCdot.PathSubst s1 s2 :=
  ⟨fun x => (σ.var x).translate⟩

@[simp] theorem PathSubst.translate_var {s1 s2 : Sig} (σ : PathSubst s1 s2)
    (x : BVar s1 .var) : σ.translate.var x = (σ.var x).translate := rfl

theorem PathSubst.translate_lift {s1 s2 : Sig} (σ : PathSubst s1 s2) :
    σ.lift.translate = σ.translate.lift := by
  apply FCdot.PathSubst.funext'
  intro x
  cases x with
  | here => rfl
  | there y => exact Path.translate_rename (σ.var y) FCdot.Rename.succ

theorem PathSubst.translate_ofRename {s1 s2 : Sig} (ρ : Rename s1 s2) :
    (PathSubst.ofRename ρ).translate = FCdot.PathSubst.ofRename ρ :=
  FCdot.PathSubst.funext' (fun _ => rfl)

theorem PathSubst.translate_one {s : Sig} (q : Path s) :
    (PathSubst.one q).translate = FCdot.PathSubst.one q.translate := by
  apply FCdot.PathSubst.funext'
  intro x
  cases x <;> rfl

theorem Path.translate_subst {s1 s2 : Sig} (p : Path s1) (σ : PathSubst s1 s2) :
    (p.subst σ).translate = p.translate.subst σ.translate := by
  induction p with
  | var x => rfl
  | sel p a ih => simp only [Path.subst, Path.translate, FCdot.Path.subst, ih]

theorem Path.translate_substPath {s : Sig} (p : Path (s,x)) (q : Path s) :
    (p.substPath q).translate = p.translate.substPath q.translate := by
  rw [← Path.subst_one, Path.translate_subst, PathSubst.translate_one, FCdot.Path.subst_one]

/-! ## Path substitution for `translate`, `tel`, `telSelfAt` -/

mutual

theorem Ty.translate_subst {s1 s2 : Sig} (T : Ty s1) (σ : PathSubst s1 s2) :
    (T.subst σ).translate = T.translate.subst σ.translate := by
  match T with
  | .top => rfl
  | .bot => rfl
  | .sel p A => simp only [Ty.subst, Ty.translate, FCdot.Ty.subst, Path.translate_subst]
  | .all S T =>
      simp only [Ty.subst, Ty.translate, FCdot.Ty.subst, Ty.translate_subst S σ,
        Ty.translate_subst T σ.lift, PathSubst.translate_lift]
  | .typ A S T =>
      simp only [Ty.subst, Ty.translate, FCdot.Ty.subst, FCdot.Telescope.subst,
        FCdot.Proposition.subst, FCdot.Ty.weaken_subst, Ty.translate_subst S σ,
        Ty.translate_subst T σ]
      rfl
  | .fld a T =>
      simp only [Ty.subst, Ty.translate, FCdot.Ty.subst, FCdot.Telescope.subst,
        FCdot.Proposition.subst, FCdot.Ty.weaken_subst, Ty.translate_subst T σ]
      rfl
  | .vfld a T =>
      simp only [Ty.subst, Ty.translate, FCdot.Ty.subst, FCdot.Telescope.subst,
        FCdot.Proposition.subst, FCdot.Ty.weaken_subst, Ty.translate_subst T σ]
      rfl
  | .sngl q =>
      simp only [Ty.subst, Ty.translate, FCdot.Ty.subst, FCdot.Telescope.subst,
        FCdot.Proposition.subst, FCdot.Path.weaken_subst_lift, Path.translate_subst]
  | .and S T =>
      simp only [Ty.subst, Ty.translate, FCdot.Ty.subst, FCdot.Telescope.append_subst',
        Ty.tel_subst S σ, Ty.tel_subst T σ]
  | .mu T =>
      simp only [Ty.subst, Ty.translate, FCdot.Ty.subst,
        Ty.telSelfAt_subst T σ.lift .here .here rfl, PathSubst.translate_lift]

theorem Ty.tel_subst {s1 s2 : Sig} (T : Ty s1) (σ : PathSubst s1 s2) :
    (T.subst σ).tel = T.tel.subst σ.translate.lift := by
  match T with
  | .top => rfl
  | .bot =>
      simp only [Ty.subst, Ty.tel, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Ty.weaken_subst]
      rfl
  | .sel p A =>
      simp only [Ty.subst, Ty.tel, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Ty.weaken_subst, FCdot.Ty.subst, Path.translate_subst]
  | .all S T =>
      simp only [Ty.subst, Ty.tel, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Ty.weaken_subst, FCdot.Ty.subst, Ty.translate_subst S σ,
        Ty.translate_subst T σ.lift, PathSubst.translate_lift]
  | .typ A S T =>
      simp only [Ty.subst, Ty.tel, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Ty.weaken_subst, Ty.translate_subst S σ, Ty.translate_subst T σ]
      rfl
  | .fld a T =>
      simp only [Ty.subst, Ty.tel, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Ty.weaken_subst, Ty.translate_subst T σ]
      rfl
  | .vfld a T =>
      simp only [Ty.subst, Ty.tel, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Ty.weaken_subst, Ty.translate_subst T σ]
      rfl
  | .sngl q =>
      simp only [Ty.subst, Ty.tel, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Path.weaken_subst_lift, Path.translate_subst]
  | .and S T =>
      simp only [Ty.subst, Ty.tel, FCdot.Telescope.append_subst', Ty.tel_subst S σ,
        Ty.tel_subst T σ]
  | .mu T0 =>
      have ih := Ty.telSelfAt_subst T0 σ.lift .here .here rfl
      rw [PathSubst.translate_lift] at ih
      cases hd : T0.isDecl with
      | true =>
          have hd' : (T0.subst σ.lift).isDecl = true := by rw [Ty.isDecl_subst]; exact hd
          simp only [Ty.subst, Ty.tel, hd, hd', if_true, ih]
      | false =>
          have hd' : (T0.subst σ.lift).isDecl = false := by rw [Ty.isDecl_subst]; exact hd
          simp only [Ty.subst, Ty.tel, hd, hd', Bool.false_eq_true, if_false, ih,
            FCdot.Telescope.subst, FCdot.Proposition.subst, FCdot.Ty.weaken_subst,
            FCdot.Ty.subst]

/-- A type whose self is the variable `self`, substituted by a path substitution that sends
`self` to a variable, has the self-telescope at that variable. -/
theorem Ty.telSelfAt_subst {s1 s2 : Sig} (T : Ty s1) (σ : PathSubst s1 s2)
    (self : BVar s1 .var) (self' : BVar s2 .var) (h : σ.var self = .var self') :
    (T.subst σ).telSelfAt self' = (T.telSelfAt self).subst σ.translate := by
  have hs : (FCdot.Path.var self).subst σ.translate = .var self' := by
    show (σ.var self).translate = _
    rw [h]
    rfl
  match T with
  | .top => rfl
  | .bot => rfl
  | .sel p A =>
      simp only [Ty.subst, Ty.telSelfAt, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Ty.subst, Path.translate_subst]
  | .all S T =>
      simp only [Ty.subst, Ty.telSelfAt, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Ty.subst, Ty.translate_subst S σ, Ty.translate_subst T σ.lift,
        PathSubst.translate_lift]
  | .typ A S T =>
      simp only [Ty.subst, Ty.telSelfAt, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Ty.subst, hs, Ty.translate_subst S σ, Ty.translate_subst T σ]
  | .fld a T =>
      simp only [Ty.subst, Ty.telSelfAt, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Ty.subst, hs, Ty.translate_subst T σ]
  | .vfld a T =>
      simp only [Ty.subst, Ty.telSelfAt, FCdot.Telescope.subst, FCdot.Proposition.subst,
        FCdot.Ty.subst, hs, Ty.translate_subst T σ]
  | .sngl q =>
      simp only [Ty.subst, Ty.telSelfAt, FCdot.Telescope.subst, FCdot.Proposition.subst,
        Path.translate_subst]
  | .and S T =>
      simp only [Ty.subst, Ty.telSelfAt, FCdot.Telescope.append_subst',
        Ty.telSelfAt_subst S σ self self' h, Ty.telSelfAt_subst T σ self self' h]
  | .mu T0 =>
      have ih := Ty.telSelfAt_subst T0 σ.lift .here .here rfl
      rw [PathSubst.translate_lift] at ih
      cases hd : T0.isDecl with
      | true =>
          have hd' : (T0.subst σ.lift).isDecl = true := by rw [Ty.isDecl_subst]; exact hd
          simp only [Ty.subst, Ty.telSelfAt, hd, hd', if_true, ih]
          have hself : σ.translate.var self = .var self' := hs
          exact (FCdot.Telescope.substVar_subst _ self self' σ.translate hself).symm
      | false =>
          have hd' : (T0.subst σ.lift).isDecl = false := by rw [Ty.isDecl_subst]; exact hd
          simp only [Ty.subst, Ty.telSelfAt, hd, hd', Bool.false_eq_true, if_false, ih,
            FCdot.Telescope.subst, FCdot.Proposition.subst, FCdot.Ty.subst]

end

/-! ## Renaming for `translate`, `tel`, `telSelfAt`, `telSelf`

A renaming is the path substitution `PathSubst.ofRename`, on both sides. -/

theorem Ty.translate_rename {s s' : Sig} (T : Ty s) (ρ : Rename s s') :
    (T.rename ρ).translate = T.translate.rename ρ := by
  rw [← Ty.subst_ofRename, Ty.translate_subst, PathSubst.translate_ofRename,
    FCdot.Ty.subst_ofRename]

theorem Ty.tel_rename {s s' : Sig} (T : Ty s) (ρ : Rename s s') :
    (T.rename ρ).tel = T.tel.rename ρ.lift := by
  rw [← Ty.subst_ofRename, Ty.tel_subst, PathSubst.translate_ofRename,
    FCdot.PathSubst.lift_ofRename, FCdot.Telescope.subst_ofRename]

theorem Ty.telSelfAt_rename {s s' : Sig} (T : Ty s) (ρ : Rename s s') (self : BVar s .var) :
    (T.rename ρ).telSelfAt (ρ.var self) = (T.telSelfAt self).rename ρ := by
  rw [← Ty.subst_ofRename, Ty.telSelfAt_subst T (PathSubst.ofRename ρ) self (ρ.var self) rfl,
    PathSubst.translate_ofRename, FCdot.Telescope.subst_ofRename]

theorem Ty.telSelf_rename {s s' : Sig} (T : Ty (s,x)) (ρ : Rename s s') :
    (T.rename ρ.lift).telSelf = T.telSelf.rename ρ.lift :=
  Ty.telSelfAt_rename T ρ.lift .here

/-! ## `translate` and instantiation of the innermost binder -/

theorem Ty.translate_substVar {s : Sig} (T : Ty (s,x)) (r : BVar s .var) :
    (T.substVar r).translate = T.translate.substVar r :=
  Ty.translate_rename T (Rename.subst r)

theorem Ty.translate_substPath {s : Sig} (T : Ty (s,x)) (q : Path s) :
    (T.substPath q).translate = T.translate.substPath q.translate := by
  rw [Ty.substPath, Ty.translate_subst, PathSubst.translate_one]
  rfl

/-! ## `tel` on a type equals `telSelf` on its weakening -/

theorem Ty.tel_eq_telSelf_weaken {s : Sig} (T : Ty s) : T.tel = (T.weaken).telSelf := by
  match T with
  | .top => rfl
  | .bot => rfl
  | .sel p A =>
      simp [Ty.weaken, Ty.rename, Ty.tel, Ty.telSelf, Ty.telSelfAt,
        FCdot.Ty.rename, FCdot.Ty.weaken, Path.translate_rename]
  | .all S T =>
      simp [Ty.weaken, Ty.rename, Ty.tel, Ty.telSelf, Ty.telSelfAt,
        FCdot.Ty.rename, FCdot.Ty.weaken,
        Ty.translate_rename S FCdot.Rename.succ,
        Ty.translate_rename T (FCdot.Rename.succ (k := Kind.var)).lift]
  | .typ A S T =>
      simp [Ty.weaken, Ty.rename, Ty.tel, Ty.telSelf, Ty.telSelfAt,
        FCdot.Ty.weaken,
        Ty.translate_rename S FCdot.Rename.succ, Ty.translate_rename T FCdot.Rename.succ]
  | .fld a T =>
      simp [Ty.weaken, Ty.rename, Ty.tel, Ty.telSelf, Ty.telSelfAt,
        FCdot.Ty.weaken,
        Ty.translate_rename T FCdot.Rename.succ]
  | .vfld a T =>
      simp [Ty.weaken, Ty.rename, Ty.tel, Ty.telSelf, Ty.telSelfAt,
        FCdot.Ty.weaken,
        Ty.translate_rename T FCdot.Rename.succ]
  | .sngl q =>
      simp [Ty.weaken, Ty.rename, Ty.tel, Ty.telSelf, Ty.telSelfAt,
        FCdot.Path.weaken, Path.translate_rename]
  | .and S T =>
      have hS := Ty.tel_eq_telSelf_weaken S
      have hT := Ty.tel_eq_telSelf_weaken T
      simp only [Ty.telSelf] at hS hT
      simp only [Ty.weaken, Ty.rename, Ty.tel, Ty.telSelf, Ty.telSelfAt] at hS hT ⊢
      rw [hS, hT]
  | .mu T0 =>
      have hw : (Ty.mu T0 : Ty s).weaken = Ty.mu (T0.rename (FCdot.Rename.succ (k := Kind.var)).lift) := by
        simp [Ty.weaken, Ty.rename]
      have h1 : (T0.rename (FCdot.Rename.succ (k := Kind.var)).lift).telSelfAt .here
          = (T0.telSelfAt .here).rename (FCdot.Rename.succ (k := Kind.var)).lift :=
        Ty.telSelfAt_rename T0 (FCdot.Rename.succ (k := Kind.var)).lift .here
      cases hd : T0.isDecl with
      | true =>
          have hd' : (T0.rename (FCdot.Rename.succ (k := Kind.var)).lift).isDecl = true := by
            rw [Ty.isDecl_rename T0 _]; exact hd
          rw [hw]
          simp only [Ty.tel, Ty.telSelf, Ty.telSelfAt, hd, hd', if_true, h1,
            FCdot.Telescope.rename_lift_substVar_succ]
      | false =>
          have hd' : (T0.rename (FCdot.Rename.succ (k := Kind.var)).lift).isDecl = false := by
            rw [Ty.isDecl_rename T0 _]; exact hd
          rw [hw]
          simp [Ty.tel, Ty.telSelf, Ty.telSelfAt, hd, hd', h1,
            FCdot.Ty.rename, FCdot.Ty.weaken]

/-! ## Opening a body at a path, and at a variable -/

/-- The unweakened form of `Ty.tel_substPath`. -/
theorem Ty.tel_substPath_eq {s : Sig} (T : Ty (s,x)) (p : Path s) :
    (T.substPath p).tel.substPath p.translate = T.telSelf.substPath p.translate := by
  cases hT : T.isObj with
  | false =>
      have hT' : (T.substPath p).isObj = false := by
        rw [Ty.substPath, Ty.isObj_subst]; exact hT
      rw [Ty.tel_of_not_isObj hT', Ty.telSelf_of_not_isObj hT, Ty.translate_substPath]
      simp only [FCdot.Telescope.substPath_cons, FCdot.Telescope.substPath_nil,
        FCdot.Proposition.substPath_bnd, FCdot.Ty.weaken_substPath]
  | true =>
      match T, hT with
      | .top, _ => rfl
      | .typ A S U, _ =>
          simp [Ty.tel, Ty.telSelf, Ty.telSelfAt, FCdot.Path.substPath,
            FCdot.Ty.weaken_substPath, Ty.translate_substPath]
      | .fld a U, _ =>
          simp [Ty.tel, Ty.telSelf, Ty.telSelfAt, FCdot.Path.substPath,
            FCdot.Ty.weaken_substPath, Ty.translate_substPath]
      | .vfld a U, _ =>
          simp [Ty.tel, Ty.telSelf, Ty.telSelfAt, FCdot.Path.substPath,
            FCdot.Ty.weaken_substPath, Ty.translate_substPath]
      | .sngl r, _ =>
          simp [Ty.tel, Ty.telSelf, Ty.telSelfAt, FCdot.Path.weaken_substPath,
            Path.translate_substPath]
      | .and S U, _ =>
          have hS := Ty.tel_substPath_eq S p
          have hU := Ty.tel_substPath_eq U p
          simp only [Ty.telSelf] at hS hU
          simp only [Ty.substPath_and, Ty.tel, Ty.telSelf, Ty.telSelfAt,
            FCdot.Telescope.append_substPath', hS, hU]
      | .mu T0, hT0 =>
          have hd : T0.isDecl = true := hT0
          have hd' : (T0.subst (PathSubst.one p).lift).isDecl = true := by
            rw [Ty.isDecl_subst]; exact hd
          have ih := Ty.telSelfAt_subst T0 (PathSubst.one p).lift .here .here rfl
          rw [PathSubst.translate_lift, PathSubst.translate_one] at ih
          show (Ty.mu (T0.subst (PathSubst.one p).lift)).tel.substPath p.translate = _
          simp only [Ty.tel, Ty.telSelf, Ty.telSelfAt, hd, hd', if_true, ih]
          exact FCdot.Telescope.subst_lift_substPath _ .here (FCdot.PathSubst.one p.translate)

/-- The analog of `Ty.tel_substVar` at a path: opening the body at `p` agrees with the
self-telescope opened at `p`.  It is what `Rec-I` and `Rec-E` at a path read. -/
theorem Ty.tel_substPath {s : Sig} (T : Ty (s,x)) (p : Path s) :
    (((T.substPath p).tel.substPath p.translate).weaken : FCdot.Telescope (s,x)) =
      (T.telSelf.substPath p.translate).weaken := by
  rw [Ty.tel_substPath_eq]

end DotMNF

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Instantiating both self binders of a declaration agree -/

theorem Ty.tel_substVar {s : Sig} (T : Ty (s,x)) (r : BVar s .var) :
    (((T.substVar r).tel.substVar r).weaken : FCdot.Telescope (s,x)) =
      (T.telSelf.substVar r).weaken := by
  have h := Ty.tel_substPath T (.var r)
  rw [Ty.substPath_var] at h
  simpa only [Path.translate, FCdot.Telescope.substPath_var] using h

end DotMNF

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Witnesses, field labels, stable labels, and the literal type -/

theorem Ty.witnesses_rename {s s' : Sig} (T : Ty (s,x)) (ρ : Rename s s') :
    (T.rename ρ.lift).witnesses = T.witnesses.rename ρ.lift := by
  match T with
  | .top => simp [Ty.rename, Ty.witnesses, FCdot.Witnesses.rename]
  | .bot => simp [Ty.rename, Ty.witnesses, FCdot.Witnesses.rename]
  | .sel p A => simp [Ty.rename, Ty.witnesses, FCdot.Witnesses.rename]
  | .all S T => simp [Ty.rename, Ty.witnesses, FCdot.Witnesses.rename]
  | .sngl q => simp [Ty.rename, Ty.witnesses, FCdot.Witnesses.rename]
  | .typ A S T =>
      simp [Ty.rename, Ty.witnesses, FCdot.Witnesses.rename, Ty.translate_rename S ρ.lift]
  | .fld a T =>
      simp [Ty.rename, Ty.witnesses, FCdot.Witnesses.rename, Ty.translate_rename T ρ.lift]
  | .vfld a T =>
      simp [Ty.rename, Ty.witnesses, FCdot.Witnesses.rename, Ty.translate_rename T ρ.lift]
  | .and S T =>
      simp [Ty.rename, Ty.witnesses, FCdot.Witnesses.append_rename,
        Ty.witnesses_rename S ρ, Ty.witnesses_rename T ρ]
  | .mu T => simp [Ty.rename, Ty.witnesses, FCdot.Witnesses.rename]

theorem Ty.fieldLabels_rename {s s' : Sig} (T : Ty s) (ρ : Rename s s') :
    (T.rename ρ).fieldLabels = T.fieldLabels := by
  match T with
  | .top => simp [Ty.rename, Ty.fieldLabels]
  | .bot => simp [Ty.rename, Ty.fieldLabels]
  | .sel p A => simp [Ty.rename, Ty.fieldLabels]
  | .all S T => simp [Ty.rename, Ty.fieldLabels]
  | .sngl q => simp [Ty.rename, Ty.fieldLabels]
  | .typ A S T => simp [Ty.rename, Ty.fieldLabels]
  | .fld a T => simp [Ty.rename, Ty.fieldLabels]
  | .vfld a T => simp [Ty.rename, Ty.fieldLabels]
  | .and S T =>
      simp [Ty.rename, Ty.fieldLabels, Ty.fieldLabels_rename S ρ, Ty.fieldLabels_rename T ρ]
  | .mu T => simp [Ty.rename, Ty.fieldLabels]

theorem Ty.valLabels_rename {s s' : Sig} (T : Ty s) (ρ : Rename s s') :
    (T.rename ρ).valLabels = T.valLabels := by
  match T with
  | .top => simp [Ty.rename, Ty.valLabels]
  | .bot => simp [Ty.rename, Ty.valLabels]
  | .sel p A => simp [Ty.rename, Ty.valLabels]
  | .all S T => simp [Ty.rename, Ty.valLabels]
  | .sngl q => simp [Ty.rename, Ty.valLabels]
  | .typ A S T => simp [Ty.rename, Ty.valLabels]
  | .fld a T => simp [Ty.rename, Ty.valLabels]
  | .vfld a T => simp [Ty.rename, Ty.valLabels]
  | .and S T =>
      simp [Ty.rename, Ty.valLabels, Ty.valLabels_rename S ρ, Ty.valLabels_rename T ρ]
  | .mu T => simp [Ty.rename, Ty.valLabels]

theorem Ty.literalTy_rename {s s' : Sig} (T : Ty (s,x)) (ρ : Rename s s') :
    (T.rename ρ.lift).literalTy = T.literalTy.rename ρ := by
  simp only [Ty.literalTy, FCdot.Ty.rename, Ty.witnesses_rename T ρ,
    Ty.fieldLabels_rename (T := T) (ρ := ρ.lift), Ty.valLabels_rename (T := T) (ρ := ρ.lift)]
  rw [FCdot.Telescope.ofLiteral_rename]

end DotMNF

/-! ## Declaration-shaped types are preserved by renaming and substitution -/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

theorem Ty.Decl.rename : ∀ {s1 s2 : Sig} {T : Ty s1}, Ty.Decl T → ∀ (ρ : Rename s1 s2),
    Ty.Decl (T.rename ρ)
  | _, _, _, .top, _ => .top
  | _, _, _, .typ, _ => .typ
  | _, _, _, .fld, _ => .fld
  | _, _, _, .vfld, _ => .vfld
  | _, _, _, .sngl, _ => .sngl
  | _, _, _, .mu h, ρ => .mu (Ty.Decl.rename h ρ.lift)
  | _, _, _, .and hS hT, ρ => .and (Ty.Decl.rename hS ρ) (Ty.Decl.rename hT ρ)

theorem Ty.Decl.substVar {s : Sig} {T : Ty (s,x)} (h : Ty.Decl T) (r : BVar s .var) :
    Ty.Decl (T.substVar r) :=
  h.rename (Rename.subst r)

theorem Ty.Decl.subst {s1 s2 : Sig} {T : Ty s1} (h : Ty.Decl T) (σ : PathSubst s1 s2) :
    Ty.Decl (T.subst σ) :=
  (Ty.isDecl_iff _).mp (by rw [Ty.isDecl_subst]; exact (Ty.isDecl_iff _).mpr h)

theorem Ty.Decl.substPath {s : Sig} {T : Ty (s,x)} (h : Ty.Decl T) (q : Path s) :
    Ty.Decl (T.substPath q) :=
  h.subst (PathSubst.one q)

/-! ## Every declaration-shaped type translates to its telescope -/

/-- A declaration shape is an object shape. -/
theorem Ty.Decl.isObj {s : Sig} {T : Ty s} (h : Ty.Decl T) : T.isObj = true := by
  cases h with
  | top => rfl
  | typ => rfl
  | fld => rfl
  | vfld => rfl
  | sngl => rfl
  | and => rfl
  | mu h' => exact (Ty.isDecl_iff _).mpr h'

theorem Ty.translate_decl {s : Sig} {T : Ty s} (h : Ty.Decl T) : T.translate = .obj T.tel :=
  Ty.translate_isObj h.isObj

end DotMNF

/-! ## Context translation and lookup -/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

theorem Ctx.translate_lookup_cons {s : Sig} (Γ : Ctx s) (T : Ty s) :
    (Γ.cons T).translate.lookupTy .here = T.translate.weaken := rfl

theorem Ctx.translate_lookup_cons_there {s : Sig} (Γ : Ctx s) (T : Ty s) (y : BVar s .var) :
    (Γ.cons T).translate.lookupTy (.there y) = (Γ.translate.lookupTy y).weaken := rfl

theorem Ctx.translate_lookup_consSelf {s : Sig} (Γ : Ctx s) (d : Defs (s,x)) (T : Ty (s,x)) :
    (Γ.consSelf d T).translate.lookupTy .here = T.literalTy.weaken := rfl

theorem Ctx.translate_lookup_consSelf_there {s : Sig} (Γ : Ctx s) (d : Defs (s,x)) (T : Ty (s,x))
    (y : BVar s .var) :
    (Γ.consSelf d T).translate.lookupTy (.there y) = (Γ.translate.lookupTy y).weaken := rfl

end DotMNF

end Paths
