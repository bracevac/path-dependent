import Coercions.DotToFCdot.Types
import Coercions.FCdot.RenameLemmas

/-!
# Renaming for the type translation (Plan III §8.1, M3)

The type translation `Ty.translate`/`Ty.tel`/`Ty.telSelf` (`DotToFCdot/Types.lean`) is a
mutual recursion mirroring the shape of `Ty`.  This file proves it commutes with renaming,
mirroring `Coercions.FCdot.RenameLemmas`, and derives the context-lookup facts the
typedness proofs (M3 second half) need.
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

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Renaming for `translate`, `tel`, `telSelf` -/

mutual

theorem Ty.translate_rename {s s' : Sig} (T : Ty s) (ρ : Rename s s') :
    (T.rename ρ).translate = T.translate.rename ρ := by
  match T with
  | .top => simp [Ty.rename, Ty.translate, FCdot.Ty.rename, FCdot.Telescope.rename]
  | .bot => simp [Ty.rename, Ty.translate, FCdot.Ty.rename, FCdot.Telescope.rename]
  | .sel (.var x) A => simp [Ty.rename, Path.rename, Ty.translate, FCdot.Ty.rename]
  | .all S T =>
      simp [Ty.rename, Ty.translate, FCdot.Ty.rename,
        Ty.translate_rename S ρ, Ty.translate_rename T ρ.lift]
  | .typ A S T =>
      simp [Ty.rename, Ty.translate, Ty.tel, FCdot.Ty.rename, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Rename.lift_here, FCdot.Ty.weaken_rename,
        Ty.translate_rename S ρ, Ty.translate_rename T ρ]
  | .fld a T =>
      simp [Ty.rename, Ty.translate, Ty.tel, FCdot.Ty.rename, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Rename.lift_here, FCdot.Ty.weaken_rename,
        Ty.translate_rename T ρ]
  | .and S T =>
      simp [Ty.rename, Ty.translate, Ty.tel, FCdot.Ty.rename, FCdot.Telescope.append_rename',
        Ty.tel_rename S ρ, Ty.tel_rename T ρ]
  | .mu T =>
      simp [Ty.rename, Ty.translate, FCdot.Ty.rename, Ty.telSelf_rename T ρ]

theorem Ty.tel_rename {s s' : Sig} (T : Ty s) (ρ : Rename s s') :
    (T.rename ρ).tel = T.tel.rename ρ.lift := by
  match T with
  | .top => simp [Ty.rename, Ty.tel, FCdot.Telescope.rename]
  | .bot => simp [Ty.rename, Ty.tel, FCdot.Telescope.rename]
  | .sel p A => simp [Ty.rename, Ty.tel, FCdot.Telescope.rename]
  | .all S T => simp [Ty.rename, Ty.tel, FCdot.Telescope.rename]
  | .typ A S T =>
      simp [Ty.rename, Ty.tel, FCdot.Telescope.rename, FCdot.Proposition.rename,
        FCdot.Ty.rename, FCdot.Rename.lift_here, FCdot.Ty.weaken_rename,
        Ty.translate_rename S ρ, Ty.translate_rename T ρ]
  | .fld a T =>
      simp [Ty.rename, Ty.tel, FCdot.Telescope.rename, FCdot.Proposition.rename,
        FCdot.Ty.rename, FCdot.Rename.lift_here, FCdot.Ty.weaken_rename,
        Ty.translate_rename T ρ]
  | .and S T =>
      simp [Ty.rename, Ty.tel, FCdot.Telescope.append_rename',
        Ty.tel_rename S ρ, Ty.tel_rename T ρ]
  | .mu T =>
      simp [Ty.rename, Ty.tel, Ty.telSelf_rename T ρ]

theorem Ty.telSelf_rename {s s' : Sig} (T : Ty (s,x)) (ρ : Rename s s') :
    (T.rename ρ.lift).telSelf = T.telSelf.rename ρ.lift := by
  match T with
  | .top => simp [Ty.rename, Ty.telSelf, FCdot.Telescope.rename]
  | .bot => simp [Ty.rename, Ty.telSelf, FCdot.Telescope.rename]
  | .sel p A => simp [Ty.rename, Ty.telSelf, FCdot.Telescope.rename]
  | .all S T => simp [Ty.rename, Ty.telSelf, FCdot.Telescope.rename]
  | .typ A S T =>
      simp [Ty.rename, Ty.telSelf, FCdot.Telescope.rename, FCdot.Proposition.rename,
        FCdot.Ty.rename, FCdot.Rename.lift_here,
        Ty.translate_rename S ρ.lift, Ty.translate_rename T ρ.lift]
  | .fld a T =>
      simp [Ty.rename, Ty.telSelf, FCdot.Telescope.rename, FCdot.Proposition.rename,
        FCdot.Ty.rename, FCdot.Rename.lift_here,
        Ty.translate_rename T ρ.lift]
  | .and S T =>
      simp [Ty.rename, Ty.telSelf, FCdot.Telescope.append_rename',
        Ty.telSelf_rename S ρ, Ty.telSelf_rename T ρ]
  | .mu T0 =>
      have hren : (Ty.mu T0 : Ty (s,x)).rename ρ.lift = Ty.mu (T0.rename ρ.lift.lift) := by
        simp [Ty.rename]
      have htelSelf : ∀ {s0 : Sig} (U : Ty ((s0,x),x)),
          (Ty.mu U : Ty (s0,x)).telSelf = (Ty.telSelf U).substVar .here := by
        intro s0 U
        simp [Ty.telSelf]
      rw [hren, htelSelf, htelSelf]
      rw [Ty.telSelf_rename T0 ρ.lift, FCdot.Telescope.substVar_rename]
      simp [FCdot.Rename.lift_here]

end

/-! ## `translate` and instantiation of the innermost binder -/

theorem Ty.translate_substVar {s : Sig} (T : Ty (s,x)) (r : BVar s .var) :
    (T.substVar r).translate = T.translate.substVar r :=
  Ty.translate_rename T (Rename.subst r)

/-! ## `tel` on a type equals `telSelf` on its weakening -/

theorem Ty.tel_eq_telSelf_weaken {s : Sig} (T : Ty s) : T.tel = (T.weaken).telSelf := by
  match T with
  | .top => simp [Ty.weaken, Ty.rename, Ty.tel, Ty.telSelf, FCdot.Telescope.rename]
  | .bot => simp [Ty.weaken, Ty.rename, Ty.tel, Ty.telSelf, FCdot.Telescope.rename]
  | .sel p A => simp [Ty.weaken, Ty.rename, Ty.tel, Ty.telSelf, FCdot.Telescope.rename]
  | .all S T => simp [Ty.weaken, Ty.rename, Ty.tel, Ty.telSelf, FCdot.Telescope.rename]
  | .typ A S T =>
      simp [Ty.weaken, Ty.rename, Ty.tel, Ty.telSelf, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Ty.rename, FCdot.Ty.weaken, FCdot.Rename.lift_here,
        Ty.translate_rename S FCdot.Rename.succ, Ty.translate_rename T FCdot.Rename.succ]
  | .fld a T =>
      simp [Ty.weaken, Ty.rename, Ty.tel, Ty.telSelf, FCdot.Telescope.rename,
        FCdot.Proposition.rename, FCdot.Ty.rename, FCdot.Ty.weaken, FCdot.Rename.lift_here,
        Ty.translate_rename T FCdot.Rename.succ]
  | .and S T =>
      simp [Ty.weaken, Ty.rename, Ty.tel, Ty.telSelf, FCdot.Telescope.append_rename',
        Ty.tel_eq_telSelf_weaken S, Ty.tel_eq_telSelf_weaken T]
  | .mu T0 =>
      have hw : (Ty.mu T0 : Ty s).weaken = Ty.mu (T0.rename (FCdot.Rename.succ (k := Kind.var)).lift) := by
        simp [Ty.weaken, Ty.rename]
      have htel : (Ty.mu T0 : Ty s).tel = Ty.telSelf T0 := by simp [Ty.tel]
      have htelSelf' :
          (Ty.mu (T0.rename (FCdot.Rename.succ (k := Kind.var)).lift) : Ty (s,x)).telSelf
            = ((T0.rename (FCdot.Rename.succ (k := Kind.var)).lift).telSelf).substVar .here := by
        simp [Ty.telSelf]
      rw [htel, hw, htelSelf']
      rw [Ty.telSelf_rename T0 FCdot.Rename.succ, FCdot.Telescope.rename_lift_substVar_succ]

end DotMNF

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Instantiating both self binders of a declaration agree -/

theorem Ty.tel_substVar {s : Sig} (T : Ty (s,x)) (r : BVar s .var) :
    (((T.substVar r).tel.substVar r).weaken : FCdot.Telescope (s,x)) =
      (T.telSelf.substVar r).weaken := by
  match T with
  | .top =>
      simp [Ty.substVar, Ty.rename, Ty.tel, Ty.telSelf, FCdot.Telescope.rename,
        FCdot.Telescope.weaken, FCdot.Telescope.substVar]
  | .bot =>
      simp [Ty.substVar, Ty.rename, Ty.tel, Ty.telSelf, FCdot.Telescope.rename,
        FCdot.Telescope.weaken, FCdot.Telescope.substVar]
  | .sel p A =>
      simp [Ty.substVar, Ty.rename, Ty.tel, Ty.telSelf, FCdot.Telescope.rename,
        FCdot.Telescope.weaken, FCdot.Telescope.substVar]
  | .all S T =>
      simp [Ty.substVar, Ty.rename, Ty.tel, Ty.telSelf, FCdot.Telescope.rename,
        FCdot.Telescope.weaken, FCdot.Telescope.substVar]
  | .typ A S T =>
      simp [Ty.substVar, Ty.rename, Ty.tel, Ty.telSelf, FCdot.Telescope.rename,
        FCdot.Telescope.weaken, FCdot.Telescope.substVar, FCdot.Proposition.rename,
        FCdot.Proposition.substVar, FCdot.Proposition.weaken, FCdot.Ty.rename,
        FCdot.Ty.substVar, FCdot.Ty.weaken, FCdot.Rename.subst_here,
        FCdot.Rename.comp_assoc, FCdot.Rename.succ_subst, FCdot.Rename.comp_id,
        Ty.translate_rename S (Rename.subst r), Ty.translate_rename T (Rename.subst r)]
  | .fld a T =>
      simp [Ty.substVar, Ty.rename, Ty.tel, Ty.telSelf, FCdot.Telescope.rename,
        FCdot.Telescope.weaken, FCdot.Telescope.substVar, FCdot.Proposition.rename,
        FCdot.Proposition.substVar, FCdot.Proposition.weaken, FCdot.Ty.rename,
        FCdot.Ty.substVar, FCdot.Ty.weaken, FCdot.Rename.subst_here,
        FCdot.Rename.comp_assoc, FCdot.Rename.succ_subst, FCdot.Rename.comp_id,
        Ty.translate_rename T (Rename.subst r)]
  | .and S T =>
      have hS := Ty.tel_substVar S r
      have hT := Ty.tel_substVar T r
      simp only [Ty.substVar, FCdot.Telescope.substVar, FCdot.Telescope.weaken,
        FCdot.Telescope.rename_comp] at hS hT
      simp only [Ty.substVar, Ty.rename, Ty.tel, Ty.telSelf, FCdot.Telescope.append_rename',
        FCdot.Telescope.substVar, FCdot.Telescope.weaken, FCdot.Telescope.rename_comp]
      rw [hS, hT]
  | .mu T0 =>
      have h1 : (T0.rename (Rename.subst r).lift).telSelf = (Ty.telSelf T0).rename (Rename.subst r).lift :=
        Ty.telSelf_rename T0 (Rename.subst r)
      have htel : ((Ty.mu T0 : Ty (s,x)).substVar r).tel = Ty.telSelf (T0.rename (Rename.subst r).lift) := by
        simp [Ty.substVar, Ty.rename, Ty.tel]
      have htelSelf : (Ty.mu T0 : Ty (s,x)).telSelf = (Ty.telSelf T0).substVar (BVar.here) := by
        simp [Ty.telSelf]
      rw [htel, htelSelf, h1]
      simp only [FCdot.Telescope.substVar, FCdot.Telescope.weaken, FCdot.Telescope.rename_comp,
        FCdot.Rename.subst_comp, FCdot.Rename.subst_here]

end DotMNF

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Witnesses, field labels, and the literal type -/

theorem Ty.witnesses_rename {s s' : Sig} (T : Ty (s,x)) (ρ : Rename s s') :
    (T.rename ρ.lift).witnesses = T.witnesses.rename ρ.lift := by
  match T with
  | .top => simp [Ty.rename, Ty.witnesses, FCdot.Witnesses.rename]
  | .bot => simp [Ty.rename, Ty.witnesses, FCdot.Witnesses.rename]
  | .sel p A => simp [Ty.rename, Ty.witnesses, FCdot.Witnesses.rename]
  | .all S T => simp [Ty.rename, Ty.witnesses, FCdot.Witnesses.rename]
  | .typ A S T =>
      simp [Ty.rename, Ty.witnesses, FCdot.Witnesses.rename, Ty.translate_rename S ρ.lift]
  | .fld a T =>
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
  | .typ A S T => simp [Ty.rename, Ty.fieldLabels]
  | .fld a T => simp [Ty.rename, Ty.fieldLabels]
  | .and S T =>
      simp [Ty.rename, Ty.fieldLabels, Ty.fieldLabels_rename S ρ, Ty.fieldLabels_rename T ρ]
  | .mu T => simp [Ty.rename, Ty.fieldLabels]

theorem Ty.literalTy_rename {s s' : Sig} (T : Ty (s,x)) (ρ : Rename s s') :
    (T.rename ρ.lift).literalTy = T.literalTy.rename ρ := by
  simp only [Ty.literalTy, FCdot.Ty.rename, Ty.witnesses_rename T ρ,
    Ty.fieldLabels_rename (T := T) (ρ := ρ.lift)]
  rw [FCdot.Telescope.ofLiteral_rename]

end DotMNF

/-! ## Declaration-shaped types are preserved by renaming -/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

theorem Ty.Decl.rename : ∀ {s1 s2 : Sig} {T : Ty s1}, Ty.Decl T → ∀ (ρ : Rename s1 s2),
    Ty.Decl (T.rename ρ)
  | _, _, _, .top, _ => .top
  | _, _, _, .typ, _ => .typ
  | _, _, _, .fld, _ => .fld
  | _, _, _, .mu h, ρ => .mu (Ty.Decl.rename h ρ.lift)
  | _, _, _, .and hS hT, ρ => .and (Ty.Decl.rename hS ρ) (Ty.Decl.rename hT ρ)

theorem Ty.Decl.substVar {s : Sig} {T : Ty (s,x)} (h : Ty.Decl T) (r : BVar s .var) :
    Ty.Decl (T.substVar r) :=
  h.rename (Rename.subst r)

/-! ## Every declaration-shaped type translates to its telescope -/

theorem Ty.translate_decl {s : Sig} {T : Ty s} (h : Ty.Decl T) : T.translate = .obj T.tel := by
  cases h <;> simp [Ty.translate, Ty.tel]

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
