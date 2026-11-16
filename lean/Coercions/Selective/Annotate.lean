import Coercions.Selective.Complete
import Coercions.Selective.Typer
import Coercions.DotMNF.Examples

/-!
# The converse translation as a function

`DotMNF.Sub`, `HasTy` and `DefsTy` are `Type`-valued, so the converse
translation of `Complete.lean` is also a computable function on derivations:

* `DotMNF.Sub.toCert : Sub Γ S T → Cert s` and
  `DotMNF.HasTy.toAtom : HasTy Γ (.path (.var x)) T → Atom s`, mutually;
* `DotMNF.HasTy.toH : HasTy Γ t T → HTm s` and
  `DotMNF.DefsTy.toH : DefsTy Γ d T → HDefs s`, mutually.

Each case is the witness that the corresponding case of `cert_complete`,
`atom_complete`, `elaboration_complete` or `defs_complete` builds: every
`Sub` node becomes evidence, every implicit `≤₀` step is `refl`.  The
`_typed` theorems state that the images are typed at the same endpoints, root
and erased program.  One DOT-MNF derivation thus yields both its `H` evidence
and its FCdot translation `d.translate`.
-/

namespace Selective

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ctx Ty Path HasTy Sub DefsTy)

mutual

/-- The certificate of a DOT-MNF inclusion. -/
def _root_.DotMNF.Sub.toCert {s : Sig} {Γ : Ctx s} {S T : Ty s} : Sub Γ S T → Cert s
  | .top => .step S .top
  | .bot => .step .bot T
  | .refl => .step S S
  | .trans d1 d2 => .seq d1.toCert d2.toCert
  | .and1 => .step S T
  | .and2 => .step S T
  | .and (T := T1) d1 d2 =>
      .seq (.step S (.and S S)) (.seq (d1.toCert.liftAndL S) (d2.toCert.liftAndR T1))
  | .fld (a := a) d => d.toCert.liftFld a
  | .typ (A := A) (S1 := S1) (T2 := T2) d1 d2 =>
      .seq (d2.toCert.liftTypU A S1) (d1.toCert.liftTypL A T2)
  | .selUpper (x := x) (A := A) h => .pos (.selU (h.toAtom?.getD (.var x)) A T)
  | .selLower (x := x) (A := A) h => .pos (.selL (h.toAtom?.getD (.var x)) A S)
  | .all (T1 := T1) (S2 := S2) d1 d2 => .seq (d1.toCert.liftAllD T1) (d2.toCert.liftAllC S2)
  termination_by structural d => d

/-- The atom of a variable typing, rooted at the variable; `none` exactly
when the term is not a variable path.  Stated for every term so that the
recursion is structural. -/
def _root_.DotMNF.HasTy.toAtom? {s : Sig} {Γ : Ctx s} {t : DotMNF.Tm s} {T : Ty s} :
    HasTy Γ t T → Option (Atom s)
  | .var (x := x) => some (.var x)
  | .recI (T := T') h => h.toAtom?.map (.fold T')
  | .recE h => h.toAtom?.map .unfold
  | .andI h1 h2 =>
      match h1.toAtom?, h2.toAtom? with
      | some a, some b => some (.both a b)
      | _, _ => none
  | .sub h d => h.toAtom?.map (fun a => .cast a d.toCert)
  | .lam _ => none
  | .app _ _ => none
  | .obj _ _ => none
  | .proj _ => none
  | .let _ _ => none
  termination_by structural h => h

/-- The annotated term of a DOT-MNF term typing. -/
def _root_.DotMNF.HasTy.toH {s : Sig} {Γ : Ctx s} {t : DotMNF.Tm s} {T : Ty s} :
    HasTy Γ t T → HTm s
  | .var (x := x) => .atom (.var x)
  | .lam (S := S) d => .val (.lam S d.toH)
  | .app (x := x) (y := y) hf hy => .app (hf.toAtom?.getD (.var x)) (hy.toAtom?.getD (.var y))
  | .obj (T := T') hd _ => .val (.obj T' hd.toH)
  | .proj (x := x) (a := a) h => .proj (h.toAtom?.getD (.var x)) a
  | .let d1 d2 => .let d1.toH d2.toH
  | .recI (x := x) (T := T') h => .atom (.fold T' (h.toAtom?.getD (.var x)))
  | .recE (x := x) h => .atom (.unfold (h.toAtom?.getD (.var x)))
  | .andI (x := x) h1 h2 => .atom (.both (h1.toAtom?.getD (.var x)) (h2.toAtom?.getD (.var x)))
  | .sub h d => .cast h.toH d.toCert
  termination_by structural h => h

/-- The annotated definitions of a DOT-MNF definition typing. -/
def _root_.DotMNF.DefsTy.toH {s : Sig} {Γ : Ctx s} {d : DotMNF.Defs s} {T : Ty s} :
    DefsTy Γ d T → HDefs s
  | .typ (A := A) (T := T') => .typ A T'
  | .trm (a := a) h => .trm a h.toH
  | .and h1 h2 => .and h1.toH h2.toH
  termination_by structural h => h

end

/-- The atom of a variable typing (the fallback `x` is never used, by
`HasTy.toAtom_typed`). -/
def _root_.DotMNF.HasTy.toAtom {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s}
    (h : HasTy Γ (.path (.var x)) T) : Atom s :=
  h.toAtom?.getD (.var x)

/-! ## The images are typed -/

mutual

theorem _root_.DotMNF.Sub.toCert_typed {s : Sig} {Γ : Ctx s} {S T : Ty s} :
    (d : Sub Γ S T) → CTy Γ d.toCert S T
  | .top => .step .top
  | .bot => .step .bot
  | .refl => .step .refl
  | .trans d1 d2 => .seq (DotMNF.Sub.toCert_typed d1) (DotMNF.Sub.toCert_typed d2)
  | .and1 => .step (.andL1 .refl)
  | .and2 => .step (.andL2 .refl)
  | .and d1 d2 =>
      .seq (.step (.andR .refl .refl))
        (.seq (DotMNF.Sub.toCert_typed d1).liftAndL (DotMNF.Sub.toCert_typed d2).liftAndR)
  | .fld d => (DotMNF.Sub.toCert_typed d).liftFld
  | .typ d1 d2 =>
      .seq (DotMNF.Sub.toCert_typed d2).liftTypU (DotMNF.Sub.toCert_typed d1).liftTypL
  | .selUpper (x := x) (A := A) (S := L) (T := U) h => by
      obtain ⟨a, ha, hr, hty⟩ := DotMNF.HasTy.toAtom?_typed h rfl
      have hp := PTy.selU hty (Exp.typ (x := a.root) (A := A) (L := L) (U := U))
      rw [hr] at hp
      show CTy Γ (.pos (.selU (h.toAtom?.getD (.var x)) A U)) _ _
      rw [ha]; exact .pos hp
  | .selLower (x := x) (A := A) (S := L) (T := U) h => by
      obtain ⟨a, ha, hr, hty⟩ := DotMNF.HasTy.toAtom?_typed h rfl
      have hp := PTy.selL hty (Exp.typ (x := a.root) (A := A) (L := L) (U := U))
      rw [hr] at hp
      show CTy Γ (.pos (.selL (h.toAtom?.getD (.var x)) A L)) _ _
      rw [ha]; exact .pos hp
  | .all d1 d2 =>
      .seq (DotMNF.Sub.toCert_typed d1).liftAllD (DotMNF.Sub.toCert_typed d2).liftAllC

theorem _root_.DotMNF.HasTy.toAtom?_typed {s : Sig} {Γ : Ctx s} {t : DotMNF.Tm s} {T : Ty s} :
    (h : HasTy Γ t T) → ∀ {x : BVar s .var}, t = .path (.var x) →
    ∃ a, h.toAtom? = some a ∧ a.root = x ∧ ATy Γ a T
  | .var, _, e => by cases e; exact ⟨_, rfl, rfl, .var⟩
  | .recI (T := T') h, _, e => by
      cases e
      obtain ⟨a, ha, hr, hty⟩ := DotMNF.HasTy.toAtom?_typed h rfl
      refine ⟨.fold T' a, ?_, hr, .fold ?_⟩
      · simp only [DotMNF.HasTy.toAtom?, ha, Option.map_some]
      · rw [hr]; exact hty
  | .recE (T := T') h, _, e => by
      cases e
      obtain ⟨a, ha, hr, hty⟩ := DotMNF.HasTy.toAtom?_typed h rfl
      have h1 := ATy.unfold hty
      rw [hr] at h1
      refine ⟨.unfold a, ?_, hr, h1⟩
      simp only [DotMNF.HasTy.toAtom?, ha, Option.map_some]
  | .andI h1 h2, _, e => by
      cases e
      obtain ⟨a, ha, hr1, hta⟩ := DotMNF.HasTy.toAtom?_typed h1 rfl
      obtain ⟨b, hb, hr2, htb⟩ := DotMNF.HasTy.toAtom?_typed h2 rfl
      refine ⟨.both a b, ?_, hr1, .both hta htb (hr1.trans hr2.symm)⟩
      simp only [DotMNF.HasTy.toAtom?, ha, hb]
  | .sub h d, _, e => by
      obtain ⟨a, ha, hr, hty⟩ := DotMNF.HasTy.toAtom?_typed h e
      refine ⟨.cast a d.toCert, ?_, hr, .cast hty (DotMNF.Sub.toCert_typed d)⟩
      simp only [DotMNF.HasTy.toAtom?, ha, Option.map_some]
  | .lam _, _, e => by cases e
  | .app _ _, _, e => by cases e
  | .obj _ _, _, e => by cases e
  | .proj _, _, e => by cases e
  | .let _ _, _, e => by cases e

end

theorem _root_.DotMNF.HasTy.toAtom_typed {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s}
    (h : HasTy Γ (.path (.var x)) T) : h.toAtom.root = x ∧ ATy Γ h.toAtom T := by
  obtain ⟨a, ha, hr, hty⟩ := DotMNF.HasTy.toAtom?_typed h rfl
  simp only [DotMNF.HasTy.toAtom, ha, Option.getD_some]
  exact ⟨hr, hty⟩

mutual

theorem _root_.DotMNF.HasTy.toH_typed {s : Sig} {Γ : Ctx s} {t : DotMNF.Tm s} {T : Ty s} :
    (h : HasTy Γ t T) → h.toH.erase = t ∧ HTy Γ h.toH T
  | .var => ⟨rfl, .atom .var⟩
  | .lam d => by
      obtain ⟨e, ht⟩ := DotMNF.HasTy.toH_typed d
      exact ⟨by simp [DotMNF.HasTy.toH, HTm.erase, HVal.erase, e], .lam ht⟩
  | .app hf hy => by
      obtain ⟨hra, ha⟩ := DotMNF.HasTy.toAtom_typed hf
      obtain ⟨hrb, hb⟩ := DotMNF.HasTy.toAtom_typed hy
      refine ⟨?_, ?_⟩
      · show HTm.erase (.app hf.toAtom hy.toAtom) = _
        simp [HTm.erase, hra, hrb]
      · have := HTy.app ha hb .refl
        rw [hrb] at this
        exact this
  | .obj (T := T') hd hdist => by
      obtain ⟨e, ht⟩ := DotMNF.DefsTy.toH_typed hd
      refine ⟨by simp [DotMNF.HasTy.toH, HTm.erase, HVal.erase, e], ?_⟩
      have ht' : HDefsTy (Γ.consSelf hd.toH.erase T') hd.toH T' := by rw [e]; exact ht
      have hdist' : hd.toH.erase.Distinct := by rw [e]; exact hdist
      exact .obj ht' hdist'
  | .proj h => by
      obtain ⟨hr, ha⟩ := DotMNF.HasTy.toAtom_typed h
      refine ⟨?_, .proj ha .fld⟩
      show HTm.erase (.proj h.toAtom _) = _
      simp [HTm.erase, hr]
  | .let d1 d2 => by
      obtain ⟨e1, h1⟩ := DotMNF.HasTy.toH_typed d1
      obtain ⟨e2, h2⟩ := DotMNF.HasTy.toH_typed d2
      exact ⟨by simp [DotMNF.HasTy.toH, HTm.erase, e1, e2], .let h1 h2⟩
  | .recI (T := T') h => by
      obtain ⟨hr, ha⟩ := DotMNF.HasTy.toAtom_typed h
      refine ⟨?_, .atom (.fold ?_)⟩
      · show HTm.erase (.atom (.fold T' h.toAtom)) = _
        simp [HTm.erase, Atom.root, hr]
      · show ATy Γ h.toAtom (T'.substVar h.toAtom.root)
        rw [hr]; exact ha
  | .recE (T := T') h => by
      obtain ⟨hr, ha⟩ := DotMNF.HasTy.toAtom_typed h
      refine ⟨?_, ?_⟩
      · show HTm.erase (.atom (.unfold h.toAtom)) = _
        simp [HTm.erase, Atom.root, hr]
      · have h1 := ATy.unfold ha
        rw [hr] at h1
        exact .atom h1
  | .andI h1 h2 => by
      obtain ⟨hr1, ha⟩ := DotMNF.HasTy.toAtom_typed h1
      obtain ⟨hr2, hb⟩ := DotMNF.HasTy.toAtom_typed h2
      refine ⟨?_, .atom (.both ha hb (hr1.trans hr2.symm))⟩
      show HTm.erase (.atom (.both h1.toAtom h2.toAtom)) = _
      simp [HTm.erase, Atom.root, hr1]
  | .sub h d => by
      obtain ⟨e, ht⟩ := DotMNF.HasTy.toH_typed h
      exact ⟨by simp [DotMNF.HasTy.toH, HTm.erase, e], .cast ht .refl (DotMNF.Sub.toCert_typed d)⟩

theorem _root_.DotMNF.DefsTy.toH_typed {s : Sig} {Γ : Ctx s} {d : DotMNF.Defs s} {T : Ty s} :
    (h : DefsTy Γ d T) → h.toH.erase = d ∧ HDefsTy Γ h.toH T
  | .typ => ⟨rfl, .typ⟩
  | .trm h => by
      obtain ⟨e, ht⟩ := DotMNF.HasTy.toH_typed h
      exact ⟨by simp [DotMNF.DefsTy.toH, HDefs.erase, e], .trm ht⟩
  | .and h1 h2 => by
      obtain ⟨e1, ht1⟩ := DotMNF.DefsTy.toH_typed h1
      obtain ⟨e2, ht2⟩ := DotMNF.DefsTy.toH_typed h2
      exact ⟨by simp [DotMNF.DefsTy.toH, HDefs.erase, e1, e2], .and ht1 ht2⟩

end

/-! ## Smoke checks on DOT-MNF's E3 -/

/-- E3's inclusion `{b:⊤} <: x.A <: {a:⊤}` as a certificate, accepted by the checker. -/
theorem E3sub_toCert_checks :
    synthC DotMNF.Examples.E3Ctx2 DotMNF.Examples.E3sub.toCert =
      some (DotMNF.Examples.E3T2, DotMNF.Examples.E3T1) := by decide

/-- E3's closed term as an annotated term, accepted by the term checker, with
the same erased program. -/
theorem E3_toH_checks :
    DotMNF.Examples.E3.toH.erase =
      .val (.lam DotMNF.Examples.E3Dom (.val (.lam DotMNF.Examples.E3T2
        (.let (.path (.var .here)) (.path (.var .here)))))) ∧
    (Ty.all DotMNF.Examples.E3Dom (.all DotMNF.Examples.E3T2 DotMNF.Examples.E3T1)) ∈
      synthTm .nil DotMNF.Examples.E3.toH := by decide

end Selective
