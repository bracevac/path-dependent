import Coercions.Selective.Sound
import Coercions.Selective.Lift

/-!
# Coverage of DOT-MNF: the converse translation

* `cert_complete : DotMNF.Sub Γ S T → ∃ c, CTy Γ c S T` and
  `atom_complete : DotMNF.HasTy Γ (.path (.var x)) T → ∃ a, a.root = x ∧ ATy Γ a T`,
  mutually, by structural recursion on the source derivations.  `selUpper` and
  `selLower` take the receiver's typing (built by any rule, `HasTy.sub`
  included) to a receiver atom; `Sub.all` becomes `liftAllD c₁ ; liftAllC c₂`.
* `elaboration_complete : DotMNF.HasTy Γ t T → ∃ h, h.erase = t ∧ HTy Γ h T`
  with `defs_complete`.  Every implicit `≤₀` step of the image is `refl`.

With the soundness directions: `typability_iff`, `coercion_iff`, `atom_iff`.
-/

namespace Selective

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ctx Ty Path HasTy Sub DefsTy)

mutual
theorem cert_complete {s : Sig} {Γ : Ctx s} : {S T : Ty s} → Sub Γ S T → ∃ c, CTy Γ c S T
  | _, _, .top => ⟨_, .step .top⟩
  | _, _, .bot => ⟨_, .step .bot⟩
  | _, _, .refl => ⟨_, .step .refl⟩
  | _, _, .trans d1 d2 => by
      obtain ⟨c1, h1⟩ := cert_complete d1; obtain ⟨c2, h2⟩ := cert_complete d2
      exact ⟨_, .seq h1 h2⟩
  | _, _, .and1 => ⟨_, .step (.andL1 .refl)⟩
  | _, _, .and2 => ⟨_, .step (.andL2 .refl)⟩
  | _, _, .and d1 d2 => by
      obtain ⟨c1, h1⟩ := cert_complete d1; obtain ⟨c2, h2⟩ := cert_complete d2
      exact ⟨_, .seq (.step (.andR .refl .refl)) (.seq h1.liftAndL h2.liftAndR)⟩
  | _, _, .fld d => by obtain ⟨c, h⟩ := cert_complete d; exact ⟨_, h.liftFld⟩
  | _, _, .typ d1 d2 => by
      obtain ⟨c1, h1⟩ := cert_complete d1; obtain ⟨c2, h2⟩ := cert_complete d2
      exact ⟨_, .seq h2.liftTypU h1.liftTypL⟩
  | _, _, @Sub.selUpper _ _ x A S T h => by
      obtain ⟨a, hr, ha⟩ := atom_complete h
      subst hr
      exact ⟨.pos (.selU a A T), .pos (.selU ha .typ)⟩
  | _, _, @Sub.selLower _ _ x A S T h => by
      obtain ⟨a, hr, ha⟩ := atom_complete h
      subst hr
      exact ⟨.pos (.selL a A S), .pos (.selL ha .typ)⟩
  | _, _, .all d1 d2 => by
      obtain ⟨c1, h1⟩ := cert_complete d1; obtain ⟨c2, h2⟩ := cert_complete d2
      exact ⟨_, .seq h1.liftAllD h2.liftAllC⟩
theorem atom_complete {s : Sig} {Γ : Ctx s} : {x : BVar s .var} → {T : Ty s} →
    HasTy Γ (.path (.var x)) T → ∃ a : Atom s, a.root = x ∧ ATy Γ a T
  | x, _, .var => ⟨.var x, rfl, .var⟩
  | _, _, @HasTy.recI _ _ _ T h => by
      obtain ⟨a, hr, ha⟩ := atom_complete h
      subst hr
      exact ⟨.fold T a, rfl, .fold ha⟩
  | _, _, @HasTy.recE _ _ _ T h => by
      obtain ⟨a, hr, ha⟩ := atom_complete h
      subst hr
      exact ⟨.unfold a, rfl, .unfold ha⟩
  | _, _, .andI h1 h2 => by
      obtain ⟨a, hr1, ha⟩ := atom_complete h1
      obtain ⟨b, hr2, hb⟩ := atom_complete h2
      exact ⟨.both a b, hr1, .both ha hb (hr1.trans hr2.symm)⟩
  | _, _, .sub h d => by
      obtain ⟨a, hr, ha⟩ := atom_complete h
      obtain ⟨c, hc⟩ := cert_complete d
      exact ⟨.cast a c, hr, .cast ha hc⟩
end

/-! ## Coverage of term typing (erasure drops casts, atoms go to roots) -/

mutual
theorem elaboration_complete {s : Sig} {Γ : Ctx s} : {t : DotMNF.Tm s} → {T : Ty s} →
    HasTy Γ t T → ∃ h : HTm s, h.erase = t ∧ HTy Γ h T
  | _, _, .var (x := x) => ⟨.atom (.var x), rfl, .atom .var⟩
  | _, _, .lam d => by
      obtain ⟨b, hb, hd⟩ := elaboration_complete d
      exact ⟨.val (.lam _ b), by simp [HTm.erase, HVal.erase, hb], .lam hd⟩
  | _, _, .app hf hy => by
      obtain ⟨a, hra, ha⟩ := atom_complete hf
      obtain ⟨b, hrb, hb⟩ := atom_complete hy
      refine ⟨.app a b, by simp [HTm.erase, hra, hrb], ?_⟩
      have := HTy.app ha hb .refl
      rwa [hrb] at this
  | _, _, .obj hd hdist => by
      obtain ⟨d', hd', hty⟩ := defs_complete hd
      subst hd'
      exact ⟨.val (.obj _ d'), rfl, .obj hty hdist⟩
  | _, _, .proj h => by
      obtain ⟨a, hr, ha⟩ := atom_complete h
      subst hr
      exact ⟨.proj a _, rfl, .proj ha .fld⟩
  | _, _, .let d1 d2 => by
      obtain ⟨t1, h1, ht1⟩ := elaboration_complete d1
      obtain ⟨t2, h2, ht2⟩ := elaboration_complete d2
      exact ⟨.let t1 t2, by simp [HTm.erase, h1, h2], .let ht1 ht2⟩
  | _, _, @HasTy.recI _ _ x T h => by
      obtain ⟨a, hr, ha⟩ := atom_complete h
      subst hr
      exact ⟨.atom (.fold T a), rfl, .atom (.fold ha)⟩
  | _, _, @HasTy.recE _ _ x T h => by
      obtain ⟨a, hr, ha⟩ := atom_complete h
      subst hr
      exact ⟨.atom (.unfold a), rfl, .atom (.unfold ha)⟩
  | _, _, .andI h1 h2 => by
      obtain ⟨a, hr1, ha⟩ := atom_complete h1
      obtain ⟨b, hr2, hb⟩ := atom_complete h2
      subst hr1
      exact ⟨.atom (.both a b), rfl, .atom (.both ha hb hr2.symm)⟩
  | _, _, .sub h d => by
      obtain ⟨t', ht', hty⟩ := elaboration_complete h
      obtain ⟨c, hc⟩ := cert_complete d
      exact ⟨.cast t' c, by simp [HTm.erase, ht'], .cast hty .refl hc⟩
theorem defs_complete {s : Sig} {Γ : Ctx s} : {d : DotMNF.Defs s} → {T : Ty s} →
    DefsTy Γ d T → ∃ d' : HDefs s, d'.erase = d ∧ HDefsTy Γ d' T
  | _, _, .typ (A := A) (T := T) => ⟨.typ A T, rfl, .typ⟩
  | _, _, .trm (a := a) h => by
      obtain ⟨t', ht', hty⟩ := elaboration_complete h
      exact ⟨.trm a t', by simp [HDefs.erase, ht'], .trm hty⟩
  | _, _, .and h1 h2 => by
      obtain ⟨d1, e1, h1'⟩ := defs_complete h1
      obtain ⟨d2, e2, h2'⟩ := defs_complete h2
      exact ⟨.and d1 d2, by simp [HDefs.erase, e1, e2], .and h1' h2'⟩
end

/-- Typability of erased programs coincides with DOT-MNF's. -/
theorem typability_iff {s : Sig} {Γ : Ctx s} {t : DotMNF.Tm s} {T : Ty s} :
    (∃ h : HTm s, h.erase = t ∧ HTy Γ h T) ↔ Nonempty (HasTy Γ t T) := by
  constructor
  · rintro ⟨h, rfl, hty⟩; exact elaboration_typed hty
  · rintro ⟨d⟩; exact elaboration_complete d

/-- Coercion existence coincides with DOT-MNF subtyping. -/
theorem coercion_iff {s : Sig} {Γ : Ctx s} {S T : Ty s} :
    (∃ c, CTy Γ c S T) ↔ Nonempty (Sub Γ S T) :=
  ⟨fun ⟨_, h⟩ => CTy.sound h, fun ⟨d⟩ => cert_complete d⟩

/-- Variable-path evidence coincides with DOT-MNF's typing of variable paths. -/
theorem atom_iff {s : Sig} {Γ : Ctx s} {x : BVar s .var} {T : Ty s} :
    (∃ a : Atom s, a.root = x ∧ ATy Γ a T) ↔ Nonempty (HasTy Γ (.path (.var x)) T) := by
  constructor
  · rintro ⟨a, rfl, h⟩; exact ATy.sound h
  · rintro ⟨d⟩; exact atom_complete d


end Selective
