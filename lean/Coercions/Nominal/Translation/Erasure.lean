import Coercions.Nominal.Translation.TermsTyped
import Coercions.Nominal.Source.Erasure
import Coercions.Nominal.FCn.Erasure

/-!
# The translation erases to the source's erasure (plan X, Part TR.8, stage X6 group g3)

FCn's erasure of the image of a derivation is the source's erasure of its term.  On the left `erase`
is FCn's (`FCp/Erasure.lean:31-49`), on the right the source's (`Source/Erasure.lean:50-77`).
`HasTy.translate_erase`, `DefTy.translate_erase` and `DefsTy.translate_erase` are one mutual theorem,
structural over `HasTy`, `DefTy` and `DefsTy`, one case per source rule.  None reads a typing of the
image.

A path image erases to its path by `HasTy.translatePath_path`.  A cast erases to what it casts, so
`Translation.toValue_erase` carries the erasure through the casts that end the image of a lambda.  A
type definition erases to nothing in FCn and to `drop A` in the source, equal when no earlier
definition has the label `A` (`Defs.addr_typ_of_hasnt`, `Source/Erasure.lean:233`), which
`ty_defs_cons` gives.  A class definition (plan XII) erases to nothing in FCn and to `drop C` in the
source, equal in the same way (`Defs.addr_cls_of_hasnt`).  A nested literal erases to `nest` of its definitions at `r.b` on both sides
(`Defs.addr_subst`, `Source/Erasure.lean:107`).

The examples.  `E3_image_erase` reads the theorem at E3.  `E3_image_erase_kernel` and
`E8_image_erase_kernel` run the translation and both erasures in the kernel, the lockstep of the
erasure on two whole programs.
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-- The value under the casts of a term is what the term erases to. -/
theorem _root_.Nominal.Translation.toValue_erase : ∀ {t : FCn.Tm s} {v : FCn.Value s},
    Translation.toValue t = some v → t.erase = .val v.erase
  | .val v', _, hv => by cases hv; rfl
  | .cast t₀ e, v, hv => by
      cases h' : Translation.toValue t₀ with
      | none => simp [Translation.toValue, h'] at hv
      | some v₀ =>
          simp only [Translation.toValue, h', Option.map_some, Option.some.injEq] at hv
          subst hv
          show t₀.erase = .val v₀.erase
          exact Translation.toValue_erase h'
  | .path _, _, hv => nomatch hv
  | .app _ _, _, hv => nomatch hv
  | .lett _ _, _, hv => nomatch hv

-- one mutual block, structural over HasTy, DefTy and DefsTy
mutual
/-- TR.8's `translate_erase`: the image of a derivation erases to the source's erasure of its term. -/
theorem HasTy.translate_erase : ∀ {G : Ctx s} {t : Tm s} {T : Ty s} (d : HasTy G t T), d.translate.erase = t.erase
  | _, _, _, .ty_var hx => by
      show FCn.Tm.erase (.path _) = _
      simp only [FCn.Tm.erase, HasTy.translatePath_path, Tm.erase]
  | _, _, _, .ty_all_intro (S := S) dt => by
      show FCn.Tm.erase (.val (.lam S.translate dt.translate)) = _
      simp only [FCn.Tm.erase, FCn.Value.erase, HasTy.translate_erase dt, Tm.erase, Val.erase]
  | _, _, _, .ty_all_elim dp dq => by
      show FCn.Tm.erase (.app _ _) = _
      simp only [FCn.Tm.erase, HasTy.translatePath_path, Tm.erase]
  | _, _, _, .ty_new_intro (T := T) dds => by
      show FCn.Tm.erase (.val (.obj T.tel dds.translate)) = _
      simp only [FCn.Tm.erase, FCn.Value.erase, DefsTy.translate_erase dds, Tm.erase, Val.erase]
  | _, _, _, .ty_new_elim d => by
      show FCn.Tm.erase (.path _) = _
      simp only [FCn.Tm.erase, HasTy.translatePath_path, Tm.erase]
  | _, _, _, .ty_rcd_intro d => by
      show FCn.Tm.erase (.path _) = _
      simp only [FCn.Tm.erase, HasTy.translatePath_path, Tm.erase]
  | _, _, _, .ty_let dt du => by
      show FCn.Tm.erase (.lett dt.translate du.translate) = _
      simp only [FCn.Tm.erase, HasTy.translate_erase dt, HasTy.translate_erase du, Tm.erase]
  | _, _, _, .ty_sngl d₁ d₂ => by
      show FCn.Tm.erase (.path _) = _
      simp only [FCn.Tm.erase, HasTy.translatePath_path, Tm.erase]
  | _, _, _, .ty_path_elim d₁ d₂ => by
      show FCn.Tm.erase (.path _) = _
      simp only [FCn.Tm.erase, HasTy.translatePath_path, Tm.erase]
  | _, _, _, .ty_rec_intro d => by
      show FCn.Tm.erase (.path _) = _
      simp only [FCn.Tm.erase, HasTy.translatePath_path, Tm.erase]
  | _, _, _, .ty_rec_elim d => by
      show FCn.Tm.erase (.path _) = _
      simp only [FCn.Tm.erase, HasTy.translatePath_path, Tm.erase]
  | _, _, _, .ty_and_intro d₁ d₂ => by
      show FCn.Tm.erase (.path _) = _
      simp only [FCn.Tm.erase, HasTy.translatePath_path, Tm.erase]
  | _, .path _, _, .ty_sub d e => by
      show FCn.Tm.erase (.path _) = _
      simp only [FCn.Tm.erase, HasTy.translatePath_path, Tm.erase]
  | _, .val _, _, .ty_sub d e => by
      show FCn.Tm.erase (.cast d.translate e.translate) = _
      simp only [FCn.Tm.erase, HasTy.translate_erase d]
  | _, .app _ _, _, .ty_sub d e => by
      show FCn.Tm.erase (.cast d.translate e.translate) = _
      simp only [FCn.Tm.erase, HasTy.translate_erase d]
  | _, .lett _ _, _, .ty_sub d e => by
      show FCn.Tm.erase (.cast d.translate e.translate) = _
      simp only [FCn.Tm.erase, HasTy.translate_erase d]
/-- The image of one definition, appended to definitions that erase to `addr r ds'`, erases to
`addr r (ds' ▹ d)`, when no definition of `ds'` has the label of `d`. -/
theorem DefTy.translate_erase : ∀ {G : Ctx s} {r : Path s} {d : Def s} {D : Dec s} (dd : DefTy G r d D)
    (ds' : Defs s), ds'.hasnt d.label → ∀ (ds : FCn.Defs s), ds.erase = Defs.addr r ds' →
      (dd.translate ds).erase = Defs.addr r (ds'.cons d)
  | _, r, _, _, .ty_def_typ (A := A) (T := T), ds', hn, ds, he => by
      show FCn.Defs.erase (.typ ds A T.translate) = _
      have hn' : ds'.hasnt A := hn
      rw [Defs.addr_typ_of_hasnt (r := r) (T := T) hn']; exact he
  | _, r, _, _, .ty_def_all (b := b) (T := T) (t := t) dl, ds', hn, ds, he => by
      obtain ⟨v, hv, _⟩ := HasTy.translate_lam_of_eq dl _ _ rfl
      have h₁ := HasTy.translate_erase dl
      rw [Translation.toValue_erase hv] at h₁
      show FCn.Defs.erase (.fld ds b (.fn ((Translation.toValue dl.translate).getD _))) = _
      rw [hv]
      simp only [FCn.Defs.erase, FCn.Rhs.erase, Defs.addr, Rhs.eraseField, he]
      simp only [Tm.erase, Val.erase, PDot.Runtime.Tm.val.injEq] at h₁
      simp only [Option.getD_some, h₁]
  | _, r, _, _, .ty_def_new (b := b) (T := T) (ds := dsn) _ dds, ds', hn, ds, he => by
      show FCn.Defs.erase (.fld ds b (.nest T.tel dds.translate)) = _
      simp only [FCn.Defs.erase, FCn.Rhs.erase, Defs.addr, Rhs.eraseField, he, DefsTy.translate_erase dds]
      rw [PDot.Runtime.Defs.substPath, Defs.addr_subst]
      rfl
  | _, r, _, _, .ty_def_path (b := b) dq, ds', hn, ds, he => by
      show FCn.Defs.erase (.fld ds b (.path dq.translatePath)) = _
      simp only [FCn.Defs.erase, FCn.Rhs.erase, Defs.addr, Rhs.eraseField, he, HasTy.translatePath_path]
  -- ty_def_cls: both sides drop the class, C new by ty_defs_cons
  | _, r, _, _, .ty_def_cls (C := C) (T := T) _, ds', hn, ds, he => by
      show FCn.Defs.erase (.cls ds C T.translate) = _
      have hn' : ds'.hasnt C := hn
      rw [Defs.addr_cls_of_hasnt (r := r) (T := T) hn']
      exact he
/-- The image of a definition list erases to the source's addressed definitions at `r`. -/
theorem DefsTy.translate_erase : ∀ {G : Ctx s} {r : Path s} {ds : Defs s} {T : Ty s} (d : DefsTy G r ds T),
    d.translate.erase = Defs.addr r ds
  | _, _, _, _, .ty_defs_one dd => DefTy.translate_erase dd .nil rfl .nil rfl
  | _, _, _, _, .ty_defs_cons dds dd hn => DefTy.translate_erase dd _ hn dds.translate (DefsTy.translate_erase dds)
end
-- end of the block

/-- E3: the image of the compiler program erases to the program's erasure. -/
theorem E3_image_erase : CP_d.translate.erase = compiler_t.erase := HasTy.translate_erase CP_d

/-- E8: the kernel runs the translation and both erasures, and they agree. -/
theorem E8_image_erase_kernel : E8_d.translate.erase = E8_prog.erase := by decide +kernel

/-- E3: the kernel runs the translation and both erasures, and they agree. -/
theorem E3_image_erase_kernel : CP_d.translate.erase = compiler_t.erase := by decide +kernel

end Nominal.Source
