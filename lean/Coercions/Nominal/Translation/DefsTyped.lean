import Coercions.Nominal.Translation.Terms

/-!
# Definitions: the lemmas outside the recursion (plan X, Parts TR.5 and TR.8, stage X6 group g3)

The typedness of terms and definitions is one mutual theorem, in `TermsTyped` (decision D1 of the
groups file).  This module holds the lemmas it reads from outside the recursion.

`DefTy.translate_labels` and `DefsTy.translate_labels` say the image of a definition list has the
source's labels, so `ty_defs_cons`'s `ds.hasnt d.label` gives `DF-*`'s premise `a ∉ ds.labels`.

Three inversions of FCn's typing, each through an equation form that generalizes the index (decision
D12, the route of `Source/Derived.lean:30-56`).  `Translation.tm_val_inv_of_eq` and
`Translation.tm_cast_inv_of_eq` invert `TM-Val` and `TM-Cast`, and `Translation.toValue_typed` reads
them to type the value under the casts of a typed term.  `Translation.defs_typ_inv_of_eq` inverts
`DF-Typ`.  The example `N5_image_untyped` reads it.

`HasTy.translate_lam_of_eq` says the image of a derivation at a lambda is a lambda under casts, so
the fallback of `ty_def_all`'s image is never read.
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-- The image of one definition puts the definition's label first. -/
theorem DefTy.translate_labels : ∀ {G : Ctx s} {r : Path s} {d : Def s} {D : Dec s} (dd : DefTy G r d D) (ds : FCn.Defs s),
    (dd.translate ds).labels = d.label :: ds.labels
  | _, _, _, _, .ty_def_typ, _ => rfl
  | _, _, _, _, .ty_def_all _, _ => rfl
  | _, _, _, _, .ty_def_new _ _, _ => rfl
  | _, _, _, _, .ty_def_path _, _ => rfl

/-- The image of a definition list has the labels of the source list. -/
theorem DefsTy.translate_labels : ∀ {G : Ctx s} {r : Path s} {ds : Defs s} {T : Ty s} (d : DefsTy G r ds T),
    d.translate.labels = ds.labels
  | _, _, _, _, .ty_defs_one dd => DefTy.translate_labels dd .nil
  | _, _, _, _, .ty_defs_cons dds dd _ => by
      show (dd.translate dds.translate).labels = _
      rw [DefTy.translate_labels, DefsTy.translate_labels dds]; rfl

/-- `TM-Val` inverted, an equation form (D12): a typed term that is `val v` types `v`. -/
theorem _root_.Nominal.Translation.tm_val_inv_of_eq : ∀ {Γ : FCn.Ctx s} {t : FCn.Tm s} {T : FCn.Ty s},
    FCn.Tm.HasType Γ t T → ∀ (v : FCn.Value s), t = .val v → FCn.Value.HasType Γ v T
  | _, _, _, .val h, _, e => by cases e; exact h
  | _, _, _, .path _, _, e => nomatch e
  | _, _, _, .app _ _, _, e => nomatch e
  | _, _, _, .lett _ _, _, e => nomatch e
  | _, _, _, .cast _ _, _, e => nomatch e

/-- `TM-Cast` inverted, an equation form (D12): a typed term that is `cast t₀ e` types `t₀` at some
`S` and `e` from `S`. -/
theorem _root_.Nominal.Translation.tm_cast_inv_of_eq : ∀ {Γ : FCn.Ctx s} {t : FCn.Tm s} {T : FCn.Ty s},
    FCn.Tm.HasType Γ t T → ∀ (t₀ : FCn.Tm s) (e : FCn.LeCo s), t = .cast t₀ e →
      ∃ S, FCn.Tm.HasType Γ t₀ S ∧ FCn.LeCo.HasType Γ e S T
  | _, _, _, .cast h he, _, _, e => by cases e; exact ⟨_, h, he⟩
  | _, _, _, .val _, _, _, e => nomatch e
  | _, _, _, .path _, _, _, e => nomatch e
  | _, _, _, .app _ _, _, _, e => nomatch e
  | _, _, _, .lett _ _, _, _, e => nomatch e

/-- The value under the casts of a typed term is typed at the term's type, by `VA-Cast` at each
cast. -/
theorem _root_.Nominal.Translation.toValue_typed : ∀ {Δ : FCn.Ctx s} {t : FCn.Tm s} {v : FCn.Value s} {T : FCn.Ty s},
    Translation.toValue t = some v → FCn.Tm.HasType Δ t T → FCn.Value.HasType Δ v T
  | _, .val v', _, _, hv, h => by
      cases hv; exact Translation.tm_val_inv_of_eq h v' rfl
  | _, .cast t₀ e, v, _, hv, h => by
      obtain ⟨S, h₀, he⟩ := Translation.tm_cast_inv_of_eq h t₀ e rfl
      cases h' : Translation.toValue t₀ with
      | none => simp [Translation.toValue, h'] at hv
      | some v₀ =>
          simp only [Translation.toValue, h', Option.map_some, Option.some.injEq] at hv
          subst hv
          exact .cast (Translation.toValue_typed h' h₀) he
  | _, .path _, _, _, hv, _ => nomatch hv
  | _, .app _ _, _, _, hv, _ => nomatch hv
  | _, .lett _ _, _, _, hv, _ => nomatch hv

/-- The image of a derivation at a lambda is a lambda under casts, an equation form (D12).  Only
`ty_all_intro` and `ty_sub` conclude a lambda, and the others are refuted by their equation. -/
theorem HasTy.translate_lam_of_eq : ∀ {G : Ctx s} {t' : Tm s} {U : Ty s} (d : HasTy G t' U) (S : Ty s) (t : Tm (s,x)),
    t' = .val (.lam S t) → ∃ v, Translation.toValue d.translate = some v ∧ v.isLam = true
  | _, _, _, .ty_all_intro (S := S') dt, _, _, e => ⟨.lam S'.translate dt.translate, rfl, rfl⟩
  | _, _, _, .ty_sub d e', S, t, e => by
      obtain ⟨v, hv, hl⟩ := HasTy.translate_lam_of_eq d S t e
      cases e
      exact ⟨.cast v e'.translate, by simp only [HasTy.translate, Translation.toValue, hv]; rfl, hl⟩
  | _, _, _, .ty_var _, _, _, e => nomatch e
  | _, _, _, .ty_all_elim _ _, _, _, e => nomatch e
  | _, _, _, .ty_new_intro _, _, _, e => nomatch e
  | _, _, _, .ty_new_elim _, _, _, e => nomatch e
  | _, _, _, .ty_rcd_intro _, _, _, e => nomatch e
  | _, _, _, .ty_let _ _, _, _, e => nomatch e
  | _, _, _, .ty_sngl _ _, _, _, e => nomatch e
  | _, _, _, .ty_path_elim _ _, _, _, e => nomatch e
  | _, _, _, .ty_rec_intro _, _, _, e => nomatch e
  | _, _, _, .ty_rec_elim _, _, _, e => nomatch e
  | _, _, _, .ty_and_intro _ _, _, _, e => nomatch e

/-- `DF-Typ` inverted, an equation form (D12): a typed list that ends in `{A = U}` has a telescope
that ends in the two bounds of one type `W`, with `U = W⟨p⟩`. -/
theorem _root_.Nominal.Translation.defs_typ_inv_of_eq : ∀ {Γ : FCn.Ctx s} {p : Path s} {ds' : FCn.Defs s} {Tel' : FCn.Telescope (s,x)},
    FCn.Defs.HasType Γ p ds' Tel' → ∀ (ds : FCn.Defs s) (A : Label) (U : FCn.Ty s), ds' = .typ ds A U →
      ∃ Tel W, Tel' = .cons (.cons Tel (.le W (.sel (.var .here) A))) (.le (.sel (.var .here) A) W) ∧
        U = W.substPath p ∧ FCn.Defs.HasType Γ p ds Tel ∧ A ∉ ds.labels
  | _, _, _, _, .typ (Tel := Tel) (W := W) hds hA hU, _, _, _, e => by
      cases e; exact ⟨Tel, W, rfl, hU, hds, hA⟩
  | _, _, _, _, .nil, _, _, _, e => nomatch e
  | _, _, _, _, .path _ _ _ _, _, _, _, e => nomatch e
  | _, _, _, _, .fn _ _ _ _, _, _, _, e => nomatch e
  | _, _, _, _, .nest _ _ _, _, _, _, e => nomatch e

end Nominal.Source
