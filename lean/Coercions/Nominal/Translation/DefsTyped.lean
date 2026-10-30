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

Plan XII adds `DefsTy.clsAgree`: every class that the type of typed definitions declares at a field
path, read by `Ty.clsAt`, is the class of the image's block at that path, translated.  It reads the
class entries of the image (`DefsTy.getCls_translate`) and its nested blocks
(`DefsTy.kids_translate`).  The distinct labels of `ty_defs_cons` make the newest-first reads of
source and target agree.  `DefsTy.clsAgree_self` is the premise `ClsAgree` of Rel-Self at the
transparent self that VA-Obj binds, which `ty_new_intro` of `HasTy.translate_typed` reads.
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
  | _, _, _, _, .ty_def_cls _, _ => rfl

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

/-! ## `DefsTy.clsAgree`: the classes of a self type are the classes of its image (plan XII) -/

/-- A type definition's declaration `{A : T..T}` declares no class. -/
theorem Ty.findCls_tdef (A C : Label) (T : Ty s) : (Ty.rcd (.typ A T T)).findCls C = none := by
  simp only [Ty.findCls]
  split
  · next h => obtain ⟨rfl, -, hb⟩ := h; cases hb
  · rfl

/-- The declaration of one typed definition declares a class only at the definition's label, and
only for `ty_def_cls`. -/
theorem DefTy.findCls_label : ∀ {G : Ctx s} {r : Path s} {d : Def s} {D : Dec s}, DefTy G r d D → ∀ {C : Label} {U : Ty s},
    (Ty.rcd D).findCls C = some U → d.label = C
  | _, _, _, _, .ty_def_typ (A := A) (T := T), C, U, h => by rw [Ty.findCls_tdef] at h; cases h
  | _, _, _, _, .ty_def_all _, _, _, h => nomatch h
  | _, _, _, _, .ty_def_new _ _, _, _, h => nomatch h
  | _, _, _, _, .ty_def_path _, _, _, h => nomatch h
  | _, _, _, _, .ty_def_cls (C := C') _, C, U, h => by
      simp only [Ty.findCls] at h
      split at h
      · next hc => exact hc.2.1.symm
      · cases h

/-- A class that the type of typed definitions declares is at one of the definitions' labels. -/
theorem DefsTy.findCls_mem : ∀ {G : Ctx s} {r : Path s} {ds : Defs s} {T : Ty s}, DefsTy G r ds T → ∀ {C : Label} {U : Ty s},
    T.findCls C = some U → C ∈ ds.labels
  | _, _, _, _, .ty_defs_one dd, C, U, h => DefTy.findCls_label dd h ▸ List.mem_cons_self ..
  | _, _, _, _, .ty_defs_cons (D := D) dds dd _, C, U, h => by
      simp only [Ty.findCls] at h
      cases h₁ : (Ty.rcd D).findCls C with
      | some V => exact DefTy.findCls_label dd h₁ ▸ List.mem_cons_self ..
      | none =>
          rw [h₁] at h
          exact List.mem_cons_of_mem _ (DefsTy.findCls_mem dds h)

/-- One definition at a label other than `C` keeps the class at `C` of the definitions before it. -/
theorem DefTy.getCls_translate : ∀ {G : Ctx s} {r : Path s} {d : Def s} {D : Dec s} (dd : DefTy G r d D) (ds : FCn.Defs s) (C : Label),
    d.label ≠ C → (dd.translate ds).tyDefs.getCls C = ds.tyDefs.getCls C
  | _, _, _, _, .ty_def_typ (A := A), ds, C, hl => by
      show (FCn.TyDefs.cons _ A _).getCls C = _
      simp only [FCn.TyDefs.getCls]
      rw [if_neg (fun e => hl e.symm)]
  | _, _, _, _, .ty_def_all _, _, _, _ => rfl
  | _, _, _, _, .ty_def_new _ _, _, _, _ => rfl
  | _, _, _, _, .ty_def_path _, _, _, _ => rfl
  | _, _, _, _, .ty_def_cls (C := C') _, ds, C, hl => by
      show (FCn.TyDefs.cls _ C' _).getCls C = _
      simp only [FCn.TyDefs.getCls]
      rw [if_neg (fun e => hl e.symm)]

/-- A class `C` that the type of typed definitions declares with body `U` is the class entry of the
image at `C`, with body `⟦U⟧`. -/
theorem DefsTy.getCls_translate : ∀ {G : Ctx s} {r : Path s} {ds : Defs s} {T : Ty s} (d : DefsTy G r ds T) (C : Label) (U : Ty s),
    T.findCls C = some U → d.translate.tyDefs.getCls C = some U.translate
  | _, _, _, _, .ty_defs_one dd, C, U, h => by
      -- only a class definition declares a class
      cases dd with
      | ty_def_typ => rw [Ty.findCls_tdef] at h; cases h
      | ty_def_all _ => cases h
      | ty_def_new _ _ => cases h
      | ty_def_path _ => cases h
      | ty_def_cls _ =>
          simp only [Ty.findCls] at h
          split at h
          · next hc =>
              cases h
              obtain ⟨-, rfl, -⟩ := hc
              show (FCn.TyDefs.cls _ C _).getCls C = _
              simp [FCn.TyDefs.getCls]
          · cases h
  | _, _, _, _, .ty_defs_cons (d := d) (D := D) dds dd hn, C, U, h => by
      simp only [Ty.findCls] at h
      cases h₁ : (Ty.rcd D).findCls C with
      | some V =>
          cases dd with
          | ty_def_typ => rw [Ty.findCls_tdef] at h₁; cases h₁
          | ty_def_all _ => cases h₁
          | ty_def_new _ _ => cases h₁
          | ty_def_path _ => cases h₁
          | ty_def_cls _ =>
              rw [h₁] at h
              cases h
              simp only [Ty.findCls] at h₁
              split at h₁
              · next hc =>
                  cases h₁
                  obtain ⟨-, rfl, -⟩ := hc
                  show (FCn.TyDefs.cls _ C _).getCls C = _
                  simp [FCn.TyDefs.getCls]
              · cases h₁
      | none =>
          rw [h₁] at h
          have hm := DefsTy.findCls_mem dds h
          have hl : d.label ≠ C := fun e => Defs.not_mem_labels_of_hasnt hn (e ▸ hm)
          show (dd.translate dds.translate).tyDefs.getCls C = _
          rw [DefTy.getCls_translate dd _ C hl]
          exact DefsTy.getCls_translate dds C U h

/-- The declaration of one typed definition declares a nested object only at its label, and then
its image's child at that label is the block of the image of the nested definitions. -/
theorem DefTy.findNest_translate : ∀ {G : Ctx s} {r : Path s} {d : Def s} {D : Dec s} (dd : DefTy G r d D) (ds : FCn.Defs s) {b : Label} {U : Ty (s,x)},
    (Ty.rcd D).findNest b = some U → d.label = b ∧
      ∃ (dsn : Defs (s,x)) (dn : DefsTy G (r.sel b) (dsn.substPath (r.sel b)) (U.substPath (r.sel b))),
        (dd.translate ds).kids.get b = some dn.translate.block
  | _, _, _, _, .ty_def_typ, _, _, _, h => nomatch h
  | _, _, _, _, .ty_def_all (b := b') _, _, b, U, h => by
      simp only [Ty.findNest] at h; split at h <;> cases h
  | _, _, _, _, .ty_def_new (b := b') (ds := dsn) _ dn, ds, b, U, h => by
      simp only [Ty.findNest, Ty.muBody] at h
      split at h
      · next e =>
          cases h; subst e
          refine ⟨rfl, dsn, dn, ?_⟩
          show FCn.Kids.get (.cons _ b _) b = _
          simp only [FCn.Kids.get]; rfl
      · cases h
  | _, _, _, _, .ty_def_path (b := b') _, _, b, U, h => by
      simp only [Ty.findNest] at h; split at h <;> cases h
  | _, _, _, _, .ty_def_cls _, _, _, _, h => nomatch h

/-- One definition at a label other than `b` keeps the child at `b` of the definitions before it. -/
theorem DefTy.kids_translate_ne : ∀ {G : Ctx s} {r : Path s} {d : Def s} {D : Dec s} (dd : DefTy G r d D) (ds : FCn.Defs s) (b : Label),
    d.label ≠ b → (dd.translate ds).kids.get b = ds.kids.get b
  | _, _, _, _, .ty_def_typ, _, _, _ => rfl
  | _, _, _, _, .ty_def_all (b := b') _, ds, b, hl => by
      show FCn.Kids.get (.cons _ b' _) b = _; simp only [FCn.Kids.get]; rw [if_neg (fun e => hl e.symm)]
  | _, _, _, _, .ty_def_new (b := b') _ _, ds, b, hl => by
      show FCn.Kids.get (.cons _ b' _) b = _; simp only [FCn.Kids.get]; rw [if_neg (fun e => hl e.symm)]
  | _, _, _, _, .ty_def_path (b := b') _, ds, b, hl => by
      show FCn.Kids.get (.cons _ b' _) b = _; simp only [FCn.Kids.get]; rw [if_neg (fun e => hl e.symm)]
  | _, _, _, _, .ty_def_cls _, _, _, _ => rfl

/-- A nested object that the type of typed definitions declares is at one of the definitions' labels. -/
theorem DefsTy.findNest_mem : ∀ {G : Ctx s} {r : Path s} {ds : Defs s} {T : Ty s}, DefsTy G r ds T → ∀ {b : Label} {U : Ty (s,x)},
    T.findNest b = some U → b ∈ ds.labels
  | _, _, _, _, .ty_defs_one dd, b, U, h => (DefTy.findNest_translate dd .nil h).1 ▸ List.mem_cons_self ..
  | _, _, _, _, .ty_defs_cons (D := D) dds dd _, b, U, h => by
      simp only [Ty.findNest] at h
      cases h₁ : (Ty.rcd D).findNest b with
      | some V => exact (DefTy.findNest_translate dd .nil h₁).1 ▸ List.mem_cons_self ..
      | none =>
          rw [h₁] at h
          exact List.mem_cons_of_mem _ (DefsTy.findNest_mem dds h)

/-- A nested object that the type of typed definitions declares at `b` with body `U` is the child
of the image at `b`, the block of the image of typed nested definitions. -/
theorem DefsTy.kids_translate : ∀ {G : Ctx s} {r : Path s} {ds : Defs s} {T : Ty s} (d : DefsTy G r ds T) (b : Label) (U : Ty (s,x)),
    T.findNest b = some U → ∃ (dsn : Defs (s,x)) (dn : DefsTy G (r.sel b) (dsn.substPath (r.sel b)) (U.substPath (r.sel b))),
      d.translate.kids.get b = some dn.translate.block
  | _, _, _, _, .ty_defs_one dd, b, U, h => (DefTy.findNest_translate dd .nil h).2
  | _, _, _, _, .ty_defs_cons (d := d) (D := D) dds dd hn, b, U, h => by
      simp only [Ty.findNest] at h
      cases h₁ : (Ty.rcd D).findNest b with
      | some V =>
          rw [h₁] at h; cases h
          exact (DefTy.findNest_translate dd dds.translate h₁).2
      | none =>
          rw [h₁] at h
          have hm := DefsTy.findNest_mem dds h
          have hl : d.label ≠ b := fun e => Defs.not_mem_labels_of_hasnt hn (e ▸ hm)
          obtain ⟨dsn, dn, e⟩ := DefsTy.kids_translate dds b U h
          exact ⟨dsn, dn, (DefTy.kids_translate_ne dd dds.translate b hl).trans e⟩

/-- `DefsTy.clsAgree`: every class the type of typed definitions declares at a field path is the
class of the image's block at that path, translated. -/
theorem DefsTy.clsAgree : ∀ (bs : List Label) {G : Ctx s} {r : Path s} {ds : Defs s} {T : Ty s} (d : DefsTy G r ds T)
    (C : Label) (U : Ty s), T.clsAt r bs C = some U → (d.translate.block.walk bs).bind (·.cls C) = some U.translate
  | [], _, _, _, _, d, C, U, h => DefsTy.getCls_translate d C U h
  | b :: bs, _, r, _, T, d, C, U, h => by
      simp only [Ty.clsAt] at h
      cases h₁ : T.findNest b with
      | none => rw [h₁] at h; cases h
      | some V =>
          rw [h₁, Option.bind_some] at h
          obtain ⟨dsn, dn, e⟩ := DefsTy.kids_translate d b V h₁
          show ((d.translate.kids.get b).bind (FCn.Block.walk · bs)).bind (·.cls C) = _
          rw [e, Option.bind_some]
          exact DefsTy.clsAgree bs dn C U h

/-- The premise `ClsAgree` of Rel-Self at `ty_new_intro`, for the transparent self that VA-Obj binds
at the image's block. -/
theorem DefsTy.clsAgree_self {G : Ctx s} {T : Ty (s,x)} {ds : Defs (s,x)} (d : DefsTy (G.consSelf T) (.var .here) ds T) (Δ : FCn.Ctx s) :
    Ctx.ClsAgree Δ T (.transparent (FCn.Ty.mu T.tel) d.translate.block) := by
  intro bs C U h
  rw [FCn.Ctx.clsAt_ext]
  exact DefsTy.clsAgree bs d C U h

end Nominal.Source
