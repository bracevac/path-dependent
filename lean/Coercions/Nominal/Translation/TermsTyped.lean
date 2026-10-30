import Coercions.Nominal.Translation.DefsTyped

/-!
# Terms and definitions are typed (plan X, Parts TR.5, TR.6 and TR.8, stage X6 group g3)

In related contexts `G ≈ Δ`, the image of a typing `G ⊢ t : T` is an FCn term of type `⟦T⟧`, and the
image of a definition list typed against an annotation opened at `r` is typed against `tel` of the
un-opened annotation, when that annotation is tight.  `HasTy.translate_typed`,
`DefTy.translate_typed` and `DefsTy.translate_typed` are one mutual theorem, structural over
`HasTy`, `DefTy` and `DefsTy`, one case per source rule, with `ty_sub` split by its term.  The context
`Δ` is bound after the derivation, since the rules with a premise under a binder pass a new context
(decision D11 of the groups file).  `DefTy.translate_typed` is the one-definition step the mutual
proof needs (decision D9): it extends typed definitions at `Tel` to `Tel ++ tel D₀`.

The cases.  The path rules are `TM-Path` over `translatePath_typed`.  `ty_all_intro` is `VA-Lam` with
`Ctx.Rel.var`.  `ty_all_elim` is `TM-App` with `Ty.translate_substPath`.  `ty_let` is `TM-Let` with
`Ty.translate_weaken`.  `ty_new_intro` is `VA-Obj`: the self binder is transparent at the image's own
block, related by `Ctx.Rel.self` with `rfl`, and the definitions are typed at
`T₀ = T.rename Rename.succ.lift`, which opens to `T` at `.here` and is tight by
`DefsTy.tight_at_self` and `Ty.tight_rename`.  `ty_sub` at a term that is not a path is `TM-Cast`.
`ty_def_typ` is `DF-Typ`: a tight `{A : S₀..U₀}` has `S₀ = U₀`, the one bound `W = ⟦S₀⟧`.
`ty_def_all` is `DF-Fun` with `HasTy.translate_lam_of_eq` and `Translation.toValue_typed`.
`ty_def_new` is `DF-Nest` with the recursive call at the nested annotation itself, tight by the
rule's first premise, and `Ty.tel_subst_lift`.  `ty_def_path` is `DF-Path`.  `ty_defs_one` and
`ty_defs_cons` read `Ty.substPath_eq_rcd` and `Ty.substPath_eq_and` and the label lemmas.

The examples type the images of X0's E3, E8 and E13.  `N5_image_untyped` shows why
`DefsTy.translate_typed` keeps its premise `T₀.tight = true` (F3, the stage's risk): at X0's N5
witnesses (`Source/Examples.lean:538-551`) the third premise of `ty_def_new` types definitions against
an annotation opened at `z.b`, and the image of those definitions is not typed against `tel` of the
un-opened annotation, whose two bounds of `A` differ.  `N5_image_typed_opened` types the same image
against a tight annotation that opens to the same type.
-/

namespace Nominal.Source

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

-- one mutual block, structural over HasTy, DefTy and DefsTy
mutual
/-- TR.8's `translate_typed`: in related contexts the image of a typing derivation is typed at the
translated type. -/
theorem HasTy.translate_typed : ∀ {G : Ctx s} {t : Tm s} {T : Ty s} (d : HasTy G t T) {Δ : FCn.Ctx s},
    Ctx.Rel G Δ → FCn.Tm.HasType Δ d.translate T.translate
  | _, _, _, .ty_var hx, _, h => .path (HasTy.translatePath_typed (.ty_var hx) h).1
  | _, _, _, .ty_all_intro (S := S) dt, _, h => .val (.lam (HasTy.translate_typed dt (.var h)))
  | _, _, _, .ty_all_elim (q := q) (T := T) dp dq, Δ, h => by
      have h₁ := HasTy.translatePath_typed dp h
      have h₂ := HasTy.translatePath_typed dq h
      have ha := FCn.Tm.HasType.app h₁.1 h₂.1
      rw [h₂.2, ← Ty.translate_substPath] at ha
      exact ha
  | _, _, _, .ty_new_intro (T := T) dds, Δ, h => by
      refine .val (.obj ?_)
      have hd := DefsTy.translate_typed dds (Ctx.Rel.self (b := .transparent (FCn.Ty.mu T.tel) dds.translate.block) h rfl)
        (T.rename Rename.succ.lift) (Ty.rename_succ_lift_substPath_here T) (Ty.tight_rename T _ (DefsTy.tight_at_self dds))
      have e : (T.rename (Rename.succ (k := .var)).lift).tel = T.tel.rename (Rename.succ (k := .var)).lift :=
        Ty.telAt_rename T ((Rename.succ (k := .var)).lift) .here
      rw [e] at hd
      exact hd
  | _, _, _, .ty_new_elim d, _, h => .path (HasTy.translatePath_typed (.ty_new_elim d) h).1
  | _, _, _, .ty_rcd_intro d, _, h => .path (HasTy.translatePath_typed (.ty_rcd_intro d) h).1
  | _, _, _, .ty_let (U := U) dt du, _, h => by
      have h₂ := HasTy.translate_typed du (.var h)
      rw [Ty.translate_weaken] at h₂
      exact .lett (HasTy.translate_typed dt h) h₂
  | _, _, _, .ty_sngl d₁ d₂, _, h => .path (HasTy.translatePath_typed (.ty_sngl d₁ d₂) h).1
  | _, _, _, .ty_path_elim d₁ d₂, _, h => .path (HasTy.translatePath_typed (.ty_path_elim d₁ d₂) h).1
  | _, _, _, .ty_rec_intro d, _, h => .path (HasTy.translatePath_typed (.ty_rec_intro d) h).1
  | _, _, _, .ty_rec_elim d, _, h => .path (HasTy.translatePath_typed (.ty_rec_elim d) h).1
  | _, _, _, .ty_and_intro d₁ d₂, _, h => .path (HasTy.translatePath_typed (.ty_and_intro d₁ d₂) h).1
  | _, .path _, _, .ty_sub d e, _, h => .path (HasTy.translatePath_typed (.ty_sub d e) h).1
  | _, .val _, _, .ty_sub d e, _, h => .cast (HasTy.translate_typed d h) (Sub.translate_typed e h)
  | _, .app _ _, _, .ty_sub d e, _, h => .cast (HasTy.translate_typed d h) (Sub.translate_typed e h)
  | _, .lett _ _, _, .ty_sub d e, _, h => .cast (HasTy.translate_typed d h) (Sub.translate_typed e h)
/-- The one-definition step (D9): for an annotation declaration `D₀` with `D₀⟨r⟩ = D` and
`D₀.tight = true`, the image of one definition extends typed definitions at `Tel` to
`Tel ++ tel D₀`, when its label is new. -/
theorem DefTy.translate_typed : ∀ {G : Ctx s} {r : Path s} {d : Def s} {D : Dec s} (dd : DefTy G r d D) {Δ : FCn.Ctx s},
    Ctx.Rel G Δ → ∀ (D₀ : Dec (s,x)), D₀.substPath r = D → D₀.tight = true →
    ∀ {ds : FCn.Defs s} {Tel : FCn.Telescope (s,x)}, FCn.Defs.HasType Δ r ds Tel → d.label ∉ ds.labels →
      FCn.Defs.HasType Δ r (dd.translate ds) (Tel ++ D₀.telAt .here)
  | _, r, _, _, .ty_def_typ (A := A) (T := T), Δ, h, D₀, hD, ht, ds, Tel, hds, hl => by
      obtain ⟨S₀, U₀, rfl, h₁, h₂⟩ := Dec.substPath_eq_typ hD
      have e : S₀ = U₀ := of_decide_eq_true ht
      subst e
      exact .typ hds hl (by rw [← h₁, Ty.translate_substPath])
  | _, r, _, _, .ty_def_all (b := b) dl, Δ, h, D₀, hD, _, ds, Tel, hds, hl => by
      obtain ⟨T₀, rfl, h₁⟩ := Dec.substPath_eq_trm hD
      obtain ⟨U₀, V₀, rfl⟩ := Ty.substPath_eq_all h₁
      have hl' := HasTy.translate_typed dl h
      obtain ⟨v, hv, hlam⟩ := HasTy.translate_lam_of_eq dl _ _ rfl
      show FCn.Defs.HasType Δ r (.fld ds b (.fn ((Translation.toValue dl.translate).getD _))) _
      rw [hv]
      refine .fn hds hl hlam ?_
      have := Translation.toValue_typed hv hl'
      rw [← h₁, Ty.translate_substPath] at this
      exact this
  | _, r, _, _, .ty_def_new (b := b) (T := T) ht' dds, Δ, h, D₀, hD, _, ds, Tel, hds, hl => by
      obtain ⟨T₀, rfl, h₁⟩ := Dec.substPath_eq_trm hD
      obtain ⟨T₁, rfl, h₂⟩ := Ty.substPath_eq_mu h₁
      have hn := DefsTy.translate_typed dds h T rfl ht'
      have e : T.tel = T₁.tel.subst (PathSubst.one r).lift := by rw [← h₂, Ty.tel_subst_lift]
      show FCn.Defs.HasType Δ r (.fld ds b (.nest T.tel dds.translate)) _
      rw [e] at hn ⊢
      exact .nest hds hl hn
  | _, r, _, _, .ty_def_path (b := b) (q := q) dq, Δ, h, D₀, hD, _, ds, Tel, hds, hl => by
      obtain ⟨T₀, rfl, h₁⟩ := Dec.substPath_eq_trm hD
      obtain ⟨q₀, rfl, h₂⟩ := Ty.substPath_eq_sngl h₁
      have hq := HasTy.translatePath_typed dq h
      exact .path hds hl hq.1 (by rw [hq.2, h₂])
/-- TR.8's `DefsTy.translate_typed`: in related contexts the image of a definition list typed against
`T = T₀⟨r⟩` is typed against `tel T₀`, when `T₀` is tight. -/
theorem DefsTy.translate_typed : ∀ {G : Ctx s} {r : Path s} {ds : Defs s} {T : Ty s} (d : DefsTy G r ds T) {Δ : FCn.Ctx s},
    Ctx.Rel G Δ → ∀ (T₀ : Ty (s,x)), T₀.substPath r = T → T₀.tight = true →
      FCn.Defs.HasType Δ r d.translate T₀.tel
  | _, r, _, _, .ty_defs_one dd, Δ, h, T₀, hT, ht => by
      obtain ⟨D₀, rfl, hD⟩ := Ty.substPath_eq_rcd hT
      have := DefTy.translate_typed dd h D₀ hD ht FCn.Defs.HasType.nil List.not_mem_nil
      rw [Translation.nil_append] at this
      exact this
  | _, r, _, _, .ty_defs_cons (d := d) dds dd hnot, Δ, h, T₀, hT, ht => by
      obtain ⟨T₀', U₀, rfl, h₁, h₂⟩ := Ty.substPath_eq_and hT
      obtain ⟨D₀, rfl, hD⟩ := Ty.substPath_eq_rcd h₂
      have ht' : T₀'.tight = true ∧ D₀.tight = true := by simpa [Ty.tight] using ht
      have hds := DefsTy.translate_typed dds h T₀' h₁ ht'.1
      have hl : d.label ∉ dds.translate.labels := by
        rw [DefsTy.translate_labels]; exact Defs.not_mem_labels_of_hasnt hnot
      show FCn.Defs.HasType Δ r (dd.translate dds.translate) (T₀'.tel ++ D₀.telAt .here)
      exact DefTy.translate_typed dd h D₀ hD ht'.2 hds hl
end
-- end of the block

/-- E3: the image of the compiler program is typed at `⟦μ(z. rT)⟧` in the empty context. -/
theorem E3_image_typed : FCn.Tm.HasType .nil CP_d.translate compiler_T.translate :=
  HasTy.translate_typed CP_d .nil

/-- E8: the image of the program with a replacement at an abstract member in both directions is
typed at `⟦⊤⟧`. -/
theorem E8_image_typed : FCn.Tm.HasType .nil E8_d.translate FCn.Ty.top :=
  HasTy.translate_typed E8_d .nil

/-- N5 (F3): the image of the third premise of `ty_def_new` at X0's N5 witnesses is not typed against
`tel` of the annotation `{B : ⊤..⊤} ∧ {A : (z.b).B .. w.B}`, which is not tight, in any context.
`DF-Typ` writes one bound twice, and the annotation's two bounds of `A` differ. -/
theorem N5_image_untyped (Δ : FCn.Ctx ([],x)) :
    ¬ FCn.Defs.HasType Δ tightEx_r N5_third_premise.translate tightEx_T.tel := by
  intro h
  obtain ⟨Tel, W, e, _, _, _⟩ := Translation.defs_typ_inv_of_eq h _ _ _ rfl
  have e' : tightEx_T.tel = .cons (.cons Tel (.le W (.sel (.var .here) tightEx_A))) (.le (.sel (.var .here) tightEx_A) W) := e
  simp only [Ty.tel, Ty.telAt, Dec.telAt, FCn.Telescope.append_cons, FCn.Telescope.cons.injEq, FCn.Pr.le.injEq] at e'
  obtain ⟨⟨_, e₁, _⟩, _, e₂⟩ := e'
  rw [← e₁] at e₂
  exact absurd e₂ (by decide)

/-- N5: the same image is typed against `tel` of a tight annotation that opens to the same type, the
opened annotation weakened past its self. -/
theorem N5_image_typed_opened :
    FCn.Defs.HasType (FCn.Ctx.nil.cons (.opaque Ty.top.translate)) tightEx_r N5_third_premise.translate
      (tightEx_T.substPath tightEx_r).weaken.tel :=
  DefsTy.translate_typed N5_third_premise (.var .nil) _ (Ty.weaken_substPath _ _) (by decide)

/-- E13: the image of the cyclic object `ν(z : {a : (z.a).type}) {a = z.a}` is typed, through `DF-Path`
at a field whose body is its own path. -/
theorem E13_image_typed : FCn.Tm.HasType .nil E13_cyclic_d.translate (Ty.mu e13_T).translate :=
  HasTy.translate_typed E13_cyclic_d .nil

end Nominal.Source
