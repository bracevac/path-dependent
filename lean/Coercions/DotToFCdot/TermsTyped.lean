import Coercions.DotToFCdot.Terms
import Coercions.DotToFCdot.EvidenceTyped

/-!
# Typedness of the term translation (Plan III §8.2, M4)

Every typing derivation of DOT-MNF translates to an FCdot term of the translated type,
and the definitions of an object literal translate to fields of the literal's own block
names.  The two theorems are mutual, as `HasTy` and `DefsTy` are.

Three cases carry the content:

* `{}-I` builds an FCdot literal from the *declaration type*: its witnesses are the exact
  bounds of the type members and the declared types of the fields (`Ty.witnesses`), its
  labels are the field labels (`Ty.fieldLabels`), and its fields are the translated
  definitions.  The literal has its precise type `T.literalTy`, from which `litCo` (M3)
  coerces to `⟦μ(x. T)⟧`.  Two side facts make the value rule apply: the translated
  fields' labels are exactly `T.fieldLabels` (`DefsTy.translateFields_labels`), and the
  witnesses are guarded (`Ty.witnesses_guarded`, from the source-side `Ty.Guarded`).
* Each field body is typed at its declared type but must be typed at the block name
  `self ∙ a`; the definition equality `self ∙ a ≐ W.get a` of the transparent self binder
  turns one into the other, and distinctness identifies `W.get a` with the field's own
  translated type (`Ty.DefSpec`, `defSpec_of`).
* `{}-E` gives `x ∙ a`, not `⟦T⟧`; the translation casts by the bound `self ∙ a ⊑ ⟦T⟧↑`,
  the proposition at index 1 of `(Ty.fld a T).tel`, instantiated at `x`.
-/

namespace FCdot

open scoped FCdot

/-! ## Concatenation of fields -/

theorem Fields.labels_append {s : Sig} :
    ∀ (F F' : Fields s), (F.append F').labels = F.labels ++ F'.labels
  | .nil, F' => by rw [Fields.append]; simp [Fields.labels]
  | .cons F ℓ t, F' => by
      rw [Fields.append]
      simp [Fields.labels, Fields.labels_append F F']

theorem Fields.HasType.append {s : Sig} {Γ : Ctx (s,x)} :
    ∀ {F₁ F₂ : Fields (s,x)}, (Γ ⊢ᶠ F₁) → (Γ ⊢ᶠ F₂) → Γ ⊢ᶠ F₁.append F₂
  | .nil, _, _, h₂ => by rw [Fields.append]; exact h₂
  | .cons F ℓ t, F₂, h₁, h₂ => by
      rw [Fields.append]
      cases h₁ with
      | cons hF ht => exact .cons (Fields.HasType.append hF h₂) ht

/-! ## Guardedness of concatenated witnesses -/

theorem Witnesses.all_append {s : Sig} (p : Ty s → Bool) :
    ∀ (W W' : Witnesses s), (W.append W').all p = (W.all p && W'.all p)
  | _, .nil => by simp [Witnesses.append, Witnesses.all]
  | W, .cons W' ℓ T => by
      simp only [Witnesses.append, Witnesses.all, Witnesses.all_append p W W']
      cases p T <;> cases W.all p <;> cases W'.all p <;> rfl

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label Morphism LeCo EqCo Has Atom Side)
open scoped FCdot

/-! ## The witnesses of a guarded declaration type are guarded -/

/-- The translation of a type that is not a bare selection on the self is not a bare name
of the self block. -/
theorem Ty.translate_not_selfName {s : Sig} :
    ∀ {T : Ty (s,x)}, T.isSelfSel = false → T.translate.isSelfName = false
  | .top, _ => by rw [Ty.translate_top]; rfl
  | .bot, _ => by rw [Ty.translate_bot]; rfl
  | .sel (.var .here) _, h => by simp [Ty.isSelfSel] at h
  | .sel (.var (.there y)) A, _ => by rw [Ty.translate_sel]; rfl
  | .all _ _, _ => by rw [Ty.translate_all]; rfl
  | .typ A S T, _ => by rw [Ty.translate_typ]; rfl
  | .fld a T, _ => by rw [Ty.translate_fld]; rfl
  | .and S T, _ => by rw [Ty.translate_and]; rfl
  | .mu T, _ => by rw [Ty.translate_mu]; rfl

theorem Ty.witnesses_guarded {s : Sig} :
    ∀ (T : Ty (s,x)), Ty.Guarded T → T.witnesses.Guarded
  | .top, _ => by simp [Ty.witnesses, FCdot.Witnesses.Guarded, FCdot.Witnesses.all]
  | .bot, _ => by simp [Ty.witnesses, FCdot.Witnesses.Guarded, FCdot.Witnesses.all]
  | .sel _ _, _ => by simp [Ty.witnesses, FCdot.Witnesses.Guarded, FCdot.Witnesses.all]
  | .all _ _, _ => by simp [Ty.witnesses, FCdot.Witnesses.Guarded, FCdot.Witnesses.all]
  | .mu _, _ => by simp [Ty.witnesses, FCdot.Witnesses.Guarded, FCdot.Witnesses.all]
  | .typ A S T, h => by
      rw [Ty.Guarded] at h
      simp [Ty.witnesses, FCdot.Witnesses.Guarded, FCdot.Witnesses.all,
        Ty.translate_not_selfName h]
  | .fld a T, h => by
      rw [Ty.Guarded] at h
      simp [Ty.witnesses, FCdot.Witnesses.Guarded, FCdot.Witnesses.all,
        Ty.translate_not_selfName h]
  | .and S T, h => by
      rw [Ty.Guarded] at h
      have hS := Ty.witnesses_guarded S h.1
      have hT := Ty.witnesses_guarded T h.2
      rw [FCdot.Witnesses.Guarded] at hS hT ⊢
      rw [Ty.witnesses, FCdot.Witnesses.all_append, hS, hT]
      rfl

/-! ## The labels of the translated fields -/

theorem DefsTy.translateFields_labels : ∀ {s : Sig} {Γ : Ctx (s,x)} {d : Defs (s,x)}
    {T : Ty (s,x)} (h : DefsTy Γ d T), h.translateFields.labels = T.fieldLabels
  | _, _, _, _, .typ => by
      simp only [DefsTy.translateFields]
      simp [FCdot.Fields.labels, Ty.fieldLabels]
  | _, _, _, _, .trm _ => by
      simp only [DefsTy.translateFields]
      simp [FCdot.Fields.labels, Ty.fieldLabels]
  | _, _, _, _, .and h₁ h₂ => by
      simp only [DefsTy.translateFields]
      rw [FCdot.Fields.labels_append, h₂.translateFields_labels, h₁.translateFields_labels,
        Ty.fieldLabels]

/-! ## What a field body needs from the literal's witnesses

A field's body is typed at its declared type and is cast to the block name `self ∙ a` by
the definition equality of the transparent self binder, which reads `self ∙ a ≐ W.get a`
for the witnesses `W` of the *whole* literal.  So the field's declared type must be what
`W.get` returns at its label; distinctness gives it. -/

/-- `Wall.get` returns the translated declared type at every field of `T`. -/
def Ty.DefSpec {s : Sig} (Wall : FCdot.Witnesses (s,x)) : Ty (s,x) → Prop
  | .fld a T => Wall.get a = T.translate
  | .and S T => Ty.DefSpec Wall S ∧ Ty.DefSpec Wall T
  | _ => True

theorem defSpec_of {s : Sig} {Wall : FCdot.Witnesses (s,x)} (hdist : Wall.Distinct) :
    ∀ (T : Ty (s,x)) (e : Nat),
      (∀ i l X, FCdot.Witnesses.At T.witnesses i l X → FCdot.Witnesses.At Wall (e + i) l X) →
      Ty.DefSpec Wall T
  | .top, _, _ => by simp [Ty.DefSpec]
  | .bot, _, _ => by simp [Ty.DefSpec]
  | .sel _ _, _, _ => by simp [Ty.DefSpec]
  | .all _ _, _, _ => by simp [Ty.DefSpec]
  | .mu _, _, _ => by simp [Ty.DefSpec]
  | .typ _ _ _, _, _ => by simp [Ty.DefSpec]
  | .fld a T', e, hpos => by
      simp only [Ty.witnesses] at hpos
      have h1 := hpos 0 a T'.translate FCdot.Witnesses.At.hereNil
      rw [Nat.add_zero] at h1
      rw [Ty.DefSpec]
      exact h1.get hdist
  | .and S T', e, hpos => by
      simp only [Ty.witnesses] at hpos
      rw [Ty.DefSpec]
      refine ⟨defSpec_of hdist S e (fun i l X hAt => hpos i l X (hAt.append_left _)), ?_⟩
      refine defSpec_of hdist T' (e + S.witnesses.length) (fun i l X hAt => ?_)
      have hh := hpos (S.witnesses.length + i) l X
        (FCdot.Witnesses.At.append_right S.witnesses hAt)
      rw [show e + (S.witnesses.length + i) = e + S.witnesses.length + i by omega] at hh
      exact hh

/-- A declaration type with distinct labels satisfies its own specification. -/
theorem Ty.defSpec_self {s : Sig} (T : Ty (s,x)) (hdl : Ty.DistinctLabels T) :
    Ty.DefSpec T.witnesses T :=
  defSpec_of (Ty.witnesses_distinct T hdl) T 0 (fun i l X hAt => by
    rw [Nat.zero_add]; exact hAt)

/-! ## Typedness of the term and field translations -/

mutual

theorem HasTy.translate_typed : ∀ {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : HasTy Γ t T), Γ.Wf →
    FCdot.Tm.HasType Γ.translate h.translate T.translate
  | _, Γ, _, _, @HasTy.var _ _ x, hwf => by
      simp only [HasTy.translate]
      exact .atom (Ctx.varAtom_typed Γ hwf x)
  | _, _, _, _, .lam h _, hwf => by
      simp only [HasTy.translate, Ty.translate_all]
      exact .val (.lam (HasTy.translate_typed h (.cons hwf)))
  | _, _, _, _, .app h₁ h₂, hwf => by
      have ha := HasTy.translateAtom_typed h₁ hwf
      have hb := HasTy.translateAtom_typed h₂ hwf
      rw [Ty.translate_all] at ha
      have happ := FCdot.Tm.HasType.app ha hb
      rw [HasTy.translateAtom_root h₂] at happ
      simp only [HasTy.translate, Ty.translate_substVar]
      exact happ
  | _, Γ, _, _, @HasTy.obj _ d T _ hd hdist _ hg, hwf => by
      have hlab : hd.translateFields.labels = T.fieldLabels := hd.translateFields_labels
      have hdl : Ty.DistinctLabels T := hd.distinctLabels hdist
      have hf : FCdot.Fields.HasType (Γ.consSelf d T).translate hd.translateFields :=
        hd.translateFields_typed (.consSelf hwf hd.literalShape hdl) (Ty.defSpec_self T hdl)
      have hval : FCdot.Value.HasType Γ.translate (.obj T.witnesses hd.translateFields)
          (μ (FCdot.Telescope.ofLiteral T.witnesses hd.translateFields.labels)) :=
        .obj (Ty.witnesses_guarded T hg) (by rw [hlab]; exact hf)
      rw [hlab] at hval
      simp only [HasTy.translate]
      exact .cast (.val hval) (litCo_typed hd hdist)
  | _, _, _, _, @HasTy.proj _ _ _ a T h, hwf => by
      have ha := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_fld, Ty.tel_fld] at ha
      have hhas := FCdot.Has.HasType.member ha .refl (FCdot.Telescope.At.zero_two _ _)
      have hle := FCdot.LeCo.HasType.member ha .refl (FCdot.Telescope.At.one_two _ _)
      rw [FCdot.Ty.substVar_sel_here, FCdot.Ty.weaken_substVar] at hle
      simp only [HasTy.translate, Ty.translate_fld, Ty.tel_fld]
      exact .cast (.proj ha hhas) hle
  | _, _, _, _, .let h₁ h₂ _, hwf => by
      have ih₂ := HasTy.translate_typed h₂ (.cons hwf)
      rw [Ty.translate_weaken] at ih₂
      simp only [HasTy.translate]
      exact .let (HasTy.translate_typed h₁ hwf) ih₂
  | _, _, _, _, .recI h hd, hwf => by
      simp only [HasTy.translate]
      exact .atom (HasTy.translateAtom_typed (.recI h hd) hwf)
  | _, _, _, _, .recE h hd, hwf => by
      simp only [HasTy.translate]
      exact .atom (HasTy.translateAtom_typed (.recE h hd) hwf)
  | _, _, _, _, .andI h₁ h₂ hT hU, hwf => by
      simp only [HasTy.translate]
      exact .atom (HasTy.translateAtom_typed (.andI h₁ h₂ hT hU) hwf)
  | _, _, _, _, .sub h d, hwf => by
      simp only [HasTy.translate]
      exact .cast (HasTy.translate_typed h hwf) (d.translate_typed hwf)

theorem DefsTy.translateFields_typed : ∀ {s : Sig} {Γ : Ctx s} {d : Defs (s,x)} {Tall : Ty (s,x)}
    {d' : Defs (s,x)} {T' : Ty (s,x)} (h : DefsTy (Γ.consSelf d Tall) d' T'),
    (Γ.consSelf d Tall).Wf → Ty.DefSpec Tall.witnesses T' →
    FCdot.Fields.HasType (Γ.consSelf d Tall).translate h.translateFields
  | _, _, _, _, _, _, .typ, _, _ => by
      simp only [DefsTy.translateFields]
      exact .nil
  | _, Γ, d, Tall, _, _, @DefsTy.trm _ _ _ T'' a h, hwf, hspec => by
      rw [Ty.DefSpec] at hspec
      have hdef : (Γ.consSelf d Tall).translate.lookupDef .here a
          = some (Tall.witnesses.get a) := rfl
      have hle : FCdot.LeCo.HasType (Γ.consSelf d Tall).translate
          (.eqToLe (.symm (.def .here a))) T''.translate (.here ∙ a) := by
        rw [← hspec]
        exact .eqToLe (.symm (.def hdef))
      simp only [DefsTy.translateFields]
      exact .cons .nil (.cast (HasTy.translate_typed h hwf) hle)
  | _, _, _, _, _, _, .and h₁ h₂, hwf, hspec => by
      rw [Ty.DefSpec] at hspec
      simp only [DefsTy.translateFields]
      exact (h₂.translateFields_typed hwf hspec.2).append (h₁.translateFields_typed hwf hspec.1)

end

end DotMNF
