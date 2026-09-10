import Coercions.CapturesCC.DotToFCdot.Terms
import Coercions.CapturesCC.DotToFCdot.EvidenceTyped
import Coercions.CapturesCC.DotToFCdot.TypesSubst

namespace CapturesCC

/-!
# Typedness of the term translation (Plan III §8.2, M4; stage A3a)

Every typing derivation of DOT-MNF^cc translates to an FCdot term of the
translated type, its use-set evidence is typed at the translated use set, and
the definitions of an object literal translate to fields of the literal's own
block names.  The three theorems are mutual, as `HasTy` and `DefsTy` are.

Four cases carry the content:

* `{}-I` builds an FCdot literal from the *declaration shape*: its type
  witnesses are the exact bounds of the type members and the declared shapes
  of the fields (`Shape.witnesses`), its capture witnesses are the declared
  capture sets of the fields and the definitions of the capture members
  (`Shape.capWitnesses`), its labels are the field labels
  (`Shape.fieldLabels`), and its fields are the translated definitions.  The
  literal has its precise type `Shape.literalTy` at the assigned set `⟦U⟧`,
  from which `litCo` coerces to `⟦(μ(x. S)) ^ U⟧`.
* Each field body is typed at its declared type but must be typed at the
  block name `self ∙ a` captured at the capture name `{self ∙ a}`.  The
  definition equality `self ∙ a ≐ W.get a` and the capture definition
  `{self ∙ a} ≐ᶜ Wᶜ.get a` of the transparent self binder turn one into the
  other, and distinctness identifies the two witnesses with the field's own
  declared shape and declared capture set (`Shape.DefSpec`,
  `Shape.CapDefSpec`).
* `{}-E` gives `(x ∙ a) ^ {x∙a}`, not `⟦T⟧`.  The translation casts by the
  bound `self ∙ a ⊑ ⟦S⟧↑` at index 1 and the capture entry
  `{self∙a} ⊑ᶜ ⟦C⟧↑` at index 2 of `(Shape.fld a (S ^ C)).tel`, both
  instantiated at `x`.
* Every binder of the target that declares a capture set takes its evidence
  from the source's own use-set evidence.  A lambda, a literal's field, a let
  and an unboxing each declare the translated source use set, and
  `HasTy.translate_uses` is what discharges them.
-/

namespace FCdot

open scoped FCdot

/-! ## Concatenation of fields -/

theorem Fields.labels_append {s : Sig} :
    ∀ (F F' : Fields s), (F.append F').labels = F.labels ++ F'.labels
  | .nil, F' => by rw [Fields.append]; simp [Fields.labels]
  | .cons F ℓ t g, F' => by
      rw [Fields.append]
      simp [Fields.labels, Fields.labels_append F F']

theorem Fields.HasType.append {s : Sig} {Γ : Ctx (s,x)} {A : CaptureSet s} :
    ∀ {F₁ F₂ : Fields (s,x)}, (Γ ⊢ᶠ[A] F₁) → (Γ ⊢ᶠ[A] F₂) → Γ ⊢ᶠ[A] F₁.append F₂
  | .nil, _, _, h₂ => by rw [Fields.append]; exact h₂
  | .cons F ℓ t g, F₂, h₁, h₂ => by
      rw [Fields.append]
      cases h₁ with
      | cons hF ht hg => exact .cons (Fields.HasType.append hF h₂) ht hg

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label Morphism ShapeCo CapCo LeCo EqCo Has Atom Side)
open scoped FCdot

/-! ## The labels of the translated fields -/

theorem DefsTy.translateFields_labels : ∀ {s : Sig} {U : CaptureSet (s,x)} {Γ : Ctx (s,x)}
    {d : Defs (s,x)} {S : Shape (s,x)} (h : DefsTy U Γ d S),
    h.translateFields.labels = S.fieldLabels
  | _, _, _, _, _, .typ => by
      simp only [DefsTy.translateFields]
      simp [FCdot.Fields.labels, Shape.fieldLabels]
  | _, _, _, _, _, .cap => by
      simp only [DefsTy.translateFields]
      simp [FCdot.Fields.labels, Shape.fieldLabels]
  | _, _, _, _, _, .trm _ => by
      simp only [DefsTy.translateFields]
      simp [FCdot.Fields.labels, Shape.fieldLabels]
  | _, _, _, _, _, .and h₁ h₂ => by
      simp only [DefsTy.translateFields]
      rw [FCdot.Fields.labels_append, h₂.translateFields_labels, h₁.translateFields_labels,
        Shape.fieldLabels]

/-! ## What a field body needs from the literal's witnesses

A field's body is typed at its declared type and is cast to the block name
`self ∙ a` and the capture name `{self ∙ a}` by the definition equality and
the capture definition of the transparent self binder.  Those read
`self ∙ a ≐ W.get a` and `{self ∙ a} ≐ᶜ Wᶜ.get a` for the witnesses `W` and
`Wᶜ` of the *whole* literal.  So the field's declared shape must be what
`W.get` returns at its label and its declared capture set what `Wᶜ.get`
returns there.  Distinctness gives both. -/

/-- `Wall.get` returns the translated declared shape at every field of `S`. -/
def Shape.DefSpec {s : Sig} (Wall : FCdot.Witnesses (s,x)) : Shape (s,x) → Prop
  | .fld a (.capt _ S) => Wall.get a = S.translate
  | .and S T => Shape.DefSpec Wall S ∧ Shape.DefSpec Wall T
  | _ => True

theorem defSpec_of {s : Sig} {Wall : FCdot.Witnesses (s,x)} (hdist : Wall.Distinct) :
    ∀ (S : Shape (s,x)) (e : Nat),
      (∀ i l X, FCdot.Witnesses.At S.witnesses i l X → FCdot.Witnesses.At Wall (e + i) l X) →
      Shape.DefSpec Wall S
  | .top, _, _ => by simp [Shape.DefSpec]
  | .bot, _, _ => by simp [Shape.DefSpec]
  | .sel _ _, _, _ => by simp [Shape.DefSpec]
  | .all _ _, _, _ => by simp [Shape.DefSpec]
  | .box _, _, _ => by simp [Shape.DefSpec]
  | .mu _, _, _ => by simp [Shape.DefSpec]
  | .typ _ _ _, _, _ => by simp [Shape.DefSpec]
  | .cap _ _ _, _, _ => by simp [Shape.DefSpec]
  | .fld a (.capt C S'), e, hpos => by
      simp only [Shape.witnesses] at hpos
      have h1 := hpos 0 a S'.translate FCdot.Witnesses.At.hereNil
      rw [Nat.add_zero] at h1
      rw [Shape.DefSpec]
      exact h1.get hdist
  | .and S T', e, hpos => by
      simp only [Shape.witnesses] at hpos
      rw [Shape.DefSpec]
      refine ⟨defSpec_of hdist S e (fun i l X hAt => hpos i l X (hAt.append_left _)), ?_⟩
      refine defSpec_of hdist T' (e + S.witnesses.length) (fun i l X hAt => ?_)
      have hh := hpos (S.witnesses.length + i) l X
        (FCdot.Witnesses.At.append_right S.witnesses hAt)
      rw [show e + (S.witnesses.length + i) = e + S.witnesses.length + i by omega] at hh
      exact hh

/-- A declaration shape with distinct labels satisfies its own type
specification. -/
theorem Shape.defSpec_self {s : Sig} (S : Shape (s,x)) (hdl : Shape.DistinctLabels S) :
    Shape.DefSpec S.witnesses S :=
  defSpec_of (Shape.witnesses_distinct S hdl) S 0 (fun i l X hAt => by
    rw [Nat.zero_add]; exact hAt)

/-- `Wall.get` returns the translated declared capture set at every field of
`S`.  The capture twin of `Shape.DefSpec`.  A capture member declares its own
name, which no field body reads, so it falls in the catch-all. -/
def Shape.CapDefSpec {s : Sig} (Wall : FCdot.CapWitnesses (s,x)) : Shape (s,x) → Prop
  | .fld a (.capt C _) => Wall.get a = C.translate
  | .and S T => Shape.CapDefSpec Wall S ∧ Shape.CapDefSpec Wall T
  | _ => True

theorem capDefSpec_of {s : Sig} {Wall : FCdot.CapWitnesses (s,x)} (hdist : Wall.Distinct) :
    ∀ (S : Shape (s,x)) (e : Nat),
      (∀ i l C, FCdot.CapWitnesses.At S.capWitnesses i l C →
        FCdot.CapWitnesses.At Wall (e + i) l C) →
      Shape.CapDefSpec Wall S
  | .top, _, _ => by simp [Shape.CapDefSpec]
  | .bot, _, _ => by simp [Shape.CapDefSpec]
  | .sel _ _, _, _ => by simp [Shape.CapDefSpec]
  | .all _ _, _, _ => by simp [Shape.CapDefSpec]
  | .box _, _, _ => by simp [Shape.CapDefSpec]
  | .mu _, _, _ => by simp [Shape.CapDefSpec]
  | .typ _ _ _, _, _ => by simp [Shape.CapDefSpec]
  | .cap _ _ _, _, _ => by simp [Shape.CapDefSpec]
  | .fld a (.capt C _), e, hpos => by
      simp only [Shape.capWitnesses] at hpos
      have h1 := hpos 0 a C.translate FCdot.CapWitnesses.At.hereNil
      rw [Nat.add_zero] at h1
      rw [Shape.CapDefSpec]
      exact h1.get hdist
  | .and S T', e, hpos => by
      simp only [Shape.capWitnesses] at hpos
      rw [Shape.CapDefSpec]
      refine ⟨capDefSpec_of hdist S e (fun i l C hAt => hpos i l C (hAt.append_left _)), ?_⟩
      refine capDefSpec_of hdist T' (e + S.capWitnesses.length) (fun i l C hAt => ?_)
      have hh := hpos (S.capWitnesses.length + i) l C
        (FCdot.CapWitnesses.At.append_right S.capWitnesses hAt)
      rw [show e + (S.capWitnesses.length + i) = e + S.capWitnesses.length + i by omega] at hh
      exact hh

/-- A declaration shape with distinct labels satisfies its own capture
specification. -/
theorem Shape.capDefSpec_self {s : Sig} (S : Shape (s,x)) (hdl : Shape.DistinctLabels S) :
    Shape.CapDefSpec S.capWitnesses S :=
  capDefSpec_of (Shape.capWitnesses_distinct S hdl) S 0 (fun i l C hAt => by
    rw [Nat.zero_add]; exact hAt)

/-! ## The use set of a translated variable term

Every rule that concludes at a variable produces an atom, possibly under
casts, so the use set of the translated term is the singleton of the
variable.  This is what makes `HasTy.translate_uses` at an atom derivation
the plan's `{x} ⊑ ⟦U⟧`. -/

theorem HasTy.translate_uses_atom : ∀ {s : Sig} {U : CaptureSet s} {Γ : Ctx s}
    {y : BVar s .var} {T : Ty s} (h : HasTy U Γ (.path (.var y)) T),
    h.translate.uses = [FCdot.CapAtom.var y]
  | _, _, Γ, y, _, .var => by
      rw [HasTy.translate]; simp [FCdot.Atom.root, Ctx.varAtom_root Γ y]
  | _, _, _, _, _, .recI h hd => by
      rw [HasTy.translate]
      simp [HasTy.translateAtom_root (HasTy.recI h hd)]
  | _, _, _, _, _, .recE h hd => by
      rw [HasTy.translate]
      simp [HasTy.translateAtom_root (HasTy.recE h hd)]
  | _, _, _, _, _, .andI h₁ h₂ => by
      rw [HasTy.translate]
      simp [HasTy.translateAtom_root (HasTy.andI h₁ h₂)]
  | _, _, _, _, _, .sub h _ _ => by
      rw [HasTy.translate]
      simpa using HasTy.translate_uses_atom h

/-! ## Typedness of the term, use-set and field translations -/

mutual

theorem HasTy.translate_typed : ∀ {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : HasTy U Γ t T), Γ.Wf →
    FCdot.Tm.HasType Γ.translate h.translate T.translate
  | _, _, Γ, _, _, @HasTy.var _ _ x, hwf => by
      have ha := HasTy.translateAtom_typed (@HasTy.var _ Γ x) hwf
      rw [HasTy.translateAtom] at ha
      simp only [HasTy.translate]
      exact .atom ha
  | _, _, _, _, _, @HasTy.lam _ _ U T1 _ _ h _, hwf => by
      simp only [HasTy.translate, Ty.translate_capt, Shape.translate_all_eq]
      have hb := HasTy.translate_typed h (hwf.body T1)
      rw [Ctx.translate_body, Ty.translate_underRootCod] at hb
      refine .val (.lam hb ?_)
      have hu := HasTy.translate_uses h (hwf.body T1)
      rw [Ctx.translate_body] at hu
      simpa using hu
  | _, _, Γ, _, _, @HasTy.app _ _ _ _ y T1 T2 _ h₁ h₂, hwf => by
      have ha := HasTy.translateAtom_typed h₁ hwf
      have hb := HasTy.translateAtom_typed h₂ hwf
      rw [Ty.translate_capt, Shape.translate_all_eq] at ha
      rw [Ty.translate_singleC] at hb
      have hb' : Γ.translate ⊢ₐ h₂.translateAtom
          : (T1.translate).subst (FCdot.Subst.singleC (.var h₂.translateAtom.root)) := by
        rw [HasTy.translateAtom_root h₂]
        exact hb
      have happ := FCdot.Tm.HasType.app ha hb'
      simp only [HasTy.translate]
      rw [Ty.translate_arg T2 h₂.translateAtom y (HasTy.translateAtom_root h₂)]
      exact happ
  | _, _, Γ, _, _, @HasTy.obj _ _ U d S hd hdist, hwf => by
      have hdlR : Shape.DistinctLabels S.underRoot := hd.distinctLabels hdist
      have hshR : Shape.LiteralShape S.underRoot := hd.literalShape
      have hdl : Shape.DistinctLabels S := Shape.distinctLabels_of_underRoot hdlR
      have hsh : Shape.LiteralShape S := Shape.literalShape_of_underRoot hshR
      have hlab : hd.translateFields.labels = S.fieldLabels := by
        rw [hd.translateFields_labels]
        exact Shape.fieldLabels_rename S FCdot.Rename.succ.lift
      have hf : FCdot.Fields.HasType (Γ.objBody d S U).translate (U.weaken).translate
          hd.translateFields :=
        hd.translateFields_typed (.consSelf (.consRoot hwf) hshR hdlR)
          (Shape.defSpec_self S.underRoot hdlR) (Shape.capDefSpec_self S.underRoot hdlR)
      rw [Ctx.translate_objBody, CaptureSet.translate_weaken] at hf
      have hval : FCdot.Value.HasType Γ.translate
          (.obj U.translate S.witnesses S.capWitnesses hd.translateFields)
          ((μ (FCdot.Telescope.ofLiteral S.witnesses S.capWitnesses
            hd.translateFields.labels)) ^ U.translate) :=
        .obj (by rw [hlab]; exact hf)
      rw [hlab] at hval
      simp only [HasTy.translate]
      refine .cast (.val hval) ?_
      simp only [FCdot.ShapeCo.atC, Ty.translate_capt]
      exact .capt (litCo_typed_of_shape hsh hdl) .refl
  | _, _, _, _, _, @HasTy.box _ _ _ _ _ h, hwf => by
      have ha := HasTy.translateAtom_typed h hwf
      simp only [HasTy.translate, Ty.translate_capt, Shape.translate_box_eq]
      exact .val (.box ha)
  | _, _, _, _, _, @HasTy.proj _ _ _ _ a (.capt CT ST) _ h, hwf => by
      have ha := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_capt, Shape.translate_fld, Shape.tel_fld] at ha
      have hhas := FCdot.Has.HasType.member ha .refl (FCdot.Telescope.At.zero_three _ _ _)
      have hle := FCdot.ShapeCo.HasType.member ha .refl (FCdot.Telescope.At.one_three _ _ _)
      have hcap := FCdot.CapCo.HasType.member ha .refl (FCdot.Telescope.At.two_three _ _ _)
      rw [FCdot.Shape.substVar_sel_here, FCdot.Shape.weaken_substVar] at hle
      rw [FCdot.CaptureSet.substVar_name_here, FCdot.CaptureSet.weaken_substVar'] at hcap
      simp only [HasTy.translate, Shape.translate_fld, Shape.tel_fld, Ty.translate_capt]
      exact .cast (.proj ha hhas) (.capt hle hcap)
  | _, _, _, _, _, @HasTy.let _ _ U _ _ _ _ h₁ h₂ _, hwf => by
      have ih₂ := HasTy.translate_typed h₂ (.cons hwf)
      rw [Ty.translate_weaken] at ih₂
      have hu := HasTy.translate_uses h₂ (.cons hwf)
      rw [CaptureSet.translate_weaken] at hu
      simp only [HasTy.translate]
      exact .let (HasTy.translate_typed h₁ hwf) ih₂ hu
  | _, _, _, _, _, @HasTy.unbox _ _ _ _ _ _ _ h f, hwf => by
      have ha := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_capt, Shape.translate_box_eq, Ty.translate_capt] at ha
      simp only [HasTy.translate, Ty.translate_capt]
      exact .unbox ha (f.translate_typed hwf)
  | _, _, _, _, _, .recI h hd, hwf => by
      simp only [HasTy.translate]
      exact .atom (HasTy.translateAtom_typed (.recI h hd) hwf)
  | _, _, _, _, _, .recE h hd, hwf => by
      simp only [HasTy.translate]
      exact .atom (HasTy.translateAtom_typed (.recE h hd) hwf)
  | _, _, _, _, _, .andI h₁ h₂, hwf => by
      simp only [HasTy.translate]
      exact .atom (HasTy.translateAtom_typed (.andI h₁ h₂) hwf)
  | _, _, _, _, _, .sub h d _, hwf => by
      simp only [HasTy.translate]
      exact .cast (HasTy.translate_typed h hwf) (d.translate_typed hwf)

theorem HasTy.translate_uses : ∀ {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : HasTy U Γ t T), Γ.Wf →
    FCdot.CapCo.HasType Γ.translate h.translateUses h.translate.uses U.translate
  | _, _, Γ, _, _, @HasTy.var _ _ x, _ => by
      rw [HasTy.translateUses, HasTy.translate_uses_atom (@HasTy.var _ Γ x)]
      exact .refl
  | _, _, _, _, _, .lam _ _, _ => by
      rw [HasTy.translateUses, HasTy.translate]
      exact .refl
  | _, _, _, _, _, .app h₁ h₂, hwf => by
      have hu₁ := HasTy.translate_uses h₁ hwf
      have hu₂ := HasTy.translate_uses h₂ hwf
      rw [HasTy.translate_uses_atom h₁] at hu₁
      rw [HasTy.translate_uses_atom h₂] at hu₂
      rw [HasTy.translateUses, HasTy.translate]
      simpa [FCdot.Tm.uses, HasTy.translateAtom_root h₁, HasTy.translateAtom_root h₂]
        using FCdot.CapCo.HasType.union hu₁ hu₂
  | _, _, _, _, _, .obj _ _, _ => by
      rw [HasTy.translateUses, HasTy.translate]
      exact .refl
  | _, _, _, _, _, .box _, _ => by
      rw [HasTy.translateUses, HasTy.translate]
      exact .refl
  | _, _, _, _, _, .proj h, hwf => by
      have hu := HasTy.translate_uses h hwf
      rw [HasTy.translate_uses_atom h] at hu
      rw [HasTy.translateUses, HasTy.translate]
      simpa [FCdot.Tm.uses, HasTy.translateAtom_root h] using hu
  | _, _, _, _, _, @HasTy.let _ _ U _ _ _ _ h₁ _ _, hwf => by
      rw [HasTy.translateUses, HasTy.translate]
      exact .union (HasTy.translate_uses h₁ hwf) .refl
  | _, _, _, _, _, @HasTy.unbox _ _ U _ _ _ _ h _, hwf => by
      have hu := HasTy.translate_uses h hwf
      rw [HasTy.translate_uses_atom h] at hu
      rw [HasTy.translateUses, HasTy.translate]
      have hun := FCdot.CapCo.HasType.union hu (FCdot.CapCo.HasType.refl (C := U.translate))
      simpa [FCdot.Tm.uses, HasTy.translateAtom_root h] using hun
  | _, _, _, _, _, .recI h hd, hwf => by
      have hu := HasTy.translate_uses h hwf
      rw [HasTy.translate_uses_atom h] at hu
      rw [HasTy.translateUses, HasTy.translate]
      simpa [FCdot.Tm.uses, HasTy.translateAtom_root (HasTy.recI h hd)] using hu
  | _, _, _, _, _, .recE h hd, hwf => by
      have hu := HasTy.translate_uses h hwf
      rw [HasTy.translate_uses_atom h] at hu
      rw [HasTy.translateUses, HasTy.translate]
      simpa [FCdot.Tm.uses, HasTy.translateAtom_root (HasTy.recE h hd)] using hu
  | _, _, _, _, _, .andI h₁ h₂, hwf => by
      have hu := HasTy.translate_uses h₁ hwf
      rw [HasTy.translate_uses_atom h₁] at hu
      rw [HasTy.translateUses, HasTy.translate]
      simpa [FCdot.Tm.uses, HasTy.translateAtom_root (HasTy.andI h₁ h₂)] using hu
  | _, _, _, _, _, .sub h _ f, hwf => by
      rw [HasTy.translateUses, HasTy.translate]
      exact .trans (HasTy.translate_uses h hwf) (f.translate_typed hwf)

theorem DefsTy.translateFields_typed : ∀ {s : Sig} {Γ : Ctx s} {U : CaptureSet s}
    {d : Defs (s,x)} {Sall : Shape (s,x)} {d' : Defs (s,x)} {S' : Shape (s,x)}
    (h : DefsTy (CaptureSet.weaken U ∪ [.var .here]) (Γ.consSelf d Sall U) d' S'),
    (Γ.consSelf d Sall U).Wf → Shape.DefSpec Sall.witnesses S' →
    Shape.CapDefSpec Sall.capWitnesses S' →
    FCdot.Fields.HasType (Γ.consSelf d Sall U).translate U.translate h.translateFields
  | _, _, _, _, _, _, _, .typ, _, _, _ => by
      simp only [DefsTy.translateFields]
      exact .nil
  | _, _, _, _, _, _, _, .cap, _, _, _ => by
      simp only [DefsTy.translateFields]
      exact .nil
  | _, Γ, U, d, Sall, _, _, @DefsTy.trm _ _ _ a _ (.capt CT ST) h, hwf, hspec, hcspec => by
      rw [Shape.DefSpec] at hspec
      rw [Shape.CapDefSpec] at hcspec
      have hdef : (Γ.consSelf d Sall U).translate.lookupDef .here a
          = some (Sall.witnesses.get a) := rfl
      have hdefC : (Γ.consSelf d Sall U).translate.lookupDefC .here a
          = some (Sall.capWitnesses.get a) := rfl
      have hle : FCdot.ShapeCo.HasType (Γ.consSelf d Sall U).translate
          (.eqToLe (.symm (.def .here a))) ST.translate (.here ∙ a) := by
        rw [← hspec]
        exact .eqToLe (.symm (.def hdef))
      have hlec : FCdot.CapCo.HasType (Γ.consSelf d Sall U).translate
          (.eqToLe (.symm (.defC .here a))) CT.translate [FCdot.CapAtom.name .here a] := by
        rw [← hcspec]
        exact .eqToLe (.symm (.defC hdefC))
      have hbody : FCdot.Tm.HasType (Γ.consSelf d Sall U).translate (fieldBody a h.translate)
          ((FCdot.Shape.sel .here a) ^ [FCdot.CapAtom.name .here a]) :=
        .cast (HasTy.translate_typed h hwf) (.capt hle hlec)
      have hg := HasTy.translate_uses h hwf
      simp only [DefsTy.translateFields]
      refine .cons .nil hbody ?_
      simpa [fieldBody] using hg
  | _, _, _, _, _, _, _, .and h₁ h₂, hwf, hspec, hcspec => by
      rw [Shape.DefSpec] at hspec
      rw [Shape.CapDefSpec] at hcspec
      simp only [DefsTy.translateFields]
      exact (h₂.translateFields_typed hwf hspec.2 hcspec.2).append
        (h₁.translateFields_typed hwf hspec.1 hcspec.1)

end

end DotMNF

end CapturesCC
