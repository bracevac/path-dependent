import Coercions.Paths.DotToFCdot.Blocks
import Coercions.Paths.FCdot.Transparency

namespace Paths

/-!
# Typedness of the term translation (Plan III §8.2, M4, and P2.4)

Every typing derivation of DOT-MNF translates to an FCdot term of the translated type,
and the definitions of an object literal translate to fields of the literal's own block
names.  The two theorems are mutual, as `HasTy` and `DefsTy` are.

Four cases carry the content:

* `{}-I` builds an FCdot literal from the *declaration type*: its witnesses are the exact
  bounds of the type members and the declared types of the fields (`Ty.witnesses`), its
  labels are the field labels (`Ty.fieldLabels`), its stable labels are those of the
  `val` fields (`Ty.valLabels`), and its fields are the translated definitions.  The
  literal has its precise type `T.literalTy`, from which `litCo` (M3) coerces to
  `⟦μ(x. T)⟧`.  The value rule types the fields under the block the target builds from
  the literal, and the translated context's self binder carries `T.blocks d`.  The two
  agree by `DefsTy.blocks_translate` (`Blocks.lean`), at the `Defs.Distinct d` that
  `HasTy.obj` carries.
* A plain field's body is typed at its declared type but must be typed at the block
  name `self ∙ a`.  Decision 26 casts it by `EqCo.member` at the self, reading the
  equation `self ∙ a ≐ W.get a` at the position `e` of the self's precise telescope.
  `Ty.EqSpec` at `e` says that entry is there.
* A stable field's body is the inner literal under `litCo`, cast to `self ∙ a` by the
  definition equality `EqCo.def`, which is table-only, so the field is stable.
  `Ty.EqSpec.defSpec` identifies `W.get a` with the field's declared type.
* `{}-E` gives `x ∙ a`, not `⟦T⟧`.  The translation casts by the bound
  `self ∙ a ⊑ ⟦T⟧↑`, the proposition at index 1 of `(Ty.fld a T).tel`, instantiated at
  `x`.  `projP` reads the same two entries by `memberP` at the path image.
-/

namespace FCdot

open scoped FCdot

/-! ## Concatenation of fields -/

theorem Fields.HasType.append {s : Sig} {Γ : Ctx (s,x)} :
    ∀ {F₁ F₂ : Fields (s,x)}, (Γ ⊢ᶠ F₁) → (Γ ⊢ᶠ F₂) → Γ ⊢ᶠ F₁.append F₂
  | .nil, _, _, h₂ => by rw [Fields.append]; exact h₂
  | .cons F ℓ t, F₂, h₁, h₂ => by
      rw [Fields.append]
      cases h₁ with
      | cons hF ht => exact .cons (Fields.HasType.append hF h₂) ht

/-! ## The equations of a literal's telescope -/

/-- Every equation of a witness list's entries is the definition of one label. -/
theorem Witnesses.eqEntriesOf_eq_inv {s' : Sig} (self : BVar s' .var) (W₀ : Witnesses s') :
    ∀ (W : Witnesses s') {i : Nat} {S T : Ty s'},
      (W₀.eqEntriesOf self W) ∋ (i ↦ S ≐ T) → ∃ ℓ, S = self ∙ ℓ ∧ T = W₀.get ℓ
  | .nil, _, _, _, h => by cases h
  | .cons W ℓ _, _, _, _, h => by
      simp only [Witnesses.eqEntriesOf] at h
      cases h with
      | here => exact ⟨ℓ, rfl, rfl⟩
      | there h' => exact Witnesses.eqEntriesOf_eq_inv self W₀ W h'

/-- Presence entries hold no equation. -/
theorem Telescope.At.hasEntries_eq_inv {s' : Sig} :
    ∀ (ls : List Label) {Tel : Telescope s'} {i : Nat} {S T : Ty s'},
      (Tel.hasEntries ls) ∋ (i ↦ S ≐ T) → Tel ∋ (i ↦ S ≐ T)
  | [], _, _, _, _, h => h
  | _ :: ls, _, _, _, _, h => by
      have h' := Telescope.At.hasEntries_eq_inv ls h
      cases h' with
      | there h'' => exact h''

/-- Stable presence entries hold no equation. -/
theorem Telescope.At.hasValEntries_eq_inv {s' : Sig} :
    ∀ (ls : List Label) {Tel : Telescope s'} {i : Nat} {S T : Ty s'},
      (Tel.hasValEntries ls) ∋ (i ↦ S ≐ T) → Tel ∋ (i ↦ S ≐ T)
  | [], _, _, _, _, h => h
  | _ :: ls, _, _, _, _, h => by
      have h' := Telescope.At.hasValEntries_eq_inv ls h
      cases h' with
      | there h'' => exact h''

/-- An equation of a literal's precise telescope at the self's label `a` reads the
witness at `a`. -/
theorem Telescope.ofLiteral_eq_inv {s : Sig} {W : Witnesses (s,x)} {ls vls : List Label}
    {i : Nat} {a : Label} {X : Ty (s,x)}
    (h : (Telescope.ofLiteral W ls vls) ∋ (i ↦ (Path.var .here) ∙ a ≐ X)) : X = W.get a := by
  unfold Telescope.ofLiteral Witnesses.eqEntries at h
  obtain ⟨ℓ, hS, hT⟩ := Witnesses.eqEntriesOf_eq_inv _ _ W
    (Telescope.At.hasEntries_eq_inv ls (Telescope.At.hasValEntries_eq_inv vls h))
  cases hS
  exact hT

/-- Weakening under the self binder and instantiating it at itself is the identity. -/
theorem Ty.rename_lift_substVar_succ {s : Sig} (T : Ty (s,x)) :
    (T.rename (Rename.succ (k := Kind.var)).lift).substVar BVar.here = T := by
  simp only [Ty.substVar, Ty.rename_comp, Rename.succ_lift_subst_here, Ty.rename_id]

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label Morphism LeCo EqCo Has Atom Side)
open scoped FCdot

/-! ## What a field body needs from the literal's witnesses

A field's body is typed at its declared type and is cast to the block name `self ∙ a` by
the definition equality of the transparent self binder, which reads `self ∙ a ≐ W.get a`
for the witnesses `W` of the *whole* literal.  So the field's declared type must be what
`W.get` returns at its label; distinctness gives it. -/

/-- `Wall.get` returns the translated declared type at every field of `T`, a stable
field included. -/
def Ty.DefSpec {s : Sig} (Wall : FCdot.Witnesses (s,x)) : Ty (s,x) → Prop
  | .fld a T => Wall.get a = T.translate
  | .vfld a T => Wall.get a = T.translate
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
  | .sngl _, _, _ => by simp [Ty.DefSpec]
  | .typ _ _ _, _, _ => by simp [Ty.DefSpec]
  | .fld a T', e, hpos => by
      simp only [Ty.witnesses] at hpos
      have h1 := hpos 0 a T'.translate FCdot.Witnesses.At.hereNil
      rw [Nat.add_zero] at h1
      rw [Ty.DefSpec]
      exact h1.get hdist
  | .vfld a T', e, hpos => by
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

/-- The equations `Ty.EqSpec` places in a literal's telescope name the witnesses, so
they give `Ty.DefSpec` (P2.8). -/
theorem Ty.EqSpec.defSpec {s : Sig} {Wall : FCdot.Witnesses (s,x)} {ls vls : List Label} :
    ∀ {T : Ty (s,x)} {e : Nat},
      Ty.EqSpec (FCdot.Telescope.ofLiteral Wall ls vls) T e → Ty.DefSpec Wall T
  | .top, _, _ => by simp [Ty.DefSpec]
  | .bot, _, _ => by simp [Ty.DefSpec]
  | .sel _ _, _, _ => by simp [Ty.DefSpec]
  | .all _ _, _, _ => by simp [Ty.DefSpec]
  | .mu _, _, _ => by simp [Ty.DefSpec]
  | .sngl _, _, _ => by simp [Ty.DefSpec]
  | .typ _ _ _, _, _ => by simp [Ty.DefSpec]
  | .fld _ _, _, h => by
      rw [Ty.EqSpec] at h
      rw [Ty.DefSpec]
      exact (FCdot.Telescope.ofLiteral_eq_inv h).symm
  | .vfld _ _, _, h => by
      rw [Ty.EqSpec] at h
      rw [Ty.DefSpec]
      exact (FCdot.Telescope.ofLiteral_eq_inv h).symm
  | .and _ _, _, h => by
      rw [Ty.EqSpec] at h
      rw [Ty.DefSpec]
      exact ⟨Ty.EqSpec.defSpec h.1, Ty.EqSpec.defSpec h.2⟩

/-- The equations of a literal's own telescope, at offset `0`. -/
theorem Ty.eqSpec_self {s : Sig} (T : Ty (s,x)) (hdl : Ty.DistinctLabels T) :
    Ty.EqSpec (FCdot.Telescope.ofLiteral T.witnesses T.fieldLabels T.valLabels) T 0 :=
  eqSpec_of (Ty.witnesses_distinct T hdl) T.fieldLabels T.valLabels T 0
    (fun i l X hAt => by rw [Nat.zero_add]; exact hAt)

/-- The translated context of a literal's self binder is the one the value rule
types the literal's fields in (P2.2, `DefsTy.blocks_translate`). -/
theorem Ctx.translate_consSelf_obj {s : Sig} {Γ : Ctx s} {d : Defs (s,x)} {T : Ty (s,x)}
    {Γ₀ : Ctx (s,x)} (hd : DefsTy Γ₀ d T) (hdist : Defs.Distinct d) :
    (Γ.consSelf d T).translate =
      Γ.translate.cons (.transparent
        (μ (FCdot.Telescope.ofLiteral T.witnesses
          (hd.translateFields .here T.literalTy.weaken 0).labels
          (hd.translateFields .here T.literalTy.weaken 0).valLabels))
        (.obj T.witnesses (hd.translateFields .here T.literalTy.weaken 0).labels
          (hd.translateFields .here T.literalTy.weaken 0).valLabels
          ((hd.translateFields .here T.literalTy.weaken 0).children (.var .here)))) := by
  have hb := hd.blocks_translate hdist T.literalTy.weaken 0
  rw [hd.translateFields_labels, hd.translateFields_valLabels hdist]
  show FCdot.Ctx.cons Γ.translate (.transparent T.literalTy (T.blocks d)) = _
  rw [hb, FCdot.Value.blockSelf, hd.translateFields_labels, hd.translateFields_valLabels hdist]
  rfl

/-- The translated literal of a derivation `hd` in the context `Γ.consSelf d T` has the
precise type `T.literalTy`, given its fields are typed. -/
theorem DefsTy.translate_obj_typed {s : Sig} {Γ : Ctx s} {d : Defs (s,x)} {T : Ty (s,x)}
    {Γ₀ : Ctx (s,x)} (hd : DefsTy Γ₀ d T) (hdist : Defs.Distinct d)
    (hf : FCdot.Fields.HasType (Γ.consSelf d T).translate
      (hd.translateFields .here T.literalTy.weaken 0)) :
    FCdot.Value.HasType Γ.translate
      (.obj T.witnesses (hd.translateFields .here T.literalTy.weaken 0)) T.literalTy := by
  rw [Ctx.translate_consSelf_obj hd hdist] at hf
  have hval := FCdot.Value.HasType.obj hf
  rw [hd.translateFields_labels, hd.translateFields_valLabels hdist] at hval
  exact hval

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
  | _, Γ, _, _, HasTy.obj (d := d) (T := T) hd hdist, hwf => by
      have hdl : Ty.DistinctLabels T := hd.distinctLabels hdist
      have hf := DefsTy.translateFields_typed hd 0 (.consSelf hwf hd.literalShape hdl)
        (Ty.eqSpec_self T hdl)
      simp only [HasTy.translate]
      exact .cast (.val (DefsTy.translate_obj_typed hd hdist hf)) (litCo_typed hd hdist)
  | _, _, _, _, @HasTy.proj _ _ _ a T h, hwf => by
      have ha := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_fld, Ty.tel_fld] at ha
      have hhas := FCdot.Has.HasType.member ha .refl (FCdot.Telescope.At.zero_two _ _)
      have hle := FCdot.LeCo.HasType.member ha .refl (FCdot.Telescope.At.one_two _ _)
      rw [FCdot.Ty.substVar_sel_here, FCdot.Ty.weaken_substVar] at hle
      simp only [HasTy.translate, Ty.translate_fld, Ty.tel_fld]
      exact .cast (.proj ha hhas) hle
  | _, Γ, _, _, @HasTy.projP _ _ x a T h, hwf => by
      obtain ⟨hP, hpath⟩ := h.translatePath_typed hwf
      rw [Ty.translate_fld, Ty.tel_fld] at hP
      have hhas := FCdot.Has.HasType.memberP hP .refl (FCdot.Telescope.At.zero_two _ _)
      have hle := FCdot.LeCo.HasType.memberP hP .refl (FCdot.Telescope.At.one_two _ _)
      rw [hpath, FCdot.Ty.weaken_substPath] at hle
      rw [hpath] at hhas
      have hx := Ctx.varAtom_typed Γ hwf x
      have hproj := FCdot.Tm.HasType.proj hx (by rw [Ctx.varAtom_root]; exact hhas)
      rw [Ctx.varAtom_root] at hproj
      simp only [HasTy.translate, Ty.translate_fld, Ty.tel_fld]
      refine .cast hproj ?_
      simpa [FCdot.Ty.substPath_sel, FCdot.Path.substPath, Path.translate] using hle
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
  | _, _, _, _, .andI h₁ h₂, hwf => by
      simp only [HasTy.translate]
      exact .atom (HasTy.translateAtom_typed (.andI h₁ h₂) hwf)
  | _, _, _, _, .sngl d, hwf => by
      simp only [HasTy.translate]
      exact .atom (HasTy.translateAtom_typed (.sngl d) hwf)
  | _, _, _, _, .sub h d, hwf => by
      simp only [HasTy.translate]
      exact .cast (HasTy.translate_typed h hwf) (d.translate_typed hwf)

/-- The fields of a literal are typed under its self binder.  `e` is the position of
the first definition equation of `T'` in the self's precise telescope, and `Ty.EqSpec`
says the equations `DefsTy.translateFields` reads sit there. -/
theorem DefsTy.translateFields_typed : ∀ {s : Sig} {Γ : Ctx s} {d : Defs (s,x)}
    {Tall : Ty (s,x)} {d' : Defs (s,x)} {T' : Ty (s,x)} (h : DefsTy (Γ.consSelf d Tall) d' T')
    (e : Nat), (Γ.consSelf d Tall).Wf →
    Ty.EqSpec (FCdot.Telescope.ofLiteral Tall.witnesses Tall.fieldLabels Tall.valLabels) T' e →
    FCdot.Fields.HasType (Γ.consSelf d Tall).translate
      (h.translateFields .here Tall.literalTy.weaken e)
  | _, _, _, _, _, _, .typ, _, _, _ => by
      simp only [DefsTy.translateFields]
      exact .nil
  | _, Γ, d, Tall, _, _, @DefsTy.trm _ _ _ T'' a h, e, hwf, hspec => by
      rw [Ty.EqSpec] at hspec
      have hAt := hspec.rename (FCdot.Rename.succ (k := Kind.var)).lift
      have hvar : (Γ.consSelf d Tall).translate ⊢ₐ .var .here :
          μ ((FCdot.Telescope.ofLiteral Tall.witnesses Tall.fieldLabels Tall.valLabels).rename
            (FCdot.Rename.succ (k := Kind.var)).lift) := FCdot.Atom.HasType.var
      have hm := FCdot.EqCo.HasType.member hvar .refl hAt
      simp only [FCdot.Atom.root, FCdot.Ty.rename_lift_substVar_succ]
        at hm
      simp only [DefsTy.translateFields]
      exact .cons .nil (.cast (HasTy.translate_typed h hwf) (.eqToLe (.symm hm)))
  | _, Γ, d, Tall, _, _, DefsTy.trmObj (a := a) (d' := d₀) (T' := T₀) h hd₀, e, hwf, hspec => by
      have hdef : (Γ.consSelf d Tall).translate.lookupDef .here a
          = some (Tall.witnesses.get a) := rfl
      have hW : Tall.witnesses.get a = (Ty.mu T₀).translate := by
        have hds := Ty.EqSpec.defSpec hspec
        rw [Ty.DefSpec] at hds
        exact hds
      have hdl₀ : Ty.DistinctLabels T₀ := h.distinctLabels hd₀
      have hf := DefsTy.translateFields_typed h 0 (.consSelf hwf h.literalShape hdl₀)
        (Ty.eqSpec_self T₀ hdl₀)
      have hle : FCdot.LeCo.HasType (Γ.consSelf d Tall).translate
          (.eqToLe (.symm (.def .here a))) (Ty.mu T₀).translate ((FCdot.Path.var .here) ∙ a) := by
        rw [← hW]
        exact .eqToLe (.symm (.def hdef))
      simp only [DefsTy.translateFields]
      exact .cons .nil
        (.cast (.cast (.val (DefsTy.translate_obj_typed h hd₀ hf)) (litCo_typed h hd₀)) hle)
  | _, _, _, _, _, _, DefsTy.and (T1 := T₁) h₁ h₂, e, hwf, hspec => by
      rw [Ty.EqSpec] at hspec
      simp only [DefsTy.translateFields]
      exact (DefsTy.translateFields_typed h₂ _ hwf hspec.2).append
        (DefsTy.translateFields_typed h₁ _ hwf hspec.1)

end

/-! ## The let at a singleton

The image of the derived `letSngl`, and of every `let` at a singleton, is the opaque
`let` (decision 32).  The same term is typed by `letPath` as well, with the forwarding
binder in scope: the body typed under the opaque binder refines to the forwarding
binder (`Ctx.Refines.ofOpaque`, `FCdot/Transparency.lean`). -/

theorem let_sngl_typed_letPath {s : Sig} {Γ' : FCdot.Ctx s} {t : FCdot.Tm s}
    {u : FCdot.Tm (s,x)} {q : FCdot.Path s} {U : FCdot.Ty s}
    (ht : FCdot.Tm.HasType Γ' t (FCdot.Ty.snglOf q))
    (hu : FCdot.Tm.HasType (Γ'.cons (.opaque (FCdot.Ty.snglOf q))) u U.weaken) :
    FCdot.Tm.HasType Γ' (.let t u) U :=
  .letPath ht (hu.refine (FCdot.Ctx.Refines.ofOpaque (FCdot.Binding.fwdAt q)))

end DotMNF

end Paths
