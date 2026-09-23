import Coercions.Paths.DotToFCdot.Terms
import Coercions.Paths.DotToFCdot.EvidenceTyped

namespace Paths

/-!
# The block of a translated literal (P2.2)

`Ty.blocks T d` is the block the source gives a literal's self binder.  It reads
the declaration type and the definitions.  `Value.blockSelf` is the block the
target builds from the translated literal.  The coherence lemma
`DefsTy.blocks_translate` says the two agree.  Both are `Block.obj` with the
witnesses `T.witnesses`, so it is three equalities.

1. The labels.  `DefsTy.translateFields_labels`.
2. The stable labels.  `DefsTy.translateFields_valLabels`.  A `trm` field is cast
   by `member` (decision 26), which is not table-only, so it is not listed.  A
   `trmObj` field is a literal under `litCo` and `def`, both table-only, so it is
   listed.  `Fields.valLabels` removes a label that a later field repeats, so the
   lemma asks for `Defs.Distinct d`.
3. The children, over an arbitrary tail of fields.
   `DefsTy.translateFields_children`.  A `trm` leaf is one lemma about the body,
   `HasTy.translate_childAt`.  A `trmObj` leaf is parts 1 to 3 at the inner
   literal.

Each lemma is first proved at an arbitrary self binder (the `…At` forms), since a
recursion over `DefsTy` at the index `Ctx (s,x)` is not structural.  The plan's
statements are those forms at `.here`.
-/

namespace FCdot

/-! ## Concatenation of fields -/

theorem Fields.append_nil {s : Sig} : ∀ (F : Fields s), F.append .nil = F
  | .nil => rfl
  | .cons F ℓ t => by rw [Fields.append, Fields.append_nil F]

theorem Fields.append_assoc {s : Sig} :
    ∀ (F G H : Fields s), (F.append G).append H = F.append (G.append H)
  | .nil, _, _ => rfl
  | .cons F ℓ t, G, H => by
      rw [Fields.append, Fields.append, Fields.append, Fields.append_assoc F G H]

theorem Fields.labels_append {s : Sig} :
    ∀ (F F' : Fields s), (F.append F').labels = F.labels ++ F'.labels
  | .nil, F' => by rw [Fields.append]; simp [Fields.labels]
  | .cons F ℓ t, F' => by
      rw [Fields.append]
      simp [Fields.labels, Fields.labels_append F F']

/-- A stable label is a label. -/
theorem Fields.valLabels_subset_labels {s : Sig} :
    ∀ (F : Fields s) {ℓ : Label}, ℓ ∈ F.valLabels → ℓ ∈ F.labels
  | .nil, _, h => by simp [Fields.valLabels] at h
  | .cons F ℓ' t, ℓ, h => by
      simp only [Fields.valLabels] at h
      simp only [Fields.labels, List.mem_cons]
      cases ht : t.isStable
      · rw [ht] at h
        simp only [Bool.false_eq_true, if_false, List.mem_filter] at h
        exact .inr (Fields.valLabels_subset_labels F h.1)
      · rw [ht] at h
        simp only [if_true, List.mem_cons] at h
        rcases h with h | h
        · exact .inl h
        · exact .inr (Fields.valLabels_subset_labels F h)

/-- The stable labels of a concatenation, when no label of the outer fields is a
label of the inner ones. -/
theorem Fields.valLabels_append {s : Sig} :
    ∀ (F G : Fields s), (∀ ℓ, ℓ ∈ F.labels → ℓ ∉ G.labels) →
      (F.append G).valLabels = F.valLabels ++ G.valLabels
  | .nil, G, _ => by rw [Fields.append]; simp [Fields.valLabels]
  | .cons F ℓ t, G, hdis => by
      rw [Fields.append]
      have ih := Fields.valLabels_append F G (fun l hl => hdis l (by simp [Fields.labels, hl]))
      simp only [Fields.valLabels, ih]
      cases ht : t.isStable
      · simp only [Bool.false_eq_true, if_false, List.filter_append]
        congr 1
        apply List.filter_eq_self.mpr
        intro l hl
        have hne : l ≠ ℓ := by
          intro he
          subst he
          exact hdis l (by simp [Fields.labels]) (Fields.valLabels_subset_labels G hl)
        simpa using hne
      · simp

/-! ## The child of a body under a cast -/

/-- A cast that is not table-only hides the child of a stable body. -/
theorem Tm.childAt_cast_of_not_tableOnly {s : Sig} {t : Tm s} {E : LeCo s}
    (hE : E.tableOnly = false) (q : Path s) :
    (Tm.cast t E).childAt q = if t.isStable then none else t.childAt q := by
  cases ht : t.isStable <;> simp [Tm.childAt, ht, hE]

/-- The child a body gives under a cast that is not table-only does not see the
casts already on it. -/
theorem Tm.plainChild_cast {s : Sig} (t : Tm s) (e : LeCo s) (q : Path s) :
    (if (Tm.cast t e).isStable then none else (Tm.cast t e).childAt q) =
      (if t.isStable then none else t.childAt q) := by
  cases ht : t.isStable <;> cases he : e.tableOnly <;> simp [Tm.isStable, Tm.childAt, ht, he]

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## The labels of the translated fields -/

theorem DefsTy.translateFields_labelsAt : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s}
    (h : DefsTy Γ d T) (self : BVar s .var) (Tself : FCdot.Ty s) (e : Nat),
    (h.translateFields self Tself e).labels = T.fieldLabels
  | _, _, _, _, .typ, _, _, _ => by
      simp [DefsTy.translateFields, FCdot.Fields.labels, Ty.fieldLabels]
  | _, _, _, _, .trm _, _, _, _ => by
      simp [DefsTy.translateFields, FCdot.Fields.labels, Ty.fieldLabels]
  | _, _, _, _, .trmObj _ _, _, _, _ => by
      simp [DefsTy.translateFields, FCdot.Fields.labels, Ty.fieldLabels]
  | _, _, _, _, .and h₁ h₂, self, Tself, e => by
      simp only [DefsTy.translateFields]
      rw [FCdot.Fields.labels_append, h₂.translateFields_labelsAt, h₁.translateFields_labelsAt,
        Ty.fieldLabels]

/-- `(h.translateFields .here Tself e).labels = T.fieldLabels`: vanilla's statement at
the new signature. -/
theorem DefsTy.translateFields_labels {s : Sig} {Γ : Ctx (s,x)} {d : Defs (s,x)} {T : Ty (s,x)}
    (h : DefsTy Γ d T) (Tself : FCdot.Ty (s,x)) (e : Nat) :
    (h.translateFields .here Tself e).labels = T.fieldLabels :=
  h.translateFields_labelsAt .here Tself e

/-- A field label of a declaration type is a label of its definitions. -/
theorem DefsTy.mem_labels_of_fieldLabels : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s},
    DefsTy Γ d T → ∀ {ℓ : Label}, ℓ ∈ T.fieldLabels → ℓ ∈ d.labels
  | _, _, _, _, .typ, _, hℓ => by simp [Ty.fieldLabels] at hℓ
  | _, _, _, _, .trm _, _, hℓ => by simpa [Ty.fieldLabels, Defs.labels] using hℓ
  | _, _, _, _, .trmObj _ _, _, hℓ => by simpa [Ty.fieldLabels, Defs.labels] using hℓ
  | _, _, _, _, .and h₁ h₂, _, hℓ => by
      simp only [Ty.fieldLabels, List.mem_append] at hℓ
      simp only [Defs.labels, List.mem_append]
      rcases hℓ with hℓ | hℓ
      · exact .inr (h₂.mem_labels_of_fieldLabels hℓ)
      · exact .inl (h₁.mem_labels_of_fieldLabels hℓ)

/-! ## The stable labels of the translated fields -/

theorem DefsTy.translateFields_valLabelsAt : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s}
    (h : DefsTy Γ d T), Defs.Distinct d → ∀ (self : BVar s .var) (Tself : FCdot.Ty s) (e : Nat),
    (h.translateFields self Tself e).valLabels = T.valLabels
  | _, _, _, _, .typ, _, _, _, _ => by
      simp [DefsTy.translateFields, FCdot.Fields.valLabels, Ty.valLabels]
  | _, _, _, _, .trm _, _, _, _, _ => by
      simp [DefsTy.translateFields, FCdot.Fields.valLabels, Ty.valLabels, FCdot.Tm.isStable,
        FCdot.LeCo.tableOnly, FCdot.EqCo.tableOnly]
  | _, _, _, _, DefsTy.trmObj (T' := T') _ _, _, _, _, _ => by
      simp [DefsTy.translateFields, FCdot.Fields.valLabels, Ty.valLabels, FCdot.Tm.isStable,
        FCdot.Value.isStableLit, FCdot.LeCo.tableOnly, FCdot.EqCo.tableOnly, litCo_tableOnly]
  | _, _, _, _, .and h₁ h₂, hd, self, Tself, e => by
      cases hd with
      | and hd₁ hd₂ hdis =>
          simp only [DefsTy.translateFields]
          rw [FCdot.Fields.valLabels_append, h₂.translateFields_valLabelsAt hd₂,
            h₁.translateFields_valLabelsAt hd₁, Ty.valLabels]
          intro ℓ hℓ hℓ'
          rw [h₂.translateFields_labelsAt] at hℓ
          rw [h₁.translateFields_labelsAt] at hℓ'
          exact hdis ℓ (h₁.mem_labels_of_fieldLabels hℓ') (h₂.mem_labels_of_fieldLabels hℓ)

/-- The stable labels of the translated fields are the declared ones, given distinct
labels (decision 30). -/
theorem DefsTy.translateFields_valLabels {s : Sig} {Γ : Ctx (s,x)} {d : Defs (s,x)}
    {T : Ty (s,x)} (h : DefsTy Γ d T) (hd : Defs.Distinct d) (Tself : FCdot.Ty (s,x))
    (e : Nat) :
    (h.translateFields .here Tself e).valLabels = T.valLabels :=
  h.translateFields_valLabelsAt hd .here Tself e

/-! ## The child of a translated `trm` field -/

/-- The child a term image gives under a cast that is not table-only, at any
declared field type. -/
theorem HasTy.translate_plainChild : ∀ {s : Sig} {Γ : Ctx s} {t : Tm s} {T' : Ty s}
    (h : HasTy Γ t T') (a : Label) (U : Ty s) (q : FCdot.Path s),
    (if h.translate.isStable then none else h.translate.childAt q) =
      Tm.childOf t (.fld a U) q
  | _, Γ, _, _, HasTy.var (x := x), _, _, _ => by
      simp [HasTy.translate, FCdot.Tm.isStable, FCdot.Tm.childAt, Tm.childOf, Ctx.varAtom_root]
  | _, _, _, _, .recI h₀ hd, _, _, _ => by
      simp [HasTy.translate, FCdot.Tm.isStable, FCdot.Tm.childAt, Tm.childOf,
        HasTy.translateAtom_root (.recI h₀ hd)]
  | _, _, _, _, .recE h₀ hd, _, _, _ => by
      simp [HasTy.translate, FCdot.Tm.isStable, FCdot.Tm.childAt, Tm.childOf,
        HasTy.translateAtom_root (.recE h₀ hd)]
  | _, _, _, _, .andI h₀ h₁, _, _, _ => by
      simp [HasTy.translate, FCdot.Tm.isStable, FCdot.Tm.childAt, Tm.childOf,
        HasTy.translateAtom_root (.andI h₀ h₁)]
  | _, _, _, _, .sngl d₀, _, _, _ => by
      simp [HasTy.translate, FCdot.Tm.isStable, FCdot.Tm.childAt, Tm.childOf,
        HasTy.translateAtom_root (.sngl d₀)]
  | _, _, _, _, .lam _ _, _, _, _ => by
      simp [HasTy.translate, FCdot.Tm.isStable, FCdot.Tm.childAt, FCdot.Value.isStableLit,
        Tm.childOf, Value.childOf]
  | _, _, _, _, .app _ _, _, _, _ => by
      simp [HasTy.translate, FCdot.Tm.isStable, FCdot.Tm.childAt, Tm.childOf]
  | _, _, _, _, .obj _ _, _, _, _ => by
      simp [HasTy.translate, FCdot.Tm.isStable, FCdot.Value.isStableLit, litCo_tableOnly,
        Tm.childOf, Value.childOf]
  | _, _, _, _, .proj _, _, _, _ => by
      simp [HasTy.translate, FCdot.Tm.isStable, FCdot.Tm.childAt, Tm.childOf]
  | _, _, _, _, .projP _, _, _, _ => by
      simp [HasTy.translate, FCdot.Tm.isStable, FCdot.Tm.childAt, Tm.childOf]
  | _, _, _, _, .let _ _ _, _, _, _ => by
      simp [HasTy.translate, FCdot.Tm.isStable, FCdot.Tm.childAt, Tm.childOf]
  | _, _, _, _, .sub h d, a, U, q => by
      simp only [HasTy.translate]
      rw [FCdot.Tm.plainChild_cast]
      exact h.translate_plainChild a U q

/-- The child a translated `trm` field gives: decision 26's cast `E` is not
table-only, so a stable body gives none and any other body gives its own. -/
theorem HasTy.translate_childAt {s : Sig} {Γ : Ctx s} {t : Tm s} {T' : Ty s}
    (h : HasTy Γ t T') {E : FCdot.LeCo s} (hE : E.tableOnly = false) (a : Label)
    (q : FCdot.Path s) :
    (FCdot.Tm.cast h.translate E).childAt q = Tm.childOf t (.fld a T') q := by
  rw [FCdot.Tm.childAt_cast_of_not_tableOnly hE]
  exact h.translate_plainChild a T' q

/-! ## The children of the translated fields -/

theorem DefsTy.translateFields_childrenAt : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s}
    (h : DefsTy Γ d T) (self : BVar s .var) (Tself : FCdot.Ty s) (e : Nat)
    (G : FCdot.Fields s) (p : FCdot.Path s),
    (FCdot.Fields.append (h.translateFields self Tself e) G).children p =
      Defs.childrenOver d T (G.children p) p
  | _, _, _, _, .typ, _, _, _, G, p => by
      simp only [DefsTy.translateFields, FCdot.Fields.append, Defs.childrenOver]
  | _, _, _, _, DefsTy.trm (a := a) (t := t) (T := T₀) h, self, Tself, e, G, p => by
      simp only [DefsTy.translateFields, FCdot.Fields.append, FCdot.Fields.children,
        Defs.childrenOver]
      rw [h.translate_childAt (by simp [FCdot.LeCo.tableOnly, FCdot.EqCo.tableOnly]) a]
      cases Tm.childOf t (.fld a T₀) (p.sel a) <;> rfl
  | _, _, _, _, DefsTy.trmObj (a := a) (d' := d') (T' := T') h hd', self, Tself, e, G, p => by
      have h1 := h.translateFields_labelsAt .here T'.literalTy.weaken 0
      have h2 := h.translateFields_valLabelsAt hd' .here T'.literalTy.weaken 0
      have h3 := h.translateFields_childrenAt .here T'.literalTy.weaken 0 .nil (.var .here)
      rw [FCdot.Fields.append_nil] at h3
      simp only [DefsTy.translateFields, FCdot.Fields.append, FCdot.Fields.children,
        Defs.childrenOver, Tm.childOf, Value.childOf, FCdot.Tm.childAt, FCdot.Tm.isStable,
        FCdot.Value.isStableLit, litCo_tableOnly, FCdot.LeCo.tableOnly, FCdot.EqCo.tableOnly,
        FCdot.Value.blockSelf, h1, h2, h3]
      rfl
  | _, _, _, _, .and h₁ h₂, self, Tself, e, G, p => by
      simp only [DefsTy.translateFields]
      rw [FCdot.Fields.append_assoc, h₂.translateFields_childrenAt,
        h₁.translateFields_childrenAt]
      rfl

theorem DefsTy.translateFields_children {s : Sig} {Γ : Ctx (s,x)} {d : Defs (s,x)}
    {T : Ty (s,x)} (h : DefsTy Γ d T) (Tself : FCdot.Ty (s,x)) (e : Nat)
    (G : FCdot.Fields (s,x)) (p : FCdot.Path (s,x)) :
    (FCdot.Fields.append (h.translateFields .here Tself e) G).children p =
      Defs.childrenOver d T (G.children p) p :=
  h.translateFields_childrenAt .here Tself e G p

/-! ## The coherence lemma -/

/-- P2.2's coherence lemma: the block the source gives a literal's self binder is the
block the target builds from the translated literal.  `Tself` and `e` are arbitrary,
since stability does not read them. -/
theorem DefsTy.blocks_translate {s : Sig} {Γ : Ctx (s,x)} {d : Defs (s,x)} {T : Ty (s,x)}
    (h : DefsTy Γ d T) (hd : Defs.Distinct d) (Tself : FCdot.Ty (s,x)) (e : Nat) :
    T.blocks d = (FCdot.Value.obj T.witnesses (h.translateFields .here Tself e)).blockSelf := by
  have h3 := h.translateFields_children Tself e .nil (.var .here)
  rw [FCdot.Fields.append_nil] at h3
  rw [Ty.blocks, FCdot.Value.blockSelf, h.translateFields_labels, h.translateFields_valLabels hd,
    h3]
  rfl

/-- The same block written at a path. -/
theorem DefsTy.blocksAt_translate {s : Sig} {Γ : Ctx (s,x)} {d : Defs (s,x)} {T : Ty (s,x)}
    (h : DefsTy Γ d T) (hd : Defs.Distinct d) (Tself : FCdot.Ty (s,x)) (e : Nat)
    (p : FCdot.Path s) :
    (T.blocks d).substPath p =
      (FCdot.Value.obj T.witnesses (h.translateFields .here Tself e)).blocksAt p := by
  rw [h.blocks_translate hd Tself e]
  rfl

end DotMNF

end Paths
