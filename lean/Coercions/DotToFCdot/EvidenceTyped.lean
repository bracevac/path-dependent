import Coercions.DotToFCdot.Evidence
import Coercions.DotToFCdot.TypesLemmas
import Coercions.FCdot.TypingRename

/-!
# Typedness of the evidence translation (Plan III §8.1, M3)

Every subtyping derivation of DOT-MNF translates to inclusion evidence with the
translated endpoints, and every typing derivation of a variable translates to an atom of
the translated type rooted at that variable.
-/

namespace FCdot

open scoped FCdot

/-! ## Concatenation of telescopes: lengths and positions -/

theorem Telescope.length_append {s : Sig} :
    ∀ (Tel Tel' : Telescope s), (Tel.append Tel').length = Tel.length + Tel'.length
  | _, .nil => rfl
  | Tel, .cons Tel' P => by
      simp only [Telescope.append, Telescope.length, Telescope.length_append Tel Tel']
      omega

/-- Positions of the second telescope of a concatenation are offset by the length of the
first.  (`Telescope.At.append_left`, in `FCdot.FormAlgebra`, is the other half.) -/
theorem Telescope.At.append_right {s : Sig} (Tel : Telescope s) {Tel' : Telescope s}
    {i : Nat} {P : Proposition s} (h : Tel' ∋ (i ↦ P)) :
    (Tel.append Tel') ∋ (Tel.length + i ↦ P) := by
  induction h with
  | @here Tel'' Q =>
      have h2 : Tel.length + Tel''.length = (Tel.append Tel'').length :=
        (Telescope.length_append Tel Tel'').symm
      rw [show Tel.append (Telescope.cons Tel'' Q) = Telescope.cons (Tel.append Tel'') Q from rfl,
        h2]
      exact .here
  | there _ ih => exact .there ih

/-! ## Concatenation of morphisms -/

theorem Morphism.HasType.append {s : Sig} {Γ : Ctx s} {src : Telescope (s,x)}
    {m₁ : Morphism s} {Tel₁ : Telescope (s,x)} (h₁ : Γ ⊢ m₁ : src ⇒ Tel₁) :
    ∀ {m₂ : Morphism s} {Tel₂ : Telescope (s,x)}, (Γ ⊢ m₂ : src ⇒ Tel₂) →
      Γ ⊢ m₁.append m₂ : src ⇒ Tel₁.append Tel₂
  | _, _, .nil => h₁
  | _, _, .le h₂ hAt hpre hpost => .le (h₁.append h₂) hAt hpre hpost
  | _, _, .leEq h₂ hAt hpre hpost => .leEq (h₁.append h₂) hAt hpre hpost
  | _, _, .leEqSym h₂ hAt hpre hpost => .leEqSym (h₁.append h₂) hAt hpre hpost
  | _, _, .eq h₂ hAt => .eq (h₁.append h₂) hAt
  | _, _, .eqSym h₂ hAt => .eqSym (h₁.append h₂) hAt
  | _, _, .has h₂ hAt => .has (h₁.append h₂) hAt


/-! ## Witnesses: labels, positions, distinctness -/

theorem Witnesses.length_append {s : Sig} :
    ∀ (W W' : Witnesses s), (W.append W').length = W.length + W'.length
  | _, .nil => rfl
  | W, .cons W' ℓ T => by
      simp only [Witnesses.append, Witnesses.length, Witnesses.length_append W W']
      omega

theorem Witnesses.labels_append {s : Sig} :
    ∀ (W W' : Witnesses s), (W.append W').labels = W.labels ++ W'.labels
  | _, .nil => by simp [Witnesses.append, Witnesses.labels]
  | W, .cons W' ℓ T => by
      simp [Witnesses.append, Witnesses.labels, Witnesses.labels_append W W']

/-- `Witnesses.At W i ℓ T`: the `i`-th witness of `W`, counted from the oldest, is `ℓ` at
type `T`. -/
inductive Witnesses.At : Witnesses s → Nat → Label → Ty s → Prop where
  | here : Witnesses.At (.cons W ℓ T) W.length ℓ T
  | there : Witnesses.At W i ℓ T → Witnesses.At (.cons W ℓ' T') i ℓ T

/-- The labels of a witness list are pairwise distinct. -/
inductive Witnesses.Distinct : Witnesses s → Prop where
  | nil : Witnesses.Distinct .nil
  | cons : Witnesses.Distinct W → ℓ ∉ W.labels → Witnesses.Distinct (.cons W ℓ T)

theorem Witnesses.At.mem_labels {s : Sig} {W : Witnesses s} {i : Nat} {ℓ : Label} {T : Ty s}
    (h : Witnesses.At W i ℓ T) : ℓ ∈ W.labels := by
  induction h with
  | here => simp [Witnesses.labels]
  | there _ ih => simp [Witnesses.labels]; exact Or.inl ih

/-- With distinct labels, `Witnesses.get` returns the witness at any position. -/
theorem Witnesses.At.get {s : Sig} {W : Witnesses s} {i : Nat} {ℓ : Label} {T : Ty s}
    (h : Witnesses.At W i ℓ T) (hd : W.Distinct) : W.get ℓ = T := by
  induction h with
  | here => simp [Witnesses.get]
  | @there W' i' ℓ' T' ℓ'' T'' hAt ih =>
      cases hd with
      | cons hd' hnot =>
          have hne : ℓ' ≠ ℓ'' := by
            intro he; exact hnot (he ▸ hAt.mem_labels)
          simp only [Witnesses.get, if_neg hne]
          exact ih hd'

theorem Witnesses.At.append_left {s : Sig} {W : Witnesses s} {i : Nat} {ℓ : Label} {T : Ty s}
    (h : Witnesses.At W i ℓ T) : ∀ W' : Witnesses s, Witnesses.At (W.append W') i ℓ T
  | .nil => h
  | .cons W' _ _ => .there (Witnesses.At.append_left h W')

theorem Witnesses.At.append_right {s : Sig} (W : Witnesses s) {W' : Witnesses s} {i : Nat}
    {ℓ : Label} {T : Ty s} (h : Witnesses.At W' i ℓ T) :
    Witnesses.At (W.append W') (W.length + i) ℓ T := by
  induction h with
  | @here W'' ℓ' T' =>
      have h2 : W.length + W''.length = (W.append W'').length :=
        (Witnesses.length_append W W'').symm
      rw [show W.append (Witnesses.cons W'' ℓ' T') = Witnesses.cons (W.append W'') ℓ' T' from rfl,
        h2]
      exact .here
  | there _ ih => exact .there ih

theorem Witnesses.Distinct.append {s : Sig} {W : Witnesses s} (hW : W.Distinct) :
    ∀ {W' : Witnesses s}, W'.Distinct → (∀ ℓ, ℓ ∈ W.labels → ℓ ∉ W'.labels) →
      (W.append W').Distinct
  | .nil, _, _ => hW
  | .cons W' ℓ T, hW', hdis => by
      cases hW' with
      | cons hW'' hnot =>
          refine .cons (hW.append hW'' ?_) ?_
          · intro ℓ' hℓ' hmem
            exact hdis ℓ' hℓ' (by simp [Witnesses.labels]; exact Or.inl hmem)
          · rw [Witnesses.labels_append]
            simp only [List.mem_append]
            rintro (h1 | h1)
            · exact hdis ℓ h1 (by simp [Witnesses.labels])
            · exact hnot h1

/-! ## Positions inside `Telescope.ofLiteral` -/

theorem Witnesses.eqEntriesOf_length {s : Sig} (self : BVar s .var) (W₀ : Witnesses s) :
    ∀ (W : Witnesses s), (W₀.eqEntriesOf self W).length = W.length
  | .nil => rfl
  | .cons W ℓ T => by
      simp only [Witnesses.eqEntriesOf, Telescope.length, Witnesses.length,
        Witnesses.eqEntriesOf_length self W₀ W]

theorem Witnesses.eqEntriesOf_At {s : Sig} (self : BVar s .var) (W₀ : Witnesses s)
    {W : Witnesses s} {i : Nat} {ℓ : Label} {T : Ty s} (h : Witnesses.At W i ℓ T) :
    (W₀.eqEntriesOf self W) ∋ (i ↦ self ∙ ℓ ≐ W₀.get ℓ) := by
  induction h with
  | @here W' ℓ' T' =>
      rw [show W₀.eqEntriesOf self (Witnesses.cons W' ℓ' T')
            = Telescope.cons (W₀.eqEntriesOf self W') (self ∙ ℓ' ≐ W₀.get ℓ') from rfl,
        ← Witnesses.eqEntriesOf_length self W₀ W']
      exact .here
  | there _ ih => exact .there ih

/-- `LabelAt ls i ℓ`: the `i`-th label of `ls`. -/
inductive LabelAt : List Label → Nat → Label → Prop where
  | here : LabelAt (ℓ :: ls) 0 ℓ
  | there : LabelAt ls i ℓ → LabelAt (ℓ' :: ls) (i+1) ℓ

theorem LabelAt.append_left {i : Nat} {ℓ : Label} {l₁ : List Label} (h : LabelAt l₁ i ℓ) :
    ∀ l₂ : List Label, LabelAt (l₁ ++ l₂) i ℓ := by
  induction h with
  | here => intro l₂; exact .here
  | there _ ih => intro l₂; exact .there (ih l₂)

theorem LabelAt.append_right {i : Nat} {ℓ : Label} {l₂ : List Label} (h : LabelAt l₂ i ℓ) :
    ∀ l₁ : List Label, LabelAt (l₁ ++ l₂) (l₁.length + i) ℓ
  | [] => by simpa using h
  | ℓ' :: l₁ => by
      have h' := (LabelAt.append_right h l₁).there (ℓ' := ℓ')
      have heq : (ℓ' :: l₁).length + i = l₁.length + i + 1 := by simp; omega
      rw [heq]
      exact h'

/-- Presence entries are appended after the entries already present, so old positions are
unchanged. -/
theorem Telescope.At.hasEntries {s : Sig} :
    ∀ (ls : List Label) {Tel : Telescope s} {i : Nat} {P : Proposition s},
      (Tel ∋ (i ↦ P)) → ((Tel.hasEntries ls) ∋ (i ↦ P))
  | [], _, _, _, h => h
  | _ :: ls, _, _, _, h => Telescope.At.hasEntries ls (.there h)

/-- The `i`-th presence entry sits at position `Tel.length + i`. -/
theorem Telescope.hasEntries_At {s : Sig} :
    ∀ {ls : List Label} {i : Nat} {ℓ : Label}, LabelAt ls i ℓ →
      ∀ Tel : Telescope s, (Tel.hasEntries ls) ∋ (Tel.length + i ↦ ∋ ℓ)
  | _, _, ℓ, .here, Tel => by
      have h : (Telescope.cons Tel (∋ ℓ)) ∋ (Tel.length ↦ ∋ ℓ) := .here
      simpa [Telescope.hasEntries] using Telescope.At.hasEntries _ h
  | _, _, _, @LabelAt.there ls i ℓ ℓ' h, Tel => by
      have hrec := Telescope.hasEntries_At h (Telescope.cons Tel (∋ ℓ'))
      simp only [Telescope.length] at hrec
      rw [show Tel.length + (i + 1) = Tel.length + 1 + i by omega]
      exact hrec


/-! ## Small positional facts

`Telescope.length` and `Atom.root` are recursions over indexed families, so their
equations are not definitional; these are the rewrite rules used below. -/

theorem Telescope.length_nil {s : Sig} : (Telescope.nil : Telescope s).length = 0 := by
  simp [Telescope.length]

theorem Telescope.length_cons {s : Sig} (Tel : Telescope s) (P : Proposition s) :
    (Tel.cons P).length = Tel.length + 1 := by simp [Telescope.length]

/-- Positions of the first telescope of a concatenation.  (`FCdot.FormAlgebra` proves the
same statement; it is repeated here so that this module need not import it.) -/
theorem Telescope.At.append_left' {s : Sig} {Tel : Telescope s} {i : Nat} {P : Proposition s}
    (h : Tel ∋ (i ↦ P)) : ∀ Tel' : Telescope s, (Tel.append Tel') ∋ (i ↦ P)
  | .nil => h
  | .cons Tel' _ => .there (Telescope.At.append_left' h Tel')

theorem Telescope.At.zero_two {s : Sig} (P Q : Proposition s) :
    (Telescope.cons (Telescope.cons .nil P) Q) ∋ (0 ↦ P) := by
  have h : (Telescope.cons (.nil : Telescope s) P) ∋ ((Telescope.nil : Telescope s).length ↦ P) :=
    .here
  rw [Telescope.length_nil] at h
  exact .there h

theorem Telescope.At.one_two {s : Sig} (P Q : Proposition s) :
    (Telescope.cons (Telescope.cons .nil P) Q) ∋ (1 ↦ Q) := by
  have h : (Telescope.cons (Telescope.cons (.nil : Telescope s) P) Q)
      ∋ ((Telescope.cons (.nil : Telescope s) P).length ↦ Q) := .here
  rw [Telescope.length_cons, Telescope.length_nil] at h
  exact h

theorem Witnesses.length_nil {s : Sig} : (Witnesses.nil : Witnesses s).length = 0 := by
  simp [Witnesses.length]

theorem Witnesses.At.hereNil {s : Sig} {l : Label} {T : Ty s} :
    Witnesses.At (Witnesses.cons .nil l T) 0 l T := by
  have h : Witnesses.At (Witnesses.cons (.nil : Witnesses s) l T)
      ((Witnesses.nil : Witnesses s).length) l T := .here
  rw [Witnesses.length_nil] at h
  exact h

theorem Ty.substVar_sel_here {s : Sig} (A : Label) (r : BVar s .var) :
    ((Ty.sel .here A : Ty (s,x)))⟦r⟧ = Ty.sel r A := by
  simp [Ty.substVar, Ty.rename]

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label Morphism LeCo EqCo Has Atom Side)
open scoped FCdot

/-! ## Equations for the type translation

`Ty.translate`, `Ty.tel` and `Ty.telSelf` are a mutual structural recursion, so their
defining equations are not definitional; these are the rewrite rules used throughout. -/

theorem Ty.translate_top {s : Sig} : (Ty.top : Ty s).translate = ⊤ := by simp [Ty.translate]

theorem Ty.translate_bot {s : Sig} : (Ty.bot : Ty s).translate = ⊥ := by simp [Ty.translate]

theorem Ty.translate_sel {s : Sig} (y : BVar s .var) (A : Label) :
    (Ty.sel (.var y) A).translate = y ∙ A := by simp [Ty.translate]

theorem Ty.translate_all {s : Sig} (S : Ty s) (T : Ty (s,x)) :
    (Ty.all S T).translate = Π(S.translate) T.translate := by simp [Ty.translate]

theorem Ty.translate_typ {s : Sig} (A : Label) (S T : Ty s) :
    (Ty.typ A S T).translate = μ (Ty.typ A S T).tel := by simp [Ty.translate]

theorem Ty.translate_fld {s : Sig} (a : Label) (T : Ty s) :
    (Ty.fld a T).translate = μ (Ty.fld a T).tel := by simp [Ty.translate]

theorem Ty.translate_and {s : Sig} (S T : Ty s) :
    (Ty.and S T).translate = μ ((Ty.tel S).append (Ty.tel T)) := by simp [Ty.translate, Ty.tel]

theorem Ty.translate_mu {s : Sig} (T : Ty (s,x)) :
    (Ty.mu T).translate = μ T.telSelf := by simp [Ty.translate]

theorem Ty.translate_weaken {s : Sig} (T : Ty s) :
    (T.weaken : Ty (s,x)).translate = (T.translate)↑ :=
  Ty.translate_rename T FCdot.Rename.succ

theorem Ty.tel_typ {s : Sig} (A : Label) (S T : Ty s) :
    (Ty.typ A S T).tel =
      FCdot.Telescope.cons (FCdot.Telescope.cons .nil ((S.translate)↑ ⊑ .here ∙ A))
        (.here ∙ A ⊑ (T.translate)↑) := by simp [Ty.tel]

theorem Ty.tel_fld {s : Sig} (a : Label) (T : Ty s) :
    (Ty.fld a T).tel =
      FCdot.Telescope.cons (FCdot.Telescope.cons .nil (∋ a)) (.here ∙ a ⊑ (T.translate)↑) := by
  simp [Ty.tel]

theorem Ty.tel_and {s : Sig} (S T : Ty s) :
    (Ty.and S T).tel = (Ty.tel S).append (Ty.tel T) := by simp [Ty.tel]

theorem Ty.telSelf_typ {s : Sig} (A : Label) (S T : Ty (s,x)) :
    (Ty.typ A S T).telSelf =
      FCdot.Telescope.cons (FCdot.Telescope.cons .nil (S.translate ⊑ .here ∙ A))
        (.here ∙ A ⊑ T.translate) := by simp [Ty.telSelf]

theorem Ty.telSelf_fld {s : Sig} (a : Label) (T : Ty (s,x)) :
    (Ty.fld a T).telSelf =
      FCdot.Telescope.cons (FCdot.Telescope.cons .nil (∋ a)) (.here ∙ a ⊑ T.translate) := by
  simp [Ty.telSelf]

theorem Ty.telSelf_and {s : Sig} (S T : Ty (s,x)) :
    (Ty.and S T).telSelf = (Ty.telSelf S).append (Ty.telSelf T) := by simp [Ty.telSelf]

/-! ## Identity templates between concatenated telescopes -/

/-- `identityMorphism off Tel` proves every proposition of `Tel` by the identical
proposition of the source, found `off` positions further along. -/
theorem identityMorphism_typed {s : Sig} {Γ : FCdot.Ctx s} {src : FCdot.Telescope (s,x)}
    (off : Nat) :
    ∀ (Tel : FCdot.Telescope (s,x)),
      (∀ i P, Tel ∋ (i ↦ P) → src ∋ (off + i ↦ P)) →
      Γ ⊢ identityMorphism off Tel : src ⇒ Tel
  | .nil, _ => by rw [identityMorphism]; exact .nil
  | .cons Tel P, h => by
      have ih : Γ ⊢ identityMorphism off Tel : src ⇒ Tel :=
        identityMorphism_typed off Tel (fun i Q hQ => h i Q hQ.there)
      have hhere : src ∋ (off + Tel.length ↦ P) := h _ _ .here
      cases P with
      | le X Y => rw [identityMorphism]; exact .le ih hhere .none .none
      | eq X Y => rw [identityMorphism]; exact .eq ih hhere
      | has l => rw [identityMorphism]; exact .has ih hhere

/-- `And₁`: the first half of a concatenation sits at the same positions. -/
theorem identityMorphism_typed_left {s : Sig} {Γ : FCdot.Ctx s}
    (Tel₁ Tel₂ : FCdot.Telescope (s,x)) :
    Γ ⊢ identityMorphism 0 Tel₁ : Tel₁.append Tel₂ ⇒ Tel₁ :=
  identityMorphism_typed 0 Tel₁ (fun _ _ hP => by
    rw [Nat.zero_add]; exact FCdot.Telescope.At.append_left' hP Tel₂)

/-- `And₂`: the second half is offset by the length of the first. -/
theorem identityMorphism_typed_right {s : Sig} {Γ : FCdot.Ctx s}
    (Tel₁ Tel₂ : FCdot.Telescope (s,x)) :
    Γ ⊢ identityMorphism Tel₁.length Tel₂ : Tel₁.append Tel₂ ⇒ Tel₂ :=
  identityMorphism_typed Tel₁.length Tel₂ (fun _ _ hP =>
    FCdot.Telescope.At.append_right Tel₁ hP)

/-! ## Shapes of the declaration type of a set of definitions -/

/-- The declaration type of a set of definitions: type members have equal bounds, and
every conjunct is a type member, a field, or an intersection of those. -/
inductive Ty.LiteralShape : {s : Sig} → Ty s → Prop where
  | typ : Ty.LiteralShape (.typ A T T)
  | fld : Ty.LiteralShape (.fld a T)
  | and : Ty.LiteralShape S → Ty.LiteralShape T → Ty.LiteralShape (.and S T)

/-- The member labels of a declaration type, left to right. -/
def Ty.declLabels : Ty s → List Label
  | .typ A _ _ => [A]
  | .fld a _ => [a]
  | .and S T => S.declLabels ++ T.declLabels
  | _ => []

/-- The member labels of a declaration type are pairwise distinct. -/
inductive Ty.DistinctLabels : {s : Sig} → Ty s → Prop where
  | typ : Ty.DistinctLabels (.typ A S T)
  | fld : Ty.DistinctLabels (.fld a T)
  | and : Ty.DistinctLabels S → Ty.DistinctLabels T →
      (∀ l, l ∈ S.declLabels → l ∉ T.declLabels) → Ty.DistinctLabels (.and S T)

theorem DefsTy.literalShape : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s},
    DefsTy Γ d T → Ty.LiteralShape T
  | _, _, _, _, .typ => .typ
  | _, _, _, _, .trm _ => .fld
  | _, _, _, _, .and h₁ h₂ => .and h₁.literalShape h₂.literalShape

theorem DefsTy.declLabels_eq : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s},
    DefsTy Γ d T → T.declLabels = d.labels
  | _, _, _, _, .typ => by simp [Ty.declLabels, Defs.labels]
  | _, _, _, _, .trm _ => by simp [Ty.declLabels, Defs.labels]
  | _, _, _, _, .and h₁ h₂ => by
      simp only [Ty.declLabels, Defs.labels, h₁.declLabels_eq, h₂.declLabels_eq]

theorem DefsTy.distinctLabels : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s},
    DefsTy Γ d T → Defs.Distinct d → Ty.DistinctLabels T
  | _, _, _, _, .typ, _ => .typ
  | _, _, _, _, .trm _, _ => .fld
  | _, _, _, _, .and h₁ h₂, hd => by
      cases hd with
      | and hd₁ hd₂ hdis =>
          refine .and (h₁.distinctLabels hd₁) (h₂.distinctLabels hd₂) ?_
          intro l hl
          rw [h₂.declLabels_eq]
          exact hdis l (h₁.declLabels_eq ▸ hl)

/-! ## Witnesses of a declaration type -/

theorem Ty.witnesses_labels {s : Sig} : ∀ (T : Ty (s,x)), T.witnesses.labels = T.declLabels
  | .top => by simp [Ty.witnesses, Ty.declLabels, FCdot.Witnesses.labels]
  | .bot => by simp [Ty.witnesses, Ty.declLabels, FCdot.Witnesses.labels]
  | .sel _ _ => by simp [Ty.witnesses, Ty.declLabels, FCdot.Witnesses.labels]
  | .all _ _ => by simp [Ty.witnesses, Ty.declLabels, FCdot.Witnesses.labels]
  | .mu _ => by simp [Ty.witnesses, Ty.declLabels, FCdot.Witnesses.labels]
  | .typ A S T => by simp [Ty.witnesses, Ty.declLabels, FCdot.Witnesses.labels]
  | .fld a T => by simp [Ty.witnesses, Ty.declLabels, FCdot.Witnesses.labels]
  | .and S T => by
      simp only [Ty.witnesses, Ty.declLabels, FCdot.Witnesses.labels_append,
        Ty.witnesses_labels S, Ty.witnesses_labels T]

theorem Ty.witnesses_distinct {s : Sig} :
    ∀ (T : Ty (s,x)), T.DistinctLabels → T.witnesses.Distinct
  | .top, h => by cases h
  | .bot, h => by cases h
  | .sel _ _, h => by cases h
  | .all _ _, h => by cases h
  | .mu _, h => by cases h
  | .typ A S T, _ => by
      rw [Ty.witnesses]
      exact .cons .nil (by simp [FCdot.Witnesses.labels])
  | .fld a T, _ => by
      rw [Ty.witnesses]
      exact .cons .nil (by simp [FCdot.Witnesses.labels])
  | .and S T, h => by
      cases h with
      | and hS hT hdis =>
          rw [Ty.witnesses]
          refine (Ty.witnesses_distinct S hS).append (Ty.witnesses_distinct T hT) ?_
          intro l hl
          rw [Ty.witnesses_labels] at hl
          rw [Ty.witnesses_labels]
          exact hdis l hl

/-! ## What the templates of `litMorphism` need from the literal's telescope -/

/-- The definition equality that the templates of `T` read, at definition offset `e`. -/
def Ty.EqSpec {s : Sig} (src : FCdot.Telescope (s,x)) : Ty (s,x) → Nat → Prop
  | .typ A S _, e => src ∋ (e ↦ .here ∙ A ≐ S.translate)
  | .fld a T, e => src ∋ (e ↦ .here ∙ a ≐ T.translate)
  | .and S T, e => Ty.EqSpec src S e ∧ Ty.EqSpec src T (e + S.witnesses.length)
  | _, _ => True

/-- The field presences that the templates of `T` inherit, at presence offset
`off`.  `Ty.fieldLabels` puts the right conjunct first, so on an intersection
it is the right conjunct that starts at `off`. -/
def Ty.HasSpec {s : Sig} (src : FCdot.Telescope (s,x)) : Ty (s,x) → Nat → Prop
  | .fld a _, off => src ∋ (off ↦ ∋ a)
  | .and S T, off => Ty.HasSpec src S (off + T.fieldLabels.length) ∧ Ty.HasSpec src T off
  | _, _ => True

/-! ## The morphism of a literal -/

theorem litMorphism_and_fst {s : Sig} (S T : Ty (s,x)) (e h : Nat) :
    (litMorphism (.and S T) e h).1 =
      (litMorphism S e (h + T.fieldLabels.length)).1.append
        (litMorphism T (litMorphism S e (h + T.fieldLabels.length)).2.1 h).1 := by
  rw [litMorphism]

theorem litMorphism_and_eq {s : Sig} (S T : Ty (s,x)) (e h : Nat) :
    (litMorphism (.and S T) e h).2.1 =
      (litMorphism T (litMorphism S e (h + T.fieldLabels.length)).2.1 h).2.1 := by
  rw [litMorphism]

theorem litMorphism_and_has {s : Sig} (S T : Ty (s,x)) (e h : Nat) :
    (litMorphism (.and S T) e h).2.2 = (litMorphism S e (h + T.fieldLabels.length)).2.2 := by
  rw [litMorphism]

theorem litMorphism_offsets {s : Sig} : ∀ (T : Ty (s,x)) (e h : Nat),
    (litMorphism T e h).2.1 = e + T.witnesses.length ∧
      (litMorphism T e h).2.2 = h + T.fieldLabels.length
  | .top, e, h => by simp [litMorphism, Ty.witnesses, Ty.fieldLabels, FCdot.Witnesses.length]
  | .bot, e, h => by simp [litMorphism, Ty.witnesses, Ty.fieldLabels, FCdot.Witnesses.length]
  | .sel _ _, e, h => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, FCdot.Witnesses.length]
  | .all _ _, e, h => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, FCdot.Witnesses.length]
  | .mu _, e, h => by simp [litMorphism, Ty.witnesses, Ty.fieldLabels, FCdot.Witnesses.length]
  | .typ A S T, e, h => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, FCdot.Witnesses.length]
  | .fld a T, e, h => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, FCdot.Witnesses.length]
  | .and S T, e, h => by
      have hS := litMorphism_offsets S e (h + T.fieldLabels.length)
      have hT := litMorphism_offsets T (litMorphism S e (h + T.fieldLabels.length)).2.1 h
      constructor
      · rw [litMorphism_and_eq, hT.1, hS.1, Ty.witnesses, FCdot.Witnesses.length_append]
        omega
      · rw [litMorphism_and_has, hS.2, Ty.fieldLabels, List.length_append]
        omega

theorem litMorphism_typed {s : Sig} {Γ : FCdot.Ctx s} {src : FCdot.Telescope (s,x)} :
    ∀ (T : Ty (s,x)), Ty.LiteralShape T → ∀ (e h : Nat),
      Ty.EqSpec src T e → Ty.HasSpec src T h →
      Γ ⊢ (litMorphism T e h).1 : src ⇒ T.telSelf
  | .top, hsh, _, _, _, _ => by cases hsh
  | .bot, hsh, _, _, _, _ => by cases hsh
  | .sel _ _, hsh, _, _, _, _ => by cases hsh
  | .all _ _, hsh, _, _, _, _ => by cases hsh
  | .mu _, hsh, _, _, _, _ => by cases hsh
  | .typ A S T', hsh, e, h, heq, _ => by
      cases hsh
      rw [Ty.EqSpec] at heq
      rw [litMorphism, Ty.telSelf_typ]
      exact .leEq (.leEqSym .nil heq .none .none) heq .none .none
  | .fld a T', _, e, h, heq, hhas => by
      rw [Ty.EqSpec] at heq
      rw [Ty.HasSpec] at hhas
      rw [litMorphism, Ty.telSelf_fld]
      exact .leEq (.has .nil hhas) heq .none .none
  | .and S T', hsh, e, h, heq, hhas => by
      cases hsh with
      | and hS hT =>
          rw [Ty.EqSpec] at heq
          rw [Ty.HasSpec] at hhas
          obtain ⟨heq₁, heq₂⟩ := heq
          obtain ⟨hhas₁, hhas₂⟩ := hhas
          have hoff := litMorphism_offsets S e (h + T'.fieldLabels.length)
          have ih₁ := litMorphism_typed (Γ := Γ) S hS e (h + T'.fieldLabels.length) heq₁ hhas₁
          have ih₂ := litMorphism_typed (Γ := Γ) T' hT
            (litMorphism S e (h + T'.fieldLabels.length)).2.1 h
            (by rw [hoff.1]; exact heq₂) hhas₂
          rw [litMorphism_and_fst, Ty.telSelf_and]
          exact ih₁.append ih₂

/-! ## The definition equalities and presences of a literal's own telescope -/

theorem eqSpec_of {s : Sig} {Wall : FCdot.Witnesses (s,x)} (hdist : Wall.Distinct)
    (lsAll : List Label) :
    ∀ (T : Ty (s,x)) (e : Nat),
      (∀ i l X, FCdot.Witnesses.At T.witnesses i l X → FCdot.Witnesses.At Wall (e + i) l X) →
      Ty.EqSpec (FCdot.Telescope.ofLiteral Wall lsAll) T e
  | .top, _, _ => by simp [Ty.EqSpec]
  | .bot, _, _ => by simp [Ty.EqSpec]
  | .sel _ _, _, _ => by simp [Ty.EqSpec]
  | .all _ _, _, _ => by simp [Ty.EqSpec]
  | .mu _, _, _ => by simp [Ty.EqSpec]
  | .typ A S T', e, hpos => by
      simp only [Ty.witnesses] at hpos
      have h1 := hpos 0 A S.translate FCdot.Witnesses.At.hereNil
      rw [Nat.add_zero] at h1
      have h2 := FCdot.Witnesses.eqEntriesOf_At FCdot.BVar.here Wall h1
      rw [h1.get hdist] at h2
      rw [Ty.EqSpec]
      exact FCdot.Telescope.At.hasEntries lsAll h2
  | .fld a T', e, hpos => by
      simp only [Ty.witnesses] at hpos
      have h1 := hpos 0 a T'.translate FCdot.Witnesses.At.hereNil
      rw [Nat.add_zero] at h1
      have h2 := FCdot.Witnesses.eqEntriesOf_At FCdot.BVar.here Wall h1
      rw [h1.get hdist] at h2
      rw [Ty.EqSpec]
      exact FCdot.Telescope.At.hasEntries lsAll h2
  | .and S T', e, hpos => by
      simp only [Ty.witnesses] at hpos
      rw [Ty.EqSpec]
      refine ⟨eqSpec_of hdist lsAll S e (fun i l X hAt => hpos i l X (hAt.append_left _)), ?_⟩
      refine eqSpec_of hdist lsAll T' (e + S.witnesses.length) (fun i l X hAt => ?_)
      have hh := hpos (S.witnesses.length + i) l X
        (FCdot.Witnesses.At.append_right S.witnesses hAt)
      rw [show e + (S.witnesses.length + i) = e + S.witnesses.length + i by omega] at hh
      exact hh

theorem hasSpec_of {s : Sig} {src : FCdot.Telescope (s,x)} :
    ∀ (T : Ty (s,x)) (off : Nat),
      (∀ i l, FCdot.LabelAt T.fieldLabels i l → src ∋ (off + i ↦ ∋ l)) →
      Ty.HasSpec src T off
  | .top, _, _ => by simp [Ty.HasSpec]
  | .bot, _, _ => by simp [Ty.HasSpec]
  | .sel _ _, _, _ => by simp [Ty.HasSpec]
  | .all _ _, _, _ => by simp [Ty.HasSpec]
  | .mu _, _, _ => by simp [Ty.HasSpec]
  | .typ _ _ _, _, _ => by simp [Ty.HasSpec]
  | .fld a T', off, hpos => by
      simp only [Ty.fieldLabels] at hpos
      have h1 := hpos 0 a .here
      rw [Nat.add_zero] at h1
      rw [Ty.HasSpec]
      exact h1
  | .and S T', off, hpos => by
      simp only [Ty.fieldLabels] at hpos
      rw [Ty.HasSpec]
      refine ⟨?_, hasSpec_of T' off (fun i l hAt => hpos i l (hAt.append_left _))⟩
      refine hasSpec_of S (off + T'.fieldLabels.length) (fun i l hAt => ?_)
      have hh := hpos (T'.fieldLabels.length + i) l (FCdot.LabelAt.append_right hAt T'.fieldLabels)
      rw [show off + (T'.fieldLabels.length + i) = off + T'.fieldLabels.length + i by omega] at hh
      exact hh

/-! ## The coercion from a literal's precise type to its declared type -/

theorem litCo_typed_of_shape {s : Sig} {Γ : FCdot.Ctx s} {T : Ty (s,x)}
    (hsh : Ty.LiteralShape T) (hdl : Ty.DistinctLabels T) :
    Γ ⊢ litCo T : T.literalTy ≤ (Ty.mu T).translate := by
  have hW : T.witnesses.Distinct := Ty.witnesses_distinct T hdl
  rw [Ty.translate_mu]
  refine .obj (litMorphism_typed T hsh 0 T.witnesses.length ?_ ?_)
  · exact eqSpec_of hW T.fieldLabels T 0 (fun i l X hAt => by rw [Nat.zero_add]; exact hAt)
  · refine hasSpec_of T T.witnesses.length (fun i l hAt => ?_)
    have hh := FCdot.Telescope.hasEntries_At hAt (T.witnesses.eqEntries)
    rw [show (T.witnesses.eqEntries).length = T.witnesses.length from
      FCdot.Witnesses.eqEntriesOf_length _ _ _] at hh
    exact hh

/-- `litCo` is closed evidence: it is typed in any context. -/
theorem litCo_typed {s : Sig} {Γ' : FCdot.Ctx s} {Γ : Ctx (s,x)} {d : Defs (s,x)}
    {T : Ty (s,x)} (hd : DefsTy Γ d T) (hdist : Defs.Distinct d) :
    Γ' ⊢ litCo T : T.literalTy ≤ (Ty.mu T).translate :=
  litCo_typed_of_shape hd.literalShape (hd.distinctLabels hdist)

/-! ## Well-formed contexts

`Ctx.consSelf` records a literal's definitions and declaration type but not the typing
derivation that relates them, so `litCo` at such a binder is typed only under a side
condition.  `HasTy.obj` supplies it (`DefsTy.literalShape`, `DefsTy.distinctLabels`). -/

inductive Ctx.Wf : {s : Sig} → Ctx s → Prop where
  | nil : Ctx.Wf .nil
  | cons : Ctx.Wf Γ → Ctx.Wf (Γ.cons T)
  | consSelf : Ctx.Wf Γ → Ty.LiteralShape T → Ty.DistinctLabels T → Ctx.Wf (Γ.consSelf d T)

/-! ## Atoms of variables -/

theorem Ctx.lookup_cons_here {s : Sig} (Γ : Ctx s) (T : Ty s) :
    (Γ.cons T).lookup .here = T.weaken := rfl

theorem Ctx.lookup_cons_there {s : Sig} (Γ : Ctx s) (T : Ty s) (y : BVar s .var) :
    (Γ.cons T).lookup (.there y) = (Γ.lookup y).weaken := rfl

theorem Ctx.lookup_consSelf_here {s : Sig} (Γ : Ctx s) (d : Defs (s,x)) (T : Ty (s,x)) :
    (Γ.consSelf d T).lookup .here = (Ty.mu T).weaken := rfl

theorem Ctx.lookup_consSelf_there {s : Sig} (Γ : Ctx s) (d : Defs (s,x)) (T : Ty (s,x))
    (y : BVar s .var) : (Γ.consSelf d T).lookup (.there y) = (Γ.lookup y).weaken := rfl

theorem Ctx.varAtom_cons_here {s : Sig} (Γ : Ctx s) (T : Ty s) :
    (Γ.cons T).varAtom .here = .var .here := rfl

theorem Ctx.varAtom_cons_there {s : Sig} (Γ : Ctx s) (T : Ty s) (y : BVar s .var) :
    (Γ.cons T).varAtom (.there y) = (Γ.varAtom y)↑ := rfl

theorem Ctx.varAtom_consSelf_here {s : Sig} (Γ : Ctx s) (d : Defs (s,x)) (T : Ty (s,x)) :
    (Γ.consSelf d T).varAtom .here = .cast (.var .here) ((litCo T)↑) := rfl

theorem Ctx.varAtom_consSelf_there {s : Sig} (Γ : Ctx s) (d : Defs (s,x)) (T : Ty (s,x))
    (y : BVar s .var) : (Γ.consSelf d T).varAtom (.there y) = (Γ.varAtom y)↑ := rfl

theorem Ctx.varAtom_root {s : Sig} : ∀ (Γ : Ctx s) (y : BVar s .var), (Γ.varAtom y).root = y
  | .cons _ _, .here => by rw [Ctx.varAtom_cons_here]; simp [FCdot.Atom.root]
  | .cons Γ _, .there y => by
      rw [Ctx.varAtom_cons_there]
      simp [FCdot.Atom.weaken, Ctx.varAtom_root Γ y]
  | .consSelf _ _ _, .here => by rw [Ctx.varAtom_consSelf_here]; simp [FCdot.Atom.root]
  | .consSelf Γ _ _, .there y => by
      rw [Ctx.varAtom_consSelf_there]
      simp [FCdot.Atom.weaken, Ctx.varAtom_root Γ y]

theorem Ctx.varAtom_typed {s : Sig} : ∀ (Γ : Ctx s), Γ.Wf → ∀ (y : BVar s .var),
    Γ.translate ⊢ₐ Γ.varAtom y : (Γ.lookup y).translate
  | .cons Γ T, _, .here => by
      rw [Ctx.lookup_cons_here, Ctx.varAtom_cons_here, Ty.translate_weaken]
      exact .var
  | .cons Γ T, hwf, .there y => by
      cases hwf with
      | cons hwf' =>
          rw [Ctx.lookup_cons_there, Ctx.varAtom_cons_there, Ty.translate_weaken]
          exact (Ctx.varAtom_typed Γ hwf' y).weaken (.opaque T.translate)
  | .consSelf Γ d T, hwf, .here => by
      cases hwf with
      | consSelf hwf' hsh hdl =>
          rw [Ctx.lookup_consSelf_here, Ctx.varAtom_consSelf_here, Ty.translate_weaken]
          exact .cast .var
            ((litCo_typed_of_shape (Γ := Γ.translate) hsh hdl).weaken
              (.transparent T.literalTy T.witnesses T.fieldLabels))
  | .consSelf Γ d T, hwf, .there y => by
      cases hwf with
      | consSelf hwf' _ _ =>
          rw [Ctx.lookup_consSelf_there, Ctx.varAtom_consSelf_there, Ty.translate_weaken]
          exact (Ctx.varAtom_typed Γ hwf' y).weaken
            (.transparent T.literalTy T.witnesses T.fieldLabels)

/-! ## The root of a translated variable typing -/

theorem HasTy.translateAtom_root : ∀ {s : Sig} {Γ : Ctx s} {y : BVar s .var} {T : Ty s}
    (h : HasTy Γ (.path (.var y)) T), h.translateAtom.root = y
  | _, Γ, y, _, .var => by rw [HasTy.translateAtom]; exact Ctx.varAtom_root Γ y
  | _, _, _, _, .recI h _ => by
      rw [HasTy.translateAtom]
      simpa [FCdot.Atom.root] using HasTy.translateAtom_root h
  | _, _, _, _, .recE h _ => by
      rw [HasTy.translateAtom]
      simpa [FCdot.Atom.root] using HasTy.translateAtom_root h
  | _, _, _, _, .andI h₁ h₂ _ _ => by
      rw [HasTy.translateAtom]
      simpa [FCdot.Atom.root] using HasTy.translateAtom_root h₁
  | _, _, _, _, .sub h _ => by
      rw [HasTy.translateAtom]
      simpa [FCdot.Atom.root] using HasTy.translateAtom_root h

/-! ## Typedness of the evidence and atom translations -/

mutual

theorem Sub.translate_typed : ∀ {s : Sig} {Γ : Ctx s} {S T : Ty s} (d : Sub Γ S T), Γ.Wf →
    Γ.translate ⊢ d.translate : S.translate ≤ T.translate
  | _, _, _, _, .top, _ => by rw [Sub.translate, Ty.translate_top]; exact .top
  | _, _, _, _, .bot, _ => by rw [Sub.translate, Ty.translate_bot]; exact .bot
  | _, _, _, _, .refl, _ => by rw [Sub.translate]; exact .refl
  | _, _, _, _, .trans d₁ d₂, hwf => by
      rw [Sub.translate]
      exact .trans (d₁.translate_typed hwf) (d₂.translate_typed hwf)
  | _, _, _, _, .and1 hS hT, _ => by
      rw [Sub.translate, Ty.tel_and, Ty.translate_and, Ty.translate_decl hS]
      exact .obj (identityMorphism_typed_left _ _)
  | _, _, _, _, .and2 hS hT, _ => by
      rw [Sub.translate, Ty.tel_and, Ty.translate_and, Ty.translate_decl hT]
      exact .obj (identityMorphism_typed_right _ _)
  | _, _, _, _, .and d₁ d₂ hT hU, hwf => by
      have i1 := d₁.translate_typed hwf
      have i2 := d₂.translate_typed hwf
      rw [Ty.translate_decl hT] at i1
      rw [Ty.translate_decl hU] at i2
      rw [Sub.translate, Ty.translate_and]
      exact .pair i1 i2
  | _, _, _, _, .fld d, hwf => by
      rw [Sub.translate]
      simp only [Ty.translate_fld, Ty.tel_fld]
      exact .obj (.le (.has .nil (FCdot.Telescope.At.zero_two _ _))
        (FCdot.Telescope.At.one_two _ _) .none (.some (d.translate_typed hwf)))
  | _, _, _, _, .typ d₁ d₂, hwf => by
      rw [Sub.translate]
      simp only [Ty.translate_typ, Ty.tel_typ]
      exact .obj (.le (.le .nil (FCdot.Telescope.At.zero_two _ _)
          (.some (d₁.translate_typed hwf)) .none)
        (FCdot.Telescope.At.one_two _ _) .none (.some (d₂.translate_typed hwf)))
  | _, _, _, _, .selUpper h, hwf => by
      have ha := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_typ, Ty.tel_typ] at ha
      have hm := FCdot.LeCo.HasType.member ha .refl (FCdot.Telescope.At.one_two _ _)
      rw [HasTy.translateAtom_root h, FCdot.Ty.substVar_sel_here, FCdot.Ty.weaken_substVar] at hm
      rw [Sub.translate, Ty.translate_sel, Ty.translate_typ, Ty.tel_typ]
      exact hm
  | _, _, _, _, .selLower h, hwf => by
      have ha := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_typ, Ty.tel_typ] at ha
      have hm := FCdot.LeCo.HasType.member ha .refl (FCdot.Telescope.At.zero_two _ _)
      rw [HasTy.translateAtom_root h, FCdot.Ty.substVar_sel_here, FCdot.Ty.weaken_substVar] at hm
      rw [Sub.translate, Ty.translate_sel, Ty.translate_typ, Ty.tel_typ]
      exact hm
  | _, _, _, _, .all d₁ d₂, hwf => by
      rw [Sub.translate]
      simp only [Ty.translate_all]
      exact .pi (d₁.translate_typed hwf) (d₂.translate_typed (.cons hwf))

theorem HasTy.translateAtom_typed : ∀ {s : Sig} {Γ : Ctx s} {y : BVar s .var} {T : Ty s}
    (h : HasTy Γ (.path (.var y)) T), Γ.Wf → Γ.translate ⊢ₐ h.translateAtom : T.translate
  | _, Γ, y, _, .var, hwf => by
      rw [HasTy.translateAtom]
      exact Ctx.varAtom_typed Γ hwf y
  | _, _, y, _, @HasTy.recI _ _ _ T h hdecl, hwf => by
      have ih := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_decl (hdecl.substVar y)] at ih
      have hroot : (HasTy.translateAtom h).root = y := HasTy.translateAtom_root h
      have hu := FCdot.Atom.HasType.unfoldSelf ih
      rw [hroot, Ty.tel_substVar T y] at hu
      rw [HasTy.translateAtom, Ty.translate_mu]
      refine FCdot.Atom.HasType.foldSelf ?_
      rw [show (FCdot.Atom.unfoldSelf (HasTy.translateAtom h)).root = y by
        simp [FCdot.Atom.root, hroot]]
      exact hu
  | _, _, y, _, @HasTy.recE _ _ _ T h hdecl, hwf => by
      have ih := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_mu] at ih
      have hroot : (HasTy.translateAtom h).root = y := HasTy.translateAtom_root h
      have hu := FCdot.Atom.HasType.unfoldSelf ih
      rw [hroot, ← Ty.tel_substVar T y] at hu
      rw [HasTy.translateAtom, Ty.translate_decl (hdecl.substVar y)]
      refine FCdot.Atom.HasType.foldSelf ?_
      rw [show (FCdot.Atom.unfoldSelf (HasTy.translateAtom h)).root = y by
        simp [FCdot.Atom.root, hroot]]
      exact hu
  | _, _, _, _, .andI h₁ h₂ hT hU, hwf => by
      have i1 := HasTy.translateAtom_typed h₁ hwf
      have i2 := HasTy.translateAtom_typed h₂ hwf
      rw [Ty.translate_decl hT] at i1
      rw [Ty.translate_decl hU] at i2
      rw [HasTy.translateAtom, Ty.translate_and]
      exact .both i1 i2 (by rw [HasTy.translateAtom_root h₁, HasTy.translateAtom_root h₂])
  | _, _, _, _, .sub h d, hwf => by
      rw [HasTy.translateAtom]
      exact .cast (HasTy.translateAtom_typed h hwf) (d.translate_typed hwf)

end

end DotMNF
