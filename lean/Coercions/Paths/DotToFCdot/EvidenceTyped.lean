import Coercions.Paths.DotToFCdot.Evidence
import Coercions.Paths.DotToFCdot.TypesLemmas
import Coercions.Paths.FCdot.TypingRename

namespace Paths

/-!
# Typedness of the evidence translation (Plan III §8.1, M3)

Every subtyping derivation of DOT-MNF translates to inclusion evidence with the
translated endpoints, and every typing derivation of a variable translates to an atom of
the translated type rooted at that variable.

Stage P2.3 adds path typing.  Every path typing translates to path evidence of the
translated type at the translated path (`PathTy.translatePath_typed`), and `Sub.mu`
translates to a template morphism typed by `SubDecl.translate_typed`.  The positions a
template reads are `Ty.typIdx_spec`, `Ty.fldIdx_spec` and `Ty.vfldIdx_spec`.  A literal's
coercion `litCo` copies stable presences by the third counter of `litMorphism`, and it
is table-only (`litMorphism_tableOnly`).  Subtyping and path typing are one mutual block.
The atom theorems come after it, since the only evidence they read is
`Sub.translate_typed` at `sub` and `PathTy.translatePath_typed` at `sngl`.
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
  | _, _, .bnd h₂ he => .bnd (h₁.append h₂) he
  | _, _, .hasVal h₂ hAt => .hasVal (h₁.append h₂) hAt
  | _, _, .hasOfVal h₂ hAt => .hasOfVal (h₁.append h₂) hAt
  | _, _, .aliasCopy h₂ hAt => .aliasCopy (h₁.append h₂) hAt

/-- A concatenation of morphisms is table-only when both parts are. -/
theorem Morphism.tableOnly_append {s : Sig} (m₁ : Morphism s) :
    ∀ m₂ : Morphism s, (m₁.append m₂).tableOnly = (m₁.tableOnly && m₂.tableOnly)
  | .nil => by simp [Morphism.append, Morphism.tableOnly]
  | .le m pre _ post => by
      simp only [Morphism.append, Morphism.tableOnly, Morphism.tableOnly_append m₁ m]
      cases m₁.tableOnly <;> simp
  | .eq m _ _ => by simp only [Morphism.append, Morphism.tableOnly, Morphism.tableOnly_append m₁ m]
  | .has m _ => by simp only [Morphism.append, Morphism.tableOnly, Morphism.tableOnly_append m₁ m]
  | .bnd m e => by
      simp only [Morphism.append, Morphism.tableOnly, Morphism.tableOnly_append m₁ m]
      cases m₁.tableOnly <;> simp
  | .hasVal m _ => by
      simp only [Morphism.append, Morphism.tableOnly, Morphism.tableOnly_append m₁ m]
  | .hasOfVal m _ => by
      simp only [Morphism.append, Morphism.tableOnly, Morphism.tableOnly_append m₁ m]
  | .aliasCopy m _ => by
      simp only [Morphism.append, Morphism.tableOnly, Morphism.tableOnly_append m₁ m]


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

private theorem Witnesses.eqEntriesOf_At {s : Sig} (self : BVar s .var) (W₀ : Witnesses s)
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
private theorem Telescope.hasEntries_At {s : Sig} :
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

/-- Stable presence entries are appended after the entries already present, so old
positions are unchanged. -/
theorem Telescope.At.hasValEntries {s : Sig} :
    ∀ (ls : List Label) {Tel : Telescope s} {i : Nat} {P : Proposition s},
      (Tel ∋ (i ↦ P)) → ((Tel.hasValEntries ls) ∋ (i ↦ P))
  | [], _, _, _, h => h
  | _ :: ls, _, _, _, h => Telescope.At.hasValEntries ls (.there h)

/-- The `i`-th stable presence entry sits at position `Tel.length + i`. -/
private theorem Telescope.hasValEntries_At {s : Sig} :
    ∀ {ls : List Label} {i : Nat} {ℓ : Label}, LabelAt ls i ℓ →
      ∀ Tel : Telescope s, (Tel.hasValEntries ls) ∋ (Tel.length + i ↦ ∋ᵛ ℓ)
  | _, _, ℓ, .here, Tel => by
      have h : (Telescope.cons Tel (∋ᵛ ℓ)) ∋ (Tel.length ↦ ∋ᵛ ℓ) := .here
      simpa [Telescope.hasValEntries] using Telescope.At.hasValEntries _ h
  | _, _, _, @LabelAt.there ls i ℓ ℓ' h, Tel => by
      have hrec := Telescope.hasValEntries_At h (Telescope.cons Tel (∋ᵛ ℓ'))
      simp only [Telescope.length] at hrec
      rw [show Tel.length + (i + 1) = Tel.length + 1 + i by omega]
      exact hrec

theorem Telescope.length_hasEntries {s : Sig} :
    ∀ (ls : List Label) (Tel : Telescope s), (Tel.hasEntries ls).length = Tel.length + ls.length
  | [], Tel => by simp [Telescope.hasEntries]
  | ℓ :: ls, Tel => by
      simp only [Telescope.hasEntries, Telescope.length_hasEntries ls, Telescope.length,
        List.length_cons]
      omega


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

theorem Telescope.At.zero_three {s : Sig} (P Q R : Proposition s) :
    (Telescope.cons (Telescope.cons (Telescope.cons .nil P) Q) R) ∋ (0 ↦ P) :=
  .there (Telescope.At.zero_two P Q)

theorem Telescope.At.one_three {s : Sig} (P Q R : Proposition s) :
    (Telescope.cons (Telescope.cons (Telescope.cons .nil P) Q) R) ∋ (1 ↦ Q) :=
  .there (Telescope.At.one_two P Q)

theorem Telescope.At.two_three {s : Sig} (P Q R : Proposition s) :
    (Telescope.cons (Telescope.cons (Telescope.cons .nil P) Q) R) ∋ (2 ↦ R) := by
  have h : (Telescope.cons (Telescope.cons (Telescope.cons (.nil : Telescope s) P) Q) R)
      ∋ ((Telescope.cons (Telescope.cons (.nil : Telescope s) P) Q).length ↦ R) := .here
  rw [Telescope.length_cons, Telescope.length_cons, Telescope.length_nil] at h
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
    ((Ty.sel (.var .here) A : Ty (s,x)))⟦r⟧ = Ty.sel (.var r) A := by
  simp [Ty.substVar, Ty.rename, Path.rename]

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label Morphism LeCo EqCo Has Atom Side PathCo AliasCo)
open scoped FCdot

/-! ## Equations for the type translation

`Ty.translate`, `Ty.tel` and `Ty.telSelfAt` are a mutual structural recursion.  These are
the rewrite rules used throughout. -/

theorem Ty.translate_top {s : Sig} : (Ty.top : Ty s).translate = ⊤ := by simp [Ty.translate]

theorem Ty.translate_bot {s : Sig} : (Ty.bot : Ty s).translate = ⊥ := by simp [Ty.translate]

theorem Ty.translate_sel {s : Sig} (y : BVar s .var) (A : Label) :
    (Ty.sel (.var y) A).translate = y ∙ A := by simp [Ty.translate, Path.translate]

/-- A selection on a path translates to the selection on the translated path. -/
theorem Ty.translate_selP {s : Sig} (p : Path s) (A : Label) :
    (Ty.sel p A).translate = p.translate ∙ A := by simp [Ty.translate]

theorem Ty.translate_all {s : Sig} (S : Ty s) (T : Ty (s,x)) :
    (Ty.all S T).translate = Π(S.translate) T.translate := by simp [Ty.translate]

theorem Ty.translate_typ {s : Sig} (A : Label) (S T : Ty s) :
    (Ty.typ A S T).translate = μ (Ty.typ A S T).tel := by simp [Ty.translate, Ty.tel]

theorem Ty.translate_fld {s : Sig} (a : Label) (T : Ty s) :
    (Ty.fld a T).translate = μ (Ty.fld a T).tel := by simp [Ty.translate, Ty.tel]

theorem Ty.translate_vfld {s : Sig} (a : Label) (T : Ty s) :
    (Ty.vfld a T).translate = μ (Ty.vfld a T).tel := by simp [Ty.translate, Ty.tel]

/-- A singleton translates to the singleton object type of the translated path. -/
theorem Ty.translate_sngl {s : Sig} (q : Path s) :
    (Ty.sngl q).translate = FCdot.Ty.snglOf q.translate := by
  simp [Ty.translate, FCdot.Ty.snglOf]

theorem Ty.translate_and {s : Sig} (S T : Ty s) :
    (Ty.and S T).translate = μ ((Ty.tel S).append (Ty.tel T)) := by simp [Ty.translate]

theorem Ty.translate_mu {s : Sig} (T : Ty (s,x)) :
    (Ty.mu T).translate = μ T.telSelf := by simp [Ty.translate, Ty.telSelf]

theorem Ty.translate_weaken {s : Sig} (T : Ty s) :
    (T.weaken : Ty (s,x)).translate = (T.translate)↑ :=
  Ty.translate_rename T FCdot.Rename.succ

theorem Ty.tel_typ {s : Sig} (A : Label) (S T : Ty s) :
    (Ty.typ A S T).tel =
      FCdot.Telescope.cons (FCdot.Telescope.cons .nil ((S.translate)↑ ⊑ (.var .here) ∙ A))
        ((.var .here) ∙ A ⊑ (T.translate)↑) := by simp [Ty.tel]

theorem Ty.tel_fld {s : Sig} (a : Label) (T : Ty s) :
    (Ty.fld a T).tel =
      FCdot.Telescope.cons (FCdot.Telescope.cons .nil (∋ a)) ((.var .here) ∙ a ⊑ (T.translate)↑) := by
  simp [Ty.tel]

theorem Ty.tel_vfld {s : Sig} (a : Label) (T : Ty s) :
    (Ty.vfld a T).tel =
      FCdot.Telescope.cons (FCdot.Telescope.cons (FCdot.Telescope.cons .nil (∋ a)) (∋ᵛ a))
        ((.var .here) ∙ a ⊑ (T.translate)↑) := by
  simp [Ty.tel]

theorem Ty.tel_and {s : Sig} (S T : Ty s) :
    (Ty.and S T).tel = (Ty.tel S).append (Ty.tel T) := by simp [Ty.tel]

theorem Ty.telSelf_top {s : Sig} : (Ty.top : Ty (s,x)).telSelf = .nil := by
  simp [Ty.telSelf, Ty.telSelfAt]

theorem Ty.telSelf_typ {s : Sig} (A : Label) (S T : Ty (s,x)) :
    (Ty.typ A S T).telSelf =
      FCdot.Telescope.cons (FCdot.Telescope.cons .nil (S.translate ⊑ (.var .here) ∙ A))
        ((.var .here) ∙ A ⊑ T.translate) := by simp [Ty.telSelf, Ty.telSelfAt]

theorem Ty.telSelf_fld {s : Sig} (a : Label) (T : Ty (s,x)) :
    (Ty.fld a T).telSelf =
      FCdot.Telescope.cons (FCdot.Telescope.cons .nil (∋ a)) ((.var .here) ∙ a ⊑ T.translate) := by
  simp [Ty.telSelf, Ty.telSelfAt]

theorem Ty.telSelf_vfld {s : Sig} (a : Label) (T : Ty (s,x)) :
    (Ty.vfld a T).telSelf =
      FCdot.Telescope.cons (FCdot.Telescope.cons (FCdot.Telescope.cons .nil (∋ a)) (∋ᵛ a))
        ((.var .here) ∙ a ⊑ T.translate) := by
  simp [Ty.telSelf, Ty.telSelfAt]

theorem Ty.telSelf_and {s : Sig} (S T : Ty (s,x)) :
    (Ty.and S T).telSelf = (Ty.telSelf S).append (Ty.telSelf T) := by
  simp [Ty.telSelf, Ty.telSelfAt]

/-! ## Telescopes without self-bounds, and telescopes with closed self-bounds -/

theorem _root_.Paths.FCdot.Telescope.NoBnd.append {s' : Sig} {Tel₁ : FCdot.Telescope s'}
    (h₁ : Tel₁.NoBnd) :
    ∀ Tel₂ : FCdot.Telescope s', Tel₂.NoBnd → (Tel₁.append Tel₂).NoBnd
  | .nil, _ => h₁
  | .cons _ (.bnd _), h₂ => h₂.elim
  | .cons Tel (.le _ _), h₂ => FCdot.Telescope.NoBnd.append h₁ Tel h₂
  | .cons Tel (.eq _ _), h₂ => FCdot.Telescope.NoBnd.append h₁ Tel h₂
  | .cons Tel (.has _), h₂ => FCdot.Telescope.NoBnd.append h₁ Tel h₂
  | .cons Tel (.hasVal _), h₂ => FCdot.Telescope.NoBnd.append h₁ Tel h₂
  | .cons Tel (.alias _), h₂ => FCdot.Telescope.NoBnd.append h₁ Tel h₂

theorem _root_.Paths.FCdot.Telescope.NoBnd.rename {s₁ s₂ : Sig} (ρ : FCdot.Rename s₁ s₂) :
    ∀ Tel : FCdot.Telescope s₁, Tel.NoBnd → (Tel.rename ρ).NoBnd
  | .nil, h => h
  | .cons _ (.bnd _), h => h.elim
  | .cons Tel (.le _ _), h => FCdot.Telescope.NoBnd.rename ρ Tel h
  | .cons Tel (.eq _ _), h => FCdot.Telescope.NoBnd.rename ρ Tel h
  | .cons Tel (.has _), h => FCdot.Telescope.NoBnd.rename ρ Tel h
  | .cons Tel (.hasVal _), h => FCdot.Telescope.NoBnd.rename ρ Tel h
  | .cons Tel (.alias _), h => FCdot.Telescope.NoBnd.rename ρ Tel h

theorem _root_.Paths.FCdot.Telescope.NoBnd.closedBnds {s : Sig} :
    ∀ {Tel : FCdot.Telescope (s,x)}, Tel.NoBnd → Tel.ClosedBnds
  | .nil, _ => .nil
  | .cons _ (.bnd _), h => h.elim
  | .cons Tel (.le _ _), h => .le (FCdot.Telescope.NoBnd.closedBnds h)
  | .cons Tel (.eq _ _), h => .eq (FCdot.Telescope.NoBnd.closedBnds h)
  | .cons Tel (.has _), h => .has (FCdot.Telescope.NoBnd.closedBnds h)
  | .cons Tel (.hasVal _), h => .hasVal (FCdot.Telescope.NoBnd.closedBnds h)
  | .cons Tel (.alias _), h => .alias (FCdot.Telescope.NoBnd.closedBnds h)

theorem _root_.Paths.FCdot.Telescope.ClosedBnds.append {s : Sig} {Tel₁ : FCdot.Telescope (s,x)}
    (h₁ : Tel₁.ClosedBnds) :
    ∀ {Tel₂ : FCdot.Telescope (s,x)}, Tel₂.ClosedBnds → (Tel₁.append Tel₂).ClosedBnds
  | _, .nil => h₁
  | _, .le h₂ => .le (FCdot.Telescope.ClosedBnds.append h₁ h₂)
  | _, .eq h₂ => .eq (FCdot.Telescope.ClosedBnds.append h₁ h₂)
  | _, .has h₂ => .has (FCdot.Telescope.ClosedBnds.append h₁ h₂)
  | _, .bnd h₂ => .bnd (FCdot.Telescope.ClosedBnds.append h₁ h₂)
  | _, .hasVal h₂ => .hasVal (FCdot.Telescope.ClosedBnds.append h₁ h₂)
  | _, .alias h₂ => .alias (FCdot.Telescope.ClosedBnds.append h₁ h₂)

/-- A declaration-shaped body has no self-bounds at all: `Ty.telSelf` only
produces one on a shape `Wf.mu` excludes. -/
theorem Ty.telSelf_noBnd_of_decl {s : Sig} :
    ∀ {S : Ty (s,x)}, Ty.Decl S → (Ty.telSelf S).NoBnd
  | .top, _ => by simp [Ty.telSelf, Ty.telSelfAt, FCdot.Telescope.NoBnd]
  | .typ _ _ _, _ => by simp [Ty.telSelf, Ty.telSelfAt, FCdot.Telescope.NoBnd]
  | .fld _ _, _ => by simp [Ty.telSelf, Ty.telSelfAt, FCdot.Telescope.NoBnd]
  | .vfld _ _, _ => by simp [Ty.telSelf, Ty.telSelfAt, FCdot.Telescope.NoBnd]
  | .sngl _, _ => by simp [Ty.telSelf, Ty.telSelfAt, FCdot.Telescope.NoBnd]
  | .and S T, h => by
      cases h with
      | and hS hT =>
          rw [Ty.telSelf_and]
          exact FCdot.Telescope.NoBnd.append (Ty.telSelf_noBnd_of_decl hS) _
            (Ty.telSelf_noBnd_of_decl hT)
  | .mu T, h => by
      cases h with
      | mu hT =>
          have hd : T.isDecl = true := (Ty.isDecl_iff T).mpr hT
          simp only [Ty.telSelf, Ty.telSelfAt, hd, ↓reduceIte, FCdot.Telescope.substVar]
          exact FCdot.Telescope.NoBnd.rename _ _ (Ty.telSelf_noBnd_of_decl hT)

/-- Every self-bound the translation of a type carries is a weakened closed
type: this is the closedness convention of `FCdot` (plan §13 item 9). -/
theorem Ty.tel_closedBnds {s : Sig} :
    ∀ S : Ty s, (Ty.tel S : FCdot.Telescope (s,x)).ClosedBnds
  | .top => by simp only [Ty.tel]; exact .nil
  | .bot => by simp only [Ty.tel]; exact .bnd .nil
  | .sel _ _ => by simp only [Ty.tel]; exact .bnd .nil
  | .all _ _ => by simp only [Ty.tel]; exact .bnd .nil
  | .typ _ _ _ => by simp only [Ty.tel]; exact .le (.le .nil)
  | .fld _ _ => by simp only [Ty.tel]; exact .le (.has .nil)
  | .vfld _ _ => by simp only [Ty.tel]; exact .le (.hasVal (.has .nil))
  | .sngl _ => by simp only [Ty.tel]; exact .alias .nil
  | .and S T => by
      simp only [Ty.tel]
      exact (Ty.tel_closedBnds S).append (Ty.tel_closedBnds T)
  | .mu T => by
      cases hd : T.isDecl with
      | true =>
          simp only [Ty.tel, hd, ↓reduceIte]
          exact (Ty.telSelf_noBnd_of_decl ((Ty.isDecl_iff T).mp hd)).closedBnds
      | false =>
          simp only [Ty.tel, hd, Bool.false_eq_true, ↓reduceIte]
          exact .bnd .nil

/-! ## Identity templates between concatenated telescopes -/

/-- `identityMorphism src off Tel` proves every proposition of `Tel` by the identical
proposition of the source, found `off` positions further along; a self-bound is
proven by the cast of `μ src` through the source's own bound there.  Stated at the
signature `(s,x)`, as in the base. -/
theorem identityMorphism_typed {s : Sig} {Γ : FCdot.Ctx s} {src : FCdot.Telescope (s,x)}
    (off : Nat) :
    ∀ {Tel : FCdot.Telescope (s,x)}, Tel.ClosedBnds →
      (∀ i P, Tel ∋ (i ↦ P) → src ∋ (off + i ↦ P)) →
      Γ ⊢ identityMorphism src off Tel : src ⇒ Tel
  | _, .nil, _ => by rw [identityMorphism]; exact .nil
  | _, .le hb, h => by
      have ih := identityMorphism_typed (Γ := Γ) (src := src) off hb (fun i Q hQ => h i Q hQ.there)
      rw [identityMorphism]; exact .le ih (h _ _ .here) .none .none
  | _, .eq hb, h => by
      have ih := identityMorphism_typed (Γ := Γ) (src := src) off hb (fun i Q hQ => h i Q hQ.there)
      rw [identityMorphism]; exact .eq ih (h _ _ .here)
  | _, .has hb, h => by
      have ih := identityMorphism_typed (Γ := Γ) (src := src) off hb (fun i Q hQ => h i Q hQ.there)
      rw [identityMorphism]; exact .has ih (h _ _ .here)
  | _, .bnd hb, h => by
      have ih := identityMorphism_typed (Γ := Γ) (src := src) off hb (fun i Q hQ => h i Q hQ.there)
      rw [identityMorphism]; exact .bnd ih (.bound (h _ _ .here))
  | _, .hasVal hb, h => by
      have ih := identityMorphism_typed (Γ := Γ) (src := src) off hb (fun i Q hQ => h i Q hQ.there)
      rw [identityMorphism]; exact .hasVal ih (h _ _ .here)
  | _, .alias hb, h => by
      have ih := identityMorphism_typed (Γ := Γ) (src := src) off hb (fun i Q hQ => h i Q hQ.there)
      rw [identityMorphism]; exact .aliasCopy ih (h _ _ .here)

/-- `And₁`: the first half of a concatenation sits at the same positions. -/
theorem identityMorphism_typed_left {s : Sig} {Γ : FCdot.Ctx s}
    (Tel₁ Tel₂ : FCdot.Telescope (s,x)) (hb : Tel₁.ClosedBnds) :
    Γ ⊢ identityMorphism (Tel₁.append Tel₂) 0 Tel₁ : Tel₁.append Tel₂ ⇒ Tel₁ :=
  identityMorphism_typed 0 hb (fun _ _ hP => by
    rw [Nat.zero_add]; exact FCdot.Telescope.At.append_left' hP Tel₂)

/-- `And₂`: the second half is offset by the length of the first. -/
theorem identityMorphism_typed_right {s : Sig} {Γ : FCdot.Ctx s}
    (Tel₁ Tel₂ : FCdot.Telescope (s,x)) (hb : Tel₂.ClosedBnds) :
    Γ ⊢ identityMorphism (Tel₁.append Tel₂) Tel₁.length Tel₂ : Tel₁.append Tel₂ ⇒ Tel₂ :=
  identityMorphism_typed Tel₁.length hb (fun _ _ hP =>
    FCdot.Telescope.At.append_right Tel₁ hP)

/-! ## Putting an operand into its telescope -/

/-- `into T` turns evidence into `⟦T⟧` into evidence into `μ (tel T)`. -/
theorem into_typed {s : Sig} {Γ : FCdot.Ctx s} {S T : Ty s} {d : FCdot.LeCo s}
    (hd : Γ ⊢ d : S.translate ≤ T.translate) : Γ ⊢ into T d : S.translate ≤ μ T.tel := by
  rw [into]
  cases h : T.isObj with
  | true => rw [if_pos rfl, ← Ty.translate_isObj h]; exact hd
  | false =>
      rw [if_neg Bool.false_ne_true, Ty.tel_of_not_isObj h]
      exact .intoBnd hd

/-- The same for atoms; `And-I` needs it on both operands. -/
theorem intoAtom_typed {s : Sig} {Γ : FCdot.Ctx s} {T : Ty s} {a : FCdot.Atom s}
    (ha : Γ ⊢ₐ a : T.translate) : Γ ⊢ₐ intoAtom T a : μ T.tel := by
  rw [intoAtom]
  cases h : T.isObj with
  | true => rw [if_pos rfl, ← Ty.translate_isObj h]; exact ha
  | false =>
      rw [if_neg Bool.false_ne_true, Ty.tel_of_not_isObj h]
      exact .cast ha (.intoBnd .refl)

/-- The same for path evidence.  `And-I` at a path needs it on both operands. -/
theorem intoPath_typed {s : Sig} {Γ : FCdot.Ctx s} {T : Ty s} {P : FCdot.PathCo s}
    (hP : Γ ⊢ᵖ P : T.translate) : Γ ⊢ᵖ intoPath T P : μ T.tel := by
  rw [intoPath]
  cases h : T.isObj with
  | true => rw [if_pos rfl, ← Ty.translate_isObj h]; exact hP
  | false =>
      rw [if_neg Bool.false_ne_true, Ty.tel_of_not_isObj h]
      exact .cast hP (.intoBnd .refl)

/-- The self-bound of a non-object operand sits at position `0` of its own
telescope. -/
theorem Ty.tel_bnd_at {s : Sig} {T : Ty s} (h : T.isObj = false) :
    (Ty.tel T : FCdot.Telescope (s,x)) ∋ (0 ↦ ⊑ T.translate↑) := by
  rw [Ty.tel_of_not_isObj h]
  exact .here

/-! ## Shapes of the declaration type of a set of definitions -/

/-- The declaration type of a set of definitions: type members have equal bounds, a
stable field is declared at the type of its literal, and every conjunct is a type
member, a field, a stable field, or an intersection of those. -/
inductive Ty.LiteralShape : {s : Sig} → Ty s → Prop where
  | typ : Ty.LiteralShape (.typ A T T)
  | fld : Ty.LiteralShape (.fld a T)
  | vfld : Ty.LiteralShape (.vfld a (.mu T))
  | and : Ty.LiteralShape S → Ty.LiteralShape T → Ty.LiteralShape (.and S T)

/-- The member labels of a declaration type, left to right. -/
def Ty.declLabels : Ty s → List Label
  | .typ A _ _ => [A]
  | .fld a _ => [a]
  | .vfld a _ => [a]
  | .and S T => S.declLabels ++ T.declLabels
  | _ => []

/-- The member labels of a declaration type are pairwise distinct. -/
inductive Ty.DistinctLabels : {s : Sig} → Ty s → Prop where
  | typ : Ty.DistinctLabels (.typ A S T)
  | fld : Ty.DistinctLabels (.fld a T)
  | vfld : Ty.DistinctLabels (.vfld a T)
  | and : Ty.DistinctLabels S → Ty.DistinctLabels T →
      (∀ l, l ∈ S.declLabels → l ∉ T.declLabels) → Ty.DistinctLabels (.and S T)

theorem DefsTy.literalShape : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s},
    DefsTy Γ d T → Ty.LiteralShape T
  | _, _, _, _, .typ => .typ
  | _, _, _, _, .trm _ => .fld
  | _, _, _, _, .trmObj _ _ => .vfld
  | _, _, _, _, .and h₁ h₂ => .and h₁.literalShape h₂.literalShape

theorem DefsTy.declLabels_eq : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s},
    DefsTy Γ d T → T.declLabels = d.labels
  | _, _, _, _, .typ => by simp [Ty.declLabels, Defs.labels]
  | _, _, _, _, .trm _ => by simp [Ty.declLabels, Defs.labels]
  | _, _, _, _, .trmObj _ _ => by simp [Ty.declLabels, Defs.labels]
  | _, _, _, _, .and h₁ h₂ => by
      simp only [Ty.declLabels, Defs.labels, h₁.declLabels_eq, h₂.declLabels_eq]

theorem DefsTy.distinctLabels : ∀ {s : Sig} {Γ : Ctx s} {d : Defs s} {T : Ty s},
    DefsTy Γ d T → Defs.Distinct d → Ty.DistinctLabels T
  | _, _, _, _, .typ, _ => .typ
  | _, _, _, _, .trm _, _ => .fld
  | _, _, _, _, .trmObj _ _, _ => .vfld
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
  | .sngl _ => by simp [Ty.witnesses, Ty.declLabels, FCdot.Witnesses.labels]
  | .typ A S T => by simp [Ty.witnesses, Ty.declLabels, FCdot.Witnesses.labels]
  | .fld a T => by simp [Ty.witnesses, Ty.declLabels, FCdot.Witnesses.labels]
  | .vfld a T => by simp [Ty.witnesses, Ty.declLabels, FCdot.Witnesses.labels]
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
  | .sngl _, h => by cases h
  | .typ A S T, _ => by
      rw [Ty.witnesses]
      exact .cons .nil (by simp [FCdot.Witnesses.labels])
  | .fld a T, _ => by
      rw [Ty.witnesses]
      exact .cons .nil (by simp [FCdot.Witnesses.labels])
  | .vfld a T, _ => by
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

/-- The definition equality that the templates of `T` read, at definition offset `e`,
a stable field included.  It is also the entry the decision-26 cast of a plain field
reads. -/
def Ty.EqSpec {s : Sig} (src : FCdot.Telescope (s,x)) : Ty (s,x) → Nat → Prop
  | .typ A S _, e => src ∋ (e ↦ (.var .here) ∙ A ≐ S.translate)
  | .fld a T, e => src ∋ (e ↦ (.var .here) ∙ a ≐ T.translate)
  | .vfld a T, e => src ∋ (e ↦ (.var .here) ∙ a ≐ T.translate)
  | .and S T, e => Ty.EqSpec src S e ∧ Ty.EqSpec src T (e + S.witnesses.length)
  | _, _ => True

/-- The field presences that the templates of `T` inherit, at presence offset
`off`, a stable field included.  `Ty.fieldLabels` puts the right conjunct first, so on
an intersection it is the right conjunct that starts at `off`. -/
def Ty.HasSpec {s : Sig} (src : FCdot.Telescope (s,x)) : Ty (s,x) → Nat → Prop
  | .fld a _, off => src ∋ (off ↦ ∋ a)
  | .vfld a _, off => src ∋ (off ↦ ∋ a)
  | .and S T, off => Ty.HasSpec src S (off + T.fieldLabels.length) ∧ Ty.HasSpec src T off
  | _, _ => True

/-- The stable presences that the templates of `T` copy, at offset `off`, right
conjunct first, as `Ty.valLabels`. -/
def Ty.ValSpec {s : Sig} (src : FCdot.Telescope (s,x)) : Ty (s,x) → Nat → Prop
  | .vfld a _, off => src ∋ (off ↦ ∋ᵛ a)
  | .and S T, off => Ty.ValSpec src S (off + T.valLabels.length) ∧ Ty.ValSpec src T off
  | _, _ => True

/-! ## The morphism of a literal -/

theorem litMorphism_and_fst {s s' : Sig} (S T : Ty s) (e h v : Nat) :
    (litMorphism (s' := s') (.and S T) e h v).1 =
      (litMorphism S e (h + T.fieldLabels.length) (v + T.valLabels.length)).1.append
        (litMorphism T
          (litMorphism (s' := s') S e (h + T.fieldLabels.length) (v + T.valLabels.length)).2.1
          h v).1 := by
  simp only [litMorphism]

theorem litMorphism_and_eq {s s' : Sig} (S T : Ty s) (e h v : Nat) :
    (litMorphism (s' := s') (.and S T) e h v).2.1 =
      (litMorphism (s' := s') T
        (litMorphism (s' := s') S e (h + T.fieldLabels.length) (v + T.valLabels.length)).2.1
        h v).2.1 := by
  simp only [litMorphism]

theorem litMorphism_and_has {s s' : Sig} (S T : Ty s) (e h v : Nat) :
    (litMorphism (s' := s') (.and S T) e h v).2.2.1 =
      (litMorphism (s' := s') S e (h + T.fieldLabels.length) (v + T.valLabels.length)).2.2.1 := by
  simp only [litMorphism]

theorem litMorphism_and_val {s s' : Sig} (S T : Ty s) (e h v : Nat) :
    (litMorphism (s' := s') (.and S T) e h v).2.2.2 =
      (litMorphism (s' := s') S e (h + T.fieldLabels.length) (v + T.valLabels.length)).2.2.2 := by
  simp only [litMorphism]

/-- The three counters advance by the witnesses, the field labels and the stable field
labels of the type. -/
theorem litMorphism_offsets {s : Sig} : ∀ (T : Ty (s,x)) (e h v : Nat),
    (litMorphism (s' := s) T e h v).2.1 = e + T.witnesses.length ∧
      (litMorphism (s' := s) T e h v).2.2.1 = h + T.fieldLabels.length ∧
      (litMorphism (s' := s) T e h v).2.2.2 = v + T.valLabels.length
  | .top, e, h, v => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, Ty.valLabels, FCdot.Witnesses.length]
  | .bot, e, h, v => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, Ty.valLabels, FCdot.Witnesses.length]
  | .sngl _, e, h, v => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, Ty.valLabels, FCdot.Witnesses.length]
  | .sel _ _, e, h, v => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, Ty.valLabels, FCdot.Witnesses.length]
  | .all _ _, e, h, v => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, Ty.valLabels, FCdot.Witnesses.length]
  | .mu _, e, h, v => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, Ty.valLabels, FCdot.Witnesses.length]
  | .typ A S T, e, h, v => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, Ty.valLabels, FCdot.Witnesses.length]
  | .fld a T, e, h, v => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, Ty.valLabels, FCdot.Witnesses.length]
  | .vfld a T, e, h, v => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, Ty.valLabels, FCdot.Witnesses.length]
  | .and S T, e, h, v => by
      have hS := litMorphism_offsets S e (h + T.fieldLabels.length)
        (v + T.valLabels.length)
      have hT := litMorphism_offsets T
        (litMorphism (s' := s) S e (h + T.fieldLabels.length) (v + T.valLabels.length)).2.1 h v
      refine ⟨?_, ?_, ?_⟩
      · rw [litMorphism_and_eq, hT.1, hS.1, Ty.witnesses, FCdot.Witnesses.length_append]
        omega
      · rw [litMorphism_and_has, hS.2.1, Ty.fieldLabels, List.length_append]
        omega
      · rw [litMorphism_and_val, hS.2.2, Ty.valLabels, List.length_append]
        omega

/-- `litMorphism` has `.none` sides and copies by index only, so it is table-only.
This is why the body of a `trmObj` field is stable. -/
theorem litMorphism_tableOnly {s s' : Sig} :
    ∀ (T : Ty s) (e h v : Nat), (litMorphism (s' := s') T e h v).1.tableOnly = true
  | .top, _, _, _ => by simp [litMorphism, FCdot.Morphism.tableOnly]
  | .bot, _, _, _ => by simp [litMorphism, FCdot.Morphism.tableOnly]
  | .sngl _, _, _, _ => by simp [litMorphism, FCdot.Morphism.tableOnly]
  | .sel _ _, _, _, _ => by simp [litMorphism, FCdot.Morphism.tableOnly]
  | .all _ _, _, _, _ => by simp [litMorphism, FCdot.Morphism.tableOnly]
  | .mu _, _, _, _ => by simp [litMorphism, FCdot.Morphism.tableOnly]
  | .typ _ _ _, _, _, _ => by
      simp [litMorphism, FCdot.Morphism.tableOnly, FCdot.Side.tableOnly]
  | .fld _ _, _, _, _ => by
      simp [litMorphism, FCdot.Morphism.tableOnly, FCdot.Side.tableOnly]
  | .vfld _ _, _, _, _ => by
      simp [litMorphism, FCdot.Morphism.tableOnly, FCdot.Side.tableOnly]
  | .and S T, e, h, v => by
      rw [litMorphism_and_fst, FCdot.Morphism.tableOnly_append, litMorphism_tableOnly S,
        litMorphism_tableOnly T]
      rfl

/-- The literal's coercion is table-only. -/
theorem litCo_tableOnly {s : Sig} (T : Ty (s,x)) : (litCo T).tableOnly = true := by
  simp only [litCo, FCdot.LeCo.tableOnly, litMorphism_tableOnly]

theorem litMorphism_typed {s : Sig} {Γ : FCdot.Ctx s} {src : FCdot.Telescope (s,x)} :
    ∀ (T : Ty (s,x)), Ty.LiteralShape T → ∀ (e h v : Nat),
      Ty.EqSpec src T e → Ty.HasSpec src T h → Ty.ValSpec src T v →
      Γ ⊢ (litMorphism T e h v).1 : src ⇒ T.telSelf
  | .top, hsh, _, _, _, _, _, _ => by cases hsh
  | .bot, hsh, _, _, _, _, _, _ => by cases hsh
  | .sngl _, hsh, _, _, _, _, _, _ => by cases hsh
  | .sel _ _, hsh, _, _, _, _, _, _ => by cases hsh
  | .all _ _, hsh, _, _, _, _, _, _ => by cases hsh
  | .mu _, hsh, _, _, _, _, _, _ => by cases hsh
  | .typ A S T', hsh, e, h, v, heq, _, _ => by
      cases hsh
      rw [Ty.EqSpec] at heq
      rw [litMorphism, Ty.telSelf_typ]
      exact .leEq (.leEqSym .nil heq .none .none) heq .none .none
  | .fld a T', _, e, h, v, heq, hhas, _ => by
      rw [Ty.EqSpec] at heq
      rw [Ty.HasSpec] at hhas
      rw [litMorphism, Ty.telSelf_fld]
      exact .leEq (.has .nil hhas) heq .none .none
  | .vfld a T', _, e, h, v, heq, hhas, hval => by
      rw [Ty.EqSpec] at heq
      rw [Ty.HasSpec] at hhas
      rw [Ty.ValSpec] at hval
      rw [litMorphism, Ty.telSelf_vfld]
      exact .leEq (.hasVal (.has .nil hhas) hval) heq .none .none
  | .and S T', hsh, e, h, v, heq, hhas, hval => by
      cases hsh with
      | and hS hT =>
          rw [Ty.EqSpec] at heq
          rw [Ty.HasSpec] at hhas
          rw [Ty.ValSpec] at hval
          obtain ⟨heq₁, heq₂⟩ := heq
          obtain ⟨hhas₁, hhas₂⟩ := hhas
          obtain ⟨hval₁, hval₂⟩ := hval
          have hoff := litMorphism_offsets S e (h + T'.fieldLabels.length)
            (v + T'.valLabels.length)
          have ih₁ := litMorphism_typed (Γ := Γ) S hS e (h + T'.fieldLabels.length)
            (v + T'.valLabels.length) heq₁ hhas₁ hval₁
          have ih₂ := litMorphism_typed (Γ := Γ) T' hT
            (litMorphism (s' := s) S e (h + T'.fieldLabels.length) (v + T'.valLabels.length)).2.1
            h v (by rw [hoff.1]; exact heq₂) hhas₂ hval₂
          rw [litMorphism_and_fst, Ty.telSelf_and]
          exact ih₁.append ih₂

/-! ## The definition equalities and presences of a literal's own telescope -/

theorem eqSpec_of {s : Sig} {Wall : FCdot.Witnesses (s,x)} (hdist : Wall.Distinct)
    (lsAll vlsAll : List Label) :
    ∀ (T : Ty (s,x)) (e : Nat),
      (∀ i l X, FCdot.Witnesses.At T.witnesses i l X → FCdot.Witnesses.At Wall (e + i) l X) →
      Ty.EqSpec (FCdot.Telescope.ofLiteral Wall lsAll vlsAll) T e
  | .top, _, _ => by simp [Ty.EqSpec]
  | .bot, _, _ => by simp [Ty.EqSpec]
  | .sel _ _, _, _ => by simp [Ty.EqSpec]
  | .all _ _, _, _ => by simp [Ty.EqSpec]
  | .mu _, _, _ => by simp [Ty.EqSpec]
  | .sngl _, _, _ => by simp [Ty.EqSpec]
  | .typ A S T', e, hpos => by
      simp only [Ty.witnesses] at hpos
      have h1 := hpos 0 A S.translate FCdot.Witnesses.At.hereNil
      rw [Nat.add_zero] at h1
      have h2 := FCdot.Witnesses.eqEntriesOf_At FCdot.BVar.here Wall h1
      rw [h1.get hdist] at h2
      rw [Ty.EqSpec]
      exact FCdot.Telescope.At.hasValEntries vlsAll (FCdot.Telescope.At.hasEntries lsAll h2)
  | .fld a T', e, hpos => by
      simp only [Ty.witnesses] at hpos
      have h1 := hpos 0 a T'.translate FCdot.Witnesses.At.hereNil
      rw [Nat.add_zero] at h1
      have h2 := FCdot.Witnesses.eqEntriesOf_At FCdot.BVar.here Wall h1
      rw [h1.get hdist] at h2
      rw [Ty.EqSpec]
      exact FCdot.Telescope.At.hasValEntries vlsAll (FCdot.Telescope.At.hasEntries lsAll h2)
  | .vfld a T', e, hpos => by
      simp only [Ty.witnesses] at hpos
      have h1 := hpos 0 a T'.translate FCdot.Witnesses.At.hereNil
      rw [Nat.add_zero] at h1
      have h2 := FCdot.Witnesses.eqEntriesOf_At FCdot.BVar.here Wall h1
      rw [h1.get hdist] at h2
      rw [Ty.EqSpec]
      exact FCdot.Telescope.At.hasValEntries vlsAll (FCdot.Telescope.At.hasEntries lsAll h2)
  | .and S T', e, hpos => by
      simp only [Ty.witnesses] at hpos
      rw [Ty.EqSpec]
      refine ⟨eqSpec_of hdist lsAll vlsAll S e
        (fun i l X hAt => hpos i l X (hAt.append_left _)), ?_⟩
      refine eqSpec_of hdist lsAll vlsAll T' (e + S.witnesses.length) (fun i l X hAt => ?_)
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
  | .sngl _, _, _ => by simp [Ty.HasSpec]
  | .typ _ _ _, _, _ => by simp [Ty.HasSpec]
  | .fld a T', off, hpos => by
      simp only [Ty.fieldLabels] at hpos
      have h1 := hpos 0 a .here
      rw [Nat.add_zero] at h1
      rw [Ty.HasSpec]
      exact h1
  | .vfld a T', off, hpos => by
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

theorem valSpec_of {s : Sig} {src : FCdot.Telescope (s,x)} :
    ∀ (T : Ty (s,x)) (off : Nat),
      (∀ i l, FCdot.LabelAt T.valLabels i l → src ∋ (off + i ↦ ∋ᵛ l)) →
      Ty.ValSpec src T off
  | .top, _, _ => by simp [Ty.ValSpec]
  | .bot, _, _ => by simp [Ty.ValSpec]
  | .sel _ _, _, _ => by simp [Ty.ValSpec]
  | .all _ _, _, _ => by simp [Ty.ValSpec]
  | .mu _, _, _ => by simp [Ty.ValSpec]
  | .sngl _, _, _ => by simp [Ty.ValSpec]
  | .typ _ _ _, _, _ => by simp [Ty.ValSpec]
  | .fld _ _, _, _ => by simp [Ty.ValSpec]
  | .vfld a T', off, hpos => by
      simp only [Ty.valLabels] at hpos
      have h1 := hpos 0 a .here
      rw [Nat.add_zero] at h1
      rw [Ty.ValSpec]
      exact h1
  | .and S T', off, hpos => by
      simp only [Ty.valLabels] at hpos
      rw [Ty.ValSpec]
      refine ⟨?_, valSpec_of T' off (fun i l hAt => hpos i l (hAt.append_left _))⟩
      refine valSpec_of S (off + T'.valLabels.length) (fun i l hAt => ?_)
      have hh := hpos (T'.valLabels.length + i) l (FCdot.LabelAt.append_right hAt T'.valLabels)
      rw [show off + (T'.valLabels.length + i) = off + T'.valLabels.length + i by omega] at hh
      exact hh

/-! ## The coercion from a literal's precise type to its declared type -/

theorem litCo_typed_of_shape {s : Sig} {Γ : FCdot.Ctx s} {T : Ty (s,x)}
    (hsh : Ty.LiteralShape T) (hdl : Ty.DistinctLabels T) :
    Γ ⊢ litCo T : T.literalTy ≤ (Ty.mu T).translate := by
  have hW : T.witnesses.Distinct := Ty.witnesses_distinct T hdl
  have hlen : (T.witnesses.eqEntries).length = T.witnesses.length :=
    FCdot.Witnesses.eqEntriesOf_length _ _ _
  rw [Ty.translate_mu]
  refine .obj (litMorphism_typed T hsh 0 T.witnesses.length
    (T.witnesses.length + T.fieldLabels.length) ?_ ?_ ?_)
  · exact eqSpec_of hW T.fieldLabels T.valLabels T 0
      (fun i l X hAt => by rw [Nat.zero_add]; exact hAt)
  · refine hasSpec_of T T.witnesses.length (fun i l hAt => ?_)
    have hh := FCdot.Telescope.hasEntries_At hAt (T.witnesses.eqEntries)
    rw [hlen] at hh
    exact FCdot.Telescope.At.hasValEntries _ hh
  · refine valSpec_of T (T.witnesses.length + T.fieldLabels.length) (fun i l hAt => ?_)
    have hh := FCdot.Telescope.hasValEntries_At hAt
      ((T.witnesses.eqEntries).hasEntries T.fieldLabels)
    rw [FCdot.Telescope.length_hasEntries, hlen] at hh
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
              (.transparent T.literalTy (T.blocks d)))
  | .consSelf Γ d T, hwf, .there y => by
      cases hwf with
      | consSelf hwf' _ _ =>
          rw [Ctx.lookup_consSelf_there, Ctx.varAtom_consSelf_there, Ty.translate_weaken]
          exact (Ctx.varAtom_typed Γ hwf' y).weaken
            (.transparent T.literalTy (T.blocks d))

/-! ## The positions `SubDecl` reads

`Ty.typIdx`, `Ty.fldIdx` and `Ty.vfldIdx` answer exactly when the declaration reader
answers, and the answer is the position of the member in `telSelfAt self D`. -/

theorem Ty.typIdx_none {s : Sig} {self : BVar s .var} {A : Label} :
    ∀ {D : Ty s} (off : Nat), D.lookupTypDecl A = none → D.typIdx self A off = none
  | .typ A' _ _, off, h => by
      simp only [Ty.lookupTypDecl] at h
      simp only [Ty.typIdx]
      split
      · next hA => rw [if_pos hA] at h; cases h
      · rfl
  | .and S T, off, h => by
      simp only [Ty.lookupTypDecl] at h
      simp only [Ty.typIdx]
      cases hT : T.lookupTypDecl A with
      | some _ => rw [hT] at h; cases h
      | none =>
          rw [hT, Option.none_or] at h
          rw [Ty.typIdx_none _ hT, Option.none_or, Ty.typIdx_none _ h]
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .fld _ _, _, _ => rfl
  | .vfld _ _, _, _ => rfl
  | .sngl _, _, _ => rfl
  | .sel _ _, _, _ => rfl
  | .mu _, _, _ => rfl
  | .all _ _, _, _ => rfl

theorem Ty.fldIdx_none {s : Sig} {self : BVar s .var} {a : Label} :
    ∀ {D : Ty s} (off : Nat), D.lookupFldDecl a = none → D.fldIdx self a off = none
  | .fld a' _, off, h => by
      simp only [Ty.lookupFldDecl] at h
      simp only [Ty.fldIdx]
      split
      · next ha => rw [if_pos ha] at h; cases h
      · rfl
  | .and S T, off, h => by
      simp only [Ty.lookupFldDecl] at h
      simp only [Ty.fldIdx]
      cases hT : T.lookupFldDecl a with
      | some _ => rw [hT] at h; cases h
      | none =>
          rw [hT, Option.none_or] at h
          rw [Ty.fldIdx_none _ hT, Option.none_or, Ty.fldIdx_none _ h]
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .typ _ _ _, _, _ => rfl
  | .vfld _ _, _, _ => rfl
  | .sngl _, _, _ => rfl
  | .sel _ _, _, _ => rfl
  | .mu _, _, _ => rfl
  | .all _ _, _, _ => rfl

theorem Ty.vfldIdx_none {s : Sig} {self : BVar s .var} {a : Label} :
    ∀ {D : Ty s} (off : Nat), D.lookupVfldDecl a = none → D.vfldIdx self a off = none
  | .vfld a' _, off, h => by
      simp only [Ty.lookupVfldDecl] at h
      simp only [Ty.vfldIdx]
      split
      · next ha => rw [if_pos ha] at h; cases h
      · rfl
  | .and S T, off, h => by
      simp only [Ty.lookupVfldDecl] at h
      simp only [Ty.vfldIdx]
      cases hT : T.lookupVfldDecl a with
      | some _ => rw [hT] at h; cases h
      | none =>
          rw [hT, Option.none_or] at h
          rw [Ty.vfldIdx_none _ hT, Option.none_or, Ty.vfldIdx_none _ h]
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .typ _ _ _, _, _ => rfl
  | .fld _ _, _, _ => rfl
  | .sngl _, _, _ => rfl
  | .sel _ _, _, _ => rfl
  | .mu _, _, _ => rfl
  | .all _ _, _, _ => rfl

/-- The positions `SubDecl.translate` reads at a type member: the lower bound at `i`,
the upper bound at `i + 1`. -/
theorem Ty.typIdx_spec {s : Sig} {self : BVar s .var} :
    ∀ {D : Ty s} {A : Label} {S₁ T₁ : Ty s} (off : Nat),
    D.lookupTypDecl A = some (S₁, T₁) →
    ∃ i, D.typIdx self A off = some (off + i) ∧
      FCdot.Telescope.At (D.telSelfAt self) i (.le S₁.translate (.sel (.var self) A)) ∧
      FCdot.Telescope.At (D.telSelfAt self) (i + 1) (.le (.sel (.var self) A) T₁.translate)
  | .typ A' S T, A, S₁, T₁, off, h => by
      simp only [Ty.lookupTypDecl] at h
      split at h
      · next hA =>
        subst hA
        cases h
        refine ⟨0, by simp [Ty.typIdx], ?_, ?_⟩
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.zero_two _ _
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.one_two _ _
      · cases h
  | .and S T, A, S₁, T₁, off, h => by
      simp only [Ty.lookupTypDecl] at h
      rcases Option.or_eq_some_cases h with hT | ⟨hT, hS⟩
      · obtain ⟨i, hi, h1, h2⟩ :=
          Ty.typIdx_spec (self := self) (off + (S.telSelfAt self).length) hT
        refine ⟨(S.telSelfAt self).length + i, ?_, ?_, ?_⟩
        · simp only [Ty.typIdx, hi, Option.some_or]
          rw [Nat.add_assoc]
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.append_right _ h1
        · simp only [Ty.telSelfAt]; rw [Nat.add_assoc]
          exact FCdot.Telescope.At.append_right _ h2
      · obtain ⟨i, hi, h1, h2⟩ := Ty.typIdx_spec (self := self) off hS
        refine ⟨i, ?_, ?_, ?_⟩
        · simp only [Ty.typIdx, Ty.typIdx_none _ hT, hi, Option.none_or]
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.append_left' h1 _
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.append_left' h2 _
  | .top, _, _, _, _, h => by simp [Ty.lookupTypDecl] at h
  | .bot, _, _, _, _, h => by simp [Ty.lookupTypDecl] at h
  | .fld _ _, _, _, _, _, h => by simp [Ty.lookupTypDecl] at h
  | .vfld _ _, _, _, _, _, h => by simp [Ty.lookupTypDecl] at h
  | .sngl _, _, _, _, _, h => by simp [Ty.lookupTypDecl] at h
  | .sel _ _, _, _, _, _, h => by simp [Ty.lookupTypDecl] at h
  | .mu _, _, _, _, _, h => by simp [Ty.lookupTypDecl] at h
  | .all _ _, _, _, _, _, h => by simp [Ty.lookupTypDecl] at h

/-- The positions `SubDecl.translate` reads at a plain field: `∋ a` at `i`, the bound
at `i + 1`. -/
theorem Ty.fldIdx_spec {s : Sig} {self : BVar s .var} :
    ∀ {D : Ty s} {a : Label} {T₁ : Ty s} (off : Nat),
    D.lookupFldDecl a = some T₁ →
    ∃ i, D.fldIdx self a off = some (off + i) ∧
      FCdot.Telescope.At (D.telSelfAt self) i (.has a) ∧
      FCdot.Telescope.At (D.telSelfAt self) (i + 1) (.le (.sel (.var self) a) T₁.translate)
  | .fld a' T, a, T₁, off, h => by
      simp only [Ty.lookupFldDecl] at h
      split at h
      · next ha =>
        subst ha
        cases h
        refine ⟨0, by simp [Ty.fldIdx], ?_, ?_⟩
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.zero_two _ _
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.one_two _ _
      · cases h
  | .and S T, a, T₁, off, h => by
      simp only [Ty.lookupFldDecl] at h
      rcases Option.or_eq_some_cases h with hT | ⟨hT, hS⟩
      · obtain ⟨i, hi, h1, h2⟩ :=
          Ty.fldIdx_spec (self := self) (off + (S.telSelfAt self).length) hT
        refine ⟨(S.telSelfAt self).length + i, ?_, ?_, ?_⟩
        · simp only [Ty.fldIdx, hi, Option.some_or]
          rw [Nat.add_assoc]
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.append_right _ h1
        · simp only [Ty.telSelfAt]; rw [Nat.add_assoc]
          exact FCdot.Telescope.At.append_right _ h2
      · obtain ⟨i, hi, h1, h2⟩ := Ty.fldIdx_spec (self := self) off hS
        refine ⟨i, ?_, ?_, ?_⟩
        · simp only [Ty.fldIdx, Ty.fldIdx_none _ hT, hi, Option.none_or]
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.append_left' h1 _
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.append_left' h2 _
  | .top, _, _, _, h => by simp [Ty.lookupFldDecl] at h
  | .bot, _, _, _, h => by simp [Ty.lookupFldDecl] at h
  | .typ _ _ _, _, _, _, h => by simp [Ty.lookupFldDecl] at h
  | .vfld _ _, _, _, _, h => by simp [Ty.lookupFldDecl] at h
  | .sngl _, _, _, _, h => by simp [Ty.lookupFldDecl] at h
  | .sel _ _, _, _, _, h => by simp [Ty.lookupFldDecl] at h
  | .mu _, _, _, _, h => by simp [Ty.lookupFldDecl] at h
  | .all _ _, _, _, _, h => by simp [Ty.lookupFldDecl] at h

/-- The positions `SubDecl.translate` reads at a stable field: `∋ a` at `i`, `∋ᵛ a` at
`i + 1`, the bound at `i + 2`. -/
theorem Ty.vfldIdx_spec {s : Sig} {self : BVar s .var} :
    ∀ {D : Ty s} {a : Label} {T₁ : Ty s} (off : Nat),
    D.lookupVfldDecl a = some T₁ →
    ∃ i, D.vfldIdx self a off = some (off + i) ∧
      FCdot.Telescope.At (D.telSelfAt self) i (.has a) ∧
      FCdot.Telescope.At (D.telSelfAt self) (i + 1) (.hasVal a) ∧
      FCdot.Telescope.At (D.telSelfAt self) (i + 2) (.le (.sel (.var self) a) T₁.translate)
  | .vfld a' T, a, T₁, off, h => by
      simp only [Ty.lookupVfldDecl] at h
      split at h
      · next ha =>
        subst ha
        cases h
        refine ⟨0, by simp [Ty.vfldIdx], ?_, ?_, ?_⟩
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.zero_three _ _ _
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.one_three _ _ _
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.two_three _ _ _
      · cases h
  | .and S T, a, T₁, off, h => by
      simp only [Ty.lookupVfldDecl] at h
      rcases Option.or_eq_some_cases h with hT | ⟨hT, hS⟩
      · obtain ⟨i, hi, h1, h2, h3⟩ :=
          Ty.vfldIdx_spec (self := self) (off + (S.telSelfAt self).length) hT
        refine ⟨(S.telSelfAt self).length + i, ?_, ?_, ?_, ?_⟩
        · simp only [Ty.vfldIdx, hi, Option.some_or]
          rw [Nat.add_assoc]
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.append_right _ h1
        · simp only [Ty.telSelfAt]; rw [Nat.add_assoc]
          exact FCdot.Telescope.At.append_right _ h2
        · simp only [Ty.telSelfAt]; rw [Nat.add_assoc]
          exact FCdot.Telescope.At.append_right _ h3
      · obtain ⟨i, hi, h1, h2, h3⟩ := Ty.vfldIdx_spec (self := self) off hS
        refine ⟨i, ?_, ?_, ?_, ?_⟩
        · simp only [Ty.vfldIdx, Ty.vfldIdx_none _ hT, hi, Option.none_or]
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.append_left' h1 _
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.append_left' h2 _
        · simp only [Ty.telSelfAt]; exact FCdot.Telescope.At.append_left' h3 _
  | .top, _, _, _, h => by simp [Ty.lookupVfldDecl] at h
  | .bot, _, _, _, h => by simp [Ty.lookupVfldDecl] at h
  | .typ _ _ _, _, _, _, h => by simp [Ty.lookupVfldDecl] at h
  | .fld _ _, _, _, _, h => by simp [Ty.lookupVfldDecl] at h
  | .sngl _, _, _, _, h => by simp [Ty.lookupVfldDecl] at h
  | .sel _ _, _, _, _, h => by simp [Ty.lookupVfldDecl] at h
  | .mu _, _, _, _, h => by simp [Ty.lookupVfldDecl] at h
  | .all _ _, _, _, _, h => by simp [Ty.lookupVfldDecl] at h

/-! ## The path of a path image -/

/-- The path image of a path typing is at the translated path. -/
theorem PathTy.translatePath_path : ∀ {s : Sig} {Γ : Ctx s} {p : Path s} {T : Ty s}
    (d : PathTy Γ p T), d.translatePath.path = p.translate
  | _, Γ, _, _, .var (x := x) => by
      rw [PathTy.translatePath, FCdot.Atom.path_toPathCo, Ctx.varAtom_root]
      rfl
  | _, _, _, _, .sel h => by
      rw [PathTy.translatePath]
      simp only [FCdot.PathCo.path, PathTy.translatePath_path h, Path.translate]
  | _, _, _, _, .recI h _ => by
      rw [PathTy.translatePath]
      simp only [FCdot.PathCo.path, PathTy.translatePath_path h]
  | _, _, _, _, .recE h _ => by
      rw [PathTy.translatePath]
      simp only [FCdot.PathCo.path, PathTy.translatePath_path h]
  | _, _, _, _, .andI h₁ _ => by
      rw [PathTy.translatePath]
      simp only [FCdot.PathCo.path, intoPath_path, PathTy.translatePath_path h₁]
  | _, _, _, _, .sub h _ => by
      rw [PathTy.translatePath]
      simp only [FCdot.PathCo.path, PathTy.translatePath_path h]
  | _, _, _, _, .snglRefl h => by
      rw [PathTy.translatePath]
      simp only [FCdot.PathCo.path, PathTy.translatePath_path h]
  | _, _, _, _, .snglTrans _ _ => by
      rw [PathTy.translatePath]
      simp only [FCdot.PathCo.path]
  | _, _, _, _, .snglSym _ h₂ => by
      rw [PathTy.translatePath]
      simp only [FCdot.PathCo.path, PathTy.translatePath_path h₂]
  | _, _, _, _, .snglInv _ => by
      rw [PathTy.translatePath]
      simp only [FCdot.PathCo.path]
  | _, _, _, _, .snglSel _ h₂ => by
      rw [PathTy.translatePath]
      simp only [FCdot.PathCo.path, PathTy.translatePath_path h₂, Path.translate]

/-! ## Typedness of the evidence translation -/

mutual

theorem SelfFree.translate_typed : ∀ {s : Sig} {Γ : Ctx s} {X Y : Ty (s,x)}
    (d : SelfFree Γ X Y), Γ.Wf →
    FCdot.Side.HasType Γ.translate d.translate X.translate Y.translate
  | _, _, _, _, .refl, _ => by rw [SelfFree.translate]; exact .none
  | _, _, _, _, .bot, _ => by rw [SelfFree.translate, Ty.translate_bot]; exact .bot
  | _, _, _, _, .top, _ => by rw [SelfFree.translate, Ty.translate_top]; exact .top
  | _, _, _, _, .closed d, hwf => by
      rw [SelfFree.translate, Ty.translate_weaken, Ty.translate_weaken]
      exact .some (d.translate_typed hwf)

theorem SubDecl.translate_typed : ∀ {s : Sig} {Γ : Ctx s} {D D' : Ty (s,x)}
    (d : SubDecl Γ D D'), Γ.Wf →
    FCdot.Morphism.HasType Γ.translate D.telSelf d.translate D'.telSelf
  | _, _, _, _, .top, _ => by rw [SubDecl.translate, Ty.telSelf_top]; exact .nil
  | _, _, _, _, .typ hl sf₁ sf₂, hwf => by
      obtain ⟨i, hi, h1, h2⟩ := Ty.typIdx_spec (self := .here) 0 hl
      rw [SubDecl.translate]
      simp only [hi, Option.getD_some, Nat.zero_add]
      rw [Ty.telSelf_typ]
      exact .le (.le .nil h1 (sf₁.translate_typed hwf) .none) h2 .none (sf₂.translate_typed hwf)
  | _, _, _, _, .fld hl sf, hwf => by
      obtain ⟨i, hi, h1, h2⟩ := Ty.fldIdx_spec (self := .here) 0 hl
      rw [SubDecl.translate]
      simp only [hi, Option.getD_some, Nat.zero_add]
      rw [Ty.telSelf_fld]
      exact .le (.has .nil h1) h2 .none (sf.translate_typed hwf)
  | _, _, _, _, .vfld hl sf, hwf => by
      obtain ⟨i, hi, h1, h2, h3⟩ := Ty.vfldIdx_spec (self := .here) 0 hl
      rw [SubDecl.translate]
      simp only [hi, Option.getD_some, Nat.zero_add]
      rw [Ty.telSelf_vfld]
      exact .le (.hasVal (.has .nil h1) h2) h3 .none (sf.translate_typed hwf)
  | _, _, _, _, .vfldToFld hl sf, hwf => by
      obtain ⟨i, hi, h1, _, h3⟩ := Ty.vfldIdx_spec (self := .here) 0 hl
      rw [SubDecl.translate]
      simp only [hi, Option.getD_some, Nat.zero_add]
      rw [Ty.telSelf_fld]
      exact .le (.has .nil h1) h3 .none (sf.translate_typed hwf)
  | _, _, _, _, .and d₁ d₂, hwf => by
      rw [SubDecl.translate, Ty.telSelf_and]
      exact (d₁.translate_typed hwf).append (d₂.translate_typed hwf)

theorem Sub.translate_typed : ∀ {s : Sig} {Γ : Ctx s} {S T : Ty s} (d : Sub Γ S T), Γ.Wf →
    Γ.translate ⊢ d.translate : S.translate ≤ T.translate
  | _, _, _, _, .top, _ => by rw [Sub.translate, Ty.translate_top]; exact .top
  | _, _, _, _, .bot, _ => by rw [Sub.translate, Ty.translate_bot]; exact .bot
  | _, _, _, _, .refl, _ => by rw [Sub.translate]; exact .refl
  | _, _, _, _, .trans d₁ d₂, hwf => by
      rw [Sub.translate]
      exact .trans (d₁.translate_typed hwf) (d₂.translate_typed hwf)
  | _, _, _, _, @Sub.and1 _ _ S T, _ => by
      cases hS : S.isObj with
      | true =>
          rw [Sub.translate, hS, if_pos rfl, Ty.tel_and, Ty.translate_and, Ty.translate_isObj hS]
          exact .obj (identityMorphism_typed_left _ _ (Ty.tel_closedBnds S))
      | false =>
          rw [Sub.translate, hS, if_neg Bool.false_ne_true, Ty.tel_and, Ty.translate_and]
          exact .bound ((Ty.tel_bnd_at hS).append_left' T.tel)
  | _, _, _, _, @Sub.and2 _ _ S T, _ => by
      cases hT : T.isObj with
      | true =>
          rw [Sub.translate, hT, if_pos rfl, Ty.tel_and, Ty.translate_and, Ty.translate_isObj hT]
          exact .obj (identityMorphism_typed_right _ _ (Ty.tel_closedBnds T))
      | false =>
          rw [Sub.translate, hT, if_neg Bool.false_ne_true, Ty.tel_and, Ty.translate_and]
          refine .bound ?_
          have h0 := FCdot.Telescope.At.append_right S.tel (Ty.tel_bnd_at hT)
          rwa [Nat.add_zero] at h0
  | _, _, _, _, .and d₁ d₂, hwf => by
      rw [Sub.translate, Ty.translate_and]
      exact .pair (into_typed (d₁.translate_typed hwf)) (into_typed (d₂.translate_typed hwf))
  | _, _, _, _, .fld d, hwf => by
      rw [Sub.translate]
      simp only [Ty.translate_fld, Ty.tel_fld]
      exact .obj (.le (.has .nil (FCdot.Telescope.At.zero_two _ _))
        (FCdot.Telescope.At.one_two _ _) .none (.some (d.translate_typed hwf)))
  | _, _, _, _, .vfld d, hwf => by
      rw [Sub.translate]
      simp only [Ty.translate_vfld, Ty.tel_vfld]
      exact .obj (.le (.hasVal (.has .nil (FCdot.Telescope.At.zero_three _ _ _))
          (FCdot.Telescope.At.one_three _ _ _))
        (FCdot.Telescope.At.two_three _ _ _) .none (.some (d.translate_typed hwf)))
  | _, _, _, _, .vfldToFld, _ => by
      rw [Sub.translate]
      simp only [Ty.translate_vfld, Ty.translate_fld, Ty.tel_vfld, Ty.tel_fld]
      exact .obj (.le (.has .nil (FCdot.Telescope.At.zero_three _ _ _))
        (FCdot.Telescope.At.two_three _ _ _) .none .none)
  | _, _, _, _, .typ d₁ d₂, hwf => by
      rw [Sub.translate]
      simp only [Ty.translate_typ, Ty.tel_typ]
      exact .obj (.le (.le .nil (FCdot.Telescope.At.zero_two _ _)
          (.some (d₁.translate_typed hwf)) .none)
        (FCdot.Telescope.At.one_two _ _) .none (.some (d₂.translate_typed hwf)))
  | _, _, _, _, @Sub.selUpper _ _ p A S T h, hwf => by
      obtain ⟨hP, hpath⟩ := h.translatePath_typed hwf
      rw [Ty.translate_typ, Ty.tel_typ] at hP
      have hm := FCdot.LeCo.HasType.memberP hP .refl (FCdot.Telescope.At.one_two _ _)
      rw [hpath, FCdot.Ty.weaken_substPath] at hm
      rw [Sub.translate, Ty.translate_selP, Ty.translate_typ, Ty.tel_typ]
      simpa [FCdot.Ty.substPath_sel, FCdot.Path.substPath] using hm
  | _, _, _, _, @Sub.selLower _ _ p A S T h, hwf => by
      obtain ⟨hP, hpath⟩ := h.translatePath_typed hwf
      rw [Ty.translate_typ, Ty.tel_typ] at hP
      have hm := FCdot.LeCo.HasType.memberP hP .refl (FCdot.Telescope.At.zero_two _ _)
      rw [hpath, FCdot.Ty.weaken_substPath] at hm
      rw [Sub.translate, Ty.translate_selP, Ty.translate_typ, Ty.tel_typ]
      simpa [FCdot.Ty.substPath_sel, FCdot.Path.substPath] using hm
  | _, _, _, _, .all d₁ d₂, hwf => by
      rw [Sub.translate]
      simp only [Ty.translate_all]
      exact .pi (d₁.translate_typed hwf) (d₂.translate_typed (.cons hwf))
  | _, _, _, _, .mu d _ _, hwf => by
      rw [Sub.translate, Ty.translate_mu, Ty.translate_mu]
      exact .obj (d.translate_typed hwf)

theorem PathTy.translatePath_typed : ∀ {s : Sig} {Γ : Ctx s} {p : Path s} {T : Ty s}
    (d : PathTy Γ p T), Γ.Wf →
    FCdot.PathCo.HasType Γ.translate d.translatePath T.translate ∧
      d.translatePath.path = p.translate
  | _, Γ, _, _, .var (x := x), hwf => by
      refine ⟨?_, PathTy.translatePath_path _⟩
      rw [PathTy.translatePath]
      exact FCdot.PathCo.HasType.ofAtom (Ctx.varAtom_typed Γ hwf x)
  | _, _, _, _, @PathTy.sel _ _ p a T h, hwf => by
      refine ⟨?_, PathTy.translatePath_path _⟩
      obtain ⟨hP, hpath⟩ := h.translatePath_typed hwf
      rw [Ty.translate_vfld, Ty.tel_vfld] at hP
      have hs := FCdot.PathCo.HasType.sel hP (FCdot.Telescope.At.one_three _ _ _)
      have hm := FCdot.LeCo.HasType.memberP hP .refl (FCdot.Telescope.At.two_three _ _ _)
      rw [FCdot.Ty.weaken_substPath] at hm
      rw [PathTy.translatePath, Ty.translate_vfld, Ty.tel_vfld]
      refine FCdot.PathCo.HasType.cast hs ?_
      simpa [FCdot.Ty.substPath_sel, FCdot.Path.substPath] using hm
  | _, _, p, _, @PathTy.recI _ _ _ T h hD, hwf => by
      refine ⟨?_, PathTy.translatePath_path _⟩
      obtain ⟨hP, hpath⟩ := h.translatePath_typed hwf
      rw [Ty.translate_decl (hD.substPath p)] at hP
      have hu := FCdot.PathCo.HasType.unfoldSelf hP
      rw [hpath, Ty.tel_substPath] at hu
      rw [PathTy.translatePath, Ty.translate_mu]
      refine FCdot.PathCo.HasType.foldSelf ?_
      have hpu : (FCdot.PathCo.unfoldSelf h.translatePath).path = p.translate := by
        simp only [FCdot.PathCo.path, hpath]
      rw [hpu]
      exact hu
  | _, _, p, _, @PathTy.recE _ _ _ T h hD, hwf => by
      refine ⟨?_, PathTy.translatePath_path _⟩
      obtain ⟨hP, hpath⟩ := h.translatePath_typed hwf
      rw [Ty.translate_mu] at hP
      have hu := FCdot.PathCo.HasType.unfoldSelf hP
      rw [hpath, ← Ty.tel_substPath T p] at hu
      rw [PathTy.translatePath, Ty.translate_decl (hD.substPath p)]
      refine FCdot.PathCo.HasType.foldSelf ?_
      have hpu : (FCdot.PathCo.unfoldSelf h.translatePath).path = p.translate := by
        simp only [FCdot.PathCo.path, hpath]
      rw [hpu]
      exact hu
  | _, _, _, _, .andI h₁ h₂, hwf => by
      refine ⟨?_, PathTy.translatePath_path _⟩
      obtain ⟨hP₁, hp₁⟩ := h₁.translatePath_typed hwf
      obtain ⟨hP₂, hp₂⟩ := h₂.translatePath_typed hwf
      rw [PathTy.translatePath, Ty.translate_and]
      exact .both (intoPath_typed hP₁) (intoPath_typed hP₂) (by simp [hp₁, hp₂])
  | _, _, _, _, .sub h d, hwf => by
      refine ⟨?_, PathTy.translatePath_path _⟩
      rw [PathTy.translatePath]
      exact .cast (h.translatePath_typed hwf).1 (d.translate_typed hwf)
  | _, _, p, _, .snglRefl h, hwf => by
      refine ⟨?_, PathTy.translatePath_path _⟩
      obtain ⟨hP, hpath⟩ := h.translatePath_typed hwf
      rw [PathTy.translatePath, Ty.translate_sngl]
      refine .sngl hP ?_
      rw [hpath]
      exact .refl
  | _, _, p, _, @PathTy.snglTrans _ _ _ q _ h₁ h₂, hwf => by
      refine ⟨?_, PathTy.translatePath_path _⟩
      obtain ⟨hP₁, hp₁⟩ := h₁.translatePath_typed hwf
      obtain ⟨hP₂, hp₂⟩ := h₂.translatePath_typed hwf
      rw [Ty.translate_sngl] at hP₁
      have hα := FCdot.alias_of_sngl hP₁
      rw [hp₁] at hα
      rw [PathTy.translatePath]
      refine .alias ?_ hP₂
      rw [hp₂]
      exact hα
  | _, _, q, _, @PathTy.snglSym _ _ p _ _ h₁ h₂, hwf => by
      refine ⟨?_, PathTy.translatePath_path _⟩
      obtain ⟨hP₁, hp₁⟩ := h₁.translatePath_typed hwf
      obtain ⟨hP₂, hp₂⟩ := h₂.translatePath_typed hwf
      rw [Ty.translate_sngl] at hP₁
      have hα := FCdot.alias_of_sngl hP₁
      rw [hp₁] at hα
      rw [PathTy.translatePath, Ty.translate_sngl]
      refine .sngl hP₂ ?_
      rw [hp₂]
      exact .symm hα
  | _, _, q, _, @PathTy.snglInv _ _ p _ h₁, hwf => by
      refine ⟨?_, PathTy.translatePath_path _⟩
      obtain ⟨hP₁, hp₁⟩ := h₁.translatePath_typed hwf
      rw [Ty.translate_sngl] at hP₁
      have hα := FCdot.alias_of_sngl hP₁
      rw [PathTy.translatePath, Ty.translate_top]
      refine .cast (.alias ?_ hP₁) .top
      exact .symm hα
  | _, _, _, _, @PathTy.snglSel _ _ p q a T h₁ h₂, hwf => by
      refine ⟨?_, PathTy.translatePath_path _⟩
      obtain ⟨hP₁, hp₁⟩ := h₁.translatePath_typed hwf
      obtain ⟨hP₂, hp₂⟩ := h₂.translatePath_typed hwf
      rw [Ty.translate_sngl] at hP₁
      have hα := FCdot.alias_of_sngl hP₁
      rw [hp₁] at hα
      rw [Ty.translate_vfld, Ty.tel_vfld] at hP₂
      have hs := FCdot.PathCo.HasType.sel hP₂ (FCdot.Telescope.At.one_three _ _ _)
      rw [PathTy.translatePath, Ty.translate_sngl]
      refine .sngl hs ?_
      simp only [FCdot.PathCo.path, hp₂]
      exact .sel hα

end

/-! ## The atom of a variable typing -/

theorem HasTy.translateAtom_var {s : Sig} (Γ : Ctx s) (y : BVar s .var) :
    (HasTy.var (Γ := Γ) (x := y)).translateAtom = Γ.varAtom y := rfl

theorem HasTy.translateAtom_recI {s : Sig} {Γ : Ctx s} {y : BVar s .var} {T : Ty (s,x)}
    (h : HasTy Γ (.path y) (T.substVar y)) (hd : Ty.Decl T) :
    (HasTy.recI h hd).translateAtom = .foldSelf T.telSelf (.unfoldSelf h.translateAtom) := rfl

theorem HasTy.translateAtom_recE {s : Sig} {Γ : Ctx s} {y : BVar s .var} {T : Ty (s,x)}
    (h : HasTy Γ (.path y) (.mu T)) (hd : Ty.Decl T) :
    (HasTy.recE h hd).translateAtom =
      .foldSelf (Ty.tel (T.substVar y)) (.unfoldSelf h.translateAtom) := rfl

theorem HasTy.translateAtom_andI {s : Sig} {Γ : Ctx s} {y : BVar s .var} {T U : Ty s}
    (h₁ : HasTy Γ (.path y) T) (h₂ : HasTy Γ (.path y) U) :
    (HasTy.andI h₁ h₂).translateAtom =
      .both T.tel U.tel (intoAtom T h₁.translateAtom) (intoAtom U h₂.translateAtom) := rfl

theorem HasTy.translateAtom_sngl {s : Sig} {Γ : Ctx s} {y : BVar s .var} {q : Path s}
    (d : PathTy Γ (.var y) (.sngl q)) :
    (HasTy.sngl d).translateAtom =
      .sngl (Γ.varAtom y) q.translate (aliasOf d.translatePath q.translate) := rfl

theorem HasTy.translateAtom_sub {s : Sig} {Γ : Ctx s} {y : BVar s .var} {T U : Ty s}
    (h : HasTy Γ (.path y) T) (d : Sub Γ T U) :
    (HasTy.sub h d).translateAtom = .cast h.translateAtom d.translate := rfl

/-- The atom of a variable typing is rooted at the variable. -/
theorem HasTy.translateAtom_root : ∀ {s : Sig} {Γ : Ctx s} {y : BVar s .var} {T : Ty s}
    (h : HasTy Γ (.path y) T), h.translateAtom.root = y
  | _, Γ, y, _, .var => by rw [HasTy.translateAtom_var]; exact Ctx.varAtom_root Γ y
  | _, _, _, _, .recI h hd => by
      rw [HasTy.translateAtom_recI]
      simpa [FCdot.Atom.root] using HasTy.translateAtom_root h
  | _, _, _, _, .recE h hd => by
      rw [HasTy.translateAtom_recE]
      simpa [FCdot.Atom.root] using HasTy.translateAtom_root h
  | _, _, _, _, .andI h₁ h₂ => by
      rw [HasTy.translateAtom_andI]
      simpa [FCdot.Atom.root] using HasTy.translateAtom_root h₁
  | _, Γ, y, _, .sngl d => by
      rw [HasTy.translateAtom_sngl]
      simpa [FCdot.Atom.root] using Ctx.varAtom_root Γ y
  | _, _, _, _, .sub h d => by
      rw [HasTy.translateAtom_sub]
      simpa [FCdot.Atom.root] using HasTy.translateAtom_root h

/-- The atom of a variable typing is typed at the translated type.  The only evidence
it reads is `Sub.translate_typed` at `sub` and `PathTy.translatePath_typed` at `sngl`. -/
theorem HasTy.translateAtom_typed : ∀ {s : Sig} {Γ : Ctx s} {y : BVar s .var} {T : Ty s}
    (h : HasTy Γ (.path y) T), Γ.Wf → Γ.translate ⊢ₐ h.translateAtom : T.translate
  | _, Γ, y, _, .var, hwf => by
      rw [HasTy.translateAtom_var]
      exact Ctx.varAtom_typed Γ hwf y
  | _, _, y, _, @HasTy.recI _ _ _ T h hdecl, hwf => by
      have ih := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_decl (hdecl.substVar y)] at ih
      have hroot : (HasTy.translateAtom h).root = y := HasTy.translateAtom_root h
      have hu := FCdot.Atom.HasType.unfoldSelf ih
      rw [hroot, Ty.tel_substVar T y] at hu
      rw [HasTy.translateAtom_recI, Ty.translate_mu]
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
      rw [HasTy.translateAtom_recE, Ty.translate_decl (hdecl.substVar y)]
      refine FCdot.Atom.HasType.foldSelf ?_
      rw [show (FCdot.Atom.unfoldSelf (HasTy.translateAtom h)).root = y by
        simp [FCdot.Atom.root, hroot]]
      exact hu
  | _, _, _, _, .andI h₁ h₂, hwf => by
      have i1 := intoAtom_typed (HasTy.translateAtom_typed h₁ hwf)
      have i2 := intoAtom_typed (HasTy.translateAtom_typed h₂ hwf)
      rw [HasTy.translateAtom_andI, Ty.translate_and]
      exact .both i1 i2
        (by simp [HasTy.translateAtom_root h₁, HasTy.translateAtom_root h₂])
  | _, Γ, y, _, .sngl d, hwf => by
      obtain ⟨hP, hpath⟩ := d.translatePath_typed hwf
      rw [Ty.translate_sngl] at hP
      have hα := FCdot.alias_of_sngl hP
      rw [hpath] at hα
      rw [HasTy.translateAtom_sngl, Ty.translate_sngl]
      refine .sngl (Ctx.varAtom_typed Γ hwf y) ?_
      rw [Ctx.varAtom_root]
      exact hα
  | _, _, _, _, .sub h d, hwf => by
      rw [HasTy.translateAtom_sub]
      exact .cast (HasTy.translateAtom_typed h hwf) (d.translate_typed hwf)

end DotMNF

end Paths
