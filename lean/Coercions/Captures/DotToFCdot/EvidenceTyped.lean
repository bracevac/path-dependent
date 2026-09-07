import Coercions.Captures.DotToFCdot.Evidence
import Coercions.Captures.DotToFCdot.TypesLemmas
import Coercions.Captures.FCdot.TypingRename

namespace Captures

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
  | _, _, .bnd h₂ he => .bnd (h₁.append h₂) he
  | _, _, .leC h₂ hAt hpre hpost => .leC (h₁.append h₂) hAt hpre hpost
  | _, _, .eqC h₂ hAt => .eqC (h₁.append h₂) hAt
  | _, _, .eqSymC h₂ hAt => .eqSymC (h₁.append h₂) hAt


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
inductive Witnesses.At : Witnesses s → Nat → Label → Shape s → Prop where
  | here : Witnesses.At (.cons W ℓ T) W.length ℓ T
  | there : Witnesses.At W i ℓ T → Witnesses.At (.cons W ℓ' T') i ℓ T

/-- The labels of a witness list are pairwise distinct. -/
inductive Witnesses.Distinct : Witnesses s → Prop where
  | nil : Witnesses.Distinct .nil
  | cons : Witnesses.Distinct W → ℓ ∉ W.labels → Witnesses.Distinct (.cons W ℓ T)

theorem Witnesses.At.mem_labels {s : Sig} {W : Witnesses s} {i : Nat} {ℓ : Label} {T : Shape s}
    (h : Witnesses.At W i ℓ T) : ℓ ∈ W.labels := by
  induction h with
  | here => simp [Witnesses.labels]
  | there _ ih => simp [Witnesses.labels]; exact Or.inl ih

/-- With distinct labels, `Witnesses.get` returns the witness at any position. -/
theorem Witnesses.At.get {s : Sig} {W : Witnesses s} {i : Nat} {ℓ : Label} {T : Shape s}
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

theorem Witnesses.At.append_left {s : Sig} {W : Witnesses s} {i : Nat} {ℓ : Label} {T : Shape s}
    (h : Witnesses.At W i ℓ T) : ∀ W' : Witnesses s, Witnesses.At (W.append W') i ℓ T
  | .nil => h
  | .cons W' _ _ => .there (Witnesses.At.append_left h W')

theorem Witnesses.At.append_right {s : Sig} (W : Witnesses s) {W' : Witnesses s} {i : Nat}
    {ℓ : Label} {T : Shape s} (h : Witnesses.At W' i ℓ T) :
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
    {W : Witnesses s} {i : Nat} {ℓ : Label} {T : Shape s} (h : Witnesses.At W i ℓ T) :
    (W₀.eqEntriesOf self W) ∋ (i ↦ self ∙ ℓ ≐ W₀.get ℓ) := by
  induction h with
  | @here W' ℓ' T' =>
      rw [show W₀.eqEntriesOf self (Witnesses.cons W' ℓ' T')
            = Telescope.cons (W₀.eqEntriesOf self W') (self ∙ ℓ' ≐ W₀.get ℓ') from rfl,
        ← Witnesses.eqEntriesOf_length self W₀ W']
      exact .here
  | there _ ih => exact .there ih

/-- The capture block of a literal's precise telescope is as long as its
capture-witness list, so the presence entries of `ofLiteral W Wᶜ ls` start at
position `W.length + Wᶜ.length`. -/
theorem CapWitnesses.eqEntriesOf_length {s : Sig} (self : BVar s .var) (W₀ : CapWitnesses s)
    (base : Telescope s) :
    ∀ (W : CapWitnesses s), (W₀.eqEntriesOf self base W).length = base.length + W.length
  | .nil => rfl
  | .cons W _ _ => by
      simp only [CapWitnesses.eqEntriesOf, Telescope.length, CapWitnesses.length,
        CapWitnesses.eqEntriesOf_length self W₀ base W]
      omega

theorem CapWitnesses.eqEntries_length {s : Sig} (W : CapWitnesses (s,x))
    (base : Telescope (s,x)) : (W.eqEntries base).length = base.length + W.length :=
  CapWitnesses.eqEntriesOf_length _ _ _ _

/-- The capture block is appended *after* the type block, so every position
of the base telescope keeps its index. -/
theorem CapWitnesses.At.eqEntriesOf {s : Sig} (self : BVar s .var) (W₀ : CapWitnesses s)
    {base : Telescope s} {i : Nat} {P : Proposition s} (h : base ∋ (i ↦ P)) :
    ∀ (W : CapWitnesses s), (W₀.eqEntriesOf self base W) ∋ (i ↦ P)
  | .nil => h
  | .cons W _ _ => .there (CapWitnesses.At.eqEntriesOf self W₀ h W)

theorem CapWitnesses.At.eqEntries {s : Sig} {W : CapWitnesses (s,x)}
    {base : Telescope (s,x)} {i : Nat} {P : Proposition (s,x)} (h : base ∋ (i ↦ P)) :
    (W.eqEntries base) ∋ (i ↦ P) :=
  CapWitnesses.At.eqEntriesOf _ _ h _

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

/-- Extending a capture-witness list by more empty witnesses leaves the
positions already present unchanged. -/
theorem CapWitnesses.At.ofLabels {s' : Sig} (self : BVar s' .var) (W₀ : CapWitnesses s')
    {base : Telescope s'} :
    ∀ {Wc : CapWitnesses s'} {i : Nat} {P : Proposition s'},
      (W₀.eqEntriesOf self base Wc) ∋ (i ↦ P) →
      ∀ ls : List Label, (W₀.eqEntriesOf self base (CapWitnesses.ofLabels Wc ls)) ∋ (i ↦ P)
  | _, _, _, h, [] => h
  | Wc, _, _, h, ℓ :: ls => by
      rw [CapWitnesses.ofLabels]
      exact CapWitnesses.At.ofLabels self W₀ (Wc := Wc.cons ℓ []) (by exact h.there) ls

/-- The capture entry of the `i`-th label of `ls` sits `i` positions after
the base telescope and the witnesses already listed. -/
theorem CapWitnesses.ofLabels_At {s' : Sig} (self : BVar s' .var) (W₀ : CapWitnesses s')
    (base : Telescope s') :
    ∀ (ls : List Label) (Wc : CapWitnesses s') {i : Nat} {ℓ : Label}, LabelAt ls i ℓ →
      (W₀.eqEntriesOf self base (CapWitnesses.ofLabels Wc ls))
        ∋ (base.length + Wc.length + i ↦ [CapAtom.name self ℓ] ≐ᶜ W₀.get ℓ)
  | [], _, _, _, h => by cases h
  | ℓ' :: ls, Wc, _, _, h => by
      cases h with
      | here =>
          have h0 : (W₀.eqEntriesOf self base (Wc.cons ℓ' []))
              ∋ ((W₀.eqEntriesOf self base Wc).length ↦ [CapAtom.name self ℓ'] ≐ᶜ W₀.get ℓ') :=
            .here
          rw [CapWitnesses.eqEntriesOf_length] at h0
          rw [CapWitnesses.ofLabels, Nat.add_zero]
          exact CapWitnesses.At.ofLabels self W₀ h0 ls
      | @there _ i' _ ℓ'' h' =>
          have ih := CapWitnesses.ofLabels_At self W₀ base ls (Wc.cons ℓ' []) h'
          rw [show (Wc.cons ℓ' ([] : CaptureSet s')).length = Wc.length + 1 from rfl,
            show base.length + (Wc.length + 1) + i' = base.length + Wc.length + (i' + 1) by
              omega] at ih
          rw [CapWitnesses.ofLabels]
          exact ih

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

/-- The three positions of a field's declared telescope: presence, bound,
capture entry. -/
theorem Telescope.At.zero_three {s : Sig} (P Q R : Proposition s) :
    (Telescope.cons (Telescope.cons (Telescope.cons .nil P) Q) R) ∋ (0 ↦ P) :=
  (Telescope.At.zero_two P Q).there

theorem Telescope.At.one_three {s : Sig} (P Q R : Proposition s) :
    (Telescope.cons (Telescope.cons (Telescope.cons .nil P) Q) R) ∋ (1 ↦ Q) :=
  (Telescope.At.one_two P Q).there

theorem Telescope.At.two_three {s : Sig} (P Q R : Proposition s) :
    (Telescope.cons (Telescope.cons (Telescope.cons .nil P) Q) R) ∋ (2 ↦ R) := by
  have h : (Telescope.cons (Telescope.cons (Telescope.cons (.nil : Telescope s) P) Q) R)
      ∋ ((Telescope.cons (Telescope.cons (.nil : Telescope s) P) Q).length ↦ R) := .here
  rw [Telescope.length_cons, Telescope.length_cons, Telescope.length_nil] at h
  exact h

theorem Witnesses.length_nil {s : Sig} : (Witnesses.nil : Witnesses s).length = 0 := by
  simp [Witnesses.length]

theorem Witnesses.At.hereNil {s : Sig} {l : Label} {T : Shape s} :
    Witnesses.At (Witnesses.cons .nil l T) 0 l T := by
  have h : Witnesses.At (Witnesses.cons (.nil : Witnesses s) l T)
      ((Witnesses.nil : Witnesses s).length) l T := .here
  rw [Witnesses.length_nil] at h
  exact h

theorem CaptureSet.substVar_name_here {s : Sig} (a : Label) (r : BVar s .var) :
    (([CapAtom.name .here a] : CaptureSet (s,x)))⟦r⟧ = [CapAtom.name r a] := by
  simp [CaptureSet.substVar, CaptureSet.rename, CapAtom.rename]

theorem CaptureSet.substVar_nil {s : Sig} (r : BVar s .var) :
    (([] : CaptureSet (s,x)))⟦r⟧ = [] := rfl

theorem Shape.substVar_sel_here {s : Sig} (A : Label) (r : BVar s .var) :
    ((Shape.sel .here A : Shape (s,x)))⟦r⟧ = Shape.sel r A := by
  simp [Shape.substVar, Shape.rename]

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label Morphism ShapeCo CapCo LeCo EqCo Has Atom Side)
open scoped FCdot

/-! ## Equations for the type translation

`Ty.translateShape`, `Ty.tel` and `Ty.telSelf` are a mutual structural recursion, so their
defining equations are not definitional; these are the rewrite rules used throughout.  Each
equation of the vanilla `Ty.translate` is the `translateShape` equation here — the vanilla
target sort is the shape sort — and the `translate` equation beside it is the same shape at
the empty capture set. -/

theorem Ty.translateShape_top {s : Sig} : (Ty.top : Ty s).translateShape = ⊤ := by
  simp [Ty.translateShape]

theorem Ty.translate_top {s : Sig} : (Ty.top : Ty s).translate = ⊤ ^ [] := by
  simp [Ty.translate, Ty.translateShape]

theorem Ty.translateShape_bot {s : Sig} : (Ty.bot : Ty s).translateShape = ⊥ := by
  simp [Ty.translateShape]

theorem Ty.translate_bot {s : Sig} : (Ty.bot : Ty s).translate = ⊥ ^ [] := by
  simp [Ty.translate, Ty.translateShape]

theorem Ty.translateShape_sel {s : Sig} (y : BVar s .var) (A : Label) :
    (Ty.sel (.var y) A).translateShape = y ∙ A := by simp [Ty.translateShape]

theorem Ty.translate_sel {s : Sig} (y : BVar s .var) (A : Label) :
    (Ty.sel (.var y) A).translate = (y ∙ A) ^ [] := by simp [Ty.translate, Ty.translateShape]

theorem Ty.translateShape_all {s : Sig} (S : Ty s) (T : Ty (s,x)) :
    (Ty.all S T).translateShape = Π(S.translate) T.translate := by
  simp [Ty.translateShape, Ty.translate]

theorem Ty.translate_all {s : Sig} (S : Ty s) (T : Ty (s,x)) :
    (Ty.all S T).translate = (Π(S.translate) T.translate) ^ [] := by
  simp [Ty.translate, Ty.translateShape]

theorem Ty.translateShape_typ {s : Sig} (A : Label) (S T : Ty s) :
    (Ty.typ A S T).translateShape = μ (Ty.typ A S T).tel := by simp [Ty.translateShape]

theorem Ty.translate_typ {s : Sig} (A : Label) (S T : Ty s) :
    (Ty.typ A S T).translate = (μ (Ty.typ A S T).tel) ^ [] := by
  simp [Ty.translate, Ty.translateShape]

theorem Ty.translateShape_fld {s : Sig} (a : Label) (T : Ty s) :
    (Ty.fld a T).translateShape = μ (Ty.fld a T).tel := by simp [Ty.translateShape]

theorem Ty.translate_fld {s : Sig} (a : Label) (T : Ty s) :
    (Ty.fld a T).translate = (μ (Ty.fld a T).tel) ^ [] := by
  simp [Ty.translate, Ty.translateShape]

theorem Ty.translateShape_and {s : Sig} (S T : Ty s) :
    (Ty.and S T).translateShape = μ ((Ty.tel S).append (Ty.tel T)) := by
  simp [Ty.translateShape, Ty.tel]

theorem Ty.translate_and {s : Sig} (S T : Ty s) :
    (Ty.and S T).translate = (μ ((Ty.tel S).append (Ty.tel T))) ^ [] := by
  simp [Ty.translate, Ty.translateShape, Ty.tel]

theorem Ty.translateShape_mu {s : Sig} (T : Ty (s,x)) :
    (Ty.mu T).translateShape = μ T.telSelf := by simp [Ty.translateShape]

theorem Ty.translate_mu {s : Sig} (T : Ty (s,x)) :
    (Ty.mu T).translate = (μ T.telSelf) ^ [] := by simp [Ty.translate, Ty.translateShape]

theorem Ty.translateShape_weaken {s : Sig} (T : Ty s) :
    (T.weaken : Ty (s,x)).translateShape = (T.translateShape)↑ :=
  Ty.translateShape_rename T FCdot.Rename.succ

theorem Ty.translate_weaken {s : Sig} (T : Ty s) :
    (T.weaken : Ty (s,x)).translate = (T.translate)↑ :=
  Ty.translate_rename T FCdot.Rename.succ

theorem Ty.tel_typ {s : Sig} (A : Label) (S T : Ty s) :
    (Ty.typ A S T).tel =
      FCdot.Telescope.cons (FCdot.Telescope.cons .nil ((S.translateShape)↑ ⊑ .here ∙ A))
        (.here ∙ A ⊑ (T.translateShape)↑) := by simp [Ty.tel]

theorem Ty.tel_fld {s : Sig} (a : Label) (T : Ty s) :
    (Ty.fld a T).tel =
      FCdot.Telescope.cons
        (FCdot.Telescope.cons (FCdot.Telescope.cons .nil (∋ a))
          (.here ∙ a ⊑ (T.translateShape)↑))
        ([FCdot.CapAtom.name .here a] ⊑ᶜ []) := by
  simp [Ty.tel]

theorem Ty.tel_and {s : Sig} (S T : Ty s) :
    (Ty.and S T).tel = (Ty.tel S).append (Ty.tel T) := by simp [Ty.tel]

theorem Ty.telSelf_typ {s : Sig} (A : Label) (S T : Ty (s,x)) :
    (Ty.typ A S T).telSelf =
      FCdot.Telescope.cons (FCdot.Telescope.cons .nil (S.translateShape ⊑ .here ∙ A))
        (.here ∙ A ⊑ T.translateShape) := by simp [Ty.telSelf]

theorem Ty.telSelf_fld {s : Sig} (a : Label) (T : Ty (s,x)) :
    (Ty.fld a T).telSelf =
      FCdot.Telescope.cons
        (FCdot.Telescope.cons (FCdot.Telescope.cons .nil (∋ a))
          (.here ∙ a ⊑ T.translateShape))
        ([FCdot.CapAtom.name .here a] ⊑ᶜ []) := by
  simp [Ty.telSelf]

theorem Ty.telSelf_and {s : Sig} (S T : Ty (s,x)) :
    (Ty.and S T).telSelf = (Ty.telSelf S).append (Ty.telSelf T) := by simp [Ty.telSelf]

/-! ## Telescopes without self-bounds, and telescopes with closed self-bounds -/

theorem _root_.Captures.FCdot.Telescope.NoBnd.append {s' : Sig} {Tel₁ : FCdot.Telescope s'}
    (h₁ : Tel₁.NoBnd) :
    ∀ Tel₂ : FCdot.Telescope s', Tel₂.NoBnd → (Tel₁.append Tel₂).NoBnd
  | .nil, _ => h₁
  | .cons _ (.bnd _), h₂ => h₂.elim
  | .cons Tel (.le _ _), h₂ => FCdot.Telescope.NoBnd.append h₁ Tel h₂
  | .cons Tel (.eq _ _), h₂ => FCdot.Telescope.NoBnd.append h₁ Tel h₂
  | .cons Tel (.has _), h₂ => FCdot.Telescope.NoBnd.append h₁ Tel h₂
  | .cons Tel (.leC _ _), h₂ => FCdot.Telescope.NoBnd.append h₁ Tel h₂
  | .cons Tel (.eqC _ _), h₂ => FCdot.Telescope.NoBnd.append h₁ Tel h₂

theorem _root_.Captures.FCdot.Telescope.NoBnd.rename {s₁ s₂ : Sig} (ρ : FCdot.Rename s₁ s₂) :
    ∀ Tel : FCdot.Telescope s₁, Tel.NoBnd → (Tel.rename ρ).NoBnd
  | .nil, h => h
  | .cons _ (.bnd _), h => h.elim
  | .cons Tel (.le _ _), h => FCdot.Telescope.NoBnd.rename ρ Tel h
  | .cons Tel (.eq _ _), h => FCdot.Telescope.NoBnd.rename ρ Tel h
  | .cons Tel (.has _), h => FCdot.Telescope.NoBnd.rename ρ Tel h
  | .cons Tel (.leC _ _), h => FCdot.Telescope.NoBnd.rename ρ Tel h
  | .cons Tel (.eqC _ _), h => FCdot.Telescope.NoBnd.rename ρ Tel h

theorem _root_.Captures.FCdot.Telescope.NoBnd.closedBnds {s : Sig} :
    ∀ {Tel : FCdot.Telescope (s,x)}, Tel.NoBnd → Tel.ClosedBnds
  | .nil, _ => .nil
  | .cons _ (.bnd _), h => h.elim
  | .cons Tel (.le _ _), h => .le (FCdot.Telescope.NoBnd.closedBnds h)
  | .cons Tel (.eq _ _), h => .eq (FCdot.Telescope.NoBnd.closedBnds h)
  | .cons Tel (.has _), h => .has (FCdot.Telescope.NoBnd.closedBnds h)
  | .cons Tel (.leC _ _), h => .leC (FCdot.Telescope.NoBnd.closedBnds h)
  | .cons Tel (.eqC _ _), h => .eqC (FCdot.Telescope.NoBnd.closedBnds h)

theorem _root_.Captures.FCdot.Telescope.ClosedBnds.append {s : Sig} {Tel₁ : FCdot.Telescope (s,x)}
    (h₁ : Tel₁.ClosedBnds) :
    ∀ {Tel₂ : FCdot.Telescope (s,x)}, Tel₂.ClosedBnds → (Tel₁.append Tel₂).ClosedBnds
  | _, .nil => h₁
  | _, .le h₂ => .le (FCdot.Telescope.ClosedBnds.append h₁ h₂)
  | _, .eq h₂ => .eq (FCdot.Telescope.ClosedBnds.append h₁ h₂)
  | _, .has h₂ => .has (FCdot.Telescope.ClosedBnds.append h₁ h₂)
  | _, .bnd h₂ => .bnd (FCdot.Telescope.ClosedBnds.append h₁ h₂)
  | _, .leC h₂ => .leC (FCdot.Telescope.ClosedBnds.append h₁ h₂)
  | _, .eqC h₂ => .eqC (FCdot.Telescope.ClosedBnds.append h₁ h₂)

/-- A declaration-shaped body has no self-bounds at all: `Ty.telSelf` only
produces one on a shape `Wf.mu` excludes. -/
theorem Ty.telSelf_noBnd_of_decl {s : Sig} :
    ∀ {S : Ty (s,x)}, Ty.Decl S → (Ty.telSelf S).NoBnd
  | .top, _ => by simp [Ty.telSelf, FCdot.Telescope.NoBnd]
  | .typ _ _ _, _ => by simp [Ty.telSelf, FCdot.Telescope.NoBnd]
  | .fld _ _, _ => by simp [Ty.telSelf, FCdot.Telescope.NoBnd]
  | .and S T, h => by
      cases h with
      | and hS hT =>
          simp only [Ty.telSelf]
          exact FCdot.Telescope.NoBnd.append (Ty.telSelf_noBnd_of_decl hS) _
            (Ty.telSelf_noBnd_of_decl hT)
  | .mu T, h => by
      cases h with
      | mu hT =>
          have hd : T.isDecl = true := (Ty.isDecl_iff T).mpr hT
          simp only [Ty.telSelf, if_pos hd, FCdot.Telescope.substVar]
          exact FCdot.Telescope.NoBnd.rename _ _ (Ty.telSelf_noBnd_of_decl hT)

/-- Every self-bound the translation of a type carries is a weakened closed
type: this is the closedness convention of `FCdot` (plan §13 item 9). -/
theorem Ty.tel_closedBnds {s : Sig} :
    ∀ S : Ty s, (Ty.tel S : FCdot.Telescope (s,x)).ClosedBnds
  | .top => by simp only [Ty.tel]; exact .nil
  | .bot => by simp only [Ty.tel]; exact .bnd .nil
  | .sel (.var _) _ => by simp only [Ty.tel]; exact .bnd .nil
  | .all _ _ => by simp only [Ty.tel]; exact .bnd .nil
  | .typ _ _ _ => by simp only [Ty.tel]; exact .le (.le .nil)
  | .fld _ _ => by simp only [Ty.tel]; exact .leC (.le (.has .nil))
  | .and S T => by
      simp only [Ty.tel]
      exact (Ty.tel_closedBnds S).append (Ty.tel_closedBnds T)
  | .mu T => by
      by_cases hd : T.isDecl = true
      · simp only [Ty.tel, if_pos hd]
        exact (Ty.telSelf_noBnd_of_decl ((Ty.isDecl_iff T).mp hd)).closedBnds
      · simp only [Ty.tel, if_neg hd]
        exact .bnd .nil

/-! ## Identity templates between concatenated telescopes -/

/-- `identityMorphism src off Tel` proves every proposition of `Tel` by the identical
proposition of the source, found `off` positions further along; a self-bound is
proven by the cast of `μ src` through the source's own bound there. -/
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
  | _, .leC hb, h => by
      have ih := identityMorphism_typed (Γ := Γ) (src := src) off hb (fun i Q hQ => h i Q hQ.there)
      rw [identityMorphism]; exact .leC ih (.leC (h _ _ .here)) .nil .nil
  | _, .eqC hb, h => by
      have ih := identityMorphism_typed (Γ := Γ) (src := src) off hb (fun i Q hQ => h i Q hQ.there)
      rw [identityMorphism]; exact .eqC ih (h _ _ .here)

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
theorem into_typed {s : Sig} {Γ : FCdot.Ctx s} {S T : Ty s} {e : FCdot.ShapeCo s}
    (he : Γ ⊢ˢ e : S.translateShape ≤ T.translateShape) :
    Γ ⊢ˢ into T e : S.translateShape ≤ μ T.tel := by
  rw [into]
  by_cases h : T.isObj = true
  · rw [if_pos h, ← Ty.translateShape_isObj h]; exact he
  · rw [if_neg h, Ty.tel_of_not_isObj (by simpa using h)]
    exact .intoBnd he

/-- The same for atoms; `And-I` needs it on both operands. -/
theorem intoAtom_typed {s : Sig} {Γ : FCdot.Ctx s} {T : Ty s} {a : FCdot.Atom s}
    (ha : Γ ⊢ₐ a : T.translate) : Γ ⊢ₐ intoAtom T a : (μ T.tel) ^ [] := by
  rw [intoAtom]
  by_cases h : T.isObj = true
  · rw [if_pos h, ← Ty.translate_isObj h]; exact ha
  · rw [if_neg h, Ty.tel_of_not_isObj (by simpa using h)]
    exact .cast ha (.capt (.intoBnd .refl) .refl)

/-- The self-bound of a non-object operand sits at position `0` of its own
telescope. -/
theorem Ty.tel_bnd_at {s : Sig} {T : Ty s} (h : T.isObj = false) :
    (Ty.tel T : FCdot.Telescope (s,x)) ∋ (0 ↦ ⊑ T.translateShape↑) := by
  rw [Ty.tel_of_not_isObj h]
  exact .here

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
  | .typ A S _, e => src ∋ (e ↦ .here ∙ A ≐ S.translateShape)
  | .fld a T, e => src ∋ (e ↦ .here ∙ a ≐ T.translateShape)
  | .and S T, e => Ty.EqSpec src S e ∧ Ty.EqSpec src T (e + S.witnesses.length)
  | _, _ => True

/-- The field presences that the templates of `T` inherit, at presence offset
`off`.  `Ty.fieldLabels` puts the right conjunct first, so on an intersection
it is the right conjunct that starts at `off`. -/
def Ty.HasSpec {s : Sig} (src : FCdot.Telescope (s,x)) : Ty (s,x) → Nat → Prop
  | .fld a _, off => src ∋ (off ↦ ∋ a)
  | .and S T, off => Ty.HasSpec src S (off + T.fieldLabels.length) ∧ Ty.HasSpec src T off
  | _, _ => True

/-- The capture equalities that the templates of `T` read, at capture offset
`off`.  The capture block of `Telescope.ofLiteral` is as long as the presence
block and in the same order (`Ty.capWitnesses` lists `Ty.fieldLabels`), so
this is `Ty.HasSpec` at a different base. -/
def Ty.CapSpec {s : Sig} (src : FCdot.Telescope (s,x)) : Ty (s,x) → Nat → Prop
  | .fld a _, off => src ∋ (off ↦ [FCdot.CapAtom.name .here a] ≐ᶜ [])
  | .and S T, off => Ty.CapSpec src S (off + T.fieldLabels.length) ∧ Ty.CapSpec src T off
  | _, _ => True

/-! ## The morphism of a literal -/

theorem litMorphism_and_fst {s : Sig} (S T : Ty (s,x)) (e c h : Nat) :
    (litMorphism (.and S T) e c h).1 =
      (litMorphism S e (c + T.fieldLabels.length) (h + T.fieldLabels.length)).1.append
        (litMorphism T
          (litMorphism S e (c + T.fieldLabels.length) (h + T.fieldLabels.length)).2.1 c h).1 := by
  rw [litMorphism]

theorem litMorphism_and_eq {s : Sig} (S T : Ty (s,x)) (e c h : Nat) :
    (litMorphism (.and S T) e c h).2.1 =
      (litMorphism T
        (litMorphism S e (c + T.fieldLabels.length) (h + T.fieldLabels.length)).2.1 c h).2.1 := by
  rw [litMorphism]

theorem litMorphism_and_cap {s : Sig} (S T : Ty (s,x)) (e c h : Nat) :
    (litMorphism (.and S T) e c h).2.2.1 =
      (litMorphism S e (c + T.fieldLabels.length) (h + T.fieldLabels.length)).2.2.1 := by
  rw [litMorphism]

theorem litMorphism_and_has {s : Sig} (S T : Ty (s,x)) (e c h : Nat) :
    (litMorphism (.and S T) e c h).2.2.2 =
      (litMorphism S e (c + T.fieldLabels.length) (h + T.fieldLabels.length)).2.2.2 := by
  rw [litMorphism]

theorem litMorphism_offsets {s : Sig} : ∀ (T : Ty (s,x)) (e c h : Nat),
    (litMorphism T e c h).2.1 = e + T.witnesses.length ∧
      (litMorphism T e c h).2.2.1 = c + T.fieldLabels.length ∧
      (litMorphism T e c h).2.2.2 = h + T.fieldLabels.length
  | .top, e, c, h => by simp [litMorphism, Ty.witnesses, Ty.fieldLabels, FCdot.Witnesses.length]
  | .bot, e, c, h => by simp [litMorphism, Ty.witnesses, Ty.fieldLabels, FCdot.Witnesses.length]
  | .sel _ _, e, c, h => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, FCdot.Witnesses.length]
  | .all _ _, e, c, h => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, FCdot.Witnesses.length]
  | .mu _, e, c, h => by simp [litMorphism, Ty.witnesses, Ty.fieldLabels, FCdot.Witnesses.length]
  | .typ A S T, e, c, h => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, FCdot.Witnesses.length]
  | .fld a T, e, c, h => by
      simp [litMorphism, Ty.witnesses, Ty.fieldLabels, FCdot.Witnesses.length]
  | .and S T, e, c, h => by
      have hS := litMorphism_offsets S e (c + T.fieldLabels.length) (h + T.fieldLabels.length)
      have hT := litMorphism_offsets T
        (litMorphism S e (c + T.fieldLabels.length) (h + T.fieldLabels.length)).2.1 c h
      refine ⟨?_, ?_, ?_⟩
      · rw [litMorphism_and_eq, hT.1, hS.1, Ty.witnesses, FCdot.Witnesses.length_append]
        omega
      · rw [litMorphism_and_cap, hS.2.1, Ty.fieldLabels, List.length_append]
        omega
      · rw [litMorphism_and_has, hS.2.2, Ty.fieldLabels, List.length_append]
        omega

theorem litMorphism_typed {s : Sig} {Γ : FCdot.Ctx s} {src : FCdot.Telescope (s,x)} :
    ∀ (T : Ty (s,x)), Ty.LiteralShape T → ∀ (e c h : Nat),
      Ty.EqSpec src T e → Ty.CapSpec src T c → Ty.HasSpec src T h →
      Γ ⊢ (litMorphism T e c h).1 : src ⇒ T.telSelf
  | .top, hsh, _, _, _, _, _, _ => by cases hsh
  | .bot, hsh, _, _, _, _, _, _ => by cases hsh
  | .sel _ _, hsh, _, _, _, _, _, _ => by cases hsh
  | .all _ _, hsh, _, _, _, _, _, _ => by cases hsh
  | .mu _, hsh, _, _, _, _, _, _ => by cases hsh
  | .typ A S T', hsh, e, c, h, heq, _, _ => by
      cases hsh
      rw [Ty.EqSpec] at heq
      rw [litMorphism, Ty.telSelf_typ]
      exact .leEq (.leEqSym .nil heq .none .none) heq .none .none
  | .fld a T', _, e, c, h, heq, hcap, hhas => by
      rw [Ty.EqSpec] at heq
      rw [Ty.CapSpec] at hcap
      rw [Ty.HasSpec] at hhas
      rw [litMorphism, Ty.telSelf_fld]
      exact .leC (.leEq (.has .nil hhas) heq .none .none) (.eqC hcap) .nil .nil
  | .and S T', hsh, e, c, h, heq, hcap, hhas => by
      cases hsh with
      | and hS hT =>
          rw [Ty.EqSpec] at heq
          rw [Ty.CapSpec] at hcap
          rw [Ty.HasSpec] at hhas
          obtain ⟨heq₁, heq₂⟩ := heq
          obtain ⟨hcap₁, hcap₂⟩ := hcap
          obtain ⟨hhas₁, hhas₂⟩ := hhas
          have hoff := litMorphism_offsets S e (c + T'.fieldLabels.length)
            (h + T'.fieldLabels.length)
          have ih₁ := litMorphism_typed (Γ := Γ) S hS e (c + T'.fieldLabels.length)
            (h + T'.fieldLabels.length) heq₁ hcap₁ hhas₁
          have ih₂ := litMorphism_typed (Γ := Γ) T' hT
            (litMorphism S e (c + T'.fieldLabels.length) (h + T'.fieldLabels.length)).2.1 c h
            (by rw [hoff.1]; exact heq₂) hcap₂ hhas₂
          rw [litMorphism_and_fst, Ty.telSelf_and]
          exact ih₁.append ih₂

/-! ## The definition equalities and presences of a literal's own telescope -/

theorem eqSpec_of {s : Sig} {Wall : FCdot.Witnesses (s,x)} (hdist : Wall.Distinct)
    (Wc : FCdot.CapWitnesses (s,x)) (lsAll : List Label) :
    ∀ (T : Ty (s,x)) (e : Nat),
      (∀ i l X, FCdot.Witnesses.At T.witnesses i l X → FCdot.Witnesses.At Wall (e + i) l X) →
      Ty.EqSpec (FCdot.Telescope.ofLiteral Wall Wc lsAll) T e
  | .top, _, _ => by simp [Ty.EqSpec]
  | .bot, _, _ => by simp [Ty.EqSpec]
  | .sel _ _, _, _ => by simp [Ty.EqSpec]
  | .all _ _, _, _ => by simp [Ty.EqSpec]
  | .mu _, _, _ => by simp [Ty.EqSpec]
  | .typ A S T', e, hpos => by
      simp only [Ty.witnesses] at hpos
      have h1 := hpos 0 A S.translateShape FCdot.Witnesses.At.hereNil
      rw [Nat.add_zero] at h1
      have h2 := FCdot.Witnesses.eqEntriesOf_At FCdot.BVar.here Wall h1
      rw [h1.get hdist] at h2
      rw [Ty.EqSpec]
      exact FCdot.Telescope.At.hasEntries lsAll (FCdot.CapWitnesses.At.eqEntries h2)
  | .fld a T', e, hpos => by
      simp only [Ty.witnesses] at hpos
      have h1 := hpos 0 a T'.translateShape FCdot.Witnesses.At.hereNil
      rw [Nat.add_zero] at h1
      have h2 := FCdot.Witnesses.eqEntriesOf_At FCdot.BVar.here Wall h1
      rw [h1.get hdist] at h2
      rw [Ty.EqSpec]
      exact FCdot.Telescope.At.hasEntries lsAll (FCdot.CapWitnesses.At.eqEntries h2)
  | .and S T', e, hpos => by
      simp only [Ty.witnesses] at hpos
      rw [Ty.EqSpec]
      refine ⟨eqSpec_of hdist Wc lsAll S e (fun i l X hAt => hpos i l X (hAt.append_left _)), ?_⟩
      refine eqSpec_of hdist Wc lsAll T' (e + S.witnesses.length) (fun i l X hAt => ?_)
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

/-- The capture equalities of a literal's own telescope, read at the offset
where its capture block starts.  The proof is `hasSpec_of` at a different
base: the capture block lists `Ty.fieldLabels` in the same order as the
presence block. -/
theorem capSpec_of {s : Sig} {src : FCdot.Telescope (s,x)} :
    ∀ (T : Ty (s,x)) (off : Nat),
      (∀ i l, FCdot.LabelAt T.fieldLabels i l →
        src ∋ (off + i ↦ [FCdot.CapAtom.name .here l] ≐ᶜ [])) →
      Ty.CapSpec src T off
  | .top, _, _ => by simp [Ty.CapSpec]
  | .bot, _, _ => by simp [Ty.CapSpec]
  | .sel _ _, _, _ => by simp [Ty.CapSpec]
  | .all _ _, _, _ => by simp [Ty.CapSpec]
  | .mu _, _, _ => by simp [Ty.CapSpec]
  | .typ _ _ _, _, _ => by simp [Ty.CapSpec]
  | .fld a T', off, hpos => by
      simp only [Ty.fieldLabels] at hpos
      have h1 := hpos 0 a .here
      rw [Nat.add_zero] at h1
      rw [Ty.CapSpec]
      exact h1
  | .and S T', off, hpos => by
      simp only [Ty.fieldLabels] at hpos
      rw [Ty.CapSpec]
      refine ⟨?_, capSpec_of T' off (fun i l hAt => hpos i l (hAt.append_left _))⟩
      refine capSpec_of S (off + T'.fieldLabels.length) (fun i l hAt => ?_)
      have hh := hpos (T'.fieldLabels.length + i) l (FCdot.LabelAt.append_right hAt T'.fieldLabels)
      rw [show off + (T'.fieldLabels.length + i) = off + T'.fieldLabels.length + i by omega] at hh
      exact hh

/-! ## The coercion from a literal's precise type to its declared type -/

theorem litCo_typed_of_shape {s : Sig} {Γ : FCdot.Ctx s} {T : Ty (s,x)}
    (hsh : Ty.LiteralShape T) (hdl : Ty.DistinctLabels T) :
    Γ ⊢ˢ litCo T : T.literalTy.shape ≤ (Ty.mu T).translateShape := by
  have hW : T.witnesses.Distinct := Ty.witnesses_distinct T hdl
  rw [Ty.translateShape_mu, Ty.literalTy_shape]
  refine .obj (litMorphism_typed T hsh 0 T.witnesses.length
    (T.witnesses.length + T.capWitnesses.length) ?_ ?_ ?_)
  · exact eqSpec_of hW T.capWitnesses T.fieldLabels T 0
      (fun i l X hAt => by rw [Nat.zero_add]; exact hAt)
  · refine capSpec_of T T.witnesses.length (fun i l hAt => ?_)
    have hh := FCdot.CapWitnesses.ofLabels_At FCdot.BVar.here T.capWitnesses
      T.witnesses.eqEntries T.fieldLabels .nil hAt
    rw [Ty.capWitnesses_get, show (FCdot.CapWitnesses.nil : FCdot.CapWitnesses (s,x)).length = 0
        from rfl,
      show (T.witnesses.eqEntries).length = T.witnesses.length from
        FCdot.Witnesses.eqEntriesOf_length _ _ _,
      Nat.add_zero] at hh
    exact FCdot.Telescope.At.hasEntries T.fieldLabels hh
  · refine hasSpec_of T (T.witnesses.length + T.capWitnesses.length) (fun i l hAt => ?_)
    have hh :=
      FCdot.Telescope.hasEntries_At hAt (T.capWitnesses.eqEntries T.witnesses.eqEntries)
    rw [FCdot.CapWitnesses.eqEntries_length,
      show (T.witnesses.eqEntries).length = T.witnesses.length from
        FCdot.Witnesses.eqEntriesOf_length _ _ _] at hh
    exact hh

/-- `litCo` is closed evidence: it is typed in any context. -/
theorem litCo_typed {s : Sig} {Γ' : FCdot.Ctx s} {Γ : Ctx (s,x)} {d : Defs (s,x)}
    {T : Ty (s,x)} (hd : DefsTy Γ d T) (hdist : Defs.Distinct d) :
    Γ' ⊢ˢ litCo T : T.literalTy.shape ≤ (Ty.mu T).translateShape :=
  litCo_typed_of_shape hd.literalShape (hd.distinctLabels hdist)

/-- The same as a type inclusion, at the empty capture set both sides. -/
theorem litCo_pure_typed {s : Sig} {Γ' : FCdot.Ctx s} {Γ : Ctx (s,x)} {d : Defs (s,x)}
    {T : Ty (s,x)} (hd : DefsTy Γ d T) (hdist : Defs.Distinct d) :
    Γ' ⊢ (litCo T).pure : T.literalTy ≤ (Ty.mu T).translate :=
  .capt (litCo_typed hd hdist) .refl

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
    (Γ.consSelf d T).varAtom .here = .cast (.var .here) (((litCo T).pure)↑) := rfl

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
            ((FCdot.LeCo.HasType.capt (litCo_typed_of_shape (Γ := Γ.translate) hsh hdl)
                FCdot.CapCo.HasType.refl).weaken
              (.transparent T.literalTy T.witnesses T.capWitnesses T.fieldLabels))
  | .consSelf Γ d T, hwf, .there y => by
      cases hwf with
      | consSelf hwf' _ _ =>
          rw [Ctx.lookup_consSelf_there, Ctx.varAtom_consSelf_there, Ty.translate_weaken]
          exact (Ctx.varAtom_typed Γ hwf' y).weaken
            (.transparent T.literalTy T.witnesses T.capWitnesses T.fieldLabels)

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
  | _, _, _, _, .andI h₁ h₂ => by
      rw [HasTy.translateAtom]
      simpa [FCdot.Atom.root] using HasTy.translateAtom_root h₁
  | _, _, _, _, .sub h _ => by
      rw [HasTy.translateAtom]
      simpa [FCdot.Atom.root] using HasTy.translateAtom_root h

/-! ## Typedness of the evidence and atom translations -/

mutual

/-- The shape half of the evidence translation is typed at the translated
shapes: the vanilla `Sub.translate_typed`, read at the shape sort. -/
theorem Sub.translateShape_typed : ∀ {s : Sig} {Γ : Ctx s} {S T : Ty s} (d : Sub Γ S T), Γ.Wf →
    Γ.translate ⊢ˢ d.translateShape : S.translateShape ≤ T.translateShape
  | _, _, _, _, .top, _ => by rw [Sub.translateShape, Ty.translateShape_top]; exact .top
  | _, _, _, _, .bot, _ => by rw [Sub.translateShape, Ty.translateShape_bot]; exact .bot
  | _, _, _, _, .refl, _ => by rw [Sub.translateShape]; exact .refl
  | _, _, _, _, .trans d₁ d₂, hwf => by
      rw [Sub.translateShape]
      exact .trans (d₁.translateShape_typed hwf) (d₂.translateShape_typed hwf)
  | _, _, _, _, @Sub.and1 _ _ S T, _ => by
      by_cases hS : S.isObj = true
      · rw [Sub.translateShape, if_pos hS, Ty.tel_and, Ty.translateShape_and, Ty.translateShape_isObj hS]
        exact .obj (identityMorphism_typed_left _ _ (Ty.tel_closedBnds S))
      · have hS' : S.isObj = false := by simpa using hS
        rw [Sub.translateShape, if_neg hS, Ty.tel_and, Ty.translateShape_and]
        exact .bound ((Ty.tel_bnd_at hS').append_left' T.tel)
  | _, _, _, _, @Sub.and2 _ _ S T, _ => by
      by_cases hT : T.isObj = true
      · rw [Sub.translateShape, if_pos hT, Ty.tel_and, Ty.translateShape_and, Ty.translateShape_isObj hT]
        exact .obj (identityMorphism_typed_right _ _ (Ty.tel_closedBnds T))
      · have hT' : T.isObj = false := by simpa using hT
        rw [Sub.translateShape, if_neg hT, Ty.tel_and, Ty.translateShape_and]
        refine .bound ?_
        have h0 := FCdot.Telescope.At.append_right S.tel (Ty.tel_bnd_at hT')
        rwa [Nat.add_zero] at h0
  | _, _, _, _, .and d₁ d₂, hwf => by
      rw [Sub.translateShape, Ty.translateShape_and]
      exact .pair (into_typed (d₁.translateShape_typed hwf)) (into_typed (d₂.translateShape_typed hwf))
  | _, _, _, _, .fld d, hwf => by
      rw [Sub.translateShape]
      simp only [Ty.translateShape_fld, Ty.tel_fld]
      exact .obj (.leC (.le (.has .nil (FCdot.Telescope.At.zero_three _ _ _))
          (FCdot.Telescope.At.one_three _ _ _) .none (.some (d.translateShape_typed hwf)))
        (.leC (FCdot.Telescope.At.two_three _ _ _)) .nil .nil)
  | _, _, _, _, .typ d₁ d₂, hwf => by
      rw [Sub.translateShape]
      simp only [Ty.translateShape_typ, Ty.tel_typ]
      exact .obj (.le (.le .nil (FCdot.Telescope.At.zero_two _ _)
          (.some (d₁.translateShape_typed hwf)) .none)
        (FCdot.Telescope.At.one_two _ _) .none (.some (d₂.translateShape_typed hwf)))
  | _, _, _, _, .selUpper h, hwf => by
      have ha := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_typ, Ty.tel_typ] at ha
      have hm := FCdot.ShapeCo.HasType.member ha .refl (FCdot.Telescope.At.one_two _ _)
      rw [HasTy.translateAtom_root h, FCdot.Shape.substVar_sel_here,
        FCdot.Shape.weaken_substVar] at hm
      rw [Sub.translateShape, Ty.translateShape_sel, Ty.translateShape_typ, Ty.tel_typ]
      exact hm
  | _, _, _, _, .selLower h, hwf => by
      have ha := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_typ, Ty.tel_typ] at ha
      have hm := FCdot.ShapeCo.HasType.member ha .refl (FCdot.Telescope.At.zero_two _ _)
      rw [HasTy.translateAtom_root h, FCdot.Shape.substVar_sel_here,
        FCdot.Shape.weaken_substVar] at hm
      rw [Sub.translateShape, Ty.translateShape_sel, Ty.translateShape_typ, Ty.tel_typ]
      exact hm
  | _, _, _, _, .all d₁ d₂, hwf => by
      rw [Sub.translateShape]
      simp only [Ty.translateShape_all]
      exact .pi (.capt (d₁.translateShape_typed hwf) .refl)
        (.capt (d₂.translateShape_typed (.cons hwf)) .refl)

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
  | _, _, _, _, .andI h₁ h₂, hwf => by
      have i1 := intoAtom_typed (HasTy.translateAtom_typed h₁ hwf)
      have i2 := intoAtom_typed (HasTy.translateAtom_typed h₂ hwf)
      rw [HasTy.translateAtom, Ty.translate_and]
      exact .both i1 i2
        (by simp [HasTy.translateAtom_root h₁, HasTy.translateAtom_root h₂])
  | _, _, _, _, .sub h d, hwf => by
      rw [HasTy.translateAtom]
      exact .cast (HasTy.translateAtom_typed h hwf) (.capt (d.translateShape_typed hwf) .refl)

end

/-- `⟦d⟧` is typed at the translated types: the shape half of the evidence
between the two shapes, the capture half `refl []` between the two (empty)
capture sets. -/
theorem Sub.translate_typed {s : Sig} {Γ : Ctx s} {S T : Ty s} (d : Sub Γ S T) (hwf : Γ.Wf) :
    Γ.translate ⊢ d.translate : S.translate ≤ T.translate :=
  .capt (d.translateShape_typed hwf) .refl

end DotMNF

end Captures
