import Coercions.CapturesCC.DotToFCdot.Evidence
import Coercions.CapturesCC.DotToFCdot.TypesLemmas
import Coercions.CapturesCC.FCdot.TypingRename

namespace CapturesCC

/-!
# Typedness of the evidence translation (Plan III §8.1, M3)

Every subcapturing derivation of DOT-MNF^cc translates to capture-inclusion
evidence with the translated endpoints, every subtyping derivation to
inclusion evidence with the translated endpoints, and every typing derivation
of a variable to an atom of the translated type rooted at that variable.
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

/-! ## Capture witnesses: the same block, for the capture sort

Stage A3a: a declaration shape has capture witnesses of its own, one per
field and one per capture member, collected by `CapWitnesses.append`.  These
are the twins of the `Witnesses` facts just above. -/

theorem CapWitnesses.length_append {s : Sig} :
    ∀ (W W' : CapWitnesses s), (W.append W').length = W.length + W'.length
  | _, .nil => rfl
  | W, .cons W' ℓ C => by
      simp only [CapWitnesses.append, CapWitnesses.length, CapWitnesses.length_append W W']
      omega

theorem CapWitnesses.labels_append {s : Sig} :
    ∀ (W W' : CapWitnesses s), (W.append W').labels = W.labels ++ W'.labels
  | _, .nil => by simp [CapWitnesses.append, CapWitnesses.labels]
  | W, .cons W' ℓ C => by
      simp [CapWitnesses.append, CapWitnesses.labels, CapWitnesses.labels_append W W']

/-- `CapWitnesses.At W i ℓ C`: the `i`-th capture witness of `W`, counted from
the oldest, is `ℓ` at the set `C`. -/
inductive CapWitnesses.At : CapWitnesses s → Nat → Label → CaptureSet s → Prop where
  | here : CapWitnesses.At (.cons W ℓ C) W.length ℓ C
  | there : CapWitnesses.At W i ℓ C → CapWitnesses.At (.cons W ℓ' C') i ℓ C

/-- The labels of a capture-witness list are pairwise distinct. -/
inductive CapWitnesses.Distinct : CapWitnesses s → Prop where
  | nil : CapWitnesses.Distinct .nil
  | cons : CapWitnesses.Distinct W → ℓ ∉ W.labels → CapWitnesses.Distinct (.cons W ℓ C)

theorem CapWitnesses.At.mem_labels {s : Sig} {W : CapWitnesses s} {i : Nat} {ℓ : Label}
    {C : CaptureSet s} (h : CapWitnesses.At W i ℓ C) : ℓ ∈ W.labels := by
  induction h with
  | here => simp [CapWitnesses.labels]
  | there _ ih => simp [CapWitnesses.labels]; exact Or.inl ih

theorem CapWitnesses.At.get {s : Sig} {W : CapWitnesses s} {i : Nat} {ℓ : Label}
    {C : CaptureSet s} (h : CapWitnesses.At W i ℓ C) (hd : W.Distinct) : W.get ℓ = C := by
  induction h with
  | here => simp [CapWitnesses.get]
  | @there W' i' ℓ' C' ℓ'' C'' hAt ih =>
      cases hd with
      | cons hd' hnot =>
          have hne : ℓ' ≠ ℓ'' := by
            intro he; exact hnot (he ▸ hAt.mem_labels)
          simp only [CapWitnesses.get, if_neg hne]
          exact ih hd'

theorem CapWitnesses.At.append_left {s : Sig} {W : CapWitnesses s} {i : Nat} {ℓ : Label}
    {C : CaptureSet s} (h : CapWitnesses.At W i ℓ C) :
    ∀ W' : CapWitnesses s, CapWitnesses.At (W.append W') i ℓ C
  | .nil => h
  | .cons W' _ _ => .there (CapWitnesses.At.append_left h W')

theorem CapWitnesses.At.append_right {s : Sig} (W : CapWitnesses s) {W' : CapWitnesses s}
    {i : Nat} {ℓ : Label} {C : CaptureSet s} (h : CapWitnesses.At W' i ℓ C) :
    CapWitnesses.At (W.append W') (W.length + i) ℓ C := by
  induction h with
  | @here W'' ℓ' C' =>
      have h2 : W.length + W''.length = (W.append W'').length :=
        (CapWitnesses.length_append W W'').symm
      rw [show W.append (CapWitnesses.cons W'' ℓ' C')
            = CapWitnesses.cons (W.append W'') ℓ' C' from rfl, h2]
      exact .here
  | there _ ih => exact .there ih

theorem CapWitnesses.Distinct.append {s : Sig} {W : CapWitnesses s} (hW : W.Distinct) :
    ∀ {W' : CapWitnesses s}, W'.Distinct → (∀ ℓ, ℓ ∈ W.labels → ℓ ∉ W'.labels) →
      (W.append W').Distinct
  | .nil, _, _ => hW
  | .cons W' ℓ C, hW', hdis => by
      cases hW' with
      | cons hW'' hnot =>
          refine .cons (hW.append hW'' ?_) ?_
          · intro ℓ' hℓ' hmem
            exact hdis ℓ' hℓ' (by simp [CapWitnesses.labels]; exact Or.inl hmem)
          · rw [CapWitnesses.labels_append]
            simp only [List.mem_append]
            rintro (h1 | h1)
            · exact hdis ℓ h1 (by simp [CapWitnesses.labels])
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

/-- The `i`-th capture definition sits `i` positions after the type block.
This is the capture-sort twin of `Witnesses.eqEntriesOf_At`. -/
theorem CapWitnesses.eqEntriesOf_At {s : Sig} (self : BVar s .var) (W₀ : CapWitnesses s)
    (base : Telescope s) {W : CapWitnesses s} {i : Nat} {ℓ : Label} {C : CaptureSet s}
    (h : CapWitnesses.At W i ℓ C) :
    (W₀.eqEntriesOf self base W) ∋ (base.length + i ↦ [CapAtom.name self ℓ] ≐ᶜ W₀.get ℓ) := by
  induction h with
  | @here W' ℓ' C' =>
      rw [show W₀.eqEntriesOf self base (CapWitnesses.cons W' ℓ' C')
            = Telescope.cons (W₀.eqEntriesOf self base W')
                ([CapAtom.name self ℓ'] ≐ᶜ W₀.get ℓ') from rfl,
        ← CapWitnesses.eqEntriesOf_length self W₀ base W']
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

theorem CapWitnesses.length_nil {s : Sig} : (CapWitnesses.nil : CapWitnesses s).length = 0 := by
  simp [CapWitnesses.length]

theorem CapWitnesses.At.hereNil {s : Sig} {l : Label} {C : CaptureSet s} :
    CapWitnesses.At (CapWitnesses.cons .nil l C) 0 l C := by
  have h : CapWitnesses.At (CapWitnesses.cons (.nil : CapWitnesses s) l C)
      ((CapWitnesses.nil : CapWitnesses s).length) l C := .here
  rw [CapWitnesses.length_nil] at h
  exact h

theorem CaptureSet.substVar_name_here {s : Sig} (a : Label) (r : BVar s .var) :
    CaptureSet.substVar ([CapAtom.name .here a] : CaptureSet (s,x)) r = [CapAtom.name r a] := by
  simp [CaptureSet.substVar, CaptureSet.rename, CapAtom.rename]

theorem CaptureSet.substVar_nil {s : Sig} (r : BVar s .var) :
    CaptureSet.substVar ([] : CaptureSet (s,x)) r = [] := rfl

theorem Shape.substVar_sel_here {s : Sig} (A : Label) (r : BVar s .var) :
    ((Shape.sel .here A : Shape (s,x)))⟦r⟧ = Shape.sel r A := by
  simp [Shape.substVar, Shape.rename]

end FCdot

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label Morphism ShapeCo CapCo LeCo EqCo ELeCo Has Atom Side)
open scoped FCdot

/-! ## Equations for the type translation

`Shape.translate`, `Shape.tel` and `Shape.telSelf` are a mutual structural recursion, so
their defining equations are not definitional; these are the rewrite rules used
throughout.  Each equation of the vanilla `Ty.translate` is the `Shape.translate` equation
here, the vanilla source and target sorts being the shape sorts, and a type is that shape
with its translated capture set (`Ty.translate_capt`). -/

theorem Shape.translate_top {s : Sig} : (Shape.top : Shape s).translate = ⊤ := by
  simp [Shape.translate]

theorem Shape.translate_bot {s : Sig} : (Shape.bot : Shape s).translate = ⊥ := by
  simp [Shape.translate]

theorem Shape.translate_sel {s : Sig} (y : BVar s .var) (A : Label) :
    (Shape.sel (.var y) A).translate = y ∙ A := by simp [Shape.translate]

theorem Shape.translate_all {s : Sig} (S : Dom s) (T : Cod s) :
    (Shape.all S T).translate = Π(S.translate) T.translate :=
  Shape.translate_all_eq S T

theorem Shape.translate_box {s : Sig} (T : Ty s) :
    (Shape.box T).translate = □ T.translate :=
  Shape.translate_box_eq T

theorem Shape.translate_typ {s : Sig} (A : Label) (S T : Shape s) :
    (Shape.typ A S T).translate = μ (Shape.typ A S T).tel := by simp [Shape.translate]

theorem Shape.translate_fld {s : Sig} (a : Label) (T : Ty s) :
    (Shape.fld a T).translate = μ (Shape.fld a T).tel := by simp [Shape.translate]

theorem Shape.translate_cap {s : Sig} (A : Label) (c₁ c₂ : CaptureSet s) :
    (Shape.cap A c₁ c₂).translate = μ (Shape.cap A c₁ c₂).tel := by simp [Shape.translate]

theorem Shape.translate_and {s : Sig} (S T : Shape s) :
    (Shape.and S T).translate = μ ((Shape.tel S).append (Shape.tel T)) := by
  simp [Shape.translate, Shape.tel]

theorem Shape.translate_mu {s : Sig} (S : Shape (s,x)) :
    (Shape.mu S).translate = μ S.telSelf := by simp [Shape.translate]

theorem Shape.translate_weaken {s : Sig} {k : Kind} (S : Shape s) :
    (S.weaken (k := k)).translate = FCdot.Shape.weaken (k := k) S.translate :=
  Shape.translate_rename S FCdot.Rename.succ

theorem Ty.translate_weaken {s : Sig} {k : Kind} (T : Ty s) :
    (T.weaken (k := k)).translate = FCdot.Ty.weaken (k := k) T.translate :=
  Ty.translate_rename T FCdot.Rename.succ

theorem ETy.translate_weaken {s : Sig} {k : Kind} (E : ETy s) :
    (E.weaken (k := k)).translate = FCdot.ETy.weaken (k := k) E.translate :=
  ETy.translate_rename E FCdot.Rename.succ

theorem Shape.tel_typ {s : Sig} (A : Label) (S T : Shape s) :
    (Shape.typ A S T).tel =
      FCdot.Telescope.cons (FCdot.Telescope.cons .nil ((S.translate)↑ ⊑ .here ∙ A))
        (.here ∙ A ⊑ (T.translate)↑) := by simp [Shape.tel]

theorem Shape.tel_fld {s : Sig} (a : Label) (C : CaptureSet s) (S : Shape s) :
    (Shape.fld a (S ^ C)).tel =
      FCdot.Telescope.cons
        (FCdot.Telescope.cons (FCdot.Telescope.cons .nil (∋ a))
          (.here ∙ a ⊑ (S.translate)↑))
        ([FCdot.CapAtom.name .here a] ⊑ᶜ (C.translate)↑) := by
  simp [Shape.tel]

theorem Shape.tel_cap {s : Sig} (A : Label) (c₁ c₂ : CaptureSet s) :
    (Shape.cap A c₁ c₂).tel =
      FCdot.Telescope.cons
        (FCdot.Telescope.cons .nil ((c₁.translate)↑ ⊑ᶜ [FCdot.CapAtom.name .here A]))
        ([FCdot.CapAtom.name .here A] ⊑ᶜ (c₂.translate)↑) := by
  simp [Shape.tel]

theorem Shape.tel_and {s : Sig} (S T : Shape s) :
    (Shape.and S T).tel = (Shape.tel S).append (Shape.tel T) := by simp [Shape.tel]

theorem Shape.telSelf_typ {s : Sig} (A : Label) (S T : Shape (s,x)) :
    (Shape.typ A S T).telSelf =
      FCdot.Telescope.cons (FCdot.Telescope.cons .nil (S.translate ⊑ .here ∙ A))
        (.here ∙ A ⊑ T.translate) := by simp [Shape.telSelf]

theorem Shape.telSelf_fld {s : Sig} (a : Label) (C : CaptureSet (s,x)) (S : Shape (s,x)) :
    (Shape.fld a (S ^ C)).telSelf =
      FCdot.Telescope.cons
        (FCdot.Telescope.cons (FCdot.Telescope.cons .nil (∋ a))
          (.here ∙ a ⊑ S.translate))
        ([FCdot.CapAtom.name .here a] ⊑ᶜ C.translate) := by
  simp [Shape.telSelf]

theorem Shape.telSelf_cap {s : Sig} (A : Label) (c₁ c₂ : CaptureSet (s,x)) :
    (Shape.cap A c₁ c₂).telSelf =
      FCdot.Telescope.cons
        (FCdot.Telescope.cons .nil (c₁.translate ⊑ᶜ [FCdot.CapAtom.name .here A]))
        ([FCdot.CapAtom.name .here A] ⊑ᶜ c₂.translate) := by
  simp [Shape.telSelf]

theorem Shape.telSelf_and {s : Sig} (S T : Shape (s,x)) :
    (Shape.and S T).telSelf = (Shape.telSelf S).append (Shape.telSelf T) := by
  simp [Shape.telSelf]

/-! ## Telescopes without self-bounds, and telescopes with closed self-bounds -/

theorem _root_.CapturesCC.FCdot.Telescope.NoBnd.append {s' : Sig} {Tel₁ : FCdot.Telescope s'}
    (h₁ : Tel₁.NoBnd) :
    ∀ Tel₂ : FCdot.Telescope s', Tel₂.NoBnd → (Tel₁.append Tel₂).NoBnd
  | .nil, _ => h₁
  | .cons _ (.bnd _), h₂ => h₂.elim
  | .cons Tel (.le _ _), h₂ => FCdot.Telescope.NoBnd.append h₁ Tel h₂
  | .cons Tel (.eq _ _), h₂ => FCdot.Telescope.NoBnd.append h₁ Tel h₂
  | .cons Tel (.has _), h₂ => FCdot.Telescope.NoBnd.append h₁ Tel h₂
  | .cons Tel (.leC _ _), h₂ => FCdot.Telescope.NoBnd.append h₁ Tel h₂
  | .cons Tel (.eqC _ _), h₂ => FCdot.Telescope.NoBnd.append h₁ Tel h₂

theorem _root_.CapturesCC.FCdot.Telescope.NoBnd.rename {s₁ s₂ : Sig} (ρ : FCdot.Rename s₁ s₂) :
    ∀ Tel : FCdot.Telescope s₁, Tel.NoBnd → (Tel.rename ρ).NoBnd
  | .nil, h => h
  | .cons _ (.bnd _), h => h.elim
  | .cons Tel (.le _ _), h => FCdot.Telescope.NoBnd.rename ρ Tel h
  | .cons Tel (.eq _ _), h => FCdot.Telescope.NoBnd.rename ρ Tel h
  | .cons Tel (.has _), h => FCdot.Telescope.NoBnd.rename ρ Tel h
  | .cons Tel (.leC _ _), h => FCdot.Telescope.NoBnd.rename ρ Tel h
  | .cons Tel (.eqC _ _), h => FCdot.Telescope.NoBnd.rename ρ Tel h

theorem _root_.CapturesCC.FCdot.Telescope.NoBnd.closedBnds {s : Sig} :
    ∀ {Tel : FCdot.Telescope (s,x)}, Tel.NoBnd → Tel.ClosedBnds
  | .nil, _ => .nil
  | .cons _ (.bnd _), h => h.elim
  | .cons Tel (.le _ _), h => .le (FCdot.Telescope.NoBnd.closedBnds h)
  | .cons Tel (.eq _ _), h => .eq (FCdot.Telescope.NoBnd.closedBnds h)
  | .cons Tel (.has _), h => .has (FCdot.Telescope.NoBnd.closedBnds h)
  | .cons Tel (.leC _ _), h => .leC (FCdot.Telescope.NoBnd.closedBnds h)
  | .cons Tel (.eqC _ _), h => .eqC (FCdot.Telescope.NoBnd.closedBnds h)

theorem _root_.CapturesCC.FCdot.Telescope.ClosedBnds.append {s : Sig} {Tel₁ : FCdot.Telescope (s,x)}
    (h₁ : Tel₁.ClosedBnds) :
    ∀ {Tel₂ : FCdot.Telescope (s,x)}, Tel₂.ClosedBnds → (Tel₁.append Tel₂).ClosedBnds
  | _, .nil => h₁
  | _, .le h₂ => .le (FCdot.Telescope.ClosedBnds.append h₁ h₂)
  | _, .eq h₂ => .eq (FCdot.Telescope.ClosedBnds.append h₁ h₂)
  | _, .has h₂ => .has (FCdot.Telescope.ClosedBnds.append h₁ h₂)
  | _, .bnd h₂ => .bnd (FCdot.Telescope.ClosedBnds.append h₁ h₂)
  | _, .leC h₂ => .leC (FCdot.Telescope.ClosedBnds.append h₁ h₂)
  | _, .eqC h₂ => .eqC (FCdot.Telescope.ClosedBnds.append h₁ h₂)

/-- A declaration-shaped body has no self-bounds at all: `Shape.telSelf` only
produces one on a shape `Wf.mu` excludes. -/
theorem Shape.telSelf_noBnd_of_decl {s : Sig} :
    ∀ {S : Shape (s,x)}, Shape.Decl S → (Shape.telSelf S).NoBnd
  | .top, _ => by simp [Shape.telSelf, FCdot.Telescope.NoBnd]
  | .typ _ _ _, _ => by simp [Shape.telSelf, FCdot.Telescope.NoBnd]
  | .fld _ (.capt _ _), _ => by simp [Shape.telSelf, FCdot.Telescope.NoBnd]
  | .cap _ _ _, _ => by simp [Shape.telSelf, FCdot.Telescope.NoBnd]
  | .and S T, h => by
      cases h with
      | and hS hT =>
          simp only [Shape.telSelf]
          exact FCdot.Telescope.NoBnd.append (Shape.telSelf_noBnd_of_decl hS) _
            (Shape.telSelf_noBnd_of_decl hT)
  | .mu T, h => by
      cases h with
      | mu hT =>
          have hd : T.isDecl = true := (Shape.isDecl_iff T).mpr hT
          simp only [Shape.telSelf, if_pos hd, FCdot.Telescope.substVar]
          exact FCdot.Telescope.NoBnd.rename _ _ (Shape.telSelf_noBnd_of_decl hT)

/-- Every self-bound the translation of a shape carries is a weakened closed
shape: this is the closedness convention of `FCdot` (plan §13 item 9). -/
theorem Shape.tel_closedBnds {s : Sig} :
    ∀ S : Shape s, (Shape.tel S : FCdot.Telescope (s,x)).ClosedBnds
  | .top => by simp only [Shape.tel]; exact .nil
  | .bot => by simp only [Shape.tel]; exact .bnd .nil
  | .sel (.var _) _ => by simp only [Shape.tel]; exact .bnd .nil
  | .all (.capt _ _) (.ty (.capt _ _)) => by simp only [Shape.tel]; exact .bnd .nil
  | .all (.capt _ _) (.ex _ (.capt _ _)) => by simp only [Shape.tel]; exact .bnd .nil
  | .box (.capt _ _) => by simp only [Shape.tel]; exact .bnd .nil
  | .typ _ _ _ => by simp only [Shape.tel]; exact .le (.le .nil)
  | .fld _ (.capt _ _) => by simp only [Shape.tel]; exact .leC (.le (.has .nil))
  | .cap _ _ _ => by simp only [Shape.tel]; exact .leC (.leC .nil)
  | .and S T => by
      simp only [Shape.tel]
      exact (Shape.tel_closedBnds S).append (Shape.tel_closedBnds T)
  | .mu T => by
      by_cases hd : T.isDecl = true
      · simp only [Shape.tel, if_pos hd]
        exact (Shape.telSelf_noBnd_of_decl ((Shape.isDecl_iff T).mp hd)).closedBnds
      · simp only [Shape.tel, if_neg hd]
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
theorem into_typed {s : Sig} {Γ : FCdot.Ctx s} {S T : Shape s} {e : FCdot.ShapeCo s}
    (he : Γ ⊢ˢ e : S.translate ≤ T.translate) :
    Γ ⊢ˢ into T e : S.translate ≤ μ T.tel := by
  rw [into]
  by_cases h : T.isObj = true
  · rw [if_pos h, ← Shape.translate_isObj h]; exact he
  · rw [if_neg h, Shape.tel_of_not_isObj (by simpa using h)]
    exact .intoBnd he

/-- The same for atoms; `And-I` needs it on both operands.  The capture set is
carried through unchanged. -/
theorem intoAtom_typed {s : Sig} {Γ : FCdot.Ctx s} {T : Shape s} {C : CaptureSet s}
    {a : FCdot.Atom s} (ha : Γ ⊢ₐ a : FCdot.Ty.capt C.translate T.translate) :
    Γ ⊢ₐ intoAtom T C a : FCdot.Ty.capt C.translate (μ T.tel) := by
  rw [intoAtom]
  by_cases h : T.isObj = true
  · rw [if_pos h, ← Shape.translate_isObj h]; exact ha
  · rw [if_neg h, Shape.tel_of_not_isObj (by simpa using h)]
    simp only [FCdot.ShapeCo.atC]
    exact .cast ha (.capt (.intoBnd .refl) .refl)

/-- The self-bound of a non-object operand sits at position `0` of its own
telescope. -/
theorem Shape.tel_bnd_at {s : Sig} {T : Shape s} (h : T.isObj = false) :
    (Shape.tel T : FCdot.Telescope (s,x)) ∋ (0 ↦ ⊑ T.translate↑) := by
  rw [Shape.tel_of_not_isObj h]
  exact .here

/-! ## Shapes of the declaration type of a set of definitions -/

/-- The declaration shape of a set of definitions: type members and capture
members have equal bounds, and every conjunct is a type member, a capture
member, a field, or an intersection of those. -/
inductive Shape.LiteralShape : {s : Sig} → Shape s → Prop where
  | typ : Shape.LiteralShape (.typ A T T)
  | cap : Shape.LiteralShape (.cap A c c)
  | fld : Shape.LiteralShape (.fld a T)
  | and : Shape.LiteralShape S → Shape.LiteralShape T → Shape.LiteralShape (.and S T)

/-- The member labels of a declaration shape, left to right. -/
def Shape.declLabels : Shape s → List Label
  | .typ A _ _ => [A]
  | .cap A _ _ => [A]
  | .fld a _ => [a]
  | .and S T => S.declLabels ++ T.declLabels
  | _ => []

/-- The member labels of a declaration shape are pairwise distinct. -/
inductive Shape.DistinctLabels : {s : Sig} → Shape s → Prop where
  | typ : Shape.DistinctLabels (.typ A S T)
  | cap : Shape.DistinctLabels (.cap A c₁ c₂)
  | fld : Shape.DistinctLabels (.fld a T)
  | and : Shape.DistinctLabels S → Shape.DistinctLabels T →
      (∀ l, l ∈ S.declLabels → l ∉ T.declLabels) → Shape.DistinctLabels (.and S T)

/-! ### The two label facts travel back through a renaming

B1.7 types a literal's definitions against its declaration shape read under
the class root, so `DefsTy.literalShape` and `DefsTy.distinctLabels` land at
`S.underRoot` while the literal's coercion is built from `S`.  Both facts
come back, the first through injectivity of renaming and the second through
the invariance of `declLabels`. -/

theorem Shape.LiteralShape.typ_inv {s : Sig} {A : Label} {S T : Shape s}
    (h : Shape.LiteralShape (.typ A S T)) : S = T := by cases h; rfl

theorem Shape.LiteralShape.cap_inv {s : Sig} {A : Label} {c₁ c₂ : CaptureSet s}
    (h : Shape.LiteralShape (.cap A c₁ c₂)) : c₁ = c₂ := by cases h; rfl

theorem Shape.LiteralShape.and_inv {s : Sig} {S T : Shape s}
    (h : Shape.LiteralShape (.and S T)) : Shape.LiteralShape S ∧ Shape.LiteralShape T := by
  cases h with | and h₁ h₂ => exact ⟨h₁, h₂⟩

theorem Shape.literalShape_of_rename {s1 s2 : Sig} (ρ : Rename s1 s2) (hρ : ρ.Injective) :
    ∀ (S : Shape s1), Shape.LiteralShape (S.rename ρ) → Shape.LiteralShape S
  | .typ A S1 S2, h => by
      simp only [Shape.rename] at h
      have he : S1.rename ρ = S2.rename ρ := Shape.LiteralShape.typ_inv h
      have hs : S1 = S2 := Shape.rename_inj S1 S2 ρ hρ he
      subst hs
      exact .typ
  | .cap A c1 c2, h => by
      simp only [Shape.rename] at h
      have he := Shape.LiteralShape.cap_inv h
      have hc : c1 = c2 := CaptureSet.rename_inj ρ hρ c1 c2 he
      subst hc
      exact .cap
  | .fld _ _, _ => .fld
  | .and S1 S2, h => by
      simp only [Shape.rename] at h
      have h' := Shape.LiteralShape.and_inv h
      exact .and (Shape.literalShape_of_rename ρ hρ S1 h'.1)
        (Shape.literalShape_of_rename ρ hρ S2 h'.2)
  | .top, h => by simp only [Shape.rename] at h; cases h
  | .bot, h => by simp only [Shape.rename] at h; cases h
  | .sel _ _, h => by simp only [Shape.rename] at h; cases h
  | .mu _, h => by simp only [Shape.rename] at h; cases h
  | .all _ _, h => by simp only [Shape.rename] at h; cases h
  | .box _, h => by simp only [Shape.rename] at h; cases h

theorem Shape.declLabels_rename {s1 s2 : Sig} :
    ∀ (S : Shape s1) (ρ : Rename s1 s2), (S.rename ρ).declLabels = S.declLabels
  | .top, _ => rfl
  | .bot, _ => rfl
  | .sel _ _, _ => rfl
  | .typ _ _ _, _ => rfl
  | .cap _ _ _, _ => rfl
  | .fld _ _, _ => rfl
  | .mu _, _ => rfl
  | .all _ _, _ => rfl
  | .box _, _ => rfl
  | .and S T, ρ => by
      simp only [Shape.rename, Shape.declLabels, Shape.declLabels_rename S ρ,
        Shape.declLabels_rename T ρ]

theorem Shape.distinctLabels_of_rename {s1 s2 : Sig} (ρ : Rename s1 s2) :
    ∀ (S : Shape s1), Shape.DistinctLabels (S.rename ρ) → Shape.DistinctLabels S
  | .typ _ _ _, _ => .typ
  | .cap _ _ _, _ => .cap
  | .fld _ _, _ => .fld
  | .and S T, h => by
      simp only [Shape.rename] at h
      cases h with
      | and h₁ h₂ hdis =>
          refine .and (Shape.distinctLabels_of_rename ρ S h₁)
            (Shape.distinctLabels_of_rename ρ T h₂) ?_
          intro l hl hl'
          exact hdis l (by rw [Shape.declLabels_rename]; exact hl)
            (by rw [Shape.declLabels_rename]; exact hl')
  | .top, h => by simp only [Shape.rename] at h; cases h
  | .bot, h => by simp only [Shape.rename] at h; cases h
  | .sel _ _, h => by simp only [Shape.rename] at h; cases h
  | .mu _, h => by simp only [Shape.rename] at h; cases h
  | .all _ _, h => by simp only [Shape.rename] at h; cases h
  | .box _, h => by simp only [Shape.rename] at h; cases h

/-- The two facts at the literal's own declaration shape, from the same two
at the shape read under the class root. -/
theorem Shape.literalShape_of_underRoot {s : Sig} {S : Shape (s,x)}
    (h : Shape.LiteralShape S.underRoot) : Shape.LiteralShape S :=
  Shape.literalShape_of_rename Rename.succ.lift Rename.succ_injective.lift S h

theorem Shape.distinctLabels_of_underRoot {s : Sig} {S : Shape (s,x)}
    (h : Shape.DistinctLabels S.underRoot) : Shape.DistinctLabels S :=
  Shape.distinctLabels_of_rename Rename.succ.lift S h

theorem DefsTy.literalShape : ∀ {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {d : Defs s}
    {S : Shape s}, DefsTy U Γ d S → Shape.LiteralShape S
  | _, _, _, _, _, .typ => .typ
  | _, _, _, _, _, .cap => .cap
  | _, _, _, _, _, .trm _ => .fld
  | _, _, _, _, _, .and h₁ h₂ => .and h₁.literalShape h₂.literalShape

theorem DefsTy.declLabels_eq : ∀ {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {d : Defs s}
    {S : Shape s}, DefsTy U Γ d S → S.declLabels = d.labels
  | _, _, _, _, _, .typ => by simp [Shape.declLabels, Defs.labels]
  | _, _, _, _, _, .cap => by simp [Shape.declLabels, Defs.labels]
  | _, _, _, _, _, .trm _ => by simp [Shape.declLabels, Defs.labels]
  | _, _, _, _, _, .and h₁ h₂ => by
      simp only [Shape.declLabels, Defs.labels, h₁.declLabels_eq, h₂.declLabels_eq]

theorem DefsTy.distinctLabels : ∀ {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {d : Defs s}
    {S : Shape s}, DefsTy U Γ d S → Defs.Distinct d → Shape.DistinctLabels S
  | _, _, _, _, _, .typ, _ => .typ
  | _, _, _, _, _, .cap, _ => .cap
  | _, _, _, _, _, .trm _, _ => .fld
  | _, _, _, _, _, .and h₁ h₂, hd => by
      cases hd with
      | and hd₁ hd₂ hdis =>
          refine .and (h₁.distinctLabels hd₁) (h₂.distinctLabels hd₂) ?_
          intro l hl
          rw [h₂.declLabels_eq]
          exact hdis l (h₁.declLabels_eq ▸ hl)

/-! ## Witnesses of a declaration shape

A type member has a type witness and no capture witness, a capture member has
a capture witness and no type witness, and a field has one of each.  So the
labels of each witness list are among the declaration labels, and
distinctness of the latter gives distinctness of both. -/

theorem Shape.mem_witnesses_labels {s : Sig} :
    ∀ (S : Shape (s,x)) {l : Label}, l ∈ S.witnesses.labels → l ∈ S.declLabels
  | .top, _, h => by simp [Shape.witnesses, FCdot.Witnesses.labels] at h
  | .bot, _, h => by simp [Shape.witnesses, FCdot.Witnesses.labels] at h
  | .sel _ _, _, h => by simp [Shape.witnesses, FCdot.Witnesses.labels] at h
  | .all _ _, _, h => by simp [Shape.witnesses, FCdot.Witnesses.labels] at h
  | .box _, _, h => by simp [Shape.witnesses, FCdot.Witnesses.labels] at h
  | .mu _, _, h => by simp [Shape.witnesses, FCdot.Witnesses.labels] at h
  | .cap _ _ _, _, h => by simp [Shape.witnesses, FCdot.Witnesses.labels] at h
  | .typ A S T, _, h => by
      simpa [Shape.witnesses, FCdot.Witnesses.labels, Shape.declLabels] using h
  | .fld a (.capt C S), _, h => by
      simpa [Shape.witnesses, FCdot.Witnesses.labels, Shape.declLabels] using h
  | .and S T, l, h => by
      rw [Shape.witnesses, FCdot.Witnesses.labels_append, List.mem_append] at h
      rw [Shape.declLabels, List.mem_append]
      exact h.imp (Shape.mem_witnesses_labels S) (Shape.mem_witnesses_labels T)

theorem Shape.mem_capWitnesses_labels {s : Sig} :
    ∀ (S : Shape (s,x)) {l : Label}, l ∈ S.capWitnesses.labels → l ∈ S.declLabels
  | .top, _, h => by simp [Shape.capWitnesses, FCdot.CapWitnesses.labels] at h
  | .bot, _, h => by simp [Shape.capWitnesses, FCdot.CapWitnesses.labels] at h
  | .sel _ _, _, h => by simp [Shape.capWitnesses, FCdot.CapWitnesses.labels] at h
  | .all _ _, _, h => by simp [Shape.capWitnesses, FCdot.CapWitnesses.labels] at h
  | .box _, _, h => by simp [Shape.capWitnesses, FCdot.CapWitnesses.labels] at h
  | .mu _, _, h => by simp [Shape.capWitnesses, FCdot.CapWitnesses.labels] at h
  | .typ _ _ _, _, h => by simp [Shape.capWitnesses, FCdot.CapWitnesses.labels] at h
  | .cap A c₁ c₂, _, h => by
      simpa [Shape.capWitnesses, FCdot.CapWitnesses.labels, Shape.declLabels] using h
  | .fld a (.capt C S), _, h => by
      simpa [Shape.capWitnesses, FCdot.CapWitnesses.labels, Shape.declLabels] using h
  | .and S T, l, h => by
      rw [Shape.capWitnesses, FCdot.CapWitnesses.labels_append, List.mem_append] at h
      rw [Shape.declLabels, List.mem_append]
      exact h.imp (Shape.mem_capWitnesses_labels S) (Shape.mem_capWitnesses_labels T)

/-- The catch-all clauses of `Shape.witnesses` and `Shape.capWitnesses`, as
rewrite rules: a capture member has no type witness, a type member no capture
witness. -/
theorem Shape.witnesses_cap {s : Sig} (A : Label) (c₁ c₂ : CaptureSet (s,x)) :
    (Shape.cap A c₁ c₂).witnesses = .nil := by simp [Shape.witnesses]

theorem Shape.capWitnesses_typ {s : Sig} (A : Label) (S T : Shape (s,x)) :
    (Shape.typ A S T).capWitnesses = .nil := by simp [Shape.capWitnesses]

theorem Shape.witnesses_distinct {s : Sig} :
    ∀ (S : Shape (s,x)), S.DistinctLabels → S.witnesses.Distinct
  | .top, h => by cases h
  | .bot, h => by cases h
  | .sel _ _, h => by cases h
  | .all _ _, h => by cases h
  | .box _, h => by cases h
  | .mu _, h => by cases h
  | .typ A S T, _ => by
      rw [Shape.witnesses]
      exact .cons .nil (by simp [FCdot.Witnesses.labels])
  | .cap A c₁ c₂, _ => by rw [Shape.witnesses_cap]; exact .nil
  | .fld a (.capt C S), _ => by
      rw [Shape.witnesses]
      exact .cons .nil (by simp [FCdot.Witnesses.labels])
  | .and S T, h => by
      cases h with
      | and hS hT hdis =>
          rw [Shape.witnesses]
          refine (Shape.witnesses_distinct S hS).append (Shape.witnesses_distinct T hT) ?_
          intro l hl hl'
          exact hdis l (Shape.mem_witnesses_labels S hl) (Shape.mem_witnesses_labels T hl')

theorem Shape.capWitnesses_distinct {s : Sig} :
    ∀ (S : Shape (s,x)), S.DistinctLabels → S.capWitnesses.Distinct
  | .top, h => by cases h
  | .bot, h => by cases h
  | .sel _ _, h => by cases h
  | .all _ _, h => by cases h
  | .box _, h => by cases h
  | .mu _, h => by cases h
  | .typ A S T, _ => by rw [Shape.capWitnesses_typ]; exact .nil
  | .cap A c₁ c₂, _ => by
      rw [Shape.capWitnesses]
      exact .cons .nil (by simp [FCdot.CapWitnesses.labels])
  | .fld a (.capt C S), _ => by
      rw [Shape.capWitnesses]
      exact .cons .nil (by simp [FCdot.CapWitnesses.labels])
  | .and S T, h => by
      cases h with
      | and hS hT hdis =>
          rw [Shape.capWitnesses]
          refine (Shape.capWitnesses_distinct S hS).append (Shape.capWitnesses_distinct T hT) ?_
          intro l hl hl'
          exact hdis l (Shape.mem_capWitnesses_labels S hl) (Shape.mem_capWitnesses_labels T hl')

/-! ## What the templates of `litMorphism` need from the literal's telescope -/

/-- The definition equality that the templates of `S` read, at definition offset `e`. -/
def Shape.EqSpec {s : Sig} (src : FCdot.Telescope (s,x)) : Shape (s,x) → Nat → Prop
  | .typ A S _, e => src ∋ (e ↦ .here ∙ A ≐ S.translate)
  | .fld a (.capt _ S), e => src ∋ (e ↦ .here ∙ a ≐ S.translate)
  | .and S T, e => Shape.EqSpec src S e ∧ Shape.EqSpec src T (e + S.witnesses.length)
  | _, _ => True

/-- The field presences that the templates of `S` inherit, at presence offset
`off`.  `Shape.fieldLabels` puts the right conjunct first, so on an
intersection it is the right conjunct that starts at `off`. -/
def Shape.HasSpec {s : Sig} (src : FCdot.Telescope (s,x)) : Shape (s,x) → Nat → Prop
  | .fld a _, off => src ∋ (off ↦ ∋ a)
  | .and S T, off => Shape.HasSpec src S (off + T.fieldLabels.length) ∧ Shape.HasSpec src T off
  | _, _ => True

/-- The capture definitions that the templates of `S` read, at capture offset
`off`.  The capture block of `Telescope.ofLiteral` follows
`Shape.capWitnesses`, which is the structural order, so this is
`Shape.EqSpec` at a different base and a different list. -/
def Shape.CapSpec {s : Sig} (src : FCdot.Telescope (s,x)) : Shape (s,x) → Nat → Prop
  | .fld a (.capt C _), off => src ∋ (off ↦ [FCdot.CapAtom.name .here a] ≐ᶜ C.translate)
  | .cap A c₁ _, off => src ∋ (off ↦ [FCdot.CapAtom.name .here A] ≐ᶜ c₁.translate)
  | .and S T, off => Shape.CapSpec src S off ∧ Shape.CapSpec src T (off + S.capWitnesses.length)
  | _, _ => True

/-! ## The morphism of a literal -/

theorem litMorphism_and_fst {s : Sig} (S T : Shape (s,x)) (e c h : Nat) :
    (litMorphism (.and S T) e c h).1 =
      (litMorphism S e c (h + T.fieldLabels.length)).1.append
        (litMorphism T (litMorphism S e c (h + T.fieldLabels.length)).2.1
          (litMorphism S e c (h + T.fieldLabels.length)).2.2.1 h).1 := by
  rw [litMorphism]

theorem litMorphism_and_eq {s : Sig} (S T : Shape (s,x)) (e c h : Nat) :
    (litMorphism (.and S T) e c h).2.1 =
      (litMorphism T (litMorphism S e c (h + T.fieldLabels.length)).2.1
        (litMorphism S e c (h + T.fieldLabels.length)).2.2.1 h).2.1 := by
  rw [litMorphism]

theorem litMorphism_and_cap {s : Sig} (S T : Shape (s,x)) (e c h : Nat) :
    (litMorphism (.and S T) e c h).2.2.1 =
      (litMorphism T (litMorphism S e c (h + T.fieldLabels.length)).2.1
        (litMorphism S e c (h + T.fieldLabels.length)).2.2.1 h).2.2.1 := by
  rw [litMorphism]

theorem litMorphism_and_has {s : Sig} (S T : Shape (s,x)) (e c h : Nat) :
    (litMorphism (.and S T) e c h).2.2.2 =
      (litMorphism S e c (h + T.fieldLabels.length)).2.2.2 := by
  rw [litMorphism]

theorem litMorphism_offsets {s : Sig} : ∀ (S : Shape (s,x)) (e c h : Nat),
    (litMorphism S e c h).2.1 = e + S.witnesses.length ∧
      (litMorphism S e c h).2.2.1 = c + S.capWitnesses.length ∧
      (litMorphism S e c h).2.2.2 = h + S.fieldLabels.length
  | .top, e, c, h => by
      simp [litMorphism, Shape.witnesses, Shape.capWitnesses, Shape.fieldLabels,
        FCdot.Witnesses.length, FCdot.CapWitnesses.length]
  | .bot, e, c, h => by
      simp [litMorphism, Shape.witnesses, Shape.capWitnesses, Shape.fieldLabels,
        FCdot.Witnesses.length, FCdot.CapWitnesses.length]
  | .sel _ _, e, c, h => by
      simp [litMorphism, Shape.witnesses, Shape.capWitnesses, Shape.fieldLabels,
        FCdot.Witnesses.length, FCdot.CapWitnesses.length]
  | .all _ _, e, c, h => by
      simp [litMorphism, Shape.witnesses, Shape.capWitnesses, Shape.fieldLabels,
        FCdot.Witnesses.length, FCdot.CapWitnesses.length]
  | .box _, e, c, h => by
      simp [litMorphism, Shape.witnesses, Shape.capWitnesses, Shape.fieldLabels,
        FCdot.Witnesses.length, FCdot.CapWitnesses.length]
  | .mu _, e, c, h => by
      simp [litMorphism, Shape.witnesses, Shape.capWitnesses, Shape.fieldLabels,
        FCdot.Witnesses.length, FCdot.CapWitnesses.length]
  | .typ A S T, e, c, h => by
      simp [litMorphism, Shape.witnesses, Shape.capWitnesses, Shape.fieldLabels,
        FCdot.Witnesses.length, FCdot.CapWitnesses.length]
  | .cap A c₁ c₂, e, c, h => by
      simp [litMorphism, Shape.witnesses, Shape.capWitnesses, Shape.fieldLabels,
        FCdot.Witnesses.length, FCdot.CapWitnesses.length]
  | .fld a (.capt C S), e, c, h => by
      simp [litMorphism, Shape.witnesses, Shape.capWitnesses, Shape.fieldLabels,
        FCdot.Witnesses.length, FCdot.CapWitnesses.length]
  | .and S T, e, c, h => by
      have hS := litMorphism_offsets S e c (h + T.fieldLabels.length)
      have hT := litMorphism_offsets T (litMorphism S e c (h + T.fieldLabels.length)).2.1
        (litMorphism S e c (h + T.fieldLabels.length)).2.2.1 h
      refine ⟨?_, ?_, ?_⟩
      · rw [litMorphism_and_eq, hT.1, hS.1, Shape.witnesses, FCdot.Witnesses.length_append]
        omega
      · rw [litMorphism_and_cap, hT.2.1, hS.2.1, Shape.capWitnesses,
          FCdot.CapWitnesses.length_append]
        omega
      · rw [litMorphism_and_has, hS.2.2, Shape.fieldLabels, List.length_append]
        omega

theorem litMorphism_typed {s : Sig} {Γ : FCdot.Ctx s} {src : FCdot.Telescope (s,x)} :
    ∀ (S : Shape (s,x)), Shape.LiteralShape S → ∀ (e c h : Nat),
      Shape.EqSpec src S e → Shape.CapSpec src S c → Shape.HasSpec src S h →
      Γ ⊢ (litMorphism S e c h).1 : src ⇒ S.telSelf
  | .top, hsh, _, _, _, _, _, _ => by cases hsh
  | .bot, hsh, _, _, _, _, _, _ => by cases hsh
  | .sel _ _, hsh, _, _, _, _, _, _ => by cases hsh
  | .all _ _, hsh, _, _, _, _, _, _ => by cases hsh
  | .box _, hsh, _, _, _, _, _, _ => by cases hsh
  | .mu _, hsh, _, _, _, _, _, _ => by cases hsh
  | .typ A S T', hsh, e, c, h, heq, _, _ => by
      cases hsh
      rw [Shape.EqSpec] at heq
      rw [litMorphism, Shape.telSelf_typ]
      exact .leEq (.leEqSym .nil heq .none .none) heq .none .none
  | .cap A c₁ c₂, hsh, e, c, h, _, hcap, _ => by
      cases hsh
      rw [Shape.CapSpec] at hcap
      rw [litMorphism, Shape.telSelf_cap]
      exact .leC (.leC .nil (.eqSymC hcap) .nil .nil) (.eqC hcap) .nil .nil
  | .fld a (.capt C S), _, e, c, h, heq, hcap, hhas => by
      rw [Shape.EqSpec] at heq
      rw [Shape.CapSpec] at hcap
      rw [Shape.HasSpec] at hhas
      rw [litMorphism, Shape.telSelf_fld]
      exact .leC (.leEq (.has .nil hhas) heq .none .none) (.eqC hcap) .nil .nil
  | .and S T', hsh, e, c, h, heq, hcap, hhas => by
      cases hsh with
      | and hS hT =>
          rw [Shape.EqSpec] at heq
          rw [Shape.CapSpec] at hcap
          rw [Shape.HasSpec] at hhas
          obtain ⟨heq₁, heq₂⟩ := heq
          obtain ⟨hcap₁, hcap₂⟩ := hcap
          obtain ⟨hhas₁, hhas₂⟩ := hhas
          have hoff := litMorphism_offsets S e c (h + T'.fieldLabels.length)
          have ih₁ := litMorphism_typed (Γ := Γ) S hS e c (h + T'.fieldLabels.length)
            heq₁ hcap₁ hhas₁
          have ih₂ := litMorphism_typed (Γ := Γ) T' hT
            (litMorphism S e c (h + T'.fieldLabels.length)).2.1
            (litMorphism S e c (h + T'.fieldLabels.length)).2.2.1 h
            (by rw [hoff.1]; exact heq₂) (by rw [hoff.2.1]; exact hcap₂) hhas₂
          rw [litMorphism_and_fst, Shape.telSelf_and]
          exact ih₁.append ih₂

/-! ## The definition equalities, capture definitions and presences of a
literal's own telescope -/

theorem eqSpec_of {s : Sig} {Wall : FCdot.Witnesses (s,x)} (hdist : Wall.Distinct)
    (Wc : FCdot.CapWitnesses (s,x)) (lsAll : List Label) :
    ∀ (S : Shape (s,x)) (e : Nat),
      (∀ i l X, FCdot.Witnesses.At S.witnesses i l X → FCdot.Witnesses.At Wall (e + i) l X) →
      Shape.EqSpec (FCdot.Telescope.ofLiteral Wall Wc lsAll) S e
  | .top, _, _ => by simp [Shape.EqSpec]
  | .bot, _, _ => by simp [Shape.EqSpec]
  | .sel _ _, _, _ => by simp [Shape.EqSpec]
  | .all _ _, _, _ => by simp [Shape.EqSpec]
  | .box _, _, _ => by simp [Shape.EqSpec]
  | .mu _, _, _ => by simp [Shape.EqSpec]
  | .cap _ _ _, _, _ => by simp [Shape.EqSpec]
  | .typ A S T', e, hpos => by
      simp only [Shape.witnesses] at hpos
      have h1 := hpos 0 A S.translate FCdot.Witnesses.At.hereNil
      rw [Nat.add_zero] at h1
      have h2 := FCdot.Witnesses.eqEntriesOf_At FCdot.BVar.here Wall h1
      rw [h1.get hdist] at h2
      rw [Shape.EqSpec]
      exact FCdot.Telescope.At.hasEntries lsAll (FCdot.CapWitnesses.At.eqEntries h2)
  | .fld a (.capt C S), e, hpos => by
      simp only [Shape.witnesses] at hpos
      have h1 := hpos 0 a S.translate FCdot.Witnesses.At.hereNil
      rw [Nat.add_zero] at h1
      have h2 := FCdot.Witnesses.eqEntriesOf_At FCdot.BVar.here Wall h1
      rw [h1.get hdist] at h2
      rw [Shape.EqSpec]
      exact FCdot.Telescope.At.hasEntries lsAll (FCdot.CapWitnesses.At.eqEntries h2)
  | .and S T', e, hpos => by
      simp only [Shape.witnesses] at hpos
      rw [Shape.EqSpec]
      refine ⟨eqSpec_of hdist Wc lsAll S e (fun i l X hAt => hpos i l X (hAt.append_left _)), ?_⟩
      refine eqSpec_of hdist Wc lsAll T' (e + S.witnesses.length) (fun i l X hAt => ?_)
      have hh := hpos (S.witnesses.length + i) l X
        (FCdot.Witnesses.At.append_right S.witnesses hAt)
      rw [show e + (S.witnesses.length + i) = e + S.witnesses.length + i by omega] at hh
      exact hh

theorem hasSpec_of {s : Sig} {src : FCdot.Telescope (s,x)} :
    ∀ (S : Shape (s,x)) (off : Nat),
      (∀ i l, FCdot.LabelAt S.fieldLabels i l → src ∋ (off + i ↦ ∋ l)) →
      Shape.HasSpec src S off
  | .top, _, _ => by simp [Shape.HasSpec]
  | .bot, _, _ => by simp [Shape.HasSpec]
  | .sel _ _, _, _ => by simp [Shape.HasSpec]
  | .all _ _, _, _ => by simp [Shape.HasSpec]
  | .box _, _, _ => by simp [Shape.HasSpec]
  | .mu _, _, _ => by simp [Shape.HasSpec]
  | .typ _ _ _, _, _ => by simp [Shape.HasSpec]
  | .cap _ _ _, _, _ => by simp [Shape.HasSpec]
  | .fld a T', off, hpos => by
      simp only [Shape.fieldLabels] at hpos
      have h1 := hpos 0 a .here
      rw [Nat.add_zero] at h1
      rw [Shape.HasSpec]
      exact h1
  | .and S T', off, hpos => by
      simp only [Shape.fieldLabels] at hpos
      rw [Shape.HasSpec]
      refine ⟨?_, hasSpec_of T' off (fun i l hAt => hpos i l (hAt.append_left _))⟩
      refine hasSpec_of S (off + T'.fieldLabels.length) (fun i l hAt => ?_)
      have hh := hpos (T'.fieldLabels.length + i) l (FCdot.LabelAt.append_right hAt T'.fieldLabels)
      rw [show off + (T'.fieldLabels.length + i) = off + T'.fieldLabels.length + i by omega] at hh
      exact hh

/-- The capture definitions of a literal's own telescope, read at the offset
where its capture block starts.  The proof is `eqSpec_of` in the capture
sort: the capture block lists `Shape.capWitnesses` in the structural order,
and it sits `Wall.length` positions after the start of the telescope. -/
theorem capSpec_of {s : Sig} (Wall : FCdot.Witnesses (s,x))
    {WcAll : FCdot.CapWitnesses (s,x)} (hdist : WcAll.Distinct) (lsAll : List Label) :
    ∀ (S : Shape (s,x)) (c : Nat),
      (∀ i l X, FCdot.CapWitnesses.At S.capWitnesses i l X →
        FCdot.CapWitnesses.At WcAll (c + i) l X) →
      Shape.CapSpec (FCdot.Telescope.ofLiteral Wall WcAll lsAll) S (Wall.length + c)
  | .top, _, _ => by simp [Shape.CapSpec]
  | .bot, _, _ => by simp [Shape.CapSpec]
  | .sel _ _, _, _ => by simp [Shape.CapSpec]
  | .all _ _, _, _ => by simp [Shape.CapSpec]
  | .box _, _, _ => by simp [Shape.CapSpec]
  | .mu _, _, _ => by simp [Shape.CapSpec]
  | .typ _ _ _, _, _ => by simp [Shape.CapSpec]
  | .cap A c₁ c₂, c, hpos => by
      simp only [Shape.capWitnesses] at hpos
      have h1 := hpos 0 A c₁.translate FCdot.CapWitnesses.At.hereNil
      rw [Nat.add_zero] at h1
      have h2 := FCdot.CapWitnesses.eqEntriesOf_At FCdot.BVar.here WcAll Wall.eqEntries h1
      rw [h1.get hdist,
        show (Wall.eqEntries).length = Wall.length from
          FCdot.Witnesses.eqEntriesOf_length _ _ _] at h2
      rw [Shape.CapSpec]
      exact FCdot.Telescope.At.hasEntries lsAll h2
  | .fld a (.capt C S), c, hpos => by
      simp only [Shape.capWitnesses] at hpos
      have h1 := hpos 0 a C.translate FCdot.CapWitnesses.At.hereNil
      rw [Nat.add_zero] at h1
      have h2 := FCdot.CapWitnesses.eqEntriesOf_At FCdot.BVar.here WcAll Wall.eqEntries h1
      rw [h1.get hdist,
        show (Wall.eqEntries).length = Wall.length from
          FCdot.Witnesses.eqEntriesOf_length _ _ _] at h2
      rw [Shape.CapSpec]
      exact FCdot.Telescope.At.hasEntries lsAll h2
  | .and S T', c, hpos => by
      simp only [Shape.capWitnesses] at hpos
      rw [Shape.CapSpec]
      refine ⟨capSpec_of Wall hdist lsAll S c
        (fun i l X hAt => hpos i l X (hAt.append_left _)), ?_⟩
      have hrec := capSpec_of Wall hdist lsAll T' (c + S.capWitnesses.length)
        (fun i l X hAt => by
          have hh := hpos (S.capWitnesses.length + i) l X
            (FCdot.CapWitnesses.At.append_right S.capWitnesses hAt)
          rw [show c + (S.capWitnesses.length + i) = c + S.capWitnesses.length + i by omega] at hh
          exact hh)
      rw [show Wall.length + c + S.capWitnesses.length
            = Wall.length + (c + S.capWitnesses.length) by omega]
      exact hrec

/-! ## The coercion from a literal's precise type to its declared type -/

theorem litCo_typed_of_shape {s : Sig} {Γ : FCdot.Ctx s} {S : Shape (s,x)}
    (hsh : Shape.LiteralShape S) (hdl : Shape.DistinctLabels S) :
    Γ ⊢ˢ litCo S : S.literalShape ≤ (Shape.mu S).translate := by
  have hW : S.witnesses.Distinct := Shape.witnesses_distinct S hdl
  have hWc : S.capWitnesses.Distinct := Shape.capWitnesses_distinct S hdl
  rw [Shape.translate_mu, Shape.literalShape]
  refine .obj (litMorphism_typed S hsh 0 S.witnesses.length
    (S.witnesses.length + S.capWitnesses.length) ?_ ?_ ?_)
  · exact eqSpec_of hW S.capWitnesses S.fieldLabels S 0
      (fun i l X hAt => by rw [Nat.zero_add]; exact hAt)
  · have h := capSpec_of S.witnesses hWc S.fieldLabels S 0
      (fun i l X hAt => by rw [Nat.zero_add]; exact hAt)
    rwa [Nat.add_zero] at h
  · refine hasSpec_of S (S.witnesses.length + S.capWitnesses.length) (fun i l hAt => ?_)
    have hh :=
      FCdot.Telescope.hasEntries_At hAt (S.capWitnesses.eqEntries S.witnesses.eqEntries)
    rw [FCdot.CapWitnesses.eqEntries_length,
      show (S.witnesses.eqEntries).length = S.witnesses.length from
        FCdot.Witnesses.eqEntriesOf_length _ _ _] at hh
    exact hh

/-- `litCo` is closed evidence: it is typed in any context. -/
theorem litCo_typed {s : Sig} {Γ' : FCdot.Ctx s} {U : CaptureSet (s,x)} {Γ : Ctx (s,x)}
    {d : Defs (s,x)} {S : Shape (s,x)} (hd : DefsTy U Γ d S) (hdist : Defs.Distinct d) :
    Γ' ⊢ˢ litCo S : S.literalShape ≤ (Shape.mu S).translate :=
  litCo_typed_of_shape hd.literalShape (hd.distinctLabels hdist)

/-- The same as a type inclusion, at one and the same capture set on both
sides: the literal's assigned set. -/
theorem litCo_atC_typed {s : Sig} {Γ' : FCdot.Ctx s} {U : CaptureSet (s,x)} {Γ : Ctx (s,x)}
    {d : Defs (s,x)} {S : Shape (s,x)} (hd : DefsTy U Γ d S) (hdist : Defs.Distinct d)
    (V : CaptureSet s) :
    Γ' ⊢ (litCo S).atC V.translate : S.literalTy V ≤ ((Shape.mu S) ^ V).translate := by
  simp only [FCdot.ShapeCo.atC, Shape.literalTy, Ty.translate_capt]
  exact .capt (litCo_typed hd hdist) .refl

/-! ## Well-formed contexts

`Ctx.consSelf` records a literal's definitions and declaration shape but not the typing
derivation that relates them, so `litCo` at such a binder is typed only under a side
condition.  `HasTy.obj` supplies it (`DefsTy.literalShape`, `DefsTy.distinctLabels`). -/

inductive Ctx.Wf : {s : Sig} → Ctx s → Prop where
  | nil : Ctx.Wf .nil
  | cons : Ctx.Wf Γ → Ctx.Wf (Γ.cons T)
  | consSelf : Ctx.Wf Γ → Shape.LiteralShape S → Shape.DistinctLabels S →
      Ctx.Wf (Γ.consSelf d S U)
  | consC : Ctx.Wf Γ → Ctx.Wf (Ctx.consC Γ)
  | consRoot : Ctx.Wf Γ → Ctx.Wf (Ctx.consRoot Γ)
  | consInst : Ctx.Wf Γ → Ctx.Wf (Ctx.consInst Γ C)

/-- A scope is well formed when its context is: it adds a root and a rigid
capture binder, neither of which carries a literal. -/
theorem Ctx.Wf.scope {s : Sig} {Γ : Ctx s} (h : Ctx.Wf Γ) : Ctx.Wf Γ.scope :=
  .consC (.consRoot h)

/-- A pack's scope is well formed when its context is: it adds a root and an
instance binder, neither of which carries a literal. -/
theorem Ctx.Wf.scopeInst {s : Sig} {Γ : Ctx s} (h : Ctx.Wf Γ) (C : CaptureSet s) :
    Ctx.Wf (Γ.scopeInst C) :=
  .consInst (.consRoot h)

/-- A lambda body is a scope with the parameter on top. -/
theorem Ctx.Wf.body {s : Sig} {Γ : Ctx s} (h : Ctx.Wf Γ) (T : Dom s) : Ctx.Wf (Γ.body T) :=
  .cons h.scope

/-! ## Atoms of variables -/

theorem Ctx.lookup_cons_here {s : Sig} (Γ : Ctx s) (T : Ty s) :
    (Γ.cons T).lookup .here = T.weaken := rfl

theorem Ctx.lookup_cons_there {s : Sig} (Γ : Ctx s) (T : Ty s) (y : BVar s .var) :
    (Γ.cons T).lookup (.there y) = (Γ.lookup y).weaken := rfl

theorem Ctx.lookup_consSelf_here {s : Sig} (Γ : Ctx s) (d : Defs (s,x)) (S : Shape (s,x))
    (U : CaptureSet s) :
    (Γ.consSelf d S U).lookup .here = (((Shape.mu S) ^ U) : Ty s).weaken := rfl

theorem Ctx.lookup_consSelf_there {s : Sig} (Γ : Ctx s) (d : Defs (s,x)) (S : Shape (s,x))
    (U : CaptureSet s) (y : BVar s .var) :
    (Γ.consSelf d S U).lookup (.there y) = (Γ.lookup y).weaken := rfl

theorem Ctx.lookup_consC_there {s : Sig} (Γ : Ctx s) (y : BVar s .var) :
    (Ctx.consC Γ).lookup (.there y) = (Γ.lookup y).weaken := rfl

theorem Ctx.lookup_consRoot_there {s : Sig} (Γ : Ctx s) (y : BVar s .var) :
    (Ctx.consRoot Γ).lookup (.there y) = (Γ.lookup y).weaken := rfl

theorem Ctx.lookup_consInst_there {s : Sig} (Γ : Ctx s) (C : CaptureSet s)
    (y : BVar s .var) :
    (Ctx.consInst Γ C).lookup (.there y) = (Γ.lookup y).weaken := rfl

theorem Ctx.varAtom_cons_here {s : Sig} (Γ : Ctx s) (T : Ty s) :
    (Γ.cons T).varAtom .here = .var .here := rfl

theorem Ctx.varAtom_cons_there {s : Sig} (Γ : Ctx s) (T : Ty s) (y : BVar s .var) :
    (Γ.cons T).varAtom (.there y) = (Γ.varAtom y)↑ := rfl

theorem Ctx.varAtom_consSelf_here {s : Sig} (Γ : Ctx s) (d : Defs (s,x)) (S : Shape (s,x))
    (U : CaptureSet s) :
    (Γ.consSelf d S U).varAtom .here
      = .cast (.var .here) (FCdot.LeCo.weaken ((litCo S).atC U.translate)) := rfl

theorem Ctx.varAtom_consSelf_there {s : Sig} (Γ : Ctx s) (d : Defs (s,x)) (S : Shape (s,x))
    (U : CaptureSet s) (y : BVar s .var) :
    (Γ.consSelf d S U).varAtom (.there y) = (Γ.varAtom y)↑ := rfl

theorem Ctx.varAtom_consC_there {s : Sig} (Γ : Ctx s) (y : BVar s .var) :
    (Ctx.consC Γ).varAtom (.there y) = (Γ.varAtom y)↑ := rfl

theorem Ctx.varAtom_consRoot_there {s : Sig} (Γ : Ctx s) (y : BVar s .var) :
    (Ctx.consRoot Γ).varAtom (.there y) = (Γ.varAtom y)↑ := rfl

theorem Ctx.varAtom_consInst_there {s : Sig} (Γ : Ctx s) (C : CaptureSet s)
    (y : BVar s .var) :
    (Ctx.consInst Γ C).varAtom (.there y) = (Γ.varAtom y)↑ := rfl

theorem Ctx.varAtom_root {s : Sig} : ∀ (Γ : Ctx s) (y : BVar s .var), (Γ.varAtom y).root = y
  | .cons _ _, .here => by rw [Ctx.varAtom_cons_here]; simp [FCdot.Atom.root]
  | .cons Γ _, .there y => by
      rw [Ctx.varAtom_cons_there]
      simp [FCdot.Atom.weaken, Ctx.varAtom_root Γ y]
  | .consSelf _ _ _ _, .here => by rw [Ctx.varAtom_consSelf_here]; simp [FCdot.Atom.root]
  | .consSelf Γ _ _ _, .there y => by
      rw [Ctx.varAtom_consSelf_there]
      simp [FCdot.Atom.weaken, Ctx.varAtom_root Γ y]
  | .consC Γ, .there y => by
      rw [Ctx.varAtom_consC_there]
      simp [FCdot.Atom.weaken, Ctx.varAtom_root Γ y]
  | .consRoot Γ, .there y => by
      rw [Ctx.varAtom_consRoot_there]
      simp [FCdot.Atom.weaken, Ctx.varAtom_root Γ y]
  | .consInst Γ _, .there y => by
      rw [Ctx.varAtom_consInst_there]
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
  | .consSelf Γ d S U, hwf, .here => by
      cases hwf with
      | consSelf hwf' hsh hdl =>
          rw [Ctx.lookup_consSelf_here, Ctx.varAtom_consSelf_here, Ty.translate_weaken]
          refine .cast .var ?_
          have h0 : Γ.translate ⊢ (litCo S).atC U.translate
              : S.literalTy U ≤ ((Shape.mu S) ^ U).translate := by
            simp only [FCdot.ShapeCo.atC, Shape.literalTy, Ty.translate_capt]
            exact .capt (litCo_typed_of_shape (Γ := Γ.translate) hsh hdl) .refl
          exact h0.weaken (.transparent (S.literalTy U) S.witnesses S.capWitnesses S.fieldLabels)
  | .consSelf Γ d S U, hwf, .there y => by
      cases hwf with
      | consSelf hwf' _ _ =>
          rw [Ctx.lookup_consSelf_there, Ctx.varAtom_consSelf_there, Ty.translate_weaken]
          exact (Ctx.varAtom_typed Γ hwf' y).weaken
            (.transparent (S.literalTy U) S.witnesses S.capWitnesses S.fieldLabels)
  | .consC Γ, hwf, .there y => by
      cases hwf with
      | consC hwf' =>
          rw [Ctx.lookup_consC_there, Ctx.varAtom_consC_there, Ty.translate_weaken]
          exact (Ctx.varAtom_typed Γ hwf' y).weakenC .star rfl
  | .consRoot Γ, hwf, .there y => by
      cases hwf with
      | consRoot hwf' =>
          rw [Ctx.lookup_consRoot_there, Ctx.varAtom_consRoot_there, Ty.translate_weaken]
          exact (Ctx.varAtom_typed Γ hwf' y).weakenRootC
  | .consInst Γ C, hwf, .there y => by
      cases hwf with
      | consInst hwf' =>
          rw [Ctx.lookup_consInst_there, Ctx.varAtom_consInst_there, Ty.translate_weaken]
          exact (Ctx.varAtom_typed Γ hwf' y).weakenC (.inst C.translate) rfl

/-! ## The root of a translated variable typing -/

theorem HasTy.translateAtom_root : ∀ {s : Sig} {U : CaptureSet s} {Γ : Ctx s} {y : BVar s .var}
    {T : Ty s} (h : HasTy U Γ (.path (.var y)) (.ty T)), h.translateAtom.root = y
  | _, _, Γ, y, _, .var => by rw [HasTy.translateAtom]; simp [FCdot.Atom.root, Ctx.varAtom_root Γ y]
  | _, _, _, _, _, .recI h _ => by
      rw [HasTy.translateAtom]
      simpa [FCdot.Atom.root] using HasTy.translateAtom_root h
  | _, _, _, _, _, .recE h _ => by
      rw [HasTy.translateAtom]
      simpa [FCdot.Atom.root] using HasTy.translateAtom_root h
  | _, _, _, _, _, .andI h₁ h₂ => by
      rw [HasTy.translateAtom]
      simpa [FCdot.Atom.root] using HasTy.translateAtom_root h₁
  | _, _, _, _, _, .sub h (.ty _) _ => by
      rw [HasTy.translateAtom]
      simpa [FCdot.Atom.root] using HasTy.translateAtom_root h

/-! ## Typedness of the evidence and atom translations -/

mutual

/-- The capture half of the evidence translation is typed at the translated
capture sets. -/
theorem Subcap.translate_typed : ∀ {s : Sig} {Γ : Ctx s} {C C' : CaptureSet s}
    (f : Subcap Γ C C'), Γ.Wf →
    Γ.translate ⊢ᶜ f.translate : C.translate ⊑ C'.translate
  | _, _, _, _, .refl, _ => by rw [Subcap.translate]; exact .refl
  | _, _, _, _, .trans f g, hwf => by
      rw [Subcap.translate]
      exact .trans (f.translate_typed hwf) (g.translate_typed hwf)
  | _, _, _, _, .elem hsub, _ => by
      rw [Subcap.translate]
      exact .elem hsub.translate
  | _, _, _, _, .union f g, hwf => by
      rw [Subcap.translate, CaptureSet.translate_union]
      exact .union (f.translate_typed hwf) (g.translate_typed hwf)
  | _, Γ, _, _, @Subcap.var _ _ x, hwf => by
      have ha := Ctx.varAtom_typed Γ hwf x
      rw [Ty.eta (Γ.lookup x), Ty.translate_capt] at ha
      have hc := FCdot.CapCo.HasType.capvar ha
      rw [Ctx.varAtom_root Γ x] at hc
      rw [Subcap.translate]
      simpa [CaptureSet.translate, CapAtom.translate?] using hc
  | _, Γ, _, _, @Subcap.inst _ _ κ C hI, _ => by
      rw [Subcap.translate]
      exact .eqToLe (.symm (.instC (Ctx.InstOf.translate hI)))
  | _, Γ, _, _, @Subcap.level _ _ e κ h₁ h₂, _ => by
      cases e <;> rw [Subcap.translate] <;>
        simp only [CaptureSet.translate_cons_var, CaptureSet.translate_cons_cvar,
          CaptureSet.translate_cons_sel, CaptureSet.translate_cons_any,
          CaptureSet.translate_cons_fresh, CaptureSet.translate_nil] <;>
        first
          | exact .level (Ctx.IsRoot.translate h₁) (Ctx.LvlLe.translate rfl h₂)
          | exact .elem (fun _ ha => absurd ha (List.not_mem_nil))
  | _, _, _, _, @Subcap.selLower _ Γ _ x A c₁ c₂ _ h, hwf => by
      have ha := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_capt, Shape.translate_cap] at ha
      have hAt : (Shape.cap A c₁ c₂).tel
          ∋ (0 ↦ (c₁.translate)↑ ⊑ᶜ [FCdot.CapAtom.name .here A]) := by
        rw [Shape.tel_cap]; exact FCdot.Telescope.At.zero_two _ _
      have hm := FCdot.CapCo.HasType.member ha .refl hAt
      rw [HasTy.translateAtom_root h, FCdot.CaptureSet.weaken_substVar',
        FCdot.CaptureSet.substVar_name_here] at hm
      rw [Subcap.translate, Shape.translate_cap]
      simpa [CaptureSet.translate, CapAtom.translate?] using hm
  | _, _, _, _, @Subcap.selUpper _ Γ _ x A c₁ c₂ _ h, hwf => by
      have ha := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_capt, Shape.translate_cap] at ha
      have hAt : (Shape.cap A c₁ c₂).tel
          ∋ (1 ↦ [FCdot.CapAtom.name .here A] ⊑ᶜ (c₂.translate)↑) := by
        rw [Shape.tel_cap]; exact FCdot.Telescope.At.one_two _ _
      have hm := FCdot.CapCo.HasType.member ha .refl hAt
      rw [HasTy.translateAtom_root h, FCdot.CaptureSet.weaken_substVar',
        FCdot.CaptureSet.substVar_name_here] at hm
      rw [Subcap.translate, Shape.translate_cap]
      simpa [CaptureSet.translate, CapAtom.translate?] using hm
  termination_by _ _ _ _ f _ => sizeOf f
  decreasing_by
    all_goals try simp_wf
    all_goals try simp only [← CaptureSet.union_def, Subcap.union.sizeOf_spec]
    all_goals omega

/-- The shape half of the evidence translation is typed at the translated
shapes: the vanilla `Sub.translate_typed`, read at the shape sort. -/
theorem SubShape.translate_typed : ∀ {s : Sig} {Γ : Ctx s} {S T : Shape s}
    (d : SubShape Γ S T), Γ.Wf →
    Γ.translate ⊢ˢ d.translate : S.translate ≤ T.translate
  | _, _, _, _, .top, _ => by rw [SubShape.translate, Shape.translate_top]; exact .top
  | _, _, _, _, .bot, _ => by rw [SubShape.translate, Shape.translate_bot]; exact .bot
  | _, _, _, _, .refl, _ => by rw [SubShape.translate]; exact .refl
  | _, _, _, _, .trans d₁ d₂, hwf => by
      rw [SubShape.translate]
      exact .trans (d₁.translate_typed hwf) (d₂.translate_typed hwf)
  | _, _, _, _, @SubShape.and1 _ _ S T, _ => by
      by_cases hS : S.isObj = true
      · rw [SubShape.translate, if_pos hS, Shape.tel_and, Shape.translate_and,
          Shape.translate_isObj hS]
        exact .obj (identityMorphism_typed_left _ _ (Shape.tel_closedBnds S))
      · have hS' : S.isObj = false := by simpa using hS
        rw [SubShape.translate, if_neg hS, Shape.tel_and, Shape.translate_and]
        exact .bound ((Shape.tel_bnd_at hS').append_left' T.tel)
  | _, _, _, _, @SubShape.and2 _ _ S T, _ => by
      by_cases hT : T.isObj = true
      · rw [SubShape.translate, if_pos hT, Shape.tel_and, Shape.translate_and,
          Shape.translate_isObj hT]
        exact .obj (identityMorphism_typed_right _ _ (Shape.tel_closedBnds T))
      · have hT' : T.isObj = false := by simpa using hT
        rw [SubShape.translate, if_neg hT, Shape.tel_and, Shape.translate_and]
        refine .bound ?_
        have h0 := FCdot.Telescope.At.append_right S.tel (Shape.tel_bnd_at hT')
        rwa [Nat.add_zero] at h0
  | _, _, _, _, .and d₁ d₂, hwf => by
      rw [SubShape.translate, Shape.translate_and]
      exact .pair (into_typed (d₁.translate_typed hwf)) (into_typed (d₂.translate_typed hwf))
  | _, _, _, _, @SubShape.fld _ _ a (.capt C S) (.capt C' S') (.capt dS dC), hwf => by
      rw [SubShape.translate]
      simp only [Shape.translate_fld, Shape.tel_fld]
      exact .obj (.leC (.le (.has .nil (FCdot.Telescope.At.zero_three _ _ _))
          (FCdot.Telescope.At.one_three _ _ _) .none (.some (dS.translate_typed hwf)))
        (.leC (FCdot.Telescope.At.two_three _ _ _))
        .nil (.cons (.closed (dC.translate_typed hwf)) .nil))
  | _, _, _, _, .typ d₁ d₂, hwf => by
      rw [SubShape.translate]
      simp only [Shape.translate_typ, Shape.tel_typ]
      exact .obj (.le (.le .nil (FCdot.Telescope.At.zero_two _ _)
          (.some (d₁.translate_typed hwf)) .none)
        (FCdot.Telescope.At.one_two _ _) .none (.some (d₂.translate_typed hwf)))
  | _, _, _, _, @SubShape.cap _ _ A c₁ c₂ c₁' c₂' f₁ f₂, hwf => by
      rw [SubShape.translate]
      simp only [Shape.translate_cap, Shape.tel_cap]
      exact .obj (.leC (.leC .nil (.leC (FCdot.Telescope.At.zero_two _ _))
          (.cons (.closed (f₁.translate_typed hwf)) .nil) .nil)
        (.leC (FCdot.Telescope.At.one_two _ _)) .nil
        (.cons (.closed (f₂.translate_typed hwf)) .nil))
  | _, _, _, _, .box d, hwf => by
      rw [SubShape.translate]
      simp only [Shape.translate_box]
      exact .boxed (d.translate_typed hwf)
  | _, _, _, _, @SubShape.selUpper _ _ _ _ A S T _ h, hwf => by
      have ha := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_capt, Shape.translate_typ, Shape.tel_typ] at ha
      have hm := FCdot.ShapeCo.HasType.member ha .refl (FCdot.Telescope.At.one_two _ _)
      rw [HasTy.translateAtom_root h, FCdot.Shape.substVar_sel_here,
        FCdot.Shape.weaken_substVar] at hm
      rw [SubShape.translate, Shape.translate_sel, Shape.translate_typ, Shape.tel_typ]
      exact hm
  | _, _, _, _, @SubShape.selLower _ _ _ _ A S T _ h, hwf => by
      have ha := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_capt, Shape.translate_typ, Shape.tel_typ] at ha
      have hm := FCdot.ShapeCo.HasType.member ha .refl (FCdot.Telescope.At.zero_two _ _)
      rw [HasTy.translateAtom_root h, FCdot.Shape.substVar_sel_here,
        FCdot.Shape.weaken_substVar] at hm
      rw [SubShape.translate, Shape.translate_sel, Shape.translate_typ, Shape.tel_typ]
      exact hm
  | _, _, _, _, @SubShape.all _ Γ T1 T2 U1 U2 d₁ d₂, hwf => by
      rw [SubShape.translate]
      simp only [Shape.translate_all]
      have h₁ := d₁.translate_typed hwf.scope
      have h₂ := d₂.translate_typed (hwf.body T2)
      rw [Ctx.translate_scope, Ty.translate_underRoot, Ty.translate_underRoot] at h₁
      rw [Ctx.translate_body, Ty.translate_underRootCod, Ty.translate_underRootCod] at h₂
      exact .pi h₁ h₂
  termination_by _ _ _ _ d _ => sizeOf d

/-- `⟦d⟧` is typed at the translated types: the shape half between the two
shapes, the capture half between the two capture sets. -/
theorem Sub.translate_typed : ∀ {s : Sig} {Γ : Ctx s} {T T' : Ty s} (d : Sub Γ T T'), Γ.Wf →
    Γ.translate ⊢ d.translate : T.translate ≤ T'.translate
  | _, _, _, _, .capt d f, hwf => by
      rw [Sub.translate]
      exact .capt (d.translate_typed hwf) (f.translate_typed hwf)
  termination_by _ _ _ _ d _ => sizeOf d

/-- `⟦d⟧` on answer inclusions is typed at the translated answers: `pack`
becomes the target's pack at the translated witness, read in the translated
pack scope, and `exist` becomes the target's congruence. -/
theorem ESub.translate_typed : ∀ {s : Sig} {Γ : Ctx s} {E E' : ETy s} (d : ESub Γ E E'), Γ.Wf →
    Γ.translate ⊢ᵉ d.translate : E.translate ≤ E'.translate
  | _, _, _, _, .ty d, hwf => by
      rw [ESub.translate.eq_def]
      exact .plain (d.translate_typed hwf)
  | _, _, _, _, @ESub.pack _ _ C _ _ _ f d, hwf => by
      rw [ESub.translate.eq_def]
      refine .pack (f.translate_typed hwf) ?_
      have h := d.translate_typed (hwf.scopeInst C)
      rwa [Ctx.translate_scopeInst, Ty.translate_weaken, Ty.translate_weaken,
        Ty.translate_underRoot] at h
  | _, _, _, _, .exist f d, hwf => by
      rw [ESub.translate.eq_def]
      refine .cong (f.translate_typed hwf) ?_
      have h := d.translate_typed hwf.scope
      rwa [Ctx.translate_scope, Ty.translate_underRoot, Ty.translate_underRoot] at h
  termination_by _ _ _ _ d _ => sizeOf d

theorem HasTy.translateAtom_typed : ∀ {s : Sig} {U : CaptureSet s} {Γ : Ctx s}
    {y : BVar s .var} {T : Ty s} (h : HasTy U Γ (.path (.var y)) (.ty T)), Γ.Wf →
    Γ.translate ⊢ₐ h.translateAtom : T.translate
  | _, _, Γ, y, _, .var, hwf => by
      have ha := Ctx.varAtom_typed Γ hwf y
      rw [Ty.eta (Γ.lookup y), Ty.translate_capt] at ha
      have hr := FCdot.Atom.HasType.recap ha
        (f := .refl [FCdot.CapAtom.var y])
        (by rw [Ctx.varAtom_root Γ y]; exact .refl)
      rw [HasTy.translateAtom]
      simpa [CaptureSet.translate, CapAtom.translate?] using hr
  | _, _, _, y, _, @HasTy.recI _ _ _ _ S C h hdecl, hwf => by
      have ih := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_decl (hdecl.substVar y)] at ih
      have hroot : (HasTy.translateAtom h).root = y := HasTy.translateAtom_root h
      have hu := FCdot.Atom.HasType.unfoldSelf ih
      rw [hroot, Shape.tel_substVar S y] at hu
      rw [HasTy.translateAtom, Ty.translate_capt, Shape.translate_mu]
      refine FCdot.Atom.HasType.foldSelf ?_
      rw [show (FCdot.Atom.unfoldSelf (HasTy.translateAtom h)).root = y by
        simp [FCdot.Atom.root, hroot]]
      exact hu
  | _, _, _, y, _, @HasTy.recE _ _ _ _ S C h hdecl, hwf => by
      have ih := HasTy.translateAtom_typed h hwf
      rw [Ty.translate_capt, Shape.translate_mu] at ih
      have hroot : (HasTy.translateAtom h).root = y := HasTy.translateAtom_root h
      have hu := FCdot.Atom.HasType.unfoldSelf ih
      rw [hroot, ← Shape.tel_substVar S y] at hu
      rw [HasTy.translateAtom, Ty.translate_decl (hdecl.substVar y)]
      refine FCdot.Atom.HasType.foldSelf ?_
      rw [show (FCdot.Atom.unfoldSelf (HasTy.translateAtom h)).root = y by
        simp [FCdot.Atom.root, hroot]]
      exact hu
  | _, _, _, _, _, @HasTy.andI _ _ _ _ S₁ S₂ C h₁ h₂, hwf => by
      have i1 := intoAtom_typed (T := S₁) (C := C)
        (by rw [← Ty.translate_capt]; exact HasTy.translateAtom_typed h₁ hwf)
      have i2 := intoAtom_typed (T := S₂) (C := C)
        (by rw [← Ty.translate_capt]; exact HasTy.translateAtom_typed h₂ hwf)
      rw [HasTy.translateAtom, Ty.translate_capt, Shape.translate_and]
      exact .both i1 i2
        (by simp [HasTy.translateAtom_root h₁, HasTy.translateAtom_root h₂])
  | _, _, _, _, _, .sub h (.ty d) _, hwf => by
      rw [HasTy.translateAtom]
      exact .cast (HasTy.translateAtom_typed h hwf) (d.translate_typed hwf)
  termination_by _ _ _ _ _ h _ => sizeOf h

end

/-! ## T17: member-free source subcapturing never lowers a level

**B3.7.**  The source has no resolution of its own and "confined" is a
target notion, so the source's scope safety is stated through the
translation (decision 32).  It is store free, and it asks for no context
predicate beyond `Ctx.Wf`, which `Subcap.translate_typed` already asks for.

It is not a store-carrying `lvl_safety` because over a typed store the
context is root free, so the store-carrying form is vacuous
(`FCdot.Store.Typed.rootFree`), and the content of the sentence lives in
rooted contexts, which no store types. -/

theorem source_lvl_safety {s : FCdot.Sig} {Γ : Ctx s} {C D : CaptureSet s} (hwf : Γ.Wf)
    {d : Subcap Γ C D} (hd : d.MemberFree) {r : FCdot.CapAtom s}
    (hD : ∀ m, Γ.translate.Confined (Γ.translate.caps m D.translate) r) :
    ∀ n, Γ.translate.Confined (Γ.translate.caps n C.translate) r :=
  FCdot.level_inversion (d.translate_typed hwf) (Subcap.translate_memberFree hd) hD

end DotMNF

end CapturesCC
