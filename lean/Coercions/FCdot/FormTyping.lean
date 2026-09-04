import Coercions.FCdot.Normalizer
import Coercions.FCdot.Resolution
import Coercions.FCdot.Typing

/-!
# Typedness of forms and views

A head form is typed *syntactically*: it is typed evidence for `S ≤ T` when
its pieces of evidence are typed and the two endpoints have the shapes the
form promises.  Shapes are read off `Γ.resolve`, which follows transparent
definitions to a non-name head.

There is one plain typedness judgment, `Γ ⊨ F : S ≤ T`: the endpoints are
closed types unrelated to any particular atom.  An object form is typed
between *opened* telescopes (`Telescope s`, no self binder): each entry is
typed against a proposition of the target (`Γ ⊨ Es : Tel₁ ⇒ Tel₂`), and each
presence entry points at a presence proposition of the source.

The chain of casts of an atom rooted at `r` is typed at the *opened* shapes
(`Γ ⊨[r] F : S ≤ T`, `ChainTyped`): plain typedness between the resolved
endpoints with their self block opened at `r` (`Ctx.resolveAt`), so
`foldSelf` and `unfoldSelf` on the atom do not change what the chain is
typed at.  Plain typedness at `S, T` gives plain typedness at the opened
shapes (`FormTyped.atRoot`, in `FormAlgebra`).

A *view* `Γ ⊨[r, σ] V : Tel` is the telescope of forms of the propositions
of `Tel`, instantiated at the atom's root `r`: inclusion entries are typed
coercion forms, equality entries record equal resolutions, presence entries
name the root and a field the object stored at the root has.

No depth index anywhere: every definition is structural in the form.
-/

namespace FCdot

/-- Field presence in a store. -/
def Store.HasField (σ : Store s) (x : BVar s .var) (ℓ : Label) : Prop :=
  ∃ W F, σ.lookup x = .obj W F ∧ (F.get? ℓ).isSome

/-! ## Shapes: resolve, and open the self block at a root -/

/-- Open the self block of an object type at a root; other types unchanged.
Idempotent, and invisible to `foldSelf`/`unfoldSelf`. -/
def Ty.unfoldAt (r : BVar s .var) : Ty s → Ty s
  | .obj Tel => .obj ((Tel.substVar r).weaken)
  | T => T

@[simp] theorem Ty.unfoldAt_top (r : BVar s .var) : (⊤ : Ty s).unfoldAt r = ⊤ := rfl
@[simp] theorem Ty.unfoldAt_bot (r : BVar s .var) : (⊥ : Ty s).unfoldAt r = ⊥ := rfl
@[simp] theorem Ty.unfoldAt_sel (r x : BVar s .var) (ℓ : Label) : (x ∙ ℓ).unfoldAt r = x ∙ ℓ := rfl
@[simp] theorem Ty.unfoldAt_pi (r : BVar s .var) (S : Ty s) (T : Ty (s,x)) :
    (Π(S) T).unfoldAt r = Π(S) T := rfl
@[simp] theorem Ty.unfoldAt_obj (r : BVar s .var) (Tel : Telescope (s,x)) :
    (μ Tel).unfoldAt r = μ ((Tel⟦r⟧)↑) := rfl

/-- The shape of a type at a root: its resolution with the self block opened
at the root.  The chain of casts of an atom is typed at the atom's root, so
that folding and unfolding the self block are invisible. -/
def Ctx.resolveAt (Γ : Ctx s) (r : BVar s .var) (T : Ty s) : Ty s := (Γ.resolve T).unfoldAt r

/-! ### Notation for typed forms

`Γ ⊨ F : S ≤ T` types a coercion form with plain shapes; `Γ ⊨ Es : Tel₁ ⇒ Tel₂`
types the entries of an object form between opened telescopes. -/

set_option hygiene false in
scoped notation:40 Γ:51 " ⊨ " F:51 " : " S:51 " ≤ " T:51 => FormTyped Γ F S T
set_option hygiene false in
scoped notation:40 Γ:51 " ⊨ " Es:51 " : " Tel₁:51 " ⇒ " Tel₂:51 => EntriesTyped Γ Tel₁ Es Tel₂

mutual

/-- `Γ ⊨ F : S ≤ T`: the head form `F` is typed evidence for `S ≤ T`, with
shapes read off `Γ.resolve`.  Object forms are between opened telescopes. -/
inductive FormTyped {s : Sig} (Γ : Ctx s) : Form s → Ty s → Ty s → Prop where
  | bot : Γ.resolve S = ⊥ → Γ ⊨ .bot : S ≤ T
  | top : Γ.resolve T = ⊤ → Γ ⊨ .top : S ≤ T
  | id : Γ.resolve S = Γ.resolve T → Γ ⊨ .id : S ≤ T
  | eqv : Γ.resolve S = Γ.resolve T → Γ ⊨ .eqv φ : S ≤ T
  | pi : Γ.resolve S = Π(S₁) T₁ → Γ.resolve T = Π(S₂) T₂ →
      Γ ⊢ d : S₂ ≤ S₁ → Γ.cons (.opaque S₂) ⊢ c : T₁ ≤ T₂ →
      Γ ⊨ .pi d c : S ≤ T
  | obj : Γ.resolve S = μ Tel₁↑ → Γ.resolve T = μ Tel₂↑ → Γ ⊨ Es : Tel₁ ⇒ Tel₂ →
      Γ ⊨ .obj Es : S ≤ T

/-- `Γ ⊨ Es : Tel₁ ⇒ Tel₂`: the entries `Es` are typed against the
propositions of the opened telescope `Tel₂`, with presence entries pointing
into the opened source `Tel₁`. -/
inductive EntriesTyped {s : Sig} (Γ : Ctx s) : Telescope s → Entries s → Telescope s → Prop where
  | nil : Γ ⊨ .nil : Tel₁ ⇒ .nil
  | le : Γ ⊨ Es : Tel₁ ⇒ Tel₂ → Γ ⊨ F : S ≤ T →
      Γ ⊨ Es ▹ .le F : Tel₁ ⇒ Tel₂ ▹ S ⊑ T
  | eq : Γ ⊨ Es : Tel₁ ⇒ Tel₂ → Γ.resolve S = Γ.resolve T →
      Γ ⊨ Es ▹ .eq : Tel₁ ⇒ Tel₂ ▹ S ≐ T
  | has : Γ ⊨ Es : Tel₁ ⇒ Tel₂ → Tel₁ ∋ (j ↦ ∋ ℓ) →
      Γ ⊨ Es ▹ .has j : Tel₁ ⇒ Tel₂ ▹ ∋ ℓ

end

open Lean PrettyPrinter in
@[app_unexpander FormTyped] def FormTyped.unexpand : Unexpander
  | `($_ $Γ $F $S $T) => `($Γ ⊨ $F : $S ≤ $T)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander EntriesTyped] def EntriesTyped.unexpand : Unexpander
  | `($_ $Γ $Tel₁ $Es $Tel₂) => `($Γ ⊨ $Es : $Tel₁ ⇒ $Tel₂)
  | _ => throw ()

/-- The chain of casts of an atom rooted at `r` is a form typed at the opened
shapes. -/
def ChainTyped (Γ : Ctx s) (r : BVar s .var) (F : Form s) (S T : Ty s) : Prop :=
  FormTyped Γ F (Γ.resolveAt r S) (Γ.resolveAt r T)

/-- `Γ ⊨[r] F : S ≤ T`: the chain of casts of an atom rooted at `r`, typed
with shapes opened at `r`. -/
scoped notation:40 Γ:51 " ⊨[" r "] " F:51 " : " S:51 " ≤ " T:51 => ChainTyped Γ r F S T

/-! ## Typed views -/

set_option hygiene false in
scoped notation:40 Γ:51 " ⊨[" r ", " σ "] " V:51 " : " Tel:51 => ViewTyped Γ r σ V Tel

/-- `Γ ⊨[r, σ] V : Tel`: over the store `σ`, the view `V` of an atom rooted
at `r` is typed against `Tel` instantiated at `r`. -/
inductive ViewTyped {s : Sig} (Γ : Ctx s) (r : BVar s .var) (σ : Store s) :
    View s → Telescope (s,x) → Prop where
  | nil : Γ ⊨[r, σ] .nil : .nil
  | le {S T : Ty (s,x)} : Γ ⊨[r, σ] V : Tel → Γ ⊨ F : S⟦r⟧ ≤ T⟦r⟧ →
      Γ ⊨[r, σ] V ▹ .le F : Tel ▹ S ⊑ T
  | eq {S T : Ty (s,x)} : Γ ⊨[r, σ] V : Tel → Γ.resolve (S⟦r⟧) = Γ.resolve (T⟦r⟧) →
      Γ ⊨[r, σ] V ▹ .eq : Tel ▹ S ≐ T
  | has : Γ ⊨[r, σ] V : Tel → σ.HasField r ℓ →
      Γ ⊨[r, σ] V ▹ .has r ℓ : Tel ▹ ∋ ℓ

open Lean PrettyPrinter in
@[app_unexpander ViewTyped] def ViewTyped.unexpand : Unexpander
  | `($_ $Γ $r $σ $V $Tel) => `($Γ ⊨[$r, $σ] $V : $Tel)
  | _ => throw ()

/-! ## Indexing telescopes, entries, and views -/

/-- A telescope position is below the telescope's length. -/
theorem Telescope.At.lt {Tel : Telescope s'} {i : Nat} {P : Proposition s'}
    (h : Tel.At i P) : i < Tel.length := by
  induction h with
  | @here Tel P => simp [Telescope.length]
  | there _ ih => simp [Telescope.length]; omega

theorem Entries.At.lt {Es : Entries s} {i : Nat} {E : Entry s}
    (h : Es ∋ (i ↦ E)) : i < Es.length := by
  induction h with
  | here => simp [Entries.length]
  | there _ ih => simp [Entries.length]; omega

theorem View.At.lt {V : View s} {i : Nat} {P : PropForm s}
    (h : V ∋ (i ↦ P)) : i < V.length := by
  induction h with
  | here => simp [View.length]
  | there _ ih => simp [View.length]; omega

/-- Executable lookup of entries agrees with the `At` relation. -/
theorem Entries.At.get? {Es : Entries s} {i : Nat} {E : Entry s}
    (h : Es ∋ (i ↦ E)) : Es.get? i = some E := by
  induction h with
  | here => simp [Entries.get?]
  | there h' ih => simp [Entries.get?, Nat.ne_of_lt h'.lt, ih]

theorem Entries.get?_At : ∀ {Es : Entries s} {i : Nat} {E : Entry s},
    Es.get? i = some E → Es ∋ (i ↦ E)
  | .nil, _, _, h => by simp [Entries.get?] at h
  | .cons Es E', i, E, h => by
      simp only [Entries.get?] at h
      by_cases hi : i = Es.length
      · subst hi; rw [if_pos rfl] at h; cases h; exact .here
      · rw [if_neg hi] at h; exact .there (Entries.get?_At h)

theorem Entries.get?_eq_some_iff_At {Es : Entries s} {i : Nat} {E : Entry s} :
    Es.get? i = some E ↔ Es ∋ (i ↦ E) :=
  ⟨Entries.get?_At, Entries.At.get?⟩

/-- Executable lookup of views agrees with the `At` relation. -/
theorem View.At.get? {V : View s} {i : Nat} {P : PropForm s}
    (h : V ∋ (i ↦ P)) : V.get? i = some P := by
  induction h with
  | here => simp [View.get?]
  | there h' ih => simp [View.get?, Nat.ne_of_lt h'.lt, ih]

theorem View.get?_At : ∀ {V : View s} {i : Nat} {P : PropForm s},
    V.get? i = some P → V ∋ (i ↦ P)
  | .nil, _, _, h => by simp [View.get?] at h
  | .cons V Q, i, P, h => by
      simp only [View.get?] at h
      by_cases hi : i = V.length
      · subst hi; rw [if_pos rfl] at h; cases h; exact .here
      · rw [if_neg hi] at h; exact .there (View.get?_At h)

theorem View.get?_eq_some_iff_At {V : View s} {i : Nat} {P : PropForm s} :
    V.get? i = some P ↔ V ∋ (i ↦ P) :=
  ⟨View.get?_At, View.At.get?⟩

/-! ## Entries of typed views -/

section
variable {σ : Store s} {Γ : Ctx s} {r : BVar s .var}

theorem ViewTyped.length {V : View s} {Tel : Telescope (s,x)}
    (hV : Γ ⊨[r, σ] V : Tel) : V.length = Tel.length := by
  induction hV with
  | nil => rfl
  | le _ _ ih => simp [View.length, Telescope.length, ih]
  | eq _ _ ih => simp [View.length, Telescope.length, ih]
  | has _ _ ih => simp [View.length, Telescope.length, ih]

/-- The entry of a typed view at an inclusion proposition is a typed coercion
form. -/
theorem ViewTyped.le_entry {V : View s} {Tel : Telescope (s,x)}
    (hV : Γ ⊨[r, σ] V : Tel) {i : Nat} {S' T' : Ty (s,x)} (hAt : Tel ∋ (i ↦ S' ⊑ T')) :
    ∃ G, V ∋ (i ↦ .le G) ∧ Γ ⊨ G : S'⟦r⟧ ≤ T'⟦r⟧ := by
  induction hV with
  | nil => cases hAt
  | le hV' hF ih =>
      cases hAt with
      | here => exact ⟨_, by rw [← hV'.length]; exact .here, hF⟩
      | there hAt' => obtain ⟨G, hG, hGt⟩ := ih hAt'; exact ⟨G, .there hG, hGt⟩
  | eq _ _ ih =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hGt⟩ := ih hAt'; exact ⟨G, .there hG, hGt⟩
  | has _ _ ih =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hGt⟩ := ih hAt'; exact ⟨G, .there hG, hGt⟩

/-- The entry of a typed view at an equality proposition is `eq`, and the two
sides resolve equally. -/
theorem ViewTyped.eq_entry {V : View s} {Tel : Telescope (s,x)}
    (hV : Γ ⊨[r, σ] V : Tel) {i : Nat} {S' T' : Ty (s,x)} (hAt : Tel ∋ (i ↦ S' ≐ T')) :
    V ∋ (i ↦ .eq) ∧ Γ.resolve (S'⟦r⟧) = Γ.resolve (T'⟦r⟧) := by
  induction hV with
  | nil => cases hAt
  | le _ _ ih =>
      cases hAt with
      | there hAt' => obtain ⟨hQ, hE⟩ := ih hAt'; exact ⟨.there hQ, hE⟩
  | eq hV' hE ih =>
      cases hAt with
      | here => exact ⟨by rw [← hV'.length]; exact .here, hE⟩
      | there hAt' => obtain ⟨hQ, hE⟩ := ih hAt'; exact ⟨.there hQ, hE⟩
  | has _ _ ih =>
      cases hAt with
      | there hAt' => obtain ⟨hQ, hE⟩ := ih hAt'; exact ⟨.there hQ, hE⟩

/-- The entry of a typed view at a presence proposition names the root and a
field the object at the root has. -/
theorem ViewTyped.has_entry {V : View s} {Tel : Telescope (s,x)}
    (hV : Γ ⊨[r, σ] V : Tel) {i : Nat} {ℓ : Label} (hAt : Tel ∋ (i ↦ ∋ ℓ)) :
    V ∋ (i ↦ .has r ℓ) ∧ σ.HasField r ℓ := by
  induction hV with
  | nil => cases hAt
  | le _ _ ih =>
      cases hAt with
      | there hAt' => obtain ⟨hQ, hH⟩ := ih hAt'; exact ⟨.there hQ, hH⟩
  | eq _ _ ih =>
      cases hAt with
      | there hAt' => obtain ⟨hQ, hH⟩ := ih hAt'; exact ⟨.there hQ, hH⟩
  | has hV' hH ih =>
      cases hAt with
      | here => exact ⟨by rw [← hV'.length]; exact .here, hH⟩
      | there hAt' => obtain ⟨hQ, hH⟩ := ih hAt'; exact ⟨.there hQ, hH⟩

/-- A typed view has an entry at every telescope position. -/
theorem ViewTyped.get?_isSome {V : View s} {Tel : Telescope (s,x)}
    (hV : Γ ⊨[r, σ] V : Tel) {i : Nat} {P : Proposition (s,x)} (h : Tel ∋ (i ↦ P)) :
    ∃ Q, V.get? i = some Q := by
  cases P with
  | le S' T' => obtain ⟨G, hG, _⟩ := hV.le_entry h; exact ⟨_, hG.get?⟩
  | eq S' T' => exact ⟨_, (hV.eq_entry h).1.get?⟩
  | has ℓ => exact ⟨_, (hV.has_entry h).1.get?⟩

end

/-! ## Field presence in a typed store -/

theorem Fields.get?_isSome_of_mem : {F : Fields s} → {ℓ : Label} → ℓ ∈ F.labels →
    (F.get? ℓ).isSome
  | .nil, _, h => by simp [Fields.labels] at h
  | .cons F ℓ' t, ℓ, h => by
      simp only [Fields.labels, List.mem_cons] at h
      by_cases hℓ : ℓ = ℓ'
      · simp [Fields.get?, hℓ]
      · simp only [Fields.get?, hℓ, if_false]
        exact Fields.get?_isSome_of_mem (h.resolve_left hℓ)

end FCdot
