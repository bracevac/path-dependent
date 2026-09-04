import Coercions.FCdot.Normalizer
import Coercions.FCdot.Resolution
import Coercions.FCdot.Typing

/-!
# Typedness of forms and views

A head form is typed *syntactically*: it is typed evidence for `S ≤ T` when
its pieces of evidence are typed and the two endpoints have the shapes the
form promises.  Shapes are read off `Γ.resolve`, which follows transparent
definitions to a non-name head.

Typedness comes in two modes.

* `Γ ⊨ F : S ≤ T` (plain) is for coercion forms and for the entries of
  views: the endpoints are closed types unrelated to any particular atom.
  An object form is typed between *opened* telescopes (`Telescope s`, no
  self binder): each entry is typed against a proposition of the target,
  and each presence entry points at a presence proposition of the source.
* `Γ ⊨[r] F : S ≤ T` (at the root `r`) is for the chain of casts of an
  atom rooted at `r`: shapes are read off the resolved type with its self
  block opened at `r`, so `foldSelf` and `unfoldSelf` on the atom do not
  change what the chain is typed at.  Plain typedness implies typedness at
  every root (`FormTyped.atRoot`, in `FormAlgebra`).

A *view* `Γ ⊨[r, σ] V : Tel` is the list of forms of the propositions of a
telescope, instantiated at the atom's root `r`: inclusion entries are typed
coercion forms, equality entries record equal resolutions, presence entries
name the root and a field the object stored at the root has.

No depth index anywhere: every definition is structural in the form.
-/

namespace FCdot

/-- Field presence in a store. -/
def Store.HasField (σ : Store s) (x : BVar s .var) (ℓ : Label) : Prop :=
  ∃ W F, σ.lookup x = .obj W F ∧ (F.get? ℓ).isSome

/-! ## Shapes: resolve, and optionally open the self block at a root -/

/-- Open the self block of an object type at a root; other types unchanged.
Idempotent, and invisible to `foldSelf`/`unfoldSelf`. -/
def Ty.unfoldAt (r : BVar s .var) : Ty s → Ty s
  | .obj Tel => .obj ((Tel.substVar r).weaken)
  | T => T

/-- The shape of a type: its resolution, opened at the root when one is
given.  Coercion forms and views use no root (their endpoints are closed
types unrelated to any atom); the chain of casts of an atom is typed at the
atom's root, so that folding and unfolding the self block are invisible. -/
def Ctx.resolveAt (Γ : Ctx s) : Option (BVar s .var) → Ty s → Ty s
  | none, T => Γ.resolve T
  | some r, T => (Γ.resolve T).unfoldAt r

/-! ### Notation for typed forms

`Γ ⊨ F : S ≤ T` types a coercion form with plain shapes; `Γ ⊨[r] F : S ≤ T`
types the chain of casts of an atom rooted at `r`, with shapes opened at
`r`.  `Γ ⊨ Es : Tel₁ ⇒ Tel₂` types the entries of an object form between
opened telescopes. -/

set_option hygiene false in
scoped notation:40 Γ:51 " ⊨ " F:51 " : " S:51 " ≤ " T:51 => FormTyped Γ none F S T
set_option hygiene false in
scoped notation:40 Γ:51 " ⊨[" r "] " F:51 " : " S:51 " ≤ " T:51 => FormTyped Γ (some r) F S T
set_option hygiene false in
scoped notation:40 Γ:51 " ⊨ " Es:51 " : " Tel₁:51 " ⇒ " Tel₂:51 => EntriesTyped Γ none Tel₁ Es Tel₂
set_option hygiene false in
scoped notation:40 Γ:51 " ⊨[" r "] " Es:51 " : " Tel₁:51 " ⇒ " Tel₂:51 => EntriesTyped Γ (some r) Tel₁ Es Tel₂

section

variable (Γ : Ctx s) (ρ : Option (BVar s .var))

mutual

/-- `FormTyped Γ ρ F S T`: the head form `F` is typed evidence for `S ≤ T`,
with shapes read off `Γ.resolveAt ρ`.  Object forms are between opened
telescopes. -/
inductive FormTyped : Form s → Ty s → Ty s → Prop where
  | bot {S T : Ty s} : Γ.resolve S = .bot → FormTyped .bot S T
  | top {S T : Ty s} : Γ.resolve T = .top → FormTyped .top S T
  | id {S T : Ty s} : Γ.resolveAt ρ S = Γ.resolveAt ρ T → FormTyped .id S T
  | eqv {φ : EqCo s} {S T : Ty s} : Γ.resolveAt ρ S = Γ.resolveAt ρ T → FormTyped (.eqv φ) S T
  | pi {d : LeCo s} {c : LeCo (s,x)} {S T S₁ S₂ : Ty s} {T₁ T₂ : Ty (s,x)} :
      Γ.resolve S = .pi S₁ T₁ → Γ.resolve T = .pi S₂ T₂ →
      LeCo.HasType Γ d S₂ S₁ → LeCo.HasType (Γ.cons (.opaque S₂)) c T₁ T₂ →
      FormTyped (.pi d c) S T
  | obj {Es : List (Entry s)} {S T : Ty s} {Tel₁ Tel₂ : Telescope s} :
      Γ.resolveAt ρ S = .obj Tel₁.weaken → Γ.resolveAt ρ T = .obj Tel₂.weaken →
      EntriesTyped Tel₁ Es Tel₂ → FormTyped (.obj Es) S T

/-- `EntriesTyped Γ ρ Tel₁ Es Tel₂`: the entries `Es` are typed against the
propositions of the opened telescope `Tel₂`, with presence entries pointing
into the opened source `Tel₁`. -/
inductive EntriesTyped : Telescope s → List (Entry s) → Telescope s → Prop where
  | nil {Tel₁ : Telescope s} : EntriesTyped Tel₁ [] .nil
  | le {Tel₁ Tel₂ : Telescope s} {Es : List (Entry s)} {F : Form s} {S' T' : Ty s} :
      EntriesTyped Tel₁ Es Tel₂ → FormTyped F S' T' →
      EntriesTyped Tel₁ (Es ++ [.le F]) (.cons Tel₂ (.le S' T'))
  | eq {Tel₁ Tel₂ : Telescope s} {Es : List (Entry s)} {S' T' : Ty s} :
      EntriesTyped Tel₁ Es Tel₂ → Γ.resolve S' = Γ.resolve T' →
      EntriesTyped Tel₁ (Es ++ [.eq]) (.cons Tel₂ (.eq S' T'))
  | has {Tel₁ Tel₂ : Telescope s} {Es : List (Entry s)} {j : Nat} {ℓ : Label} :
      EntriesTyped Tel₁ Es Tel₂ → Tel₁.At j (.has ℓ) →
      EntriesTyped Tel₁ (Es ++ [.has j]) (.cons Tel₂ (.has ℓ))

end

end

open Lean PrettyPrinter in
@[app_unexpander FormTyped] def FormTyped.unexpand : Unexpander
  | `($_ $Γ $ρ $F $S $T) =>
    match ρ with
    | `(none) => `($Γ ⊨ $F : $S ≤ $T)
    | `(some $r) => `($Γ ⊨[$r] $F : $S ≤ $T)
    | _ => throw ()
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander EntriesTyped] def EntriesTyped.unexpand : Unexpander
  | `($_ $Γ $ρ $Tel₁ $Es $Tel₂) =>
    match ρ with
    | `(none) => `($Γ ⊨ $Es : $Tel₁ ⇒ $Tel₂)
    | `(some $r) => `($Γ ⊨[$r] $Es : $Tel₁ ⇒ $Tel₂)
    | _ => throw ()
  | _ => throw ()

section
variable (Γ : Ctx s) (r : BVar s .var) (σ : Store s)

/-- Typedness of one proposition form against a proposition instantiated at
the root.  Forms in views are coercion forms: plain shapes. -/
def PropFormTyped : Option (PropForm s) → Proposition s → Prop
  | some (.le F), .le S T => FormTyped Γ none F S T
  | some .eq, .eq S T => Γ.resolve S = Γ.resolve T
  | some (.has x ℓ), .has ℓ' => x = r ∧ ℓ = ℓ' ∧ σ.HasField r ℓ
  | _, _ => False

/-- A view is typed against a telescope at the root. -/
def ViewTyped (V : View s) (Tel : Telescope (s,x)) : Prop :=
  V.length = Tel.length ∧
  ∀ i P, Tel.At i P → PropFormTyped Γ r σ (View.nth? V i) (P.substVar r)

end

/-- `Γ ⊨[r, σ] V : Tel`: over the store `σ`, the view `V` of an atom rooted
at `r` is typed against `Tel` instantiated at `r`. -/
scoped notation:40 Γ:51 " ⊨[" r ", " σ "] " V:51 " : " Tel:51 => ViewTyped Γ r σ V Tel

/-! ## Indexing appended views -/

theorem View.nth?_append_lt : ∀ (V V' : View s) (i : Nat), i < V.length →
    View.nth? (V ++ V') i = View.nth? V i
  | [], _, i, h => by simp at h
  | _ :: V, V', 0, _ => rfl
  | _ :: V, V', i + 1, h => by
      simp only [List.cons_append, View.nth?]
      exact View.nth?_append_lt V V' i (by simpa using h)

theorem View.nth?_append_length : ∀ (V : View s) (P : PropForm s),
    View.nth? (V ++ [P]) V.length = some P
  | [], P => rfl
  | Q :: V, P => by
      simp only [List.cons_append, List.length_cons, View.nth?]
      exact View.nth?_append_length V P

theorem View.nth?_lt_length : ∀ (V : View s) (i : Nat) (P : PropForm s),
    View.nth? V i = some P → i < V.length
  | [], _, _, h => by simp [View.nth?] at h
  | _ :: V, 0, _, _ => by simp
  | _ :: V, i + 1, P, h => by
      simp only [View.nth?] at h
      have := View.nth?_lt_length V i P h
      simp; omega

theorem Entries.nth?_append_length : ∀ (Es : List (Entry s)) (E : Entry s),
    Entries.nth? (Es ++ [E]) Es.length = some E
  | [], E => rfl
  | _ :: Es, E => by
      simp only [List.cons_append, List.length_cons, Entries.nth?]
      exact Entries.nth?_append_length Es E

theorem Entries.nth?_append_lt : ∀ (Es Es' : List (Entry s)) (i : Nat), i < Es.length →
    Entries.nth? (Es ++ Es') i = Entries.nth? Es i
  | [], _, i, h => by simp at h
  | _ :: Es, Es', 0, _ => rfl
  | _ :: Es, Es', i + 1, h => by
      simp only [List.cons_append, Entries.nth?]
      exact Entries.nth?_append_lt Es Es' i (by simpa using h)

/-- A telescope position is below the telescope's length. -/
theorem Telescope.At.lt {Tel : Telescope s'} {i : Nat} {P : Proposition s'}
    (h : Tel.At i P) : i < Tel.length := by
  induction h with
  | @here Tel P => simp [Telescope.length]
  | there _ ih => simp [Telescope.length]; omega

/-! ## Typed views -/

section
variable {σ : Store s} {Γ : Ctx s}

theorem ViewTyped_nil {r : BVar s .var} : ViewTyped Γ r σ [] (.nil : Telescope (s,x)) :=
  ⟨rfl, fun _ _ h => by cases h⟩

theorem ViewTyped_cons {V : View s} {Tel : Telescope (s,x)} {P : Proposition (s,x)}
    {P' : PropForm s} {r : BVar s .var}
    (hV : Γ ⊨[r, σ] V : Tel)
    (hP : PropFormTyped Γ r σ (some P') (P⟦r⟧)) :
    Γ ⊨[r, σ] (V ++ [P']) : .cons Tel P := by
  refine ⟨by simp [Telescope.length, hV.1], fun i Q hQ => ?_⟩
  cases hQ with
  | here =>
      rw [← hV.1, View.nth?_append_length]
      exact hP
  | there hQ' =>
      rw [View.nth?_append_lt _ _ _ (by rw [hV.1]; exact hQ'.lt)]
      exact hV.2 i Q hQ'

/-- A typed view has an entry at every telescope position. -/
theorem ViewTyped.nth?_isSome {V : View s} {Tel : Telescope (s,x)} {r : BVar s .var}
    (hV : Γ ⊨[r, σ] V : Tel) {i : Nat} {P : Proposition (s,x)} (h : Tel.At i P) :
    ∃ Q, View.nth? V i = some Q := by
  have := hV.2 i P h
  cases hq : View.nth? V i with
  | none => rw [hq] at this; cases P <;> exact absurd this (by simp [PropFormTyped])
  | some Q => exact ⟨Q, rfl⟩

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
