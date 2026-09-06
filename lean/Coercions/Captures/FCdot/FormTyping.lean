import Coercions.Captures.FCdot.Normalizer
import Coercions.Captures.FCdot.Resolution
import Coercions.Captures.FCdot.Typing

namespace Captures

/-!
# Typedness of forms and views

A head form is typed *syntactically*: it is typed evidence for `S ≤ T` when
its pieces of evidence are typed and the two endpoints have the shapes the
form promises.  Shapes are read off `Γ.resolve`, which follows transparent
definitions to a non-name head.

Typedness has a *mode* `ρ : Option (BVar s .var)`: shapes are read off
`Ctx.resolveAt? ρ`, which is `Γ.resolve` in the plain mode `none` and
`Γ.resolveAt r` (resolution with the self block opened at `r`) in the mode
`some r`.  `Γ ⊨ F : S ≤ T` is the plain mode; `Γ ⊨[r] F : S ≤ T`
(`ChainTyped`) is the mode at a root, at which the chain of casts of an atom
rooted at `r` is typed, so that `foldSelf` and `unfoldSelf` on the atom do
not change what the chain is typed at.  Plain typedness gives typedness at
any root (`FormTyped.atRoot`, in `FormAlgebra`).

An object form is typed between closed telescopes
(`EntriesTyped Γ ρ Tel₁ Es Tel₂`): each entry is a template proving a target
proposition from a source proposition named by index, with closed sides
(`SideTyped`) between weakened closed shapes, or -- for a target bound -- a
closed coercion out of the source object type.  A coercion whose entries do
not consult the view of the source is typed by `BndsTyped Γ ρ S Es Tel`;
such entries are either bounds or *routed* (`Entry.thru`), reaching another
object type by a form out of the source and proving the target proposition
there (`EntryTyped`).  Templates never eliminate through the self's members,
which is what keeps everything structural.

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

/-- Open the self block of an object shape at a root; other shapes
unchanged.  Idempotent, and invisible to `foldSelf`/`unfoldSelf`.  A capture
set is not a resolvable head, so this and every function below live at the
shape sort, which is where the vanilla line's `Ty` now sits. -/
def Shape.unfoldAt (r : BVar s .var) : Shape s → Shape s
  | .obj Tel => .obj ((Tel.substVar r).weaken)
  | S => S

@[simp] theorem Shape.unfoldAt_top (r : BVar s .var) : (⊤ : Shape s).unfoldAt r = ⊤ := rfl
@[simp] theorem Shape.unfoldAt_bot (r : BVar s .var) : (⊥ : Shape s).unfoldAt r = ⊥ := rfl
@[simp] theorem Shape.unfoldAt_sel (r x : BVar s .var) (ℓ : Label) :
    (x ∙ ℓ).unfoldAt r = x ∙ ℓ := rfl
@[simp] theorem Shape.unfoldAt_pi (r : BVar s .var) (S : Dom s) (T : Cod s) :
    (Π(S) T).unfoldAt r = Π(S) T := rfl
@[simp] theorem Shape.unfoldAt_box (r : BVar s .var) (T : Ty s) : (□ T).unfoldAt r = □ T := rfl
@[simp] theorem Shape.unfoldAt_obj (r : BVar s .var) (Tel : Telescope (s,x)) :
    (μ Tel).unfoldAt r = μ ((Tel⟦r⟧)↑) := rfl

/-- The shape at a root: the resolution of a shape with the self block
opened at the root.  The chain of casts of an atom is typed at the atom's root, so
that folding and unfolding the self block are invisible. -/
def Ctx.resolveAt (Γ : Ctx s) (r : BVar s .var) (S : Shape s) : Shape s :=
  (Γ.resolve S).unfoldAt r

/-- The shape at a root is the plain shape, opened. -/
theorem Ctx.resolveAt_of_resolve {Γ : Ctx s} {S U : Shape s} (r : BVar s .var)
    (h : Γ.resolve S = U) : Γ.resolveAt r S = U.unfoldAt r := by rw [Ctx.resolveAt, h]

/-! ### Modes

Typedness of a form is read in one of two *modes*: plainly (`none`), or at a
root (`some r`), where the self block of an object shape is opened at `r`. -/

/-- Shapes in a mode: plain resolution, or resolution opened at a root. -/
def Ctx.resolveAt? (Γ : Ctx s) (ρ : Option (BVar s .var)) (S : Shape s) : Shape s :=
  match ρ with
  | none => Γ.resolve S
  | some r => Γ.resolveAt r S

/-- A telescope opened in a mode. -/
def Telescope.openAt? (ρ : Option (BVar s .var)) (Tel : Telescope (s,x)) : Telescope (s,x) :=
  match ρ with
  | none => Tel
  | some r => (Tel⟦r⟧)↑

@[simp] theorem Ctx.resolveAt?_none (Γ : Ctx s) (S : Shape s) :
    Γ.resolveAt? none S = Γ.resolve S := rfl
@[simp] theorem Ctx.resolveAt?_some (Γ : Ctx s) (r : BVar s .var) (S : Shape s) :
    Γ.resolveAt? (some r) S = Γ.resolveAt r S := rfl
@[simp] theorem Telescope.openAt?_none (Tel : Telescope (s,x)) :
    Telescope.openAt? none Tel = Tel := rfl
@[simp] theorem Telescope.openAt?_some (r : BVar s .var) (Tel : Telescope (s,x)) :
    Telescope.openAt? (some r) Tel = (Tel⟦r⟧)↑ := rfl

@[simp] theorem Ctx.resolveAt?_obj (Γ : Ctx s) (ρ : Option (BVar s .var)) (Tel : Telescope (s,x)) :
    Γ.resolveAt? ρ (μ Tel) = μ (Telescope.openAt? ρ Tel) := by
  cases ρ <;> simp [Ctx.resolveAt?, Ctx.resolveAt, Telescope.openAt?]

@[simp] theorem Ctx.resolveAt?_bot (Γ : Ctx s) (ρ : Option (BVar s .var)) :
    Γ.resolveAt? ρ (⊥ : Shape s) = ⊥ := by cases ρ <;> simp [Ctx.resolveAt?, Ctx.resolveAt]

@[simp] theorem Ctx.resolveAt?_pi (Γ : Ctx s) (ρ : Option (BVar s .var)) (S : Dom s) (T : Cod s) :
    Γ.resolveAt? ρ (Π(S) T) = Π(S) T := by cases ρ <;> simp [Ctx.resolveAt?, Ctx.resolveAt]

@[simp] theorem Ctx.resolveAt?_box (Γ : Ctx s) (ρ : Option (BVar s .var)) (T : Ty s) :
    Γ.resolveAt? ρ (□ T) = □ T := by cases ρ <;> simp [Ctx.resolveAt?, Ctx.resolveAt]

/-- Opening a telescope in a mode is idempotent. -/
@[simp] theorem Telescope.openAt?_idem (ρ : Option (BVar s .var)) (Tel : Telescope (s,x)) :
    Telescope.openAt? ρ (Telescope.openAt? ρ Tel) = Telescope.openAt? ρ Tel := by
  cases ρ with
  | none => rfl
  | some r => simp [Telescope.openAt?]

/-- A shape read in a mode is already open in that mode. -/
theorem Ctx.resolveAt?_opened {Γ : Ctx s} {ρ : Option (BVar s .var)} {S : Shape s}
    {Tel : Telescope (s,x)} (h : Γ.resolveAt? ρ S = μ Tel) : Telescope.openAt? ρ Tel = Tel := by
  cases ρ with
  | none => rfl
  | some r =>
      simp only [Ctx.resolveAt?, Ctx.resolveAt] at h
      cases hres : Γ.resolve S with
      | obj Tel₀ =>
          rw [hres] at h
          simp only [Shape.unfoldAt_obj] at h
          obtain rfl := Shape.obj.inj h
          simp [Telescope.openAt?]
      | bot => rw [hres] at h; simp [Shape.unfoldAt] at h
      | sel x l => rw [hres] at h; simp [Shape.unfoldAt] at h
      | pi S₀ T₀ => rw [hres] at h; simp [Shape.unfoldAt] at h
      | box T₀ => rw [hres] at h; simp [Shape.unfoldAt] at h

/-- A shape read in a mode: the resolved object type is stable. -/
theorem Ctx.resolveAt?_obj_self {Γ : Ctx s} {ρ : Option (BVar s .var)} {S : Shape s}
    {Tel : Telescope (s,x)} (h : Γ.resolveAt? ρ S = μ Tel) : Γ.resolveAt? ρ (μ Tel) = μ Tel := by
  rw [Ctx.resolveAt?_obj, Ctx.resolveAt?_opened h]

/-! ## Holes -/

/-- `Tel.HoleAt h X Y`: the hole `h` reads the source proposition it names as
the inclusion `X ≤ Y`. -/
inductive Telescope.HoleAt (Tel : Telescope (s,x)) :
    Hole → Shape (s,x) → Shape (s,x) → Prop where
  | le : Tel ∋ (j ↦ X ⊑ Y) → Tel.HoleAt (.le j) X Y
  | eq : Tel ∋ (j ↦ X ≐ Y) → Tel.HoleAt (.eq j) X Y
  | eqSym : Tel ∋ (j ↦ Y ≐ X) → Tel.HoleAt (.eqSym j) X Y

/-! ### Typed forms

`FormTyped Γ ρ F S T` types a coercion form with the shapes of mode `ρ`;
`Γ ⊨ F : S ≤ T` is the plain mode, `Γ ⊨[r] F : S ≤ T` the mode at a root.
`EntriesTyped Γ ρ Tel₁ Es Tel₂` types the entries of an object form between
closed telescopes, and `BndsTyped Γ ρ S Es Tel` the bound entries of a
coercion into a bounds-only object type. -/

mutual

/-- `FormTyped Γ ρ F S T`: the head form `F` is typed evidence for `S ≤ T`,
with shapes read off `Γ.resolveAt? ρ`.  Object forms are between closed
telescopes. -/
inductive FormTyped {s : Sig} (Γ : Ctx s) :
    Option (BVar s .var) → Form s → Shape s → Shape s → Prop where
  | bot : Γ.resolveAt? ρ S = ⊥ → FormTyped Γ ρ .bot S T
  | top : Γ.resolveAt? ρ T = ⊤ → FormTyped Γ ρ .top S T
  | id : Γ.resolveAt? ρ S = Γ.resolveAt? ρ T → FormTyped Γ ρ .id S T
  | eqv : Γ.resolveAt? ρ S = Γ.resolveAt? ρ T → FormTyped Γ ρ (.eqv φ) S T
  | pi : Γ.resolveAt? ρ S = Π(S₁) T₁ → Γ.resolveAt? ρ T = Π(S₂) T₂ →
      Γ ⊢ d : S₂ ≤ S₁ → Γ.cons (.opaque S₂) ⊢ c : T₁ ≤ T₂ →
      FormTyped Γ ρ (.pi d c) S T
  | obj : Γ.resolveAt? ρ S = μ Tel₁ → Γ.resolveAt? ρ T = μ Tel₂ →
      EntriesTyped Γ ρ Tel₁ Es Tel₂ → FormTyped Γ ρ (.obj Es) S T
  /-- A box is inert: a coercion between box shapes is a coercion between
      the boxed types, read at their shapes. -/
  | boxed : Γ.resolveAt? ρ S = □ X → Γ.resolveAt? ρ T = □ Y →
      FormTyped Γ ρ G X.shape Y.shape → FormTyped Γ ρ (.boxed G) S T
  /-- Reaching a box shape from a source that is not one: the recorded form
      reaches the boxed type itself.  This is the head form of the chain of a
      `box` atom, whose content is reached from the atom's root. -/
  | boxIn : Γ.resolveAt? ρ T = □ Y → FormTyped Γ ρ F S Y.shape →
      FormTyped Γ ρ (.boxIn F) S T
  /-- Cast by a bound of the source object type. -/
  | bnd : Γ.resolveAt? ρ S = μ Tel → Tel ∋ (i ↦ ⊑ T↑) → FormTyped Γ ρ F T U →
      FormTyped Γ ρ (.bnd i F) S U
  /-- Coercion into a bounds-only object type. -/
  | into : Γ.resolveAt? ρ T = μ Tel → BndsTyped Γ ρ S Es Tel →
      FormTyped Γ ρ (.into Es) S T

/-- A template side as a form: `id` leaves the endpoint unchanged; any other
form is a closed coercion between weakened closed shapes.  A side's evidence
is a `ShapeCo`, so its head form is typed between shapes. -/
inductive SideTyped {s : Sig} (Γ : Ctx s) : Form s → Shape (s,x) → Shape (s,x) → Prop where
  | id : SideTyped Γ .id X X
  | closed : FormTyped Γ none F A B → SideTyped Γ F A↑ B↑

/-- `EntriesTyped Γ ρ Tel₁ Es Tel₂`: each entry of `Es` proves the
corresponding proposition of the target `Tel₂` from a proposition of the
source `Tel₁`: an inclusion by a template around a source inclusion or
equality, an equality from a source equality, a presence from a source
presence, a bound by a closed coercion out of the source object type or by
copying a source bound. -/
inductive EntriesTyped {s : Sig} (Γ : Ctx s) :
    Option (BVar s .var) → Telescope (s,x) → Entries s → Telescope (s,x) → Prop where
  | nil : EntriesTyped Γ ρ Tel₁ .nil .nil
  | le : EntriesTyped Γ ρ Tel₁ Es Tel₂ → Tel₁.HoleAt h X Y →
      SideTyped Γ pre S X → SideTyped Γ post Y T →
      EntriesTyped Γ ρ Tel₁ (Es ▹ .le pre h post) (Tel₂ ▹ S ⊑ T)
  | eq : EntriesTyped Γ ρ Tel₁ Es Tel₂ → Tel₁ ∋ (j ↦ X ≐ Y) →
      EntriesTyped Γ ρ Tel₁ (Es ▹ .eq j false) (Tel₂ ▹ X ≐ Y)
  | eqSym : EntriesTyped Γ ρ Tel₁ Es Tel₂ → Tel₁ ∋ (j ↦ X ≐ Y) →
      EntriesTyped Γ ρ Tel₁ (Es ▹ .eq j true) (Tel₂ ▹ Y ≐ X)
  | has : EntriesTyped Γ ρ Tel₁ Es Tel₂ → Tel₁ ∋ (j ↦ ∋ ℓ) →
      EntriesTyped Γ ρ Tel₁ (Es ▹ .has j) (Tel₂ ▹ ∋ ℓ)
  | bnd : EntriesTyped Γ ρ Tel₁ Es Tel₂ → FormTyped Γ ρ G (μ Tel₁) T →
      EntriesTyped Γ ρ Tel₁ (Es ▹ .bnd G) (Tel₂ ▹ ⊑ T↑)
  /-- The identity template on a source bound, whatever its type. -/
  | bndId : EntriesTyped Γ ρ Tel₁ Es Tel₂ → Tel₁ ∋ (j ↦ ⊑ X) →
      EntriesTyped Γ ρ Tel₁ (Es ▹ .bnd (.bnd j .id)) (Tel₂ ▹ ⊑ X)

/-- `EntryTyped Γ ρ Tel₁ E P`: a single entry proving `P` from the
propositions of `Tel₁`.  Routes never nest and never end in a general bound
entry, so this covers exactly the entries a route can end in. -/
inductive EntryTyped {s : Sig} (Γ : Ctx s) :
    Option (BVar s .var) → Telescope (s,x) → Entry s → Proposition (s,x) → Prop where
  | le : Telescope.HoleAt Tel₁ h X Y → SideTyped Γ pre S X → SideTyped Γ post Y T →
      EntryTyped Γ ρ Tel₁ (.le pre h post) (S ⊑ T)
  | eq : Tel₁ ∋ (j ↦ X ≐ Y) → EntryTyped Γ ρ Tel₁ (.eq j false) (X ≐ Y)
  | eqSym : Tel₁ ∋ (j ↦ X ≐ Y) → EntryTyped Γ ρ Tel₁ (.eq j true) (Y ≐ X)
  | has : Tel₁ ∋ (j ↦ ∋ ℓ) → EntryTyped Γ ρ Tel₁ (.has j) (∋ ℓ)
  | bnd : FormTyped Γ ρ (.bnd j .id) (μ Tel₁) T →
      EntryTyped Γ ρ Tel₁ (.bnd (.bnd j .id)) (⊑ T↑)
  | bndId : Tel₁ ∋ (j ↦ ⊑ X) → EntryTyped Γ ρ Tel₁ (.bnd (.bnd j .id)) (⊑ X)

/-- `BndsTyped Γ ρ S Es Tel`: the entries of a coercion from `S` into the
object type `μ Tel` that do not consult the view of the source. -/
inductive BndsTyped {s : Sig} (Γ : Ctx s) :
    Option (BVar s .var) → Shape s → Entries s → Telescope (s,x) → Prop where
  | nil : BndsTyped Γ ρ S .nil .nil
  | cons : BndsTyped Γ ρ S Es Tel → FormTyped Γ ρ F S T →
      BndsTyped Γ ρ S (Es ▹ .bnd F) (Tel ▹ ⊑ T↑)
  | thru : BndsTyped Γ ρ S Es Tel → FormTyped Γ ρ H S M →
      Γ.resolveAt? ρ M = μ TelM → EntryTyped Γ ρ TelM E P →
      BndsTyped Γ ρ S (Es ▹ .thru H E) (Tel ▹ P)

end

/-! ### Notation for typed forms

`Γ ⊨ F : S ≤ T` types a coercion form with plain shapes, `Γ ⊨[r] F : S ≤ T`
at a root; `Γ ⊨ Es : Tel₁ ⇒ Tel₂` types the entries of an object form
between closed telescopes, plainly. -/

scoped notation:40 Γ:51 " ⊨ " F:51 " : " S:51 " ≤ " T:51 => FormTyped Γ none F S T
scoped notation:40 Γ:51 " ⊨[" r "] " F:51 " : " S:51 " ≤ " T:51 => FormTyped Γ (some r) F S T
scoped notation:40 Γ:51 " ⊨ " Es:51 " : " Tel₁:51 " ⇒ " Tel₂:51 => EntriesTyped Γ none Tel₁ Es Tel₂

/-- The chain of casts of an atom rooted at `r` is a form typed at the root. -/
abbrev ChainTyped (Γ : Ctx s) (r : BVar s .var) (F : Form s) (S T : Shape s) : Prop :=
  FormTyped Γ (some r) F S T

/-! ## Instantiation and weakening of propositions and telescopes -/

@[simp] theorem Telescope.substVar_nil (r : BVar s .var) :
    (Telescope.nil : Telescope (s,x)).substVar r = .nil := rfl
@[simp] theorem Telescope.substVar_cons (Tel : Telescope (s,x)) (P : Proposition (s,x)) (r : BVar s .var) :
    (Tel ▹ P).substVar r = Tel.substVar r ▹ P.substVar r := rfl
@[simp] theorem Proposition.substVar_le (S T : Shape (s,x)) (r : BVar s .var) :
    (S ⊑ T).substVar r = S⟦r⟧ ⊑ T⟦r⟧ := rfl
@[simp] theorem Proposition.substVar_eq (S T : Shape (s,x)) (r : BVar s .var) :
    (S ≐ T).substVar r = S⟦r⟧ ≐ T⟦r⟧ := rfl
@[simp] theorem Proposition.substVar_has (ℓ : Label) (r : BVar s .var) :
    (Proposition.has (s := (s,x)) ℓ).substVar r = ∋ ℓ := rfl
@[simp] theorem Proposition.substVar_bnd (X : Shape (s,x)) (r : BVar s .var) :
    (⊑ X).substVar r = ⊑ X⟦r⟧ := rfl

/-! ## Typed views -/

set_option hygiene false in
scoped notation:40 Γ:51 " ⊨[" r ", " σ "] " V:51 " : " Tel:51 => ViewTyped Γ r σ V Tel

/-- `Γ ⊨[r, σ] V : Tel`: over the store `σ`, the view `V` of an atom rooted
at `r` is typed against `Tel` instantiated at `r`. -/
inductive ViewTyped {s : Sig} (Γ : Ctx s) (r : BVar s .var) (σ : Store s) :
    View s → Telescope (s,x) → Prop where
  | nil : Γ ⊨[r, σ] .nil : .nil
  | le {S T : Shape (s,x)} : Γ ⊨[r, σ] V : Tel → Γ ⊨ F : S⟦r⟧ ≤ T⟦r⟧ →
      Γ ⊨[r, σ] V ▹ .le F : Tel ▹ S ⊑ T
  | eq {S T : Shape (s,x)} : Γ ⊨[r, σ] V : Tel → Γ.resolve (S⟦r⟧) = Γ.resolve (T⟦r⟧) →
      Γ ⊨[r, σ] V ▹ .eq : Tel ▹ S ≐ T
  | has : Γ ⊨[r, σ] V : Tel → σ.HasField r ℓ →
      Γ ⊨[r, σ] V ▹ .has r ℓ : Tel ▹ ∋ ℓ
  /-- A bound of the atom's type, instantiated at the root: a form typed from
      the root's type at the root. -/
  | bnd {X : Shape (s,x)} : Γ ⊨[r, σ] V : Tel →
      FormTyped Γ (some r) G (Γ.lookupTy r).shape (X⟦r⟧) →
      Γ ⊨[r, σ] V ▹ .bnd G : Tel ▹ ⊑ X

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
  | bnd _ _ ih => simp [View.length, Telescope.length, ih]

/-- The entry of a typed view at an inclusion proposition is a typed coercion
form. -/
theorem ViewTyped.le_entry {V : View s} {Tel : Telescope (s,x)}
    (hV : Γ ⊨[r, σ] V : Tel) {i : Nat} {S' T' : Shape (s,x)} (hAt : Tel ∋ (i ↦ S' ⊑ T')) :
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
  | bnd _ _ ih =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hGt⟩ := ih hAt'; exact ⟨G, .there hG, hGt⟩

/-- The entry of a typed view at an equality proposition is `eq`, and the two
sides resolve equally. -/
theorem ViewTyped.eq_entry {V : View s} {Tel : Telescope (s,x)}
    (hV : Γ ⊨[r, σ] V : Tel) {i : Nat} {S' T' : Shape (s,x)} (hAt : Tel ∋ (i ↦ S' ≐ T')) :
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
  | bnd _ _ ih =>
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
  | bnd _ _ ih =>
      cases hAt with
      | there hAt' => obtain ⟨hQ, hH⟩ := ih hAt'; exact ⟨.there hQ, hH⟩

/-- The entry of a typed view at a bound is a form from the root's type to
the bound's type, instantiated at the root. -/
theorem ViewTyped.bnd_entry {V : View s} {Tel : Telescope (s,x)}
    (hV : Γ ⊨[r, σ] V : Tel) {i : Nat} {X : Shape (s,x)} (hAt : Tel ∋ (i ↦ ⊑ X)) :
    ∃ G, V ∋ (i ↦ .bnd G) ∧ FormTyped Γ (some r) G (Γ.lookupTy r).shape (X⟦r⟧) := by
  induction hV with
  | nil => cases hAt
  | le _ _ ih =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hGt⟩ := ih hAt'; exact ⟨G, .there hG, hGt⟩
  | eq _ _ ih =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hGt⟩ := ih hAt'; exact ⟨G, .there hG, hGt⟩
  | has _ _ ih =>
      cases hAt with
      | there hAt' => obtain ⟨G, hG, hGt⟩ := ih hAt'; exact ⟨G, .there hG, hGt⟩
  | bnd hV' hG ih =>
      cases hAt with
      | here => exact ⟨_, by rw [← hV'.length]; exact .here, hG⟩
      | there hAt' => obtain ⟨G, hG', hGt⟩ := ih hAt'; exact ⟨G, .there hG', hGt⟩

/-- A typed view has an entry at every telescope position. -/
theorem ViewTyped.get?_isSome {V : View s} {Tel : Telescope (s,x)}
    (hV : Γ ⊨[r, σ] V : Tel) {i : Nat} {P : Proposition (s,x)} (h : Tel ∋ (i ↦ P)) :
    ∃ Q, V.get? i = some Q := by
  cases P with
  | le S' T' => obtain ⟨G, hG, _⟩ := hV.le_entry h; exact ⟨_, hG.get?⟩
  | eq S' T' => exact ⟨_, (hV.eq_entry h).1.get?⟩
  | has ℓ => exact ⟨_, (hV.has_entry h).1.get?⟩
  | bnd X => obtain ⟨G, hG, _⟩ := hV.bnd_entry h; exact ⟨_, hG.get?⟩

/-! ## Views are stable under folding and unfolding the self block -/

theorem ViewTyped_unfold {V : View s} {Tel : Telescope (s,x)}
    (h : Γ ⊨[r, σ] V : Tel) : Γ ⊨[r, σ] V : ((Tel⟦r⟧)↑) := by
  induction h with
  | nil => exact .nil
  | le _ hF ih =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_le,
        Proposition.weaken_le]
      exact .le ih (by rwa [Shape.weaken_substVar, Shape.weaken_substVar])
  | eq _ hE ih =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_eq,
        Proposition.weaken_eq]
      exact .eq ih (by rwa [Shape.weaken_substVar, Shape.weaken_substVar])
  | has _ hH ih =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_has,
        Proposition.weaken_has]
      exact .has ih hH
  | bnd _ hG ih =>
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_bnd,
        Proposition.weaken_bnd]
      exact .bnd ih (by rwa [Shape.weaken_substVar])

theorem ViewTyped_fold : ∀ {V : View s} {Tel : Telescope (s,x)},
    Γ ⊨[r, σ] V : ((Tel⟦r⟧)↑) → Γ ⊨[r, σ] V : Tel
  | _, .nil, h => by cases h; exact .nil
  | _, .cons Tel (.le S T), h => by
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_le,
        Proposition.weaken_le] at h
      cases h with
      | le hV hF =>
          exact .le (ViewTyped_fold hV) (by rwa [Shape.weaken_substVar, Shape.weaken_substVar] at hF)
  | _, .cons Tel (.eq S T), h => by
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_eq,
        Proposition.weaken_eq] at h
      cases h with
      | eq hV hE =>
          exact .eq (ViewTyped_fold hV) (by rwa [Shape.weaken_substVar, Shape.weaken_substVar] at hE)
  | _, .cons Tel (.has ℓ), h => by
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_has,
        Proposition.weaken_has] at h
      cases h with
      | has hV hH => exact .has (ViewTyped_fold hV) hH
  | _, .cons Tel (.bnd X), h => by
      simp only [Telescope.substVar_cons, Telescope.weaken_cons, Proposition.substVar_bnd,
        Proposition.weaken_bnd] at h
      cases h with
      | bnd hV hG => exact .bnd (ViewTyped_fold hV) (by rwa [Shape.weaken_substVar] at hG)

end

/-! ## The precise view of a literal has no bounds -/

/-- A view with no bound entries. -/
def View.NoBnd (V : View s) : Prop := ∀ (i : Nat) (G : Form s), ¬ View.At V i (.bnd G)

theorem View.NoBnd.nil : View.NoBnd (View.nil (s := s)) := by
  intro i G h; cases h

theorem View.NoBnd.cons {V : View s} {P : PropForm s} (hV : V.NoBnd)
    (hP : ∀ G, P ≠ .bnd G) : (V ▹ P).NoBnd := by
  intro i G h
  cases h with
  | here => exact hP G rfl
  | there h' => exact hV _ _ h'

theorem Witnesses.eqForms_noBnd : ∀ W : Witnesses (s,x), W.eqForms.NoBnd
  | .nil => by rw [Witnesses.eqForms]; exact View.NoBnd.nil
  | .cons W _ _ => by
      rw [Witnesses.eqForms]
      exact (Witnesses.eqForms_noBnd W).cons (by intro G h; cases h)

theorem Fields.hasForms_noBnd (x : BVar s .var) :
    ∀ (ls : List Label) (V : View s), V.NoBnd → (Fields.hasForms x V ls).NoBnd
  | [], V, hV => hV
  | _ :: ls, V, hV => by
      rw [Fields.hasForms]
      exact Fields.hasForms_noBnd x ls _ (hV.cons (by intro G h; cases h))

/-- A literal's precise view has only equality and presence entries. -/
theorem Value.precView_noBnd (x : BVar s .var) (v : Value s) : (v.precView x).NoBnd := by
  cases v with
  | obj W F => exact Fields.hasForms_noBnd x F.labels _ (Witnesses.eqForms_noBnd W)
  | lam S t => exact View.NoBnd.nil
  | cast v e => exact View.NoBnd.nil

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

end Captures
