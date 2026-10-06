import Coercions.FCdot.Store

/-!
# The normalizer: head normal forms of closed evidence

Inclusion evidence over a store normalizes to a head form: `bot`, `top`,
identity, a function coercion with closed domain
and codomain evidence, or an object coercion given by the normal forms of
its templates. Inclusion templates are finite compositions of source facts
with closed coercion sides. The normal form of a coercion does not depend
on the atom it is applied to: it is a telescope of entries, one per target
proposition. Object composition substitutes templates for source facts.
Application interprets the finite template against a supplied receiver
view and combines its resulting forms.

The *view* of a concrete atom is the telescope of normal forms of the
propositions of its (resolved) object type: a location's view is read off
its literal, and the view of a cast atom is obtained by applying the head
form of the cast to the view of the underlying atom.  Eliminating a member
fact looks a view up. The executable normalizer uses fuel. Canonical forms
establish sufficient fuel for well-typed evidence over a store, using
induction on typing together with the composition and interpretation
algebra for forms.

Entries and views are telescope-shaped (oldest first, `cons` at the end),
indexed by an `At` relation mirroring `Telescope.At`, with executable
lookups `get?`.
-/

namespace FCdot

/-! ## Resolution of names through transparent definitions -/

def Ctx.length : Ctx s → Nat
  | .nil => 0
  | .cons Γ _ => Γ.length + 1

/-- One alias step: `some W` if the head of the type is a name defined by a
transparent binder, `none` if the type is settled (a shape, or a name whose
binder is opaque). -/
def Ctx.next (Γ : Ctx s) : Ty s → Option (Ty s)
  | .sel x ℓ => Γ.lookupDef x ℓ
  | _ => none

/-- Follow definitions at the head of a type, with fuel.  Aliases within a
block are allowed, so a chain of definitions may be cyclic; running out of
fuel on a defined name means it is, and a cycle resolves to `⊤`, the object
type with no propositions. -/
def Ctx.resolveFuel (Γ : Ctx s) : Nat → Ty s → Ty s
  | 0, T =>
      match Γ.next T with
      | none => T
      | some _ => ⊤
  | n + 1, T =>
      match Γ.next T with
      | none => T
      | some W => Γ.resolveFuel n W

/-- All defined names of the context, as pairs of binder and label: the
labels of the witnesses of each transparent binder. -/
def Ctx.defPairs : Ctx s → List (BVar s .var × Label)
  | .nil => []
  | .cons Γ b =>
      (Ctx.defPairs Γ).map (fun p => (BVar.there p.1, p.2)) ++
        (match b with
         | .transparent _ W _ => W.labels.map (fun ℓ => (BVar.here, ℓ))
         | .opaque _ => [])

/-- Resolution with enough fuel for any alias chain in the context: a chain
longer than the number of defined names repeats a name, hence is cyclic. -/
def Ctx.resolve (Γ : Ctx s) (T : Ty s) : Ty s := Γ.resolveFuel (Γ.defPairs.length + 1) T

/-! ## Forms, entries, views -/

mutual

/-- Head normal forms of inclusion evidence, closed over the store scope `s`. -/
inductive Form (s : Sig) : Type where
  | bot : Form s
  | top : Form s
  /-- Identity between endpoints with equal resolved shapes. -/
  | id : Form s
  /-- Function coercion: closed domain evidence and codomain evidence under
      the target domain binder. -/
  | pi : LeCo s → LeCo (s,x) → Form s
  /-- Object coercion: one entry per proposition of the target telescope. -/
  | obj : Entries s → Form s
  /-- Cast by a bound: the source resolves to an object type whose `i`-th
      proposition is a bound, and the rest of the coercion goes on from the
      bound's type. -/
  | bnd : Nat → Form s → Form s
  /-- Coercion into an object type using bounds or routes from the source. -/
  | into : FreeEntries s → Form s

/-- A local template. A copied bound is distinguished from a general
coercion out of the source object type. -/
inductive LocalEntry (s : Sig) : Type where
  | le : Form s → Hole → Form s → LocalEntry s
  /-- Compose two inclusion templates over the same source view. -/
  | trans : Form s → LocalEntry s → LocalEntry s → Form s → LocalEntry s
  | eq : Nat → Bool → LocalEntry s
  | has : Nat → LocalEntry s
  | copyBound : Nat → LocalEntry s

/-- An entry of an object coercion. Object entries contain no routes. -/
inductive Entry (s : Sig) : Type where
  | le : Form s → Hole → Form s → Entry s
  | trans : Form s → LocalEntry s → LocalEntry s → Form s → Entry s
  | eq : Nat → Bool → Entry s
  | has : Nat → Entry s
  | bnd : Form s → Entry s
  | copyBound : Nat → Entry s

/-- A view-free entry. Routes end in local templates and cannot nest. -/
inductive FreeEntry (s : Sig) : Type where
  | bnd : Form s → FreeEntry s
  | thru : Form s → LocalEntry s → FreeEntry s

/-- Entries of an object coercion, oldest first. -/
inductive Entries (s : Sig) : Type where
  | nil : Entries s
  | cons : Entries s → Entry s → Entries s

/-- View-free entries, oldest first. -/
inductive FreeEntries (s : Sig) : Type where
  | nil : FreeEntries s
  | cons : FreeEntries s → FreeEntry s → FreeEntries s

end

/-- Decidable tests for the two absorbing forms. -/
def Form.isBot : Form s → Bool
  | .bot => true
  | _ => false

def Form.isTop : Form s → Bool
  | .top => true
  | _ => false

theorem Form.isBot_eq_true {F : Form s} : F.isBot = true ↔ F = .bot := by
  cases F <;> simp [Form.isBot]

theorem Form.isTop_eq_true {F : Form s} : F.isTop = true ↔ F = .top := by
  cases F <;> simp [Form.isTop]

/-- The normal form of one proposition of a concrete atom's telescope. -/
inductive PropForm (s : Sig) : Type where
  | le : Form s → PropForm s
  | eq : PropForm s
  /-- Field `ℓ` is present at binder `x`. -/
  | has : BVar s .var → Label → PropForm s
  /-- A bound of the atom's type: a form typed from the root's type. -/
  | bnd : Form s → PropForm s

/-- The form of a bound entry of a view. -/
def PropForm.bndForm? : PropForm s → Option (Form s)
  | .bnd G => some G
  | _ => none

/-- The view of an atom: the forms of its propositions, oldest first. -/
inductive View (s : Sig) : Type where
  | nil : View s
  | cons : View s → PropForm s → View s

/-! ### Notation for entries and views

`Es ▹ E`, `V ▹ P` extend entries and views; `Es ∋ (i ↦ E)`, `V ∋ (i ↦ P)`
are the `i`-th entry and proposition form, counted from the oldest. -/

scoped infixl:65 " ▹ " => Entries.cons
scoped infixl:65 " ▹ " => FreeEntries.cons
scoped infixl:65 " ▹ " => View.cons

def Entries.length : Entries s → Nat
  | .nil => 0
  | .cons Es _ => Es.length + 1

def FreeEntries.length : FreeEntries s → Nat
  | .nil => 0
  | .cons Es _ => Es.length + 1

def View.length : View s → Nat
  | .nil => 0
  | .cons V _ => V.length + 1

/-- `Es ∋ (i ↦ E)`: the `i`-th entry of `Es` (from the oldest) is `E`. -/
inductive Entries.At : Entries s → Nat → Entry s → Prop where
  | here : Entries.At (Es ▹ E) Es.length E
  | there : Entries.At Es i E → Entries.At (Es ▹ E') i E

/-- The entry at an index of a view-free list. -/
inductive FreeEntries.At : FreeEntries s → Nat → FreeEntry s → Prop where
  | here : FreeEntries.At (Es ▹ E) Es.length E
  | there : FreeEntries.At Es i E → FreeEntries.At (Es ▹ E') i E

/-- `V ∋ (i ↦ P)`: the `i`-th proposition form of `V` (from the oldest) is `P`. -/
inductive View.At : View s → Nat → PropForm s → Prop where
  | here : View.At (V ▹ P) V.length P
  | there : View.At V i P → View.At (V ▹ Q) i P

scoped notation:50 Es:51 " ∋ " "(" i " ↦ " E ")" => Entries.At Es i E
scoped notation:50 Es:51 " ∋ " "(" i " ↦ " E ")" => FreeEntries.At Es i E
scoped notation:50 V:51 " ∋ " "(" i " ↦ " P ")" => View.At V i P

/-- Lookup by index, executable. -/
def Entries.get? : Entries s → Nat → Option (Entry s)
  | .nil, _ => none
  | .cons Es E, i => if i = Es.length then some E else Es.get? i

/-- Lookup by index, executable. -/
def FreeEntries.get? : FreeEntries s → Nat → Option (FreeEntry s)
  | .nil, _ => none
  | .cons Es E, i => if i = Es.length then some E else Es.get? i

/-- Lookup by index, executable. -/
def View.get? : View s → Nat → Option (PropForm s)
  | .nil, _ => none
  | .cons V P, i => if i = V.length then some P else V.get? i

/-! ## Composition of forms -/

/-- The index named by a hole. -/
def Hole.index : Hole → Nat
  | .le j => j
  | .eq j => j
  | .eqSym j => j

/-- Flip the direction of an equality hole. -/
def Hole.flip : Hole → Hole
  | .le j => .le j
  | .eq j => .eqSym j
  | .eqSym j => .eq j

/-- Embed a local recipe into an object entry. -/
def LocalEntry.toEntry : LocalEntry s → Entry s
  | .le pre h post => .le pre h post
  | .trans pre E₁ E₂ post => .trans pre E₁ E₂ post
  | .eq j b => .eq j b
  | .has j => .has j
  | .copyBound j => .copyBound j

/-- General bounds require the whole source coercion; every other entry is local. -/
def Entry.toLocal? : Entry s → Option (LocalEntry s)
  | .le pre h post => some (.le pre h post)
  | .trans pre E₁ E₂ post => some (.trans pre E₁ E₂ post)
  | .eq j b => some (.eq j b)
  | .has j => some (.has j)
  | .copyBound j => some (.copyBound j)
  | .bnd _ => none

@[simp] theorem LocalEntry.toLocal?_toEntry (E : LocalEntry s) :
    E.toEntry.toLocal? = some E := by cases E <;> rfl

/-- A local part is no larger than the object entry containing it. -/
theorem Entry.toLocal?_sizeOf {E : Entry s} {L : LocalEntry s}
    (h : E.toLocal? = some L) : sizeOf L ≤ sizeOf E := by
  cases E <;> simp only [Entry.toLocal?, Option.some.injEq] at h <;> cases h <;> simp

/-- An entry found by lookup is a subterm. -/
theorem Entries.get?_sizeOf : ∀ {Es : Entries s} {j : Nat} {E : Entry s},
    Es.get? j = some E → sizeOf E < sizeOf Es
  | .nil, _, _, h => by simp [Entries.get?] at h
  | .cons Es E', j, E, h => by
      simp only [Entries.get?] at h
      by_cases hj : j = Es.length
      · rw [if_pos hj] at h; cases h; simp; omega
      · rw [if_neg hj] at h
        have := Entries.get?_sizeOf h
        simp; omega

/-- Lookup returning the entry together with the fact that it is a subterm,
for the termination of composition. -/
def Entries.get?Attach : (Es : Entries s) → Nat → Option {E : Entry s // sizeOf E < sizeOf Es}
  | .nil, _ => none
  | .cons Es E, i =>
      if i = Es.length then some ⟨E, by simp; omega⟩
      else (Es.get?Attach i).map fun ⟨E', h⟩ => ⟨E', by simp; omega⟩

theorem Entries.get?Attach_val : ∀ (Es : Entries s) (j : Nat),
    (Es.get?Attach j).map Subtype.val = Es.get? j
  | .nil, _ => rfl
  | .cons Es E, i => by
      simp only [Entries.get?Attach, Entries.get?]
      by_cases h : i = Es.length
      · simp [h]
      · simp [h, ← Entries.get?Attach_val Es i, Option.map_map]

theorem Entries.get?Attach_eq_some {Es : Entries s} {j : Nat} {E : Entry s}
    (h : Es.get? j = some E) : ∃ hlt, Es.get?Attach j = some ⟨E, hlt⟩ := by
  have := Entries.get?Attach_val Es j
  rw [h] at this
  cases hA : Es.get?Attach j with
  | none => rw [hA] at this; simp at this
  | some p =>
      rw [hA] at this
      obtain ⟨E', hlt⟩ := p
      simp at this
      subst this
      exact ⟨hlt, rfl⟩

/-- An entry found by lookup is a subterm. -/
theorem FreeEntries.get?_sizeOf : ∀ {Es : FreeEntries s} {j : Nat} {E : FreeEntry s},
    Es.get? j = some E → sizeOf E < sizeOf Es
  | .nil, _, _, h => by simp [FreeEntries.get?] at h
  | .cons Es E', j, E, h => by
      simp only [FreeEntries.get?] at h
      by_cases hj : j = Es.length
      · rw [if_pos hj] at h; cases h; simp; omega
      · rw [if_neg hj] at h
        have := FreeEntries.get?_sizeOf h
        simp; omega

/-- Lookup returning the entry together with the fact that it is a subterm,
for the termination of composition. -/
def FreeEntries.get?Attach : (Es : FreeEntries s) → Nat → Option {E : FreeEntry s // sizeOf E < sizeOf Es}
  | .nil, _ => none
  | .cons Es E, i =>
      if i = Es.length then some ⟨E, by simp; omega⟩
      else (Es.get?Attach i).map fun ⟨E', h⟩ => ⟨E', by simp; omega⟩

theorem FreeEntries.get?Attach_val : ∀ (Es : FreeEntries s) (j : Nat),
    (Es.get?Attach j).map Subtype.val = Es.get? j
  | .nil, _ => rfl
  | .cons Es E, i => by
      simp only [FreeEntries.get?Attach, FreeEntries.get?]
      by_cases h : i = Es.length
      · simp [h]
      · simp [h, ← FreeEntries.get?Attach_val Es i, Option.map_map]

theorem FreeEntries.get?Attach_eq_some {Es : FreeEntries s} {j : Nat} {E : FreeEntry s}
    (h : Es.get? j = some E) : ∃ hlt, Es.get?Attach j = some ⟨E, hlt⟩ := by
  have := FreeEntries.get?Attach_val Es j
  rw [h] at this
  cases hA : Es.get?Attach j with
  | none => rw [hA] at this; simp at this
  | some p =>
      rw [hA] at this
      obtain ⟨E', hlt⟩ := p
      simp at this
      subst this
      exact ⟨hlt, rfl⟩


mutual

/-- Surround an inclusion recipe with closed forms. Its internal composition
structure is retained, so this operation never evaluates a receiver. -/
def LocalEntry.surround (pre : Form s) : LocalEntry s → Form s → Option (LocalEntry s)
  | .le F h G, post => do
      let F' ← Form.combine pre F
      let G' ← Form.combine G post
      pure (.le F' h G')
  | .trans F E₁ E₂ G, post => do
      let F' ← Form.combine pre F
      let G' ← Form.combine G post
      pure (.trans F' E₁ E₂ G')
  | _, _ => none
termination_by E post => sizeOf pre + sizeOf E + sizeOf post
 decreasing_by all_goals (simp_wf; (try simp at *); (try omega))

/-- Substitute object entries for the source facts of a finite local recipe. -/
def LocalEntry.through (Es₁ : Entries s) : LocalEntry s → Option (LocalEntry s)
  | .le pre h post =>
      match Es₁.get?Attach h.index, h with
      | some ⟨E, _⟩, .le _ =>
          match hL : E.toLocal? with
          | some L =>
              have := Entry.toLocal?_sizeOf hL
              LocalEntry.surround pre L post
          | none => none
      | some ⟨.eq k b, _⟩, .eq _ => some (.le pre (if b then .eqSym k else .eq k) post)
      | some ⟨.eq k b, _⟩, .eqSym _ => some (.le pre (if b then .eq k else .eqSym k) post)
      | _, _ => none
  | .trans pre E₁ E₂ post => do
      let E₁' ← LocalEntry.through Es₁ E₁
      let E₂' ← LocalEntry.through Es₁ E₂
      pure (.trans pre E₁' E₂' post)
  | .eq j b =>
      match Es₁.get? j with
      | some (.eq k b') => some (.eq k (xor b b'))
      | _ => none
  | .has j =>
      match Es₁.get? j with
      | some (.has k) => some (.has k)
      | _ => none
  | .copyBound j => (Es₁.get? j).bind Entry.toLocal?
termination_by E => sizeOf Es₁ + sizeOf E
 decreasing_by
  all_goals (simp_wf; (try simp at *))
  all_goals omega

/-- Compose object entries by substituting finite recipes for source facts. -/
def Entry.through (Es₁ : Entries s) : Entry s → Option (Entry s)
  | .le pre h post => (LocalEntry.through Es₁ (.le pre h post)).map LocalEntry.toEntry
  | .trans pre E₁ E₂ post =>
      (LocalEntry.through Es₁ (.trans pre E₁ E₂ post)).map LocalEntry.toEntry
  | .eq j b =>
      match Es₁.get? j with
      | some (.eq k b') => some (.eq k (xor b b'))
      | _ => none
  | .has j =>
      match Es₁.get? j with
      | some (.has k) => some (.has k)
      | _ => none
  | .bnd G => (Form.combine (.obj Es₁) G).map .bnd
  | .copyBound j => Es₁.get? j
termination_by E => sizeOf Es₁ + sizeOf E + 1
 decreasing_by all_goals (simp_wf; (try simp at *); (try omega))

def Entries.through (Es₁ : Entries s) : Entries s → Option (Entries s)
  | .nil => some .nil
  | .cons Es E =>
      (Entries.through Es₁ Es).bind fun Es' =>
        (Entry.through Es₁ E).bind fun E' =>
          some (Es' ▹ E')
termination_by Es => sizeOf Es₁ + sizeOf Es + 1
decreasing_by all_goals simp_wf <;> omega

/-- Prefix an object entry. Only local templates become routed. -/
def Entry.prefix (H : Form s) : Entry s → Option (FreeEntry s)
  | .copyBound j => some (.thru H (.copyBound j))
  | .bnd G => (Form.combine H G).map FreeEntry.bnd
  | .le pre h post => some (.thru H (.le pre h post))
  | .trans pre E₁ E₂ post => some (.thru H (.trans pre E₁ E₂ post))
  | .eq j b => some (.thru H (.eq j b))
  | .has j => some (.thru H (.has j))
termination_by E => sizeOf H + sizeOf E
decreasing_by all_goals (simp_wf; (try simp at *); (try omega))

/-- Prefix a view-free entry by composing its bound or its route. -/
def FreeEntry.prefix (H : Form s) : FreeEntry s → Option (FreeEntry s)
  | .bnd G => (Form.combine H G).map FreeEntry.bnd
  | .thru H' E => (Form.combine H H').map fun H'' => FreeEntry.thru H'' E
termination_by E => sizeOf H + sizeOf E
decreasing_by all_goals (simp_wf; (try simp at *); (try omega))

/-- Prefix the entries of an object coercion. -/
def Entries.mapPrefix (H : Form s) : Entries s → Option (FreeEntries s)
  | .nil => some .nil
  | .cons Es E =>
      (Entries.mapPrefix H Es).bind fun Es' =>
        (Entry.prefix H E).bind fun E' => some (Es' ▹ E')
termination_by Es => sizeOf H + sizeOf Es
decreasing_by all_goals simp_wf <;> omega

/-- Prefix view-free entries. -/
def FreeEntries.mapPrefix (H : Form s) : FreeEntries s → Option (FreeEntries s)
  | .nil => some .nil
  | .cons Es E =>
      (FreeEntries.mapPrefix H Es).bind fun Es' =>
        (FreeEntry.prefix H E).bind fun E' => some (Es' ▹ E')
termination_by Es => sizeOf H + sizeOf Es
decreasing_by all_goals simp_wf <;> omega

/-- Combine the head forms of two composable coercions. Identity forms are
absorbed; object composition substitutes the first templates into the second. -/
def Form.combine : Form s → Form s → Option (Form s)
  | .id, F => some F
  | F, .id => some F
  | .bot, _ => some .bot
  | _, .top => some .top
  | .pi d₁ c₁, .pi d₂ c₂ =>
      some (.pi (.trans d₂ d₁) (.trans (c₁.subst (Subst.selfCast d₂↑)) c₂))
  | .obj Es₁, .obj Es₂ => (Entries.through Es₁ Es₂).map .obj
  | .into Es₁, .obj Es₂ => (Entries.mapPrefix (.into Es₁) Es₂).map .into
  | .top, .obj Es => (Entries.mapPrefix .top Es).map .into
  | F, .into Es => (FreeEntries.mapPrefix F Es).map .into
  | .bnd i F, G => (Form.combine F G).map (Form.bnd i)
  | .obj Es, .bnd i F =>
      match Es.get?Attach i with
      | some ⟨.bnd G, _⟩ => Form.combine G F
      | some ⟨.copyBound j, _⟩ => some (.bnd j F)
      | _ => none
  | .into Es, .bnd i F =>
      match Es.get?Attach i with
      | some ⟨.bnd G, _⟩ => Form.combine G F
      | some ⟨.thru H (.copyBound j), _⟩ => Form.combine H (.bnd j F)
      | _ => none
  | F, _ => some F
termination_by F G => sizeOf F + sizeOf G
decreasing_by all_goals (simp_wf; (try simp at *); (try omega))

end

/-- The identity entries of a telescope: each proposition from itself. -/
def Telescope.identityEntries : Telescope (s,x) → Entries s
  | .nil => .nil
  | .cons Tel (.le _ _) => Tel.identityEntries ▹ .le .id (.le Tel.length) .id
  | .cons Tel (.eq _ _) => Tel.identityEntries ▹ .eq Tel.length false
  | .cons Tel (.has _) => Tel.identityEntries ▹ .has Tel.length
  | .cons Tel (.bnd _) => Tel.identityEntries ▹ .copyBound Tel.length

/-- Concatenation of entries. -/
def Entries.append : Entries s → Entries s → Entries s
  | Es, .nil => Es
  | Es, .cons Es' E => (Es.append Es') ▹ E

instance : Append (Entries s) := ⟨Entries.append⟩

/-- Concatenation of view-free entries. -/
def FreeEntries.append : FreeEntries s → FreeEntries s → FreeEntries s
  | Es, .nil => Es
  | Es, .cons Es' E => (Es.append Es') ▹ E

instance : Append (FreeEntries s) := ⟨FreeEntries.append⟩

/-- The entries of a coercion into an object type with telescope `Tel`, read
off its head form: an object form gives its entries, identity gives the
identity entries of `Tel`, and so does `top` (its target is `⊤ = μ .nil`, so
`Tel` is empty). -/
def Form.toEntries (Tel : Telescope (s,x)) : Form s → Option (Entries s)
  | .obj Es => some Es
  | .id => some Tel.identityEntries
  | .top => some Tel.identityEntries
  | _ => none

/-- The entries of a coercion into an object type that do not consult the
view of the source: an `into` form gives its entries, a bound cast routes
its entries through the bound, and any other form routes its entries
through the identity. -/
def Form.freeEntries (Tel : Telescope (s,x)) : Form s → Option (FreeEntries s)
  | .into Es => some Es
  | .bnd i F => (Form.freeEntries Tel F).bind (FreeEntries.mapPrefix (.bnd i .id))
  | F => (F.toEntries Tel).bind (Entries.mapPrefix .id)

/-- A form that proves every inclusion out of its source: `bot`, possibly
behind bound casts. -/
def Form.absorbs : Form s → Bool
  | .bot => true
  | .bnd _ F => F.absorbs
  | _ => false

/-- The head form of a pairing: `bot` if either component is, `top` if both
are, an absorbing component if there is one, else the concatenated
view-free entries of the two components. -/
def Form.pair (Tel₁ Tel₂ : Telescope (s,x)) : Form s → Form s → Option (Form s)
  | .bot, _ => some .bot
  | _, .bot => some .bot
  | .top, .top => some .top
  | F, G =>
      if F.absorbs then some F
      else if G.absorbs then some G
      else do
        let Es₁ ← F.freeEntries Tel₁
        let Es₂ ← G.freeEntries Tel₂
        pure (.into (Es₁ ++ Es₂))

/-! ## The view of a literal -/

/-- Presence forms for the fields of a literal at binder `x`, appended to a
view (as `Telescope.hasEntries`). -/
def Fields.hasForms (x : BVar s .var) : View s → List Label → View s
  | V, [] => V
  | V, ℓ :: ls => Fields.hasForms x (V ▹ .has x ℓ) ls

/-- Equation forms for the witnesses of a literal. -/
def Witnesses.eqForms : Witnesses (s,x) → View s
  | .nil => .nil
  | .cons W _ _ => W.eqForms ▹ .eq

/-- The view of a stored literal at its precise type: one entry per
proposition of `Telescope.ofLiteral`. -/
def Value.precView (x : BVar s .var) : Value s → View s
  | .obj W F => Fields.hasForms x W.eqForms F.labels
  | _ => .nil

/-! ## The normalizer -/

/-- Concatenation of views. -/
def View.append : View s → View s → View s
  | V, .nil => V
  | V, .cons V' P => (V.append V') ▹ P

instance : Append (View s) := ⟨View.append⟩

/-- Interpret a local template using a supplied view. -/
def LocalEntry.at : View s → LocalEntry s → Option (PropForm s)
  | V, .le pre h post => do
      let mid ← match h, ← V.get? h.index with
        | .le _, .le F => some F
        | .eq _, .eq => some .id
        | .eqSym _, .eq => some .id
        | _, _ => none
      let F ← pre.combine mid
      let G ← F.combine post
      pure (.le G)
  | V, .trans pre E₁ E₂ post => do
      let .le F₁ ← LocalEntry.at V E₁ | none
      let .le F₂ ← LocalEntry.at V E₂ | none
      let F ← pre.combine F₁
      let G ← F.combine F₂
      let H ← G.combine post
      pure (.le H)
  | V, .eq j _ => do
      match ← V.get? j with
      | .eq => pure .eq
      | _ => none
  | V, .has j => do
      match ← V.get? j with
      | .has y ℓ => pure (.has y ℓ)
      | _ => none
  | V, .copyBound j => do
      match ← V.get? j with
      | .bnd G => pure (.bnd G)
      | _ => none

/-- Interpret an object entry using a supplied view and cast chain. -/
def Entry.at (_σ : Store s) : Nat → Atom s → Form s → View s → Entry s → Option (PropForm s)
  | 0, _, _, _, _ => none
  | _ + 1, _, _, V, .le pre h post => LocalEntry.at V (.le pre h post)
  | _ + 1, _, _, V, .trans pre E₁ E₂ post => LocalEntry.at V (.trans pre E₁ E₂ post)
  | _ + 1, _, _, V, .eq j b => LocalEntry.at V (.eq j b)
  | _ + 1, _, _, V, .has j => LocalEntry.at V (.has j)
  | _ + 1, _, C, _, .bnd G => (C.combine G).map PropForm.bnd
  | _ + 1, _, _, V, .copyBound j => LocalEntry.at V (.copyBound j)

/-- Instantiate object entries at a supplied view. -/
def entriesAt (σ : Store s) : Nat → Atom s → Form s → View s → Entries s → Option (View s)
  | 0, _, _, _, _ => none
  | _ + 1, _, _, _, .nil => some .nil
  | n + 1, a, C, V, .cons Es E => do
      let V' ← entriesAt σ n a C V Es
      let P ← Entry.at σ n a C V E
      pure (V' ▹ P)

mutual

/-- Interpret a view-free entry. A route is evaluated once, then its local
endpoint is read from the resulting view. -/
def FreeEntry.at (σ : Store s) : Nat → Atom s → Form s → FreeEntry s → Option (PropForm s)
  | 0, _, _, _ => none
  | _ + 1, _, C, .bnd G => (C.combine G).map PropForm.bnd
  | n + 1, a, _, .thru H E => do
      let V' ← viewThrough σ n H a
      LocalEntry.at V' E

/-- Instantiate view-free entries. -/
def freeEntriesAt (σ : Store s) : Nat → Atom s → Form s → FreeEntries s → Option (View s)
  | 0, _, _, _ => none
  | _ + 1, _, _, .nil => some .nil
  | n + 1, a, C, .cons Es E => do
      let V' ← freeEntriesAt σ n a C Es
      let P ← FreeEntry.at σ n a C E
      pure (V' ▹ P)

/-- The normal form of a template side, with fuel: `id` when absent. -/
def sideForm (σ : Store s) : Nat → Side s → Option (Form s)
  | 0, _ => none
  | _ + 1, .none => some .id
  | n + 1, .some e => hnf σ n e

/-- Head form of closed inclusion evidence, with fuel. -/
def hnf (σ : Store s) : Nat → LeCo s → Option (Form s)
  | 0, _ => none
  | _ + 1, .refl _ => some .id
  | _ + 1, .eqToLe _ => some .id
  | _ + 1, .top _ => some .top
  | _ + 1, .bot _ => some .bot
  | _ + 1, .pi d c => some (.pi d c)
  | n + 1, .obj _ m => (entries σ n m).map .obj
  | n + 1, .pair Tel₁ Tel₂ e f => do
      let F ← hnf σ n e
      let G ← hnf σ n f
      Form.pair Tel₁ Tel₂ F G
  | _ + 1, .bound _ i => some (.bnd i .id)
  | n + 1, .intoBnd e => do
      let F ← hnf σ n e
      pure (.into (.nil ▹ .bnd F))
  | n + 1, .trans e f => do
      let F ← hnf σ n e
      let G ← hnf σ n f
      F.combine G
  | n + 1, .member a e i => do
      let F ← hnf σ n e
      let V ← viewThrough σ n F a
      match V.get? i with
      | some (.le G) => some G
      | _ => none

/-- Entries of a morphism: the normal forms of its templates. -/
def entries (σ : Store s) : Nat → Morphism s → Option (Entries s)
  | 0, _ => none
  | _ + 1, .nil => some .nil
  | n + 1, .le m pre h post => do
      let Es ← entries σ n m
      let F ← sideForm σ n pre
      let G ← sideForm σ n post
      pure (Es ▹ .le F h G)
  | n + 1, .leTrans m p q => do
      let Es ← entries σ n m
      let .cons .nil E₁ ← entries σ n p | none
      let .cons .nil E₂ ← entries σ n q | none
      let L₁ ← E₁.toLocal?
      let L₂ ← E₂.toLocal?
      pure (Es ▹ .trans .id L₁ L₂ .id)
  | n + 1, .eq m j b => do
      let Es ← entries σ n m
      pure (Es ▹ .eq j b)
  | n + 1, .has m j => do
      let Es ← entries σ n m
      pure (Es ▹ .has j)
  | n + 1, .bnd m e => do
      let Es ← entries σ n m
      let F ← hnf σ n e
      pure (Es ▹ .bnd F)

/-- The view of a concrete atom at its resolved object type. -/
def view (σ : Store s) : Nat → Atom s → Option (View s)
  | 0, _ => none
  | _ + 1, .var x => some ((σ.lookup x).precView x)
  | n + 1, .cast a e => do
      let F ← hnf σ n e
      viewThrough σ n F a
  | n + 1, .foldSelf _ a => view σ n a
  | n + 1, .unfoldSelf a => view σ n a
  | n + 1, .both _ _ a b => do
      let V ← view σ n a
      let V' ← view σ n b
      pure (V ++ V')

/-- The view of an atom through a head form applied to it. -/
def viewThrough (σ : Store s) : Nat → Form s → Atom s → Option (View s)
  | 0, _, _ => none
  | n + 1, .id, a => view σ n a
  | n + 1, .obj Es, a => do
      let V ← view σ n a
      let C ← closedAtomForm σ n a
      entriesAt σ n a C V Es
  | n + 1, .into Es, a => do
      let C ← closedAtomForm σ n a
      freeEntriesAt σ n a C Es
  | n + 1, .bnd i F, a => do
      let V ← view σ n a
      let P ← V.get? i
      let G ← P.bndForm?
      let H ← G.combine F
      viewThrough σ n H (.var a.root)
  -- A non-object target has no telescope: its view is empty.
  | _ + 1, .pi _ _, _ => some .nil
  | _ + 1, .top, _ => some .nil
  | _ + 1, .bot, _ => some .nil

/-- Field presence witnessed by `has` evidence at the expected binder `x`. -/
def hasView (σ : Store s) : Nat → BVar s .var → Has s → Option (BVar s .var × Label)
  | 0, _, _ => none
  | _ + 1, x, .field ℓ => some (x, ℓ)
  | n + 1, _, .member a e i => do
      let F ← hnf σ n e
      let V ← viewThrough σ n F a
      match V.get? i with
      | some (.has y ℓ) => some (y, ℓ)
      | _ => none

/-- The head form of a closed atom's wrappers, from its root. -/
def closedAtomForm (σ : Store s) : Nat → Atom s → Option (Form s)
  | 0, _ => none
  | _ + 1, .var _ => some .id
  | n + 1, .cast a e => do
      let F ← closedAtomForm σ n a
      let G ← hnf σ n e
      F.combine G
  | n + 1, .foldSelf _ a => closedAtomForm σ n a
  | n + 1, .unfoldSelf a => closedAtomForm σ n a
  | n + 1, .both Tel₁ Tel₂ a b => do
      let F ← closedAtomForm σ n a
      let G ← closedAtomForm σ n b
      Form.pair Tel₁ Tel₂ F G

end

/-! ### Notation for normalization

`σ ⊢ e ⇓[n] F`: with fuel `n`, `e` normalizes to `F` over `σ`; likewise
`⇓ₘ` for morphisms, `⇓ᵥ` for views of atoms, `⇓ₕ` for presence evidence. -/

scoped notation:40 σ:51 " ⊢ " e:51 " ⇓[" n "] " F:51 => hnf σ n e = some F
scoped notation:40 σ:51 " ⊢ " m:51 " ⇓ₘ[" n "] " Es:51 => entries σ n m = some Es
scoped notation:40 σ:51 " ⊢ " a:51 " ⇓ᵥ[" n "] " V:51 => view σ n a = some V
scoped notation:40 σ:51 " ⊢ " x:51 " ; " h:51 " ⇓ₕ[" n "] " P:51 => hasView σ n x h = some P

/-- `σ ⊢ a ⇓ᶜ[n] F`: the chain of casts of `a` normalizes to `F`. -/
scoped notation:40 σ:51 " ⊢ " a:51 " ⇓ᶜ[" n "] " r:51 => closedAtomForm σ n a = some r

end FCdot
