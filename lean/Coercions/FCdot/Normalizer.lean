import Coercions.FCdot.Store

/-!
# The normalizer: head normal forms of closed evidence

Inclusion evidence over a store normalizes to a head form: `bot`, `top`,
identity, a definitional conversion, a function coercion with closed domain
and codomain evidence, or an object coercion given by the normal forms of
its templates.  A template proves a target proposition as
`pre ∘ (source proposition j) ∘ post` with closed sides, so the normal form
of a coercion does not depend on the atom it is applied to: it is a
telescope of *entries*, one per target proposition, each naming a source
proposition by index.  Composition substitutes templates into templates;
application to an atom looks the source proposition up in the atom's view
and combines the sides with it.

The *view* of a concrete atom is the telescope of normal forms of the
propositions of its (resolved) object type: a location's view is read off
its literal, and the view of a cast atom is obtained by applying the head
form of the cast to the view of the underlying atom.  Eliminating a member
fact looks a view up.  Every recursion is structural in the closed evidence
term or atom, so the normalizer is a fuel-indexed total function whose fuel
bound is syntactic.

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
  /-- Syntactic identity: both endpoints are the same type. -/
  | id : Form s
  /-- Definitional conversion: closed equality evidence between the endpoints. -/
  | eqv : EqCo s → Form s
  /-- Function coercion: closed domain evidence and codomain evidence under
      the target domain binder. -/
  | pi : LeCo s → LeCo (s,x) → Form s
  /-- Object coercion: one entry per proposition of the target telescope. -/
  | obj : Entries s → Form s

/-- The normal form of one target proposition of an object coercion: a
template `pre ∘ (source proposition) ∘ post` with normalized sides (`id` for
an absent side), a source equality possibly flipped, or an inherited
presence. -/
inductive Entry (s : Sig) : Type where
  | le : Form s → Hole → Form s → Entry s
  | eq : Nat → Bool → Entry s
  | has : Nat → Entry s

/-- Entries of an object coercion, oldest first. -/
inductive Entries (s : Sig) : Type where
  | nil : Entries s
  | cons : Entries s → Entry s → Entries s

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

/-- The view of an atom: the forms of its propositions, oldest first. -/
inductive View (s : Sig) : Type where
  | nil : View s
  | cons : View s → PropForm s → View s

/-! ### Notation for entries and views

`Es ▹ E`, `V ▹ P` extend entries and views; `Es ∋ (i ↦ E)`, `V ∋ (i ↦ P)`
are the `i`-th entry and proposition form, counted from the oldest. -/

scoped infixl:65 " ▹ " => Entries.cons
scoped infixl:65 " ▹ " => View.cons

def Entries.length : Entries s → Nat
  | .nil => 0
  | .cons Es _ => Es.length + 1

def View.length : View s → Nat
  | .nil => 0
  | .cons V _ => V.length + 1

/-- `Es ∋ (i ↦ E)`: the `i`-th entry of `Es` (from the oldest) is `E`. -/
inductive Entries.At : Entries s → Nat → Entry s → Prop where
  | here : Entries.At (Es ▹ E) Es.length E
  | there : Entries.At Es i E → Entries.At (Es ▹ E') i E

/-- `V ∋ (i ↦ P)`: the `i`-th proposition form of `V` (from the oldest) is `P`. -/
inductive View.At : View s → Nat → PropForm s → Prop where
  | here : View.At (V ▹ P) V.length P
  | there : View.At V i P → View.At (V ▹ Q) i P

scoped notation:50 Es:51 " ∋ " "(" i " ↦ " E ")" => Entries.At Es i E
scoped notation:50 V:51 " ∋ " "(" i " ↦ " P ")" => View.At V i P

/-- Lookup by index, executable. -/
def Entries.get? : Entries s → Nat → Option (Entry s)
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

mutual

/-- Route an entry of the second coercion through the entries of the first:
the hole of a template is replaced by the first coercion's template for that
source proposition, and the sides are composed. -/
def Entry.through (Es₁ : Entries s) : Entry s → Option (Entry s)
  | .le pre h post =>
      match Es₁.get?Attach h.index, h with
      | some ⟨.le pre₁ h₁ post₁, _⟩, .le _ =>
          (Form.combine pre pre₁).bind fun pre' =>
            (Form.combine post₁ post).bind fun post' =>
              some (.le pre' h₁ post')
      | some ⟨.eq k b, _⟩, .eq _ => some (.le pre (if b then .eqSym k else .eq k) post)
      | some ⟨.eq k b, _⟩, .eqSym _ => some (.le pre (if b then .eq k else .eqSym k) post)
      | _, _ => none
  | .eq j b =>
      match Es₁.get? j with
      | some (.eq k b') => some (.eq k (xor b b'))
      | _ => none
  | .has j =>
      match Es₁.get? j with
      | some (.has k) => some (.has k)
      | _ => none
termination_by E => sizeOf Es₁ + sizeOf E
decreasing_by
  all_goals (simp_wf; (try simp at *); omega)

def Entries.through (Es₁ : Entries s) : Entries s → Option (Entries s)
  | .nil => some .nil
  | .cons Es E =>
      (Entries.through Es₁ Es).bind fun Es' =>
        (Entry.through Es₁ E).bind fun E' =>
          some (Es' ▹ E')
termination_by Es => sizeOf Es₁ + sizeOf Es
decreasing_by all_goals simp_wf <;> omega

/-- Combine the head forms of two composable coercions.  Conversions compose
as equalities and are absorbed into function and object forms; the
composite of two object coercions is the second, with its templates routed
through the first. -/
def Form.combine : Form s → Form s → Option (Form s)
  | .id, F => some F
  | F, .id => some F
  | .bot, _ => some .bot
  | _, .top => some .top
  | .eqv _, .bot => some .bot
  | .eqv φ, .eqv ψ => some (.eqv (.trans φ ψ))
  | .eqv _, .pi d c => some (.pi d c)
  | .pi d c, .eqv _ => some (.pi d c)
  | .eqv _, .obj Es => some (.obj Es)
  | .obj Es, .eqv _ => some (.obj Es)
  | .pi d₁ c₁, .pi d₂ c₂ =>
      some (.pi (.trans d₂ d₁) (.trans (c₁.subst (Subst.selfCast d₂↑)) c₂))
  | .obj Es₁, .obj Es₂ => (Entries.through Es₁ Es₂).map .obj
  | F, _ => some F
termination_by F G => sizeOf F + sizeOf G
decreasing_by all_goals simp_wf <;> omega

end

/-- The identity entries of a telescope: each proposition from itself. -/
def Telescope.identityEntries : Telescope (s,x) → Entries s
  | .nil => .nil
  | .cons Tel (.le _ _) => Tel.identityEntries ▹ .le .id (.le Tel.length) .id
  | .cons Tel (.eq _ _) => Tel.identityEntries ▹ .eq Tel.length false
  | .cons Tel (.has _) => Tel.identityEntries ▹ .has Tel.length

/-- Concatenation of entries. -/
def Entries.append : Entries s → Entries s → Entries s
  | Es, .nil => Es
  | Es, .cons Es' E => (Es.append Es') ▹ E

instance : Append (Entries s) := ⟨Entries.append⟩

/-- The entries of a coercion into an object type with telescope `Tel`, read
off its head form: an object form gives its entries, a conversion gives the
identity entries of `Tel`, and so does `top` (its target is `⊤ = μ .nil`, so
`Tel` is empty). -/
def Form.toEntries (Tel : Telescope (s,x)) : Form s → Option (Entries s)
  | .obj Es => some Es
  | .id => some Tel.identityEntries
  | .eqv _ => some Tel.identityEntries
  | .top => some Tel.identityEntries
  | _ => none

/-- The head form of a pairing: `bot` if either component is, `top` if both
are, else the concatenated entries. -/
def Form.pair (Tel₁ Tel₂ : Telescope (s,x)) : Form s → Form s → Option (Form s)
  | .bot, _ => some .bot
  | _, .bot => some .bot
  | .top, .top => some .top
  | F, G => do
      let Es₁ ← F.toEntries Tel₁
      let Es₂ ← G.toEntries Tel₂
      pure (.obj (Es₁ ++ Es₂))

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

/-- Instantiate a template at a view: the hole is replaced by the view's
form of the source proposition (an equality reads as `id`), then the sides
are combined. -/
def Entry.at (V : View s) : Entry s → Option (PropForm s)
  | .le pre h post => do
      let mid ← match h, ← V.get? h.index with
        | .le _, .le F => some F
        | .eq _, .eq => some .id
        | .eqSym _, .eq => some .id
        | _, _ => none
      let F ← pre.combine mid
      let G ← F.combine post
      pure (.le G)
  | .eq j _ => do
      match ← V.get? j with
      | .eq => pure .eq
      | _ => none
  | .has j => do
      match ← V.get? j with
      | .has y ℓ => pure (.has y ℓ)
      | _ => none

/-- Instantiate the entries of an object coercion at an atom whose view is `V`. -/
def entriesAt (V : View s) : Entries s → Option (View s)
  | .nil => some .nil
  | .cons Es E => do
      let V' ← entriesAt V Es
      let P ← E.at V
      pure (V' ▹ P)

mutual

/-- The normal form of a template side, with fuel: `id` when absent. -/
def sideForm (σ : Store s) : Nat → Side s → Option (Form s)
  | 0, _ => none
  | _ + 1, .none => some .id
  | n + 1, .some e => hnf σ n e

/-- Head form of closed inclusion evidence, with fuel. -/
def hnf (σ : Store s) : Nat → LeCo s → Option (Form s)
  | 0, _ => none
  | _ + 1, .refl T => some (.eqv (.refl T))
  | _ + 1, .top _ => some .top
  | _ + 1, .bot _ => some .bot
  | _ + 1, .eqToLe φ => some (.eqv φ)
  | _ + 1, .pi d c => some (.pi d c)
  | n + 1, .obj _ m => (entries σ n m).map .obj
  | n + 1, .pair Tel₁ Tel₂ e f => do
      let F ← hnf σ n e
      let G ← hnf σ n f
      Form.pair Tel₁ Tel₂ F G
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
  | n + 1, .eq m j b => do
      let Es ← entries σ n m
      pure (Es ▹ .eq j b)
  | n + 1, .has m j => do
      let Es ← entries σ n m
      pure (Es ▹ .has j)

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
  | n + 1, .eqv _, a => view σ n a
  | n + 1, .obj Es, a => do
      let V ← view σ n a
      entriesAt V Es
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

end

/-! ### Notation for normalization

`σ ⊢ e ⇓[n] F`: with fuel `n`, `e` normalizes to `F` over `σ`; likewise
`⇓ₘ` for morphisms, `⇓ᵥ` for views of atoms, `⇓ₕ` for presence evidence. -/

scoped notation:40 σ:51 " ⊢ " e:51 " ⇓[" n "] " F:51 => hnf σ n e = some F
scoped notation:40 σ:51 " ⊢ " m:51 " ⇓ₘ[" n "] " Es:51 => entries σ n m = some Es
scoped notation:40 σ:51 " ⊢ " a:51 " ⇓ᵥ[" n "] " V:51 => view σ n a = some V
scoped notation:40 σ:51 " ⊢ " x:51 " ; " h:51 " ⇓ₕ[" n "] " P:51 => hasView σ n x h = some P

/-- The head form of a closed atom's wrappers, from its root. -/
def closedAtomForm (σ : Store s) : Nat → Atom s → Option (Atom s × Form s)
  | 0, _ => none
  | _ + 1, .var x => some (.var x, .id)
  | n + 1, .cast a e => do
      let (a', F) ← closedAtomForm σ n a
      let G ← hnf σ n e
      let H ← F.combine G
      pure (.cast a' e, H)
  | n + 1, .foldSelf Tel a => do
      let (a', F) ← closedAtomForm σ n a
      pure (.foldSelf Tel a', F)
  | n + 1, .unfoldSelf a => do
      let (a', F) ← closedAtomForm σ n a
      pure (.unfoldSelf a', F)
  | n + 1, .both Tel₁ Tel₂ a b => do
      let (a', F) ← closedAtomForm σ n a
      let (b', G) ← closedAtomForm σ n b
      let H ← Form.pair Tel₁ Tel₂ F G
      pure (.both Tel₁ Tel₂ a' b', H)

/-- `σ ⊢ a ⇓ᶜ[n] (a', F)`: the chain of casts of `a` normalizes to `F`. -/
scoped notation:40 σ:51 " ⊢ " a:51 " ⇓ᶜ[" n "] " r:51 => closedAtomForm σ n a = some r

end FCdot
