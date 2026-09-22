import Coercions.Paths.FCdot.Store

namespace Paths

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

/-- One alias step: `some W` if the head of the type is a block name defined
by the forest, `none` if the type is settled (a shape, or a name whose block
is opaque). -/
def Ctx.next (Γ : Ctx s) : Ty s → Option (Ty s)
  | .sel p ℓ => Γ.lookupDefP p ℓ
  | _ => none

/-- The head name of a type, if it has one. -/
def Ty.headName? : Ty s → Option (Path s × Label)
  | .sel p ℓ => some (p, ℓ)
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

/-! ### The nodes of the forest

`Ctx.defPairs` enumerates the forest, not the context spine.  Each node
contributes the pairs of its own labels at its own path and the head name of
each of its witnesses.  The second half is what a chain stands at after one
step: the type a step produces is a witness of a node, so if it is a name at
all it is one of the listed head names. -/

/-- The head names of a list of witnesses. -/
def Witnesses.headNames : Witnesses s → List (Path s × Label)
  | .nil => []
  | .cons W _ T => T.headName?.toList ++ W.headNames

mutual
/-- Every node of a block, with the path it sits at. -/
def Block.nodes : Block s → Path s → List (Path s × Block s)
  | .obj W ls vls ch, p => (p, .obj W ls vls ch) :: ch.nodes p
  | .fwd r, p => [(p, .fwd r)]

/-- Every node of a child list, with the path it sits at. -/
def Children.nodes : Children s → Path s → List (Path s × Block s)
  | .nil, _ => []
  | .cons ch a b, p => b.nodes (.sel p a) ++ ch.nodes p
end

/-- The pairs one node contributes: its own labels at its own path, and the
head name of each of its witnesses.  A forwarding node contributes none: the
walk follows it, and the node it reaches contributes for it. -/
def Block.pairsAt : Block s → Path s → List (Path s × Label)
  | .obj W _ _ _, p => W.labels.map (fun ℓ => (p, ℓ)) ++ W.headNames
  | .fwd _, _ => []

/-- The pairs of a list of nodes. -/
def nodePairs : List (Path s × Block s) → List (Path s × Label)
  | [] => []
  | n :: ns => n.2.pairsAt n.1 ++ nodePairs ns

/-- Every node of the context's forest, with the path it sits at.  The nodes
of the spine are weakened through the binder that extends it, as
`Ctx.blockAt` weakens the block it reads. -/
def Ctx.nodes : Ctx s → List (Path s × Block s)
  | .nil => []
  | .cons Γ b =>
      (Ctx.nodes Γ).map (fun n => (n.1.weaken, n.2.weaken)) ++
        (match b with
         | .transparent _ B => B.nodes (.var .here)
         | .opaque _ => [])

/-- Every pair a chain can stand at after its first step, and every name the
forest defines. -/
def Ctx.defPairs (Γ : Ctx s) : List (Path s × Label) := nodePairs Γ.nodes

/-- Resolution with enough fuel for any alias chain in the context, plus one
step of slack for a first name that is not itself listed: a chain longer than
the list of pairs stands twice at one block and label, hence is cyclic. -/
def Ctx.resolve (Γ : Ctx s) (T : Ty s) : Ty s := Γ.resolveFuel (Γ.defPairs.length + 2) T

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
  /-- Cast by a bound: the source resolves to an object type whose `i`-th
      proposition is a bound, and the rest of the coercion goes on from the
      bound's type. -/
  | bnd : Nat → Form s → Form s
  /-- Coercion into a bounds-only object type: one bound entry per target
      proposition. -/
  | into : Entries s → Form s

/-- The normal form of one target proposition of an object coercion: a
template `pre ∘ (source proposition) ∘ post` with normalized sides (`id` for
an absent side), a source equality possibly flipped, or an inherited
presence. -/
inductive Entry (s : Sig) : Type where
  | le : Form s → Hole → Form s → Entry s
  | eq : Nat → Bool → Entry s
  | has : Nat → Entry s
  /-- A bound entry: a coercion out of the source object type. -/
  | bnd : Form s → Entry s
  /-- A routed entry: the coercion `H` reaches another object type from the
      source, and `E` proves the target proposition there.  `E` is never
      itself routed (routing composes). -/
  | thru : Form s → Entry s → Entry s
  /-- An inherited stable presence: the target `∋ᵛ ℓ` is the source
      proposition of that index. -/
  | hasVal : Nat → Entry s
  /-- An inherited alias: the target `≈ q` is the source proposition of that
      index. -/
  | alias : Nat → Entry s
  /-- A constant alias, the normal form of `LeCo.intoSngl`: the receiver is
      the path `p`, whose block is the block of `q`.  It reads nothing of the
      source, as `Side.bot` and `Side.top` do. -/
  | aliasTo : Path s → Path s → Entry s

/-- Entries of an object coercion, oldest first. -/
inductive Entries (s : Sig) : Type where
  | nil : Entries s
  | cons : Entries s → Entry s → Entries s

end

deriving instance DecidableEq for Form, Entry, Entries

/-- Decidable tests for the two absorbing forms. -/
def Form.isBot : Form s → Bool
  | .bot => true
  | _ => false

/-- The identity template on a source bound, `bnd j id`: the one bound entry
that `Entry.prefix` keeps routed rather than composing. -/
def Form.isBndId : Form s → Bool
  | .bnd _ .id => true
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
  /-- Field `ℓ` is present at the block of the path `p`. -/
  | has : Path s → Label → PropForm s
  /-- A bound of the atom's type: a form typed from the root's type. -/
  | bnd : Form s → PropForm s
  /-- Field `ℓ` is present and holds a stable body.  The block it is read at
      is the root of the atom whose view this is. -/
  | hasVal : Label → PropForm s
  /-- The block of the atom is the block of the path `q`. -/
  | alias : Path s → PropForm s

/-- The form of a bound entry of a view. -/
def PropForm.bndForm? : PropForm s → Option (Form s)
  | .bnd G => some G
  | _ => none

/-- The view of an atom: the forms of its propositions, oldest first. -/
inductive View (s : Sig) : Type where
  | nil : View s
  | cons : View s → PropForm s → View s

deriving instance DecidableEq for PropForm, View

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

/-- Lookup of a bound entry, with the size proof composition needs. -/
def Entries.getBnd?Attach (Es : Entries s) (i : Nat) : Option {G : Form s // sizeOf G < sizeOf Es} :=
  match Es.get?Attach i with
  | some ⟨.bnd G, h⟩ => some ⟨G, by simp at h; omega⟩
  | _ => none

theorem Entries.getBnd?Attach_eq_some {Es : Entries s} {i : Nat} {G : Form s}
    (h : Es.get? i = some (.bnd G)) : ∃ hlt, Es.getBnd?Attach i = some ⟨G, hlt⟩ := by
  obtain ⟨hlt, hA⟩ := Entries.get?Attach_eq_some h
  exact ⟨by simp at hlt; omega, by simp [Entries.getBnd?Attach, hA]⟩

theorem Entries.getBnd?Attach_eq_none {Es : Entries s} {i : Nat}
    (h : ∀ G, Es.get? i ≠ some (.bnd G)) : Es.getBnd?Attach i = none := by
  cases hA : Es.get?Attach i with
  | none => simp [Entries.getBnd?Attach, hA]
  | some p =>
      obtain ⟨E, hlt⟩ := p
      have hv : Es.get? i = some E := by
        have := Entries.get?Attach_val Es i; rw [hA] at this; simpa using this.symm
      cases E with
      | bnd G => exact absurd hv (h G)
      | _ => simp [Entries.getBnd?Attach, hA]

mutual

/-- Route an entry of the second coercion through the entries of the first:
the hole of a template is replaced by the first coercion's template for that
source proposition, and the sides are composed.  If the source template is
itself routed, the composite is routed the same way.  A bound entry and a
routed entry are routed by composing the whole first coercion with them. -/
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
      -- A presence inherited from a stable presence reads that entry.
      | some (.hasVal k) => some (.has k)
      | _ => none
  | .hasVal j =>
      match Es₁.get? j with
      | some (.hasVal k) => some (.hasVal k)
      | _ => none
  | .alias j =>
      match Es₁.get? j with
      | some (.alias k) => some (.alias k)
      -- An alias inherited from a constant alias is that constant alias.
      | some (.aliasTo p q) => some (.aliasTo p q)
      | _ => none
  | .aliasTo p q => some (.aliasTo p q)
  | .bnd G => (Form.combine (.obj Es₁) G).map .bnd
  -- Object forms never carry routed entries, so this case does not arise.
  | .thru _ _ => none
termination_by E => sizeOf Es₁ + sizeOf E + 1
decreasing_by
  all_goals (simp_wf; (try simp at *); (try omega))

def Entries.through (Es₁ : Entries s) : Entries s → Option (Entries s)
  | .nil => some .nil
  | .cons Es E =>
      (Entries.through Es₁ Es).bind fun Es' =>
        (Entry.through Es₁ E).bind fun E' =>
          some (Es' ▹ E')
termination_by Es => sizeOf Es₁ + sizeOf Es + 1
decreasing_by all_goals simp_wf <;> omega

/-- Prefix an entry with a coercion `H` into the object type its source is:
a bound entry composes with `H` (the identity template on a source bound is
kept as a routed entry, so that composing past it stays one step), a routed
entry composes its route, and every other entry becomes routed through `H`. -/
def Entry.prefix (H : Form s) : Entry s → Option (Entry s)
  | .bnd (.bnd j .id) => some (.thru H (.bnd (.bnd j .id)))
  | .bnd G => (Form.combine H G).map Entry.bnd
  | .thru H' E => (Form.combine H H').map fun H'' => Entry.thru H'' E
  -- A constant alias reads nothing of the source, so a prefix leaves it as
  -- it is, exactly as `Entry.through` does.
  | .aliasTo p q => some (.aliasTo p q)
  | E => some (.thru H E)
termination_by E => sizeOf H + sizeOf E
decreasing_by all_goals (simp_wf; (try simp at *); (try omega))

/-- Prefix every entry of a coercion with a form on the left. -/
def Entries.mapPrefix (H : Form s) : Entries s → Option (Entries s)
  | .nil => some .nil
  | .cons Es E =>
      (Entries.mapPrefix H Es).bind fun Es' =>
        (Entry.prefix H E).bind fun E' => some (Es' ▹ E')
termination_by Es => sizeOf H + sizeOf Es
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
  | .eqv _, .bnd i F => some (.bnd i F)
  | .eqv _, .into Es => some (.into Es)
  | .into Es, .eqv _ => some (.into Es)
  | .pi d₁ c₁, .pi d₂ c₂ =>
      some (.pi (.trans d₂ d₁) (.trans (c₁.subst (Subst.selfCast d₂↑)) c₂))
  | .obj Es₁, .obj Es₂ => (Entries.through Es₁ Es₂).map .obj
  | .into Es₁, .obj Es₂ => (Entries.mapPrefix (.into Es₁) Es₂).map .into
  | .top, .obj Es => (Entries.mapPrefix .top Es).map .into
  | F, .into Es => (Entries.mapPrefix F Es).map .into
  | .bnd i F, G => (Form.combine F G).map (Form.bnd i)
  | .obj Es, .bnd i F =>
      match Es.getBnd?Attach i with
      | some ⟨G, _⟩ => Form.combine G F
      | none => none
  | .into Es, .bnd i F =>
      match Es.get?Attach i with
      | some ⟨.bnd G, _⟩ => Form.combine G F
      | some ⟨.thru H (.bnd (.bnd j .id)), _⟩ => Form.combine H (.bnd j F)
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
  | .cons Tel (.bnd _) => Tel.identityEntries ▹ .bnd (.bnd Tel.length .id)
  | .cons Tel (.hasVal _) => Tel.identityEntries ▹ .hasVal Tel.length
  | .cons Tel (.alias _) => Tel.identityEntries ▹ .alias Tel.length

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

/-- The entries of a coercion into an object type that do not consult the
view of the source: an `into` form gives its entries, a bound cast routes
its entries through the bound, and any other form routes its entries
through the identity. -/
def Form.freeEntries (Tel : Telescope (s,x)) : Form s → Option (Entries s)
  | .into Es => some Es
  | .bnd i F => (Form.freeEntries Tel F).bind (Entries.mapPrefix (.bnd i .id))
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

/-- Presence forms for the fields of a literal at the path `p`, appended to a
view (as `Telescope.hasEntries`). -/
def Fields.hasForms (p : Path s) : View s → List Label → View s
  | V, [] => V
  | V, ℓ :: ls => Fields.hasForms p (V ▹ .has p ℓ) ls

/-- Stable-presence forms for the stable fields of a literal, appended to a
view (as `Telescope.hasValEntries`).  A stable presence carries no block: it
is read at the root of the view it sits in. -/
def Fields.hasValForms : View s → List Label → View s
  | V, [] => V
  | V, ℓ :: ls => Fields.hasValForms (V ▹ .hasVal ℓ) ls

/-- Equation forms for the witnesses of a literal. -/
def Witnesses.eqForms : Witnesses (s,x) → View s
  | .nil => .nil
  | .cons W _ _ => W.eqForms ▹ .eq

/-- Equation forms for the witnesses of a node of the forest, which are
written at absolute paths. -/
def Witnesses.eqFormsAt : Witnesses s → View s
  | .nil => .nil
  | .cons W _ _ => W.eqFormsAt ▹ .eq

/-- The view of a stored literal at its precise type: one entry per
proposition of `Telescope.ofLiteral`, the stable presences last. -/
def Value.precView (p : Path s) : Value s → View s
  | .obj W F => Fields.hasValForms (Fields.hasForms p W.eqForms F.labels) F.valLabels
  | _ => .nil

/-- The view of a node of the forest, read at the path the node sits at: one
entry per proposition of the telescope the node's literal has. -/
def Block.precView : Block s → Path s → Option (View s)
  | .obj W ls vls _, p => some (Fields.hasValForms (Fields.hasForms p W.eqFormsAt ls) vls)
  | .fwd _, _ => none

/-- The block a path denotes over the store.  A field holding an atom gets a
forwarding to that atom's root, and the block of a stored value is never a
forwarding, so following is one step and the walk is structural on the path.
Over a typed store this is `Ctx.lookupBlock` (invariant A of P1.8). -/
def Store.blockOf (σ : Store s) : Path s → Option (Block s)
  | .var x => some ((σ.lookup x).blocksAt (.var x))
  | .sel p a =>
      match σ.blockOf p with
      | some (.obj _ _ _ ch) =>
          match ch.at? a with
          | some (.fwd (.var y)) => some ((σ.lookup y).blocksAt (.var y))
          | some (.fwd (.sel _ _)) => none
          | b => b
      | _ => none

/-- The view of the block a path denotes. -/
def Store.blockView (σ : Store s) (p : Path s) : Option (View s) :=
  (σ.blockOf p).bind (fun B => B.precView p)

/-! ## The normalizer -/

/-- Concatenation of views. -/
def View.append : View s → View s → View s
  | V, .nil => V
  | V, .cons V' P => (V.append V') ▹ P

instance : Append (View s) := ⟨View.append⟩

mutual

/-- Instantiate a template at a view: the hole is replaced by the view's
form of the source proposition (an equality reads as `id`), then the sides
are combined.  A bound entry is read through the chain `C` of the atom whose
view is being computed; a routed entry recomputes the view of the atom
through its route and reads the inner entry there. -/
def Entry.at (σ : Store s) : Nat → Atom s → Form s → View s → Entry s → Option (PropForm s)
  | 0, _, _, _, _ => none
  | _ + 1, _, _, V, .le pre h post => do
      let mid ← match h, ← V.get? h.index with
        | .le _, .le F => some F
        | .eq _, .eq => some .id
        | .eqSym _, .eq => some .id
        | _, _ => none
      let F ← pre.combine mid
      let G ← F.combine post
      pure (.le G)
  | _ + 1, _, _, V, .eq j _ => do
      match ← V.get? j with
      | .eq => pure .eq
      | _ => none
  | _ + 1, a, _, V, .has j => do
      match ← V.get? j with
      | .has y ℓ => pure (.has y ℓ)
      -- A stable presence is a presence, read at the atom's own block.
      | .hasVal ℓ => pure (.has (.var a.root) ℓ)
      | _ => none
  | _ + 1, _, _, V, .hasVal j => do
      match ← V.get? j with
      | .hasVal ℓ => pure (.hasVal ℓ)
      | _ => none
  | _ + 1, _, _, V, .alias j => do
      match ← V.get? j with
      | .alias q => pure (.alias q)
      | _ => none
  | _ + 1, a, _, _, .aliasTo p q =>
      if p = (Path.var a.root) then some (.alias q) else none
  | _ + 1, _, C, _, .bnd G => (C.combine G).map PropForm.bnd
  | n + 1, a, C, _, .thru H E => do
      let V' ← viewThrough σ n H a
      let C' ← C.combine H
      Entry.at σ n a C' V' E

/-- Instantiate the entries of an object coercion at an atom whose view is
`V` and whose chain of casts is `C`. -/
def entriesAt (σ : Store s) : Nat → Atom s → Form s → View s → Entries s → Option (View s)
  | 0, _, _, _, _ => none
  | _ + 1, _, _, _, .nil => some .nil
  | n + 1, a, C, V, .cons Es E => do
      let V' ← entriesAt σ n a C V Es
      let P ← Entry.at σ n a C V E
      pure (V' ▹ P)

/-- The normal form of a template side, with fuel: `id` when absent. -/
def sideForm (σ : Store s) : Nat → Side s → Option (Form s)
  | 0, _ => none
  | _ + 1, .none => some .id
  | n + 1, .some e => hnf σ n e
  | _ + 1, .bot _ => some .bot
  | _ + 1, .top _ => some .top

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
  | n + 1, .memberP P e i => do
      let F ← hnf σ n e
      let V ← pathViewThrough σ n F P
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
  | n + 1, .bnd m e => do
      let Es ← entries σ n m
      let F ← hnf σ n e
      pure (Es ▹ .bnd F)
  | n + 1, .hasVal m j => do
      let Es ← entries σ n m
      pure (Es ▹ .hasVal j)
  | n + 1, .hasOfVal m j => do
      let Es ← entries σ n m
      pure (Es ▹ .has j)
  | n + 1, .aliasCopy m j => do
      let Es ← entries σ n m
      pure (Es ▹ .alias j)

/-- The view of a concrete atom at its resolved object type. -/
def view (σ : Store s) : Nat → Atom s → Option (View s)
  | 0, _ => none
  | _ + 1, .var x => some ((σ.lookup x).precView (.var x))
  | n + 1, .cast a e => do
      let F ← hnf σ n e
      viewThrough σ n F a
  | n + 1, .foldSelf _ a => view σ n a
  | n + 1, .unfoldSelf a => view σ n a
  | n + 1, .both _ _ a b => do
      let V ← view σ n a
      let V' ← view σ n b
      pure (V ++ V')
  -- A `sngl` step knows one proposition of its block, the alias.
  | _ + 1, .sngl _ q _ => some (.nil ▹ .alias q)

/-- The view of an atom through a head form applied to it. -/
def viewThrough (σ : Store s) : Nat → Form s → Atom s → Option (View s)
  | 0, _, _ => none
  | n + 1, .id, a => view σ n a
  | n + 1, .eqv _, a => view σ n a
  | n + 1, .obj Es, a => do
      let V ← view σ n a
      let (_, C) ← closedAtomForm σ n a
      entriesAt σ n a C V Es
  | n + 1, .into Es, a => do
      let V ← view σ n a
      let (_, C) ← closedAtomForm σ n a
      entriesAt σ n a C V Es
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

/-- Field presence witnessed by `has` evidence at the expected path `p`. -/
def hasView (σ : Store s) : Nat → Path s → Has s → Option (Path s × Label)
  | 0, _, _ => none
  | _ + 1, p, .field ℓ => some (p, ℓ)
  | n + 1, _, .member a e i => do
      let F ← hnf σ n e
      let V ← viewThrough σ n F a
      match V.get? i with
      | some (.has y ℓ) => some (y, ℓ)
      | _ => none
  | n + 1, _, .memberP P e i => do
      let F ← hnf σ n e
      let V ← pathViewThrough σ n F P
      match V.get? i with
      | some (.has y ℓ) => some (y, ℓ)
      | _ => none

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
  -- The chain form of a `sngl` step is the constant alias, composed in.
  | n + 1, .sngl a q α => do
      let (a', F) ← closedAtomForm σ n a
      let H ← F.combine (.into (.nil ▹ .aliasTo (.var a.root) q))
      pure (.sngl a' q α, H)

/-- Instantiate a template at the view of a stable path.  The atom family's
`Entry.at`, with the receiver a path in place of an atom: the two differ only
in what a stable presence and a routed entry are read at.  `C` is the chain of
the path, from the node's type to the type whose view `V` is. -/
def pathEntryAt (σ : Store s) :
    Nat → Path s → Form s → View s → Entry s → Option (PropForm s)
  | 0, _, _, _, _ => none
  | _ + 1, _, _, V, .le pre h post => do
      let mid ← match h, ← V.get? h.index with
        | .le _, .le F => some F
        | .eq _, .eq => some .id
        | .eqSym _, .eq => some .id
        | _, _ => none
      let F ← pre.combine mid
      let G ← F.combine post
      pure (.le G)
  | _ + 1, _, _, V, .eq j _ => do
      match ← V.get? j with
      | .eq => pure .eq
      | _ => none
  | _ + 1, r, _, V, .has j => do
      match ← V.get? j with
      | .has y ℓ => pure (.has y ℓ)
      | .hasVal ℓ => pure (.has r ℓ)
      | _ => none
  | _ + 1, _, _, V, .hasVal j => do
      match ← V.get? j with
      | .hasVal ℓ => pure (.hasVal ℓ)
      | _ => none
  | _ + 1, _, _, V, .alias j => do
      match ← V.get? j with
      | .alias q => pure (.alias q)
      | _ => none
  | _ + 1, r, _, _, .aliasTo p q => if p = r then some (.alias q) else none
  | _ + 1, _, C, _, .bnd G => (C.combine G).map PropForm.bnd
  -- A routed entry reads the block at `r` through the chain composed with the
  -- route.  The route starts at the path's type and the block's view at the
  -- node's type, and the chain `C` goes from the second to the first, so the
  -- view is read through `C` then `H`.  At a node root the chain is `.id` and
  -- this is the route alone.
  | n + 1, r, C, _, .thru H E => do
      let C' ← C.combine H
      let V' ← pathViewThroughPath σ n C' r
      pathEntryAt σ n r C' V' E

/-- Instantiate the entries of an object coercion at a stable path. -/
def pathEntriesAt (σ : Store s) :
    Nat → Path s → Form s → View s → Entries s → Option (View s)
  | 0, _, _, _, _ => none
  | _ + 1, _, _, _, .nil => some .nil
  | n + 1, r, C, V, .cons Es E => do
      let V' ← pathEntriesAt σ n r C V Es
      let P ← pathEntryAt σ n r C V E
      pure (V' ▹ P)

/-- The view of the block of a path through a head form applied to it. -/
def pathViewThroughPath (σ : Store s) : Nat → Form s → Path s → Option (View s)
  | 0, _, _ => none
  | _ + 1, .id, r => σ.blockView r
  | _ + 1, .eqv _, r => σ.blockView r
  | n + 1, .obj Es, r => do
      let V ← σ.blockView r
      pathEntriesAt σ n r .id V Es
  | n + 1, .into Es, r => do
      let V ← σ.blockView r
      pathEntriesAt σ n r .id V Es
  | n + 1, .bnd i F, r => do
      let V ← σ.blockView r
      let P ← V.get? i
      let G ← P.bndForm?
      let H ← G.combine F
      pathViewThroughPath σ n H r
  | _ + 1, .pi _ _, _ => some .nil
  | _ + 1, .top, _ => some .nil
  | _ + 1, .bot, _ => some .nil

/-- The view of a stable path: the forms of the propositions known of the
block at that path, with the casts of the `PathCo` applied.  `view`
generalized from an atom to a stable path (P1.6). -/
def pathView (σ : Store s) : Nat → PathCo s → Option (View s)
  | 0, _ => none
  | _ + 1, .var x => some ((σ.lookup x).precView (.var x))
  -- One field step: the precise view of the child node, read through the
  -- coercion of the field, which the store closes over its scope.
  | n + 1, .sel P a _ => do
      let E ← σ.fieldCo P.path a
      let F ← hnf σ n E
      pathViewThroughPath σ n F (.sel P.path a)
  | n + 1, .cast P e => do
      let F ← hnf σ n e
      pathViewThrough σ n F P
  -- Two names of one block have one view.
  | n + 1, .alias _ _ P => pathView σ n P
  | n + 1, .foldSelf _ P => pathView σ n P
  | n + 1, .unfoldSelf P => pathView σ n P
  | n + 1, .both _ _ P Q => do
      let V ← pathView σ n P
      let V' ← pathView σ n Q
      pure (V ++ V')
  -- A `sngl` step knows one proposition of its block, the alias.
  | _ + 1, .sngl _ q _ => some (.nil ▹ .alias q)
  -- A node is read at its precise view.
  | _ + 1, .node p _ _ _ => σ.blockView p

/-- The view of a stable path through a head form applied to it. -/
def pathViewThrough (σ : Store s) : Nat → Form s → PathCo s → Option (View s)
  | 0, _, _ => none
  | n + 1, .id, P => pathView σ n P
  | n + 1, .eqv _, P => pathView σ n P
  | n + 1, .obj Es, P => do
      let V ← pathView σ n P
      let C ← pathChainForm σ n P
      pathEntriesAt σ n P.path C V Es
  | n + 1, .into Es, P => do
      let V ← pathView σ n P
      let C ← pathChainForm σ n P
      pathEntriesAt σ n P.path C V Es
  | n + 1, .bnd i F, P => do
      let V ← pathView σ n P
      let Q ← V.get? i
      let G ← Q.bndForm?
      let H ← G.combine F
      pathViewThroughPath σ n H P.path
  | _ + 1, .pi _ _, _ => some .nil
  | _ + 1, .top, _ => some .nil
  | _ + 1, .bot, _ => some .nil

/-- The head form of the casts a stable path carries, from its block. -/
def pathChainForm (σ : Store s) : Nat → PathCo s → Option (Form s)
  | 0, _ => none
  | _ + 1, .var _ => some .id
  -- The chain of a field step is the coercion of the field.
  | n + 1, .sel P a _ => do
      let E ← σ.fieldCo P.path a
      hnf σ n E
  | n + 1, .cast P e => do
      let F ← pathChainForm σ n P
      let G ← hnf σ n e
      F.combine G
  | n + 1, .alias _ _ P => pathChainForm σ n P
  | n + 1, .foldSelf _ P => pathChainForm σ n P
  | n + 1, .unfoldSelf P => pathChainForm σ n P
  | n + 1, .both Tel₁ Tel₂ P Q => do
      let F ← pathChainForm σ n P
      let G ← pathChainForm σ n Q
      Form.pair Tel₁ Tel₂ F G
  -- The chain form of a `sngl` step is the constant alias, composed in.
  | n + 1, .sngl P q _ => do
      let F ← pathChainForm σ n P
      F.combine (.into (.nil ▹ .aliasTo P.path q))
  -- A node starts its own chain.
  | _ + 1, .node _ _ _ _ => some .id

end

/-! ### Notation for normalization

`σ ⊢ e ⇓[n] F`: with fuel `n`, `e` normalizes to `F` over `σ`; likewise
`⇓ₘ` for morphisms, `⇓ᵥ` for views of atoms, `⇓ₕ` for presence evidence. -/

scoped notation:40 σ:51 " ⊢ " e:51 " ⇓[" n "] " F:51 => hnf σ n e = some F
scoped notation:40 σ:51 " ⊢ " m:51 " ⇓ₘ[" n "] " Es:51 => entries σ n m = some Es
scoped notation:40 σ:51 " ⊢ " a:51 " ⇓ᵥ[" n "] " V:51 => view σ n a = some V
scoped notation:40 σ:51 " ⊢ " x:51 " ; " h:51 " ⇓ₕ[" n "] " P:51 => hasView σ n x h = some P

/-- `σ ⊢ a ⇓ᶜ[n] (a', F)`: the chain of casts of `a` normalizes to `F`. -/
scoped notation:40 σ:51 " ⊢ " a:51 " ⇓ᶜ[" n "] " r:51 => closedAtomForm σ n a = some r

end FCdot

end Paths
