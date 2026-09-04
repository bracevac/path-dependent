import Coercions.FCdot.Store

/-!
# The normalizer: head normal forms of closed evidence

Inclusion evidence over a store normalizes to a head form: `bot`, `top`,
identity, a definitional conversion, a function coercion with closed domain
and codomain evidence, or an object coercion given by the normal forms of
its target's propositions.  Object coercions are between opened telescopes
(no self block), so the normal form of a coercion does not depend on the
atom it is applied to: it is a telescope of *entries*, one per target
proposition, where a presence entry refers to the source by index.

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

/-- Follow definitions at the head of a type, with fuel. -/
def Ctx.resolveFuel (Γ : Ctx s) : Nat → Ty s → Ty s
  | 0, T => T
  | n + 1, .sel x ℓ =>
      match Γ.lookupDef x ℓ with
      | some W => Γ.resolveFuel n W
      | none => .sel x ℓ
  | _ + 1, T => T

/-- Resolution with enough fuel for any alias chain in the context. -/
def Ctx.resolve (Γ : Ctx s) (T : Ty s) : Ty s := Γ.resolveFuel (Γ.length + 1) T

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
  /-- Object coercion: one entry per proposition of the (opened) target. -/
  | obj : Entries s → Form s

/-- The normal form of one target proposition of an object coercion. -/
inductive Entry (s : Sig) : Type where
  | le : Form s → Entry s
  | eq : Entry s
  /-- Presence, inherited from the source's `j`-th proposition. -/
  | has : Nat → Entry s

/-- Entries of an object coercion, oldest first. -/
inductive Entries (s : Sig) : Type where
  | nil : Entries s
  | cons : Entries s → Entry s → Entries s

end

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

/-- Route a presence entry of the second coercion through the first. -/
def Entry.through (Es₁ : Entries s) : Entry s → Option (Entry s)
  | .le F => some (.le F)
  | .eq => some .eq
  | .has j => Es₁.get? j

def Entries.through (Es₁ : Entries s) : Entries s → Option (Entries s)
  | .nil => some .nil
  | .cons Es E => do
      let Es' ← Entries.through Es₁ Es
      let E' ← Entry.through Es₁ E
      pure (Es' ▹ E')

/-- Combine the head forms of two composable coercions.  Conversions compose
as equalities and are absorbed into function and object forms; the
composite of two object coercions is the second, with its presence entries
routed through the first. -/
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

/-- Instantiate the entries of an object coercion at an atom whose view is `V`. -/
def entriesAt (V : View s) : Entries s → Option (View s)
  | .nil => some .nil
  | .cons Es (.le F) => do
      let V' ← entriesAt V Es
      pure (V' ▹ .le F)
  | .cons Es .eq => do
      let V' ← entriesAt V Es
      pure (V' ▹ .eq)
  | .cons Es (.has j) => do
      let V' ← entriesAt V Es
      let P ← V.get? j
      pure (V' ▹ P)

mutual

/-- Head form of closed inclusion evidence, with fuel. -/
def hnf (σ : Store s) : Nat → LeCo s → Option (Form s)
  | 0, _ => none
  | _ + 1, .refl T => some (.eqv (.refl T))
  | _ + 1, .top _ => some .top
  | _ + 1, .bot _ => some .bot
  | _ + 1, .eqToLe φ => some (.eqv φ)
  | _ + 1, .pi d c => some (.pi d c)
  | n + 1, .obj _ m => (entries σ n m).map .obj
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

/-- Entries of a morphism: the normal forms of its pieces of evidence. -/
def entries (σ : Store s) : Nat → Morphism s → Option (Entries s)
  | 0, _ => none
  | _ + 1, .nil => some .nil
  | n + 1, .le m e => do
      let Es ← entries σ n m
      let F ← hnf σ n e
      pure (Es ▹ .le F)
  | n + 1, .eq m _ => do
      let Es ← entries σ n m
      pure (Es ▹ .eq)
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

/-- `σ ⊢ a ⇓ᶜ[n] (a', F)`: the chain of casts of `a` normalizes to `F`. -/
scoped notation:40 σ:51 " ⊢ " a:51 " ⇓ᶜ[" n "] " r:51 => closedAtomForm σ n a = some r

end FCdot
