/-!
# Intrinsically scoped heterogeneous variables

`Sig` is the one index used by every DotFC syntax category.  It records term,
type, evidence, and reusable-member-handle binders in a single list.  A
`BVar s k` can select only a binder of kind `k` from `s`, so this representation
rules out cross-sort variable mistakes by construction.

The representation and the orientation of `Rename.comp` follow Capybara's
de Bruijn kernel: `ρ₁.comp ρ₂` first applies `ρ₁`, then `ρ₂`.
-/

namespace DotFC

/-- The proof relation witnessed by an evidence variable.  Equality is
symmetric; inclusion is deliberately directed. -/
inductive Relation : Type where
  | equality
  | inclusion
deriving DecidableEq, Repr

/-- Every kind of binder in the two calculi.  Member binders name reusable
member-exposure handles rather than repeating an exposure derivation at each
selection bound. -/
inductive BinderKind : Type where
  | term
  | type
  | evidence (relation : Relation)
  | member
deriving DecidableEq, Repr

/-- The shape of a heterogeneous context.  There is one signature index for
all syntax, rather than an independent index for each variable sort. -/
@[reducible]
def Sig : Type := List BinderKind

namespace Sig

/-- Extend a signature with a binder of kind `k`.  The newest binder is at
the head, as expected for de Bruijn indices. -/
def extend (s : Sig) (k : BinderKind) : Sig := k :: s

/-- Extend a signature with several heterogeneous binders.  The head of `ks`
is the newest binder in the resulting signature. -/
def extendMany (s : Sig) : Sig → Sig
  | [] => s
  | k :: ks => extend (extendMany s ks) k

@[simp]
theorem extendMany_nil (s : Sig) : extendMany s [] = s := rfl

@[simp]
theorem extendMany_cons (s : Sig) (k : BinderKind) (ks : Sig) :
    extendMany s (k :: ks) = extend (extendMany s ks) k := rfl

/-- Extending by an append is the corresponding iterated extension. -/
theorem extendMany_append (s : Sig) (ks₁ ks₂ : Sig) :
    extendMany s (ks₁ ++ ks₂) = extendMany (extendMany s ks₂) ks₁ := by
  induction ks₁ with
  | nil => rfl
  | cons k ks ih =>
      simp only [List.cons_append, extendMany_cons, ih]

end Sig

/-- Signature extension notation. -/
infixl:65 " ▹ " => Sig.extend

/-- A bound variable in a heterogeneous signature.  Its second index ensures
that a variable can only be used at the kind at which it was bound. -/
inductive BVar : Sig → BinderKind → Type where
  | here {s : Sig} {k : BinderKind} : BVar (s ▹ k) k
  | there {s : Sig} {k k₀ : BinderKind} : BVar s k → BVar (s ▹ k₀) k
deriving DecidableEq

/-- A single, kind-polymorphic map between heterogeneous signatures. -/
structure Rename (s₁ s₂ : Sig) where
  var : {k : BinderKind} → BVar s₁ k → BVar s₂ k

namespace Rename

/-- The identity renaming. -/
def id {s : Sig} : Rename s s where
  var := fun x => x

/-- Composition in diagrammatic order: `ρ₁.comp ρ₂` first applies `ρ₁`
and then `ρ₂`. -/
def comp {s₁ s₂ s₃ : Sig} (ρ₁ : Rename s₁ s₂)
    (ρ₂ : Rename s₂ s₃) : Rename s₁ s₃ where
  var := fun x => ρ₂.var (ρ₁.var x)

/-- Lift a renaming below one binder.  The new variable maps to itself and all
old variables are transported below it. -/
def lift {s₁ s₂ : Sig} {k : BinderKind} (ρ : Rename s₁ s₂) :
    Rename (s₁ ▹ k) (s₂ ▹ k) where
  var := fun
    | .here => .here
    | .there x => .there (ρ.var x)

/-- Lift a renaming below several heterogeneous binders. -/
def liftMany {s₁ s₂ : Sig} (ρ : Rename s₁ s₂) (ks : Sig) :
    Rename (Sig.extendMany s₁ ks) (Sig.extendMany s₂ ks) :=
  match ks with
  | [] => ρ
  | k :: ks => (liftMany ρ ks).lift (k := k)

/-- Weakening below one new binder. -/
def succ {s : Sig} {k : BinderKind} : Rename s (s ▹ k) where
  var := fun x => .there x

@[simp]
theorem id_var {s : Sig} {k : BinderKind} (x : BVar s k) :
    (id (s := s)).var x = x := rfl

@[simp]
theorem comp_var {s₁ s₂ s₃ : Sig} (ρ₁ : Rename s₁ s₂)
    (ρ₂ : Rename s₂ s₃) {k : BinderKind} (x : BVar s₁ k) :
    (ρ₁.comp ρ₂).var x = ρ₂.var (ρ₁.var x) := rfl

@[simp]
theorem lift_here {s₁ s₂ : Sig} {k : BinderKind} (ρ : Rename s₁ s₂) :
    (ρ.lift (k := k)).var (.here : BVar (s₁ ▹ k) k) = .here := rfl

@[simp]
theorem lift_there {s₁ s₂ : Sig} {k k₀ : BinderKind}
    (ρ : Rename s₁ s₂) (x : BVar s₁ k) :
    (ρ.lift (k := k₀)).var (.there x) = .there (ρ.var x) := rfl

@[simp]
theorem succ_var {s : Sig} {k k₀ : BinderKind} (x : BVar s k) :
    (succ (s := s) (k := k₀)).var x = .there x := rfl

/-- Two renamings are equal when they agree on every kind of variable. -/
@[ext]
theorem ext {s₁ s₂ : Sig} {ρ₁ ρ₂ : Rename s₁ s₂}
    (h : ∀ {k : BinderKind} (x : BVar s₁ k), ρ₁.var x = ρ₂.var x) :
    ρ₁ = ρ₂ := by
  cases ρ₁
  cases ρ₂
  congr
  funext k x
  exact h x

/-- Capybara-compatible name for renaming extensionality. -/
theorem funext {s₁ s₂ : Sig} {ρ₁ ρ₂ : Rename s₁ s₂}
    (h : ∀ {k : BinderKind} (x : BVar s₁ k), ρ₁.var x = ρ₂.var x) :
    ρ₁ = ρ₂ := ext h

@[simp]
theorem comp_id {s₁ s₂ : Sig} (ρ : Rename s₁ s₂) :
    ρ.comp id = ρ := by
  apply ext
  intro k x
  rfl

@[simp]
theorem id_comp {s₁ s₂ : Sig} (ρ : Rename s₁ s₂) :
    id.comp ρ = ρ := by
  apply ext
  intro k x
  rfl

/-- Renaming composition is associative in diagrammatic order. -/
theorem comp_assoc {s₁ s₂ s₃ s₄ : Sig} (ρ₁ : Rename s₁ s₂)
    (ρ₂ : Rename s₂ s₃) (ρ₃ : Rename s₃ s₄) :
    (ρ₁.comp ρ₂).comp ρ₃ = ρ₁.comp (ρ₂.comp ρ₃) := by
  apply ext
  intro k x
  rfl

/-- Lifting the identity yields the identity. -/
@[simp]
theorem lift_id {s : Sig} {k : BinderKind} :
    (id (s := s)).lift (k := k) = id := by
  apply ext
  intro k' x
  cases x <;> rfl

/-- Lifting distributes over composition. -/
@[simp]
theorem lift_comp {s₁ s₂ s₃ : Sig} {k : BinderKind}
    (ρ₁ : Rename s₁ s₂) (ρ₂ : Rename s₂ s₃) :
    (ρ₁.comp ρ₂).lift (k := k) = ρ₁.lift.comp ρ₂.lift := by
  apply ext
  intro k' x
  cases x <;> rfl

/-- Weakening commutes with lifting. -/
theorem succ_lift_comm {s₁ s₂ : Sig} {k : BinderKind} (ρ : Rename s₁ s₂) :
    (succ (s := s₁) (k := k)).comp ρ.lift =
      ρ.comp (succ (s := s₂) (k := k)) := by
  apply ext
  intro k' x
  cases x <;> rfl

@[simp]
theorem liftMany_nil {s₁ s₂ : Sig} (ρ : Rename s₁ s₂) :
    ρ.liftMany [] = ρ := rfl

@[simp]
theorem liftMany_cons {s₁ s₂ : Sig} (ρ : Rename s₁ s₂)
    (k : BinderKind) (ks : Sig) :
    ρ.liftMany (k :: ks) = (ρ.liftMany ks).lift := rfl

/-- Lifting the identity below any signature yields the identity. -/
@[simp]
theorem liftMany_id {s : Sig} (ks : Sig) :
    (id (s := s)).liftMany ks = id := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      simp only [liftMany_cons, ih, lift_id]
      rfl

/-- Iterated lifting distributes over composition. -/
@[simp]
theorem liftMany_comp {s₁ s₂ s₃ : Sig} (ρ₁ : Rename s₁ s₂)
    (ρ₂ : Rename s₂ s₃) (ks : Sig) :
    (ρ₁.comp ρ₂).liftMany ks =
      (Rename.comp (ρ₁.liftMany ks) (ρ₂.liftMany ks)) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      simp only [liftMany_cons, ih, lift_comp]
      rfl

end Rename

end DotFC
