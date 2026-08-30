import DotFCRP.Source.Syntax

/-!
# Finite transparent alias resolution

An `AliasStore` is a finite, immutable spine of transparent term-field
definitions.  Lookup is newest-wins and proof relevant.  A path is traceable
when every selected receiver resolves to a variable with a visible field and
the field target is itself traceable.  Opaque records and dynamic receivers
have no constructor in this judgment.
-/

namespace DotFCRP.Source

open DotFC

/-- One transparent field in a finite alias-record spine. -/
structure AliasField (scope : Sig) where
  owner : BVar scope .term
  label : Name
  target : Path scope
deriving DecidableEq

/-- A finite immutable alias store.  The head is the newest field. -/
abbrev AliasStore (scope : Sig) : Type := List (AliasField scope)

namespace AliasField

def rename {source target : Sig} (field : AliasField source)
    (rho : Rename source target) : AliasField target where
  owner := rho.var field.owner
  label := field.label
  target := field.target.rename rho

end AliasField

namespace AliasStore

def rename {source target : Sig} (store : AliasStore source)
    (rho : Rename source target) : AliasStore target :=
  store.map fun field => field.rename rho

def weaken {scope : Sig} {kind : BinderKind} (store : AliasStore scope) :
    AliasStore (scope ▹ kind) :=
  store.rename Rename.succ

@[simp]
theorem rename_nil {source target : Sig} (rho : Rename source target) :
    rename ([] : AliasStore source) rho = [] := rfl

@[simp]
theorem rename_cons {source target : Sig} (field : AliasField source)
    (store : AliasStore source) (rho : Rename source target) :
    rename (field :: store) rho = field.rename rho :: store.rename rho := rfl

end AliasStore

/-- Proof-relevant newest-wins lookup of a transparent field.  `there`
requires that the newer field has a different `(owner,label)` key. -/
inductive FieldAt : {scope : Sig} → AliasStore scope →
    BVar scope .term → Name → Path scope → Type where
  | here {scope : Sig} {field : AliasField scope}
      {store : AliasStore scope} :
      FieldAt (field :: store) field.owner field.label field.target
  | there {scope : Sig} {field : AliasField scope}
      {store : AliasStore scope} {owner : BVar scope .term}
      {label : Name} {target : Path scope}
      (different : owner ≠ field.owner ∨ label ≠ field.label)
      (older : FieldAt store owner label target) :
      FieldAt (field :: store) owner label target

namespace FieldAt

/-- Newest-wins field lookup has a unique target. -/
theorem deterministic {scope : Sig} {store : AliasStore scope}
    {owner : BVar scope .term} {label : Name} {first second : Path scope}
    (firstLookup : FieldAt store owner label first)
    (secondLookup : FieldAt store owner label second) : first = second := by
  induction firstLookup with
  | here =>
      cases secondLookup with
      | here => rfl
      | there different older =>
          cases different with
          | inl ownerDifferent => exact False.elim (ownerDifferent rfl)
          | inr labelDifferent => exact False.elim (labelDifferent rfl)
  | there different older induction =>
      cases secondLookup with
      | here =>
          cases different with
          | inl ownerDifferent => exact False.elim (ownerDifferent rfl)
          | inr labelDifferent => exact False.elim (labelDifferent rfl)
      | there _ secondOlder => exact induction secondOlder

/-- Field lookup is natural under an injective renaming. -/
def rename {source target : Sig} {store : AliasStore source}
    {owner : BVar source .term} {label : Name} {fieldTarget : Path source}
    (lookup : FieldAt store owner label fieldTarget)
    (rho : Rename source target)
    (injective : Function.Injective
      (fun root : BVar source .term => rho.var root)) :
    FieldAt (store.rename rho) (rho.var owner) label
      (fieldTarget.rename rho) :=
  match lookup with
  | .here => .here
  | @there _ field _ foundOwner foundLabel _ different older =>
      .there (by
        cases different with
        | inl ownerDifferent =>
            exact Or.inl (fun equal => ownerDifferent (injective equal))
        | inr labelDifferent => exact Or.inr labelDifferent)
        (older.rename rho injective)

/-- Weakening cannot merge two field owners. -/
def weaken {scope : Sig} {store : AliasStore scope}
    {owner : BVar scope .term} {label : Name} {target : Path scope}
    (lookup : FieldAt store owner label target) {kind : BinderKind} :
    FieldAt (store.weaken (kind := kind)) (.there owner) label
      target.weaken :=
  lookup.rename Rename.succ (by
    intro first second equal
    exact BVar.there.inj equal)

end FieldAt

/-- Resolution of a stable path to its final variable anchor. -/
inductive Traceable : {scope : Sig} → AliasStore scope →
    Path scope → BVar scope .term → Type where
  | var {scope : Sig} {store : AliasStore scope}
      {anchor : BVar scope .term} :
      Traceable store (.var anchor) anchor
  | select {scope : Sig} {store : AliasStore scope}
      {receiver target : Path scope} {owner anchor : BVar scope .term}
      {label : Name}
      (receiverTrace : Traceable store receiver owner)
      (field : FieldAt store owner label target)
      (targetTrace : Traceable store target anchor) :
      Traceable store (.select receiver label) anchor

namespace Traceable

/-- Transparent resolution has one final anchor. -/
theorem deterministic {scope : Sig} {store : AliasStore scope}
    {path : Path scope} {first second : BVar scope .term}
    (firstTrace : Traceable store path first)
    (secondTrace : Traceable store path second) : first = second := by
  induction firstTrace generalizing second with
  | var =>
      cases secondTrace
      rfl
  | select firstReceiver firstField firstTargetTrace receiverInduction
      targetInduction =>
      cases secondTrace with
      | select secondReceiver secondField secondTargetTrace =>
          have ownerEqual := receiverInduction secondReceiver
          cases ownerEqual
          have targetEqual :=
            FieldAt.deterministic firstField secondField
          cases targetEqual
          exact targetInduction secondTargetTrace

/-- Resolution is natural under an injective renaming. -/
def rename {source target : Sig} {store : AliasStore source}
    {path : Path source} {anchor : BVar source .term}
    (trace : Traceable store path anchor) (rho : Rename source target)
    (injective : Function.Injective
      (fun root : BVar source .term => rho.var root)) :
    Traceable (store.rename rho) (path.rename rho) (rho.var anchor) :=
  match trace with
  | .var => .var
  | .select receiverTrace field targetTrace =>
      .select (receiverTrace.rename rho injective)
        (field.rename rho injective) (targetTrace.rename rho injective)

/-- Weakening transports a complete trace below any fresh binder. -/
def weaken {scope : Sig} {store : AliasStore scope} {path : Path scope}
    {anchor : BVar scope .term} (trace : Traceable store path anchor)
    {kind : BinderKind} :
    Traceable (store.weaken (kind := kind)) path.weaken (.there anchor) :=
  trace.rename Rename.succ (by
    intro first second equal
    exact BVar.there.inj equal)

/-- A weakened ambient path cannot resolve to the fresh term binder. -/
theorem weaken_not_fresh {scope : Sig} {store : AliasStore scope}
    {path : Path scope} {anchor : BVar scope .term}
    (trace : Traceable store path anchor) :
    Traceable (store.weaken (kind := .term)) path.weaken
      (.here : BVar (scope ▹ .term) .term) → False := by
  intro freshTrace
  have impossible := deterministic trace.weaken freshTrace
  cases impossible

end Traceable

/-! ## Co-resolution and path equality -/

/-- Proof-relevant equality of stable paths: both resolve to one anchor. -/
structure CoResolved {scope : Sig} (store : AliasStore scope)
    (left right : Path scope) : Type where
  anchor : BVar scope .term
  leftTrace : Traceable store left anchor
  rightTrace : Traceable store right anchor

/-- The source path-equality judgment is exactly transparent co-resolution. -/
abbrev PathEq {scope : Sig} (store : AliasStore scope)
    (left right : Path scope) : Type :=
  CoResolved store left right

namespace CoResolved

def refl {scope : Sig} {store : AliasStore scope} {path : Path scope}
    {anchor : BVar scope .term} (trace : Traceable store path anchor) :
    CoResolved store path path :=
  ⟨anchor, trace, trace⟩

def symm {scope : Sig} {store : AliasStore scope} {left right : Path scope}
    (equality : CoResolved store left right) :
    CoResolved store right left :=
  ⟨equality.anchor, equality.rightTrace, equality.leftTrace⟩

def trans {scope : Sig} {store : AliasStore scope}
    {first second third : Path scope}
    (left : CoResolved store first second)
    (right : CoResolved store second third) :
    CoResolved store first third := by
  cases left with
  | mk leftAnchor firstTrace secondTrace =>
      cases right with
      | mk rightAnchor secondTrace' thirdTrace =>
          have anchorsEqual : leftAnchor = rightAnchor :=
            Traceable.deterministic secondTrace secondTrace'
          subst rightAnchor
          exact ⟨leftAnchor, firstTrace, thirdTrace⟩

/-- Co-resolution is preserved by injective renaming. -/
def rename {source target : Sig} {store : AliasStore source}
    {left right : Path source} (equality : CoResolved store left right)
    (rho : Rename source target)
    (injective : Function.Injective
      (fun root : BVar source .term => rho.var root)) :
    CoResolved (store.rename rho) (left.rename rho) (right.rename rho) :=
  ⟨rho.var equality.anchor,
    equality.leftTrace.rename rho injective,
    equality.rightTrace.rename rho injective⟩

def weaken {scope : Sig} {store : AliasStore scope}
    {left right : Path scope} (equality : CoResolved store left right)
    {kind : BinderKind} :
    CoResolved (store.weaken (kind := kind)) left.weaken right.weaken :=
  ⟨.there equality.anchor, equality.leftTrace.weaken,
    equality.rightTrace.weaken⟩

end CoResolved

/-- A path bundled with its finite trace certificate. -/
structure CertifiedPath {scope : Sig} (store : AliasStore scope) where
  path : Path scope
  anchor : BVar scope .term
  trace : Traceable store path anchor

namespace CertifiedPath

/-- Propositional quotient relation induced by proof-relevant co-resolution. -/
def Equivalent {scope : Sig} {store : AliasStore scope}
    (left right : CertifiedPath store) : Prop :=
  Nonempty (CoResolved store left.path right.path)

theorem equivalent_refl {scope : Sig} {store : AliasStore scope}
    (path : CertifiedPath store) : Equivalent path path :=
  ⟨CoResolved.refl path.trace⟩

theorem equivalent_symm {scope : Sig} {store : AliasStore scope}
    {left right : CertifiedPath store} :
    Equivalent left right → Equivalent right left := by
  rintro ⟨equality⟩
  exact ⟨equality.symm⟩

theorem equivalent_trans {scope : Sig} {store : AliasStore scope}
    {first second third : CertifiedPath store} :
    Equivalent first second → Equivalent second third →
      Equivalent first third := by
  rintro ⟨left⟩ ⟨right⟩
  exact ⟨left.trans right⟩

instance {scope : Sig} {store : AliasStore scope} :
    Setoid (CertifiedPath store) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

end CertifiedPath

/-! ## Observable path reduction -/

/-- One transparent field-reduction step.  The receiver must resolve to the
owner of the selected field, and the target must itself be traceable.  The
latter premise excludes cyclic or otherwise unrealizable alias stores from
the supported reduction fragment. -/
inductive PathStep : {scope : Sig} → AliasStore scope →
    Path scope → Path scope → Type where
  | field {scope : Sig} {store : AliasStore scope}
      {receiver target : Path scope} {owner anchor : BVar scope .term}
      {label : Name}
      (receiverTrace : Traceable store receiver owner)
      (lookup : FieldAt store owner label target)
      (targetTrace : Traceable store target anchor) :
      PathStep store (.select receiver label) target

namespace PathStep

/-- Resolving the reduct also resolves the redex. -/
def traceBack {scope : Sig} {store : AliasStore scope}
    {source target : Path scope} (step : PathStep store source target)
    {anchor : BVar scope .term} (targetTrace : Traceable store target anchor) :
    Traceable store source anchor :=
  match step with
  | .field receiverTrace lookup _ => .select receiverTrace lookup targetTrace

/-- A field step preserves the final anchor in the forward direction. -/
def traceForward {scope : Sig} {store : AliasStore scope}
    {source target : Path scope} (step : PathStep store source target)
    {anchor : BVar scope .term} (sourceTrace : Traceable store source anchor) :
    Traceable store target anchor := by
  cases step with
  | field stepReceiver stepLookup _ =>
      cases sourceTrace with
      | select sourceReceiver sourceLookup sourceTargetTrace =>
          have ownerEqual :=
            Traceable.deterministic stepReceiver sourceReceiver
          cases ownerEqual
          have targetEqual :=
            FieldAt.deterministic stepLookup sourceLookup
          cases targetEqual
          exact sourceTargetTrace

/-- A reduction step witnesses path equality between redex and reduct. -/
def coResolved {scope : Sig} {store : AliasStore scope}
    {source target : Path scope} (step : PathStep store source target)
    {anchor : BVar scope .term} (targetTrace : Traceable store target anchor) :
    CoResolved store source target :=
  ⟨anchor, step.traceBack targetTrace, targetTrace⟩

end PathStep

/-! ## Fresh-binder separation -/

/-- A fresh variable is traceable to itself. -/
def freshTrace {scope : Sig} {store : AliasStore (scope ▹ .term)} :
    Traceable store (.var .here) (.here : BVar (scope ▹ .term) .term) :=
  .var

/-- The fresh variable has its expected reflexive equality certificate. -/
def freshRefl {scope : Sig} {store : AliasStore (scope ▹ .term)} :
    CoResolved store (.var .here) (.var .here) :=
  CoResolved.refl freshTrace

/-- No weakened ambient trace aliases the fresh variable. -/
theorem weakened_not_coResolved_fresh {scope : Sig}
    {store : AliasStore scope} {path : Path scope}
    {anchor : BVar scope .term} (trace : Traceable store path anchor) :
    CoResolved (store.weaken (kind := .term)) path.weaken (.var .here) →
      False := by
  intro equality
  have anchorEqual :=
    Traceable.deterministic equality.rightTrace freshTrace
  exact trace.weaken_not_fresh (anchorEqual ▸ equality.leftTrace)

end DotFCRP.Source
