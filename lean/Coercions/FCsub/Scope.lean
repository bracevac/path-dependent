/-!
# Intrinsically scoped heterogeneous variables for FCsub

This module is deliberately standalone: it has no dependency on `DotFC` or
on a source language.  One heterogeneous signature indexes terms, abstract
type names, and proof evidence.  Equality and directed inclusion evidence are
different binder kinds, and there is no source-specific member-handle kind.
-/

namespace FCsub

/-- The relation witnessed by an evidence variable.  Equality is symmetric;
inclusion is directed. -/
inductive Relation : Type where
  | equality
  | inclusion
deriving DecidableEq, Repr

/-- The complete binder vocabulary of the independent FCsub kernel. -/
inductive BinderKind : Type where
  | term
  | type
  | evidence (relation : Relation)
deriving DecidableEq, Repr

/-- A heterogeneous de Bruijn signature. -/
@[reducible]
def Sig : Type := List BinderKind

namespace Sig

/-- Add one newest binder. -/
def extend (scope : Sig) (kind : BinderKind) : Sig := kind :: scope

/-- Add a heterogeneous list of binders; the head of `kinds` is newest. -/
def extendMany (scope : Sig) : Sig → Sig
  | [] => scope
  | kind :: kinds => extend (extendMany scope kinds) kind

/-- Add `count` binders of one kind. -/
def extendN (scope : Sig) (kind : BinderKind) : Nat → Sig
  | 0 => scope
  | count + 1 => extend (extendN scope kind count) kind

@[simp]
theorem extendMany_nil (scope : Sig) : extendMany scope [] = scope := rfl

@[simp]
theorem extendMany_cons (scope : Sig) (kind : BinderKind) (kinds : Sig) :
    extendMany scope (kind :: kinds) =
      extend (extendMany scope kinds) kind := rfl

theorem extendMany_append (scope : Sig) (first second : Sig) :
    extendMany scope (first ++ second) =
      extendMany (extendMany scope second) first := by
  induction first with
  | nil => rfl
  | cons kind rest induction =>
      simp only [List.cons_append, extendMany_cons, induction]

@[simp]
theorem extendN_zero (scope : Sig) (kind : BinderKind) :
    extendN scope kind 0 = scope := rfl

@[simp]
theorem extendN_succ (scope : Sig) (kind : BinderKind) (count : Nat) :
    extendN scope kind (count + 1) =
      extend (extendN scope kind count) kind := rfl

/-- Repeated extension composes by addition. -/
theorem extendN_add (scope : Sig) (kind : BinderKind) (first second : Nat) :
    extendN scope kind (first + second) =
      extendN (extendN scope kind second) kind first := by
  induction first with
  | zero => simp
  | succ first induction =>
      simp only [Nat.succ_add, extendN_succ, induction]

end Sig

/-- Signature extension notation. -/
infixl:65 " ▹ " => Sig.extend

/-- Scope after allocating all abstract type names of a telescope. -/
@[reducible]
def TypeScope (scope : Sig) (names : Nat) : Sig :=
  Sig.extendN scope .type names

/-- Scope after allocating all names and then all directed constraints. -/
@[reducible]
def StaticScope (scope : Sig) (names constraints : Nat) : Sig :=
  Sig.extendN (TypeScope scope names) (.evidence .inclusion) constraints

/-- The static telescope scope followed by its separate runtime payload. -/
@[reducible]
def PayloadScope (scope : Sig) (names constraints : Nat) : Sig :=
  StaticScope scope names constraints ▹ .term

/-- Scope of one fresh abstract name and a private equality witness. -/
@[reducible]
def NewtypeScope (scope : Sig) : Sig :=
  (scope ▹ .type) ▹ .evidence .equality

/-- A variable can select only a binder of the requested kind. -/
inductive BVar : Sig → BinderKind → Type where
  | here {scope : Sig} {kind : BinderKind} : BVar (scope ▹ kind) kind
  | there {scope : Sig} {kind newest : BinderKind} :
      BVar scope kind → BVar (scope ▹ newest) kind
deriving DecidableEq

/-- A kind-preserving map between heterogeneous signatures. -/
structure Rename (source target : Sig) where
  var : {kind : BinderKind} → BVar source kind → BVar target kind

namespace Rename

/-- Identity renaming. -/
def id {scope : Sig} : Rename scope scope where
  var := fun index => index

/-- Diagrammatic composition: apply `first`, then `second`. -/
def comp {first second third : Sig} (rho₁ : Rename first second)
    (rho₂ : Rename second third) : Rename first third where
  var := fun index => rho₂.var (rho₁.var index)

/-- Lift a renaming under one binder. -/
def lift {source target : Sig} {kind : BinderKind}
    (rho : Rename source target) :
    Rename (source ▹ kind) (target ▹ kind) where
  var := fun
    | .here => .here
    | .there index => .there (rho.var index)

/-- Lift under a heterogeneous sequence of binders. -/
def liftMany {source target : Sig} (rho : Rename source target)
    (kinds : Sig) :
    Rename (Sig.extendMany source kinds) (Sig.extendMany target kinds) :=
  match kinds with
  | [] => rho
  | kind :: rest => (liftMany rho rest).lift (kind := kind)

/-- Lift under `count` binders of one kind. -/
def liftN {source target : Sig} (rho : Rename source target)
    (kind : BinderKind) : (count : Nat) →
    Rename (Sig.extendN source kind count) (Sig.extendN target kind count)
  | 0 => rho
  | count + 1 => (liftN rho kind count).lift (kind := kind)

/-- Lift below all names of a names-first telescope. -/
def liftTypes {source target : Sig} (rho : Rename source target)
    (names : Nat) : Rename (TypeScope source names) (TypeScope target names) :=
  rho.liftN .type names

/-- Lift below all static binders of a names-first telescope. -/
def liftStatic {source target : Sig} (rho : Rename source target)
    (names constraints : Nat) :
    Rename (StaticScope source names constraints)
      (StaticScope target names constraints) :=
  (rho.liftTypes names).liftN (.evidence .inclusion) constraints

/-- Lift below a static telescope and its separate runtime payload. -/
def liftPayload {source target : Sig} (rho : Rename source target)
    (names constraints : Nat) :
    Rename (PayloadScope source names constraints)
      (PayloadScope target names constraints) :=
  (rho.liftStatic names constraints).lift (kind := .term)

/-- Lift below a fresh name and its private equality witness. -/
def liftNewtype {source target : Sig} (rho : Rename source target) :
    Rename (NewtypeScope source) (NewtypeScope target) :=
  (rho.lift (kind := .type)).lift (kind := .evidence .equality)

/-- Weakening below one new binder. -/
def succ {scope : Sig} {kind : BinderKind} : Rename scope (scope ▹ kind) where
  var := fun index => .there index

/-- Weakening below several same-kind binders. -/
def weakenN {scope : Sig} (kind : BinderKind) : (count : Nat) →
    Rename scope (Sig.extendN scope kind count)
  | 0 => id
  | count + 1 => (weakenN kind count).comp succ

/-- Weaken an ambient scope below all abstract names. -/
def weakenTypes {scope : Sig} (names : Nat) :
    Rename scope (TypeScope scope names) :=
  weakenN .type names

/-- Weaken an ambient scope below a complete static telescope. -/
def weakenStatic {scope : Sig} (names constraints : Nat) :
    Rename scope (StaticScope scope names constraints) :=
  (weakenTypes names).comp (weakenN (.evidence .inclusion) constraints)

/-- Weaken an ambient scope below a static telescope and payload binder. -/
def weakenPayload {scope : Sig} (names constraints : Nat) :
    Rename scope (PayloadScope scope names constraints) :=
  (weakenStatic names constraints).comp succ

@[simp]
theorem id_var {scope : Sig} {kind : BinderKind} (index : BVar scope kind) :
    (id (scope := scope)).var index = index := rfl

@[simp]
theorem comp_var {first second third : Sig} (rho₁ : Rename first second)
    (rho₂ : Rename second third) {kind : BinderKind}
    (index : BVar first kind) :
    (rho₁.comp rho₂).var index = rho₂.var (rho₁.var index) := rfl

@[simp]
theorem lift_here {source target : Sig} {kind : BinderKind}
    (rho : Rename source target) :
    (rho.lift (kind := kind)).var (.here : BVar (source ▹ kind) kind) =
      .here := rfl

@[simp]
theorem lift_there {source target : Sig} {kind newest : BinderKind}
    (rho : Rename source target) (index : BVar source kind) :
    (rho.lift (kind := newest)).var (.there index) =
      .there (rho.var index) := rfl

@[simp]
theorem succ_var {scope : Sig} {kind newest : BinderKind}
    (index : BVar scope kind) :
    (succ (scope := scope) (kind := newest)).var index = .there index := rfl

@[ext]
theorem ext {source target : Sig} {rho₁ rho₂ : Rename source target}
    (pointwise : ∀ {kind : BinderKind} (index : BVar source kind),
      rho₁.var index = rho₂.var index) : rho₁ = rho₂ := by
  cases rho₁
  cases rho₂
  congr
  funext kind index
  exact pointwise index

theorem funext {source target : Sig} {rho₁ rho₂ : Rename source target}
    (pointwise : ∀ {kind : BinderKind} (index : BVar source kind),
      rho₁.var index = rho₂.var index) : rho₁ = rho₂ :=
  ext pointwise

@[simp]
theorem comp_id {source target : Sig} (rho : Rename source target) :
    rho.comp id = rho := by
  apply ext
  intro kind index
  rfl

@[simp]
theorem id_comp {source target : Sig} (rho : Rename source target) :
    id.comp rho = rho := by
  apply ext
  intro kind index
  rfl

theorem comp_assoc {first second third fourth : Sig}
    (rho₁ : Rename first second) (rho₂ : Rename second third)
    (rho₃ : Rename third fourth) :
    (rho₁.comp rho₂).comp rho₃ = rho₁.comp (rho₂.comp rho₃) := by
  apply ext
  intro kind index
  rfl

@[simp]
theorem lift_id {scope : Sig} {kind : BinderKind} :
    (id (scope := scope)).lift (kind := kind) = id := by
  apply ext
  intro other index
  cases index <;> rfl

@[simp]
theorem lift_comp {first second third : Sig} {kind : BinderKind}
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (rho₁.comp rho₂).lift (kind := kind) =
      rho₁.lift.comp rho₂.lift := by
  apply ext
  intro other index
  cases index <;> rfl

/-- Weakening commutes with lifting. -/
theorem succ_lift_comm {source target : Sig} {kind : BinderKind}
    (rho : Rename source target) :
    (succ (scope := source) (kind := kind)).comp rho.lift =
      rho.comp (succ (scope := target) (kind := kind)) := by
  apply ext
  intro other index
  rfl

@[simp]
theorem liftMany_id {scope : Sig} (kinds : Sig) :
    (id (scope := scope)).liftMany kinds = id := by
  induction kinds with
  | nil => rfl
  | cons kind rest induction =>
      simp only [liftMany, induction, lift_id]
      rfl

@[simp]
theorem liftMany_comp {first second third : Sig}
    (rho₁ : Rename first second) (rho₂ : Rename second third)
    (kinds : Sig) :
    (rho₁.comp rho₂).liftMany kinds =
      (rho₁.liftMany kinds).comp (rho₂.liftMany kinds) := by
  induction kinds with
  | nil => rfl
  | cons kind rest induction =>
      simp only [liftMany, induction, lift_comp]
      rfl

@[simp]
theorem liftN_id {scope : Sig} (kind : BinderKind) (count : Nat) :
    (id (scope := scope)).liftN kind count = id := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [liftN, induction, lift_id]
      rfl

@[simp]
theorem liftN_comp {first second third : Sig}
    (rho₁ : Rename first second) (rho₂ : Rename second third)
    (kind : BinderKind) (count : Nat) :
    (rho₁.comp rho₂).liftN kind count =
      (rho₁.liftN kind count).comp (rho₂.liftN kind count) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [liftN, induction, lift_comp]
      rfl

/-- Weakening below a homogeneous suffix is natural in the ambient
renaming. -/
theorem weakenN_natural {source target : Sig} (rho : Rename source target)
    (kind : BinderKind) (count : Nat) :
    (weakenN (scope := source) kind count).comp (rho.liftN kind count) =
      rho.comp (weakenN (scope := target) kind count) := by
  induction count with
  | zero => simp [weakenN, liftN]
  | succ count induction =>
      apply ext
      intro other index
      simp only [weakenN, liftN, comp_var, succ_var, lift_there]
      congr 1
      exact congrArg (fun mapping => mapping.var index) induction

/-- Names-first weakening is natural. -/
theorem weakenTypes_natural {source target : Sig} (rho : Rename source target)
    (names : Nat) :
    (weakenTypes (scope := source) names).comp (rho.liftTypes names) =
      rho.comp (weakenTypes (scope := target) names) := by
  simpa [weakenTypes, liftTypes] using weakenN_natural rho .type names

/-- Complete static-telescope weakening is natural. -/
theorem weakenStatic_natural {source target : Sig}
    (rho : Rename source target) (names constraints : Nat) :
    (weakenStatic (scope := source) names constraints).comp
        (rho.liftStatic names constraints) =
      rho.comp (weakenStatic (scope := target) names constraints) := by
  unfold weakenStatic liftStatic
  rw [comp_assoc]
  rw [weakenN_natural]
  rw [← comp_assoc, weakenTypes_natural, comp_assoc]

/-- Static-plus-payload weakening is natural. -/
theorem weakenPayload_natural {source target : Sig}
    (rho : Rename source target) (names constraints : Nat) :
    (weakenPayload (scope := source) names constraints).comp
        (rho.liftPayload names constraints) =
      rho.comp (weakenPayload (scope := target) names constraints) := by
  unfold weakenPayload liftPayload
  rw [comp_assoc, succ_lift_comm, ← comp_assoc,
    weakenStatic_natural, comp_assoc]

@[simp]
theorem liftTypes_id {scope : Sig} (names : Nat) :
    (id (scope := scope)).liftTypes names = id := by
  simp [liftTypes]

@[simp]
theorem liftTypes_comp {first second third : Sig}
    (rho₁ : Rename first second) (rho₂ : Rename second third)
    (names : Nat) :
    (rho₁.comp rho₂).liftTypes names =
      (rho₁.liftTypes names).comp (rho₂.liftTypes names) := by
  simp [liftTypes]

@[simp]
theorem liftStatic_id {scope : Sig} (names constraints : Nat) :
    (id (scope := scope)).liftStatic names constraints = id := by
  simp [liftStatic]

@[simp]
theorem liftStatic_comp {first second third : Sig}
    (rho₁ : Rename first second) (rho₂ : Rename second third)
    (names constraints : Nat) :
    (rho₁.comp rho₂).liftStatic names constraints =
      (rho₁.liftStatic names constraints).comp
        (rho₂.liftStatic names constraints) := by
  simp [liftStatic]

@[simp]
theorem liftPayload_id {scope : Sig} (names constraints : Nat) :
    (id (scope := scope)).liftPayload names constraints = id := by
  simp [liftPayload]

@[simp]
theorem liftPayload_comp {first second third : Sig}
    (rho₁ : Rename first second) (rho₂ : Rename second third)
    (names constraints : Nat) :
    (rho₁.comp rho₂).liftPayload names constraints =
      (rho₁.liftPayload names constraints).comp
        (rho₂.liftPayload names constraints) := by
  simp [liftPayload]

@[simp]
theorem liftNewtype_id {scope : Sig} :
    liftNewtype (id (scope := scope)) = id := by
  simp [liftNewtype]

@[simp]
theorem liftNewtype_comp {first second third : Sig}
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    liftNewtype (rho₁.comp rho₂) =
      (liftNewtype rho₁).comp (liftNewtype rho₂) := by
  simp [liftNewtype]

end Rename

end FCsub
