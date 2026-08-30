/-!
# Intrinsic scopes for the binder-only DOT-with-captures source

This source calculus deliberately owns its scope language.  It does not reuse
the binder vocabulary of the coercion target: source contexts contain only
term variables and sorted static variables.
-/

namespace DOTCapture.BinderOnly

/-- Static variables range over either types or capture sets. -/
inductive StaticSort : Type where
  | type
  | capture
deriving DecidableEq, Repr

/-- The binders present in the binder-only source language. -/
inductive BinderKind : Type where
  | term
  | static (sort : StaticSort)
deriving DecidableEq, Repr

/-- A heterogeneous de Bruijn signature, newest binder first. -/
@[reducible]
def Sig : Type := List BinderKind

namespace Sig

/-- Add one newest binder. -/
def extend (scope : Sig) (kind : BinderKind) : Sig := kind :: scope

/-- Add a heterogeneous sequence of binders, with its head newest. -/
def extendMany (scope : Sig) : Sig → Sig
  | [] => scope
  | kind :: kinds => extend (extendMany scope kinds) kind

@[simp]
theorem extendMany_nil (scope : Sig) : extendMany scope [] = scope := rfl

@[simp]
theorem extendMany_cons (scope : Sig) (kind : BinderKind)
    (kinds : Sig) :
    extendMany scope (kind :: kinds) =
      extend (extendMany scope kinds) kind := rfl

theorem extendMany_append (scope : Sig) (first second : Sig) :
    extendMany scope (first ++ second) =
      extendMany (extendMany scope second) first := by
  induction first with
  | nil => rfl
  | cons kind rest induction =>
      simp only [List.cons_append, extendMany_cons, induction]

end Sig

/-- Signature extension notation. -/
infixl:65 " ▹ " => Sig.extend

/-- An intrinsically kinded variable in a heterogeneous signature. -/
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
def comp {first second third : Sig} (firstRename : Rename first second)
    (secondRename : Rename second third) : Rename first third where
  var := fun index => secondRename.var (firstRename.var index)

/-- Lift a renaming below one binder. -/
def lift {source target : Sig} {kind : BinderKind}
    (rho : Rename source target) :
    Rename (source ▹ kind) (target ▹ kind) where
  var := fun
    | .here => .here
    | .there index => .there (rho.var index)

/-- Lift a renaming below a heterogeneous block. -/
def liftMany {source target : Sig} (rho : Rename source target)
    (kinds : Sig) :
    Rename (Sig.extendMany source kinds) (Sig.extendMany target kinds) :=
  match kinds with
  | [] => rho
  | kind :: rest => (rho.liftMany rest).lift (kind := kind)

/-- Weaken every existing variable below one new binder. -/
def succ {scope : Sig} {kind : BinderKind} :
    Rename scope (scope ▹ kind) where
  var := fun index => .there index

@[simp]
theorem id_var {scope : Sig} {kind : BinderKind}
    (index : BVar scope kind) :
    (id (scope := scope)).var index = index := rfl

@[simp]
theorem comp_var {first second third : Sig}
    (firstRename : Rename first second) (secondRename : Rename second third)
    {kind : BinderKind} (index : BVar first kind) :
    (firstRename.comp secondRename).var index =
      secondRename.var (firstRename.var index) := rfl

@[simp]
theorem lift_here {source target : Sig} {kind : BinderKind}
    (rho : Rename source target) :
    (rho.lift (kind := kind)).var
      (.here : BVar (source ▹ kind) kind) = .here := rfl

@[simp]
theorem lift_there {source target : Sig} {kind newest : BinderKind}
    (rho : Rename source target) (index : BVar source kind) :
    (rho.lift (kind := newest)).var (.there index) =
      .there (rho.var index) := rfl

@[simp]
theorem succ_var {scope : Sig} {kind newest : BinderKind}
    (index : BVar scope kind) :
    (succ (scope := scope) (kind := newest)).var index =
      .there index := rfl

@[simp]
theorem liftMany_nil {source target : Sig} (rho : Rename source target) :
    rho.liftMany [] = rho := rfl

@[simp]
theorem liftMany_cons {source target : Sig} (rho : Rename source target)
    (kind : BinderKind) (rest : Sig) :
    rho.liftMany (kind :: rest) =
      (rho.liftMany rest).lift (kind := kind) := rfl

@[ext]
theorem ext {source target : Sig} {first second : Rename source target}
    (pointwise : ∀ {kind : BinderKind} (index : BVar source kind),
      first.var index = second.var index) : first = second := by
  cases first
  cases second
  congr
  funext kind index
  exact pointwise index

theorem funext {source target : Sig} {first second : Rename source target}
    (pointwise : ∀ {kind : BinderKind} (index : BVar source kind),
      first.var index = second.var index) : first = second :=
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
    (firstRename : Rename first second)
    (secondRename : Rename second third)
    (thirdRename : Rename third fourth) :
    (firstRename.comp secondRename).comp thirdRename =
      firstRename.comp (secondRename.comp thirdRename) := by
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
    (firstRename : Rename first second)
    (secondRename : Rename second third) :
    (firstRename.comp secondRename).lift (kind := kind) =
      firstRename.lift.comp secondRename.lift := by
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
      simp only [liftMany_cons, induction, lift_id]
      rfl

@[simp]
theorem liftMany_comp {first second third : Sig}
    (firstRename : Rename first second)
    (secondRename : Rename second third) (kinds : Sig) :
    (firstRename.comp secondRename).liftMany kinds =
      (firstRename.liftMany kinds).comp
        (secondRename.liftMany kinds) := by
  induction kinds with
  | nil => rfl
  | cons kind rest induction =>
      simp only [liftMany_cons, induction, lift_comp]
      rfl

end Rename

end DOTCapture.BinderOnly
