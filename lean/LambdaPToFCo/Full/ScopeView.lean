import LambdaPToFCo.Full.PlanScope

/-!
# Arbitrary-context views of opened value scopes

A `ScopeView` lets several plan views inhabit one already-established target
context. Different views may use different observation plans while retaining
the same stable identity and payload at each source-variable slot.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

/-- One opened target interface for every source variable, all in the same
current target context. -/
def ScopeView (arity : Nat) {sig : Sig} (context : Ctx sig) : Type :=
  Fin arity -> ValueInterface context

namespace ScopeView

/-- Canonical arbitrary-context view of an intrinsically grown plan scope. -/
noncomputable def ofPlanScope
    {arity : Nat} {sig : Sig} {context : Ctx sig}
    (scope : PlanScope arity context) : ScopeView arity context :=
  scope.lookup

@[simp] theorem ofPlanScope_apply
    {arity : Nat} {sig : Sig} {context : Ctx sig}
    (scope : PlanScope arity context) (index : Fin arity) :
    ofPlanScope scope index = scope.lookup index := by
  rfl

/-- Rename every opened interface into another current context. -/
noncomputable def rename
    {arity : Nat} {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    (view : ScopeView arity sourceContext)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    ScopeView arity targetContext :=
  fun index => (view index).rename mapping typed

@[simp] theorem rename_apply
    {arity : Nat} {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    (view : ScopeView arity sourceContext)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping)
    (index : Fin arity) :
    view.rename mapping typed index = (view index).rename mapping typed := by
  rfl

/-- Add an already-adapted newest interface without extending the target
signature or context. Index zero denotes the new slot. -/
def snocExisting
    {arity : Nat} {sig : Sig} {context : Ctx sig}
    (older : ScopeView arity context) (newest : ValueInterface context) :
    ScopeView (arity + 1) context :=
  fun index => Fin.cases newest older index

@[simp] theorem snocExisting_here
    {arity : Nat} {sig : Sig} {context : Ctx sig}
    (older : ScopeView arity context) (newest : ValueInterface context) :
    older.snocExisting newest 0 = newest := by
  rfl

@[simp] theorem snocExisting_there
    {arity : Nat} {sig : Sig} {context : Ctx sig}
    (older : ScopeView arity context) (newest : ValueInterface context)
    (index : Fin arity) :
    older.snocExisting newest index.succ = older index := by
  rfl

theorem snocExisting_rename
    {arity : Nat} {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    (older : ScopeView arity sourceContext)
    (newest : ValueInterface sourceContext)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    (older.snocExisting newest).rename mapping typed =
      (older.rename mapping typed).snocExisting
        (newest.rename mapping typed) := by
  funext index
  refine Fin.cases ?_ (fun olderIndex => ?_) index
  · rfl
  · rfl

/-- Converting a plan-scope snoc first renames every older slot into the
larger current context, then inserts the canonical freshly opened slot. -/
theorem ofPlanScope_snoc
    {arity : Nat} {sig : Sig} {context : Ctx sig}
    (older : PlanScope arity context) (plan : ValuePlan sig) :
    ofPlanScope (PlanScope.snoc older plan) =
      ((ofPlanScope older).rename plan.telescope.weaken
        (plan.telescope.weaken_typed context)).snocExisting
          (ValueInterface.ofArguments (plan.rename plan.telescope.weaken)
            (Telescope.Args.identity plan.telescope context)) := by
  funext index
  refine Fin.cases ?_ (fun olderIndex => ?_) index
  · rfl
  · rfl

end ScopeView

/-- Exact stable-identity agreement for one variable slot. Observation plans
are intentionally unconstrained. -/
structure SlotAlignment {sig : Sig} {context : Ctx sig}
    (left right : ValueInterface context) : Type where
  identity_eq : left.identity = right.identity
  payload_eq : left.payload = right.payload

namespace SlotAlignment

def identity (interface : ValueInterface context) :
    SlotAlignment interface interface where
  identity_eq := rfl
  payload_eq := rfl

def symm (alignment : SlotAlignment left right) :
    SlotAlignment right left where
  identity_eq := alignment.identity_eq.symm
  payload_eq := alignment.payload_eq.symm

def compose (first : SlotAlignment left middle)
    (second : SlotAlignment middle right) : SlotAlignment left right where
  identity_eq := first.identity_eq.trans second.identity_eq
  payload_eq := first.payload_eq.trans second.payload_eq

noncomputable def rename
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target}
    {left right : ValueInterface sourceContext}
    (alignment : SlotAlignment left right)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    SlotAlignment (left.rename mapping typed) (right.rename mapping typed) := by
  constructor
  · rw [ValueInterface.rename_identity,
      ValueInterface.rename_identity]
    exact congrArg (fun identity => identity.rename mapping)
      alignment.identity_eq
  · rw [ValueInterface.rename_payload,
      ValueInterface.rename_payload]
    exact congrArg (fun payload => payload.rename mapping)
      alignment.payload_eq

end SlotAlignment

/-- Per-slot stable identity and payload agreement between two arbitrary
views. Plans and observations may differ at every slot. -/
structure ScopeAlignment {arity : Nat} {sig : Sig} {context : Ctx sig}
    (left right : ScopeView arity context) : Type where
  slot : (index : Fin arity) -> SlotAlignment (left index) (right index)

namespace ScopeAlignment

def identity (view : ScopeView arity context) : ScopeAlignment view view where
  slot index := SlotAlignment.identity (view index)

def symm (alignment : ScopeAlignment left right) :
    ScopeAlignment right left where
  slot index := (alignment.slot index).symm

def compose (first : ScopeAlignment left middle)
    (second : ScopeAlignment middle right) : ScopeAlignment left right where
  slot index := (first.slot index).compose (second.slot index)

/-- Stable identity equality at a selected source-variable slot. -/
theorem identity_eq
    {arity : Nat} {sig : Sig} {context : Ctx sig}
    {left right : ScopeView arity context}
    (alignment : ScopeAlignment left right)
    (index : Fin arity) :
    (left index).identity = (right index).identity :=
  (alignment.slot index).identity_eq

/-- Stable payload equality at a selected source-variable slot. -/
theorem payload_eq
    {arity : Nat} {sig : Sig} {context : Ctx sig}
    {left right : ScopeView arity context}
    (alignment : ScopeAlignment left right)
    (index : Fin arity) :
    (left index).payload = (right index).payload :=
  (alignment.slot index).payload_eq

noncomputable def rename
    {arity : Nat} {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {left right : ScopeView arity sourceContext}
    (alignment : ScopeAlignment left right)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    ScopeAlignment (left.rename mapping typed)
      (right.rename mapping typed) where
  slot index := (alignment.slot index).rename mapping typed

def snoc
    {arity : Nat} {sig : Sig} {context : Ctx sig}
    {left right : ScopeView arity context}
    {leftNewest rightNewest : ValueInterface context}
    (older : ScopeAlignment left right)
    (newest : SlotAlignment leftNewest rightNewest) :
    ScopeAlignment (left.snocExisting leftNewest)
      (right.snocExisting rightNewest) where
  slot index := Fin.cases newest (fun olderIndex => older.slot olderIndex) index

@[simp] theorem snoc_here
    {arity : Nat} {sig : Sig} {context : Ctx sig}
    {left right : ScopeView arity context}
    {leftNewest rightNewest : ValueInterface context}
    (older : ScopeAlignment left right)
    (newest : SlotAlignment leftNewest rightNewest) :
    (older.snoc newest).slot 0 = newest := by
  rfl

@[simp] theorem snoc_there
    {arity : Nat} {sig : Sig} {context : Ctx sig}
    {left right : ScopeView arity context}
    {leftNewest rightNewest : ValueInterface context}
    (older : ScopeAlignment left right)
    (newest : SlotAlignment leftNewest rightNewest)
    (index : Fin arity) :
    (older.snoc newest).slot index.succ = older.slot index := by
  rfl

end ScopeAlignment

end LambdaPToFCo.Full
