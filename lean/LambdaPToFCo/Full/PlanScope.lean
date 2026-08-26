import LambdaPToFCo.Full.ValueInterface
import SystemFCoExt.TelescopeInstances

/-!
# Target scopes of opened full-value plans

This low layer records only the target interface chosen for each source term
variable.  It deliberately carries no source well-formedness premise: the
full source calculus admits useful typing and subtyping derivations whose
intermediate types are not independently well formed.  Derivation-directed
producer and demand evidence refines these slots in later modules.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

/-- A target context obtained by opening one stable-identity value interface
for every source term variable. -/
inductive PlanScope : (arity : Nat) -> {sig : Sig} -> Ctx sig -> Type where
| nil : PlanScope 0 Ctx.empty
| snoc {sig : Sig} {context : Ctx sig}
    (older : PlanScope arity context) (plan : ValuePlan sig) :
    PlanScope (arity + 1) (plan.context context)

namespace PlanScope

/-- Every source variable denotes the already-opened interface fields in the
current target context. -/
noncomputable def lookup {arity : Nat} {sig : Sig} {context : Ctx sig}
    (scope : PlanScope arity context) (index : Fin arity) :
    ValueInterface context :=
  match scope with
  | .snoc older plan =>
      Fin.cases
        (ValueInterface.ofArguments (plan.rename plan.telescope.weaken)
          (Telescope.Args.identity plan.telescope _))
        (fun olderIndex =>
          (older.lookup olderIndex).rename plan.telescope.weaken
            (plan.telescope.weaken_typed _))
        index

@[simp] theorem lookup_here {arity : Nat} {sig : Sig}
    {context : Ctx sig} (older : PlanScope arity context)
    (plan : ValuePlan sig) :
    (PlanScope.snoc older plan).lookup 0 =
      ValueInterface.ofArguments (plan.rename plan.telescope.weaken)
        (Telescope.Args.identity plan.telescope context) := by
  rfl

@[simp] theorem lookup_there {arity : Nat} {sig : Sig}
    {context : Ctx sig} (older : PlanScope arity context)
    (plan : ValuePlan sig) (index : Fin arity) :
    (PlanScope.snoc older plan).lookup index.succ =
      (older.lookup index).rename plan.telescope.weaken
        (plan.telescope.weaken_typed context) := by
  rfl

end PlanScope

end LambdaPToFCo.Full
