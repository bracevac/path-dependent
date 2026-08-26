import LambdaPToFCo.Full.TranslationInterfaces

/-!
# Exact binding facts for certified scopes

`ScopeModel.bind` stores its newest and older slot proofs through equality
transports introduced by the dependent `Fin.cases` motive.  They are
heterogeneously equal to the corresponding structural `.bound` and
`.underBinding` constructors.  Exposing those facts lets later
model-instantiation certificates recover the construction history without
assuming that telescope contexts or plans are injective.
-/

namespace LambdaPToFCo.Full

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

private theorem mpr_heq
    {alpha beta : Sort u} (equal : beta = alpha) (value : alpha) :
    HEq (Eq.mpr equal value) value := by
  cases equal
  rfl

namespace ScopeModel

/-- The newest slot installed by `bind` is exactly the structural bound
model, modulo the dependent motive's proof-only transport. -/
theorem bind_slot_zero_heq
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan) :
    HEq ((scope.bind model).slot 0) (ProducerPlanModel.bound model) := by
  unfold ScopeModel.bind
  simp only [LambdaPFC.Ctx.lookup, Fin.cases_zero, ScopeView.bindPlan]
  apply mpr_heq

/-- Every older slot installed by `bind` is exactly its previous model under
the structural binder, modulo the dependent motive's proof-only transport. -/
theorem bind_slot_succ_heq
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan) (index : Fin n) :
    HEq ((scope.bind model).slot index.succ)
      (ProducerPlanModel.underBinding model (scope.slot index)) := by
  unfold ScopeModel.bind
  simp only [LambdaPFC.Ctx.lookup, Fin.cases_succ, ScopeView.bindPlan]
  apply mpr_heq

end ScopeModel

end LambdaPToFCo.Full
