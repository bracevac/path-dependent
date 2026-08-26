import LambdaPToFCo.Full.PathTermWellFormed
import LambdaPToFCo.Full.WfPlan

/-!
# Certified plans for full application operands

Although a general full term can advertise a non-well-formed dependent
application result, both operands of `Tm.Ty.app` are path terms.  Their result
types are therefore well formed.  This module turns that precise source fact
into the structural plans needed by application compilation, conditional
only on the same exact path resolver used by `WfPlan`.
-/

namespace LambdaPToFCo.Full.ApplicationPlanning

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

/-- Build the complete bidirectional plan for any typed path operand. -/
noncomputable def pathPlan
    (resolver : WfPlan.Resolver)
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {path : LambdaPFC.Path n} {result : LambdaPFC.Ty n}
    (typing : LambdaPFC.Tm.Ty sourceContext (.path path) result) :
    WfPlan.Proper sourceContext targetContext scope result :=
  WfPlan.properWithResolver resolver scope (PathTermTyping.resultWf typing)

/-- A function-use demand is fixed by the actual application premise and one
demand-local certified plan for its function type.  Callers that have already
translated the needed path can therefore avoid manufacturing a global path
resolver. -/
def functionDemandFromPlan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {path : LambdaPFC.Path n}
    {domain : LambdaPFC.Ty n} {codomain : LambdaPFC.Ty (n + 1)}
    (typing : LambdaPFC.Tm.Ty sourceContext (.path path)
      (.Fun domain codomain))
    (planned : WfPlan.Proper sourceContext targetContext scope
      (.Fun domain codomain)) :
    ProperDemand sourceContext targetContext scope (.Fun domain codomain) :=
  { trace := .root (.structural (.functionUse typing))
    model := ⟨planned.plan, planned.model.demand⟩ }

/-- Convenience wrapper that obtains the function plan from the total
resolver API. -/
noncomputable def functionDemand
    (resolver : WfPlan.Resolver)
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {path : LambdaPFC.Path n}
    {domain : LambdaPFC.Ty n} {codomain : LambdaPFC.Ty (n + 1)}
    (typing : LambdaPFC.Tm.Ty sourceContext (.path path)
      (.Fun domain codomain)) :
    ProperDemand sourceContext targetContext scope (.Fun domain codomain) :=
  functionDemandFromPlan scope typing (pathPlan resolver scope typing)

end LambdaPToFCo.Full.ApplicationPlanning
