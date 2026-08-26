import LambdaPToFCo.OperationalDirectFunctionCompatibility

/-!
# Wrapper-aware lexical function compatibility

`DirectNativeCompatibility` deliberately applies only when the current
lexical slot and the physical allocation slot expose literally the same
target expression.  That condition is false for an arrow-typed alias whose
behavior retains a structural arrow cast.

This module states the target-facing boundary at the correct endpoint.  A
`LexicalFunctionCompatibility` carries a `NativeFunctionImage` indexed by the
*adapted lexical slot behavior*.  Its `FunctionValue` may therefore contain
the arrow-cast tower introduced before an existing location was rebound.
Only equality of the advertised base-domain plan remains external.

The structure is intentionally independent of source-body provenance.  A
recursive store invariant can pair it with the physical binding's retained
source closure when constructing the CK beta successor.
-/

namespace LambdaPToFCo
namespace OperationalLexicalFunctionCompatibility

open SystemFCo
open StaticTranslation
open OperationalEnvironment
open OperationalBindingView
open OperationalApplication
open OperationalApplicationTranslation
open OperationalApplicationSpine
open OperationalStoreEnvironment
open OperationalPathCoherence
open OperationalTypedPathView
open OperationalFunctionPathSpine

/-- A wrapper-aware function image at the behavior exposed by the current
lexical slot.  Unlike `DirectNativeCompatibility`, this does not identify the
adapted slot with the physical allocation slot. -/
structure LexicalFunctionCompatibility
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope environment)
    {functionPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken)}
    (spine : FunctionPathSpine typing) : Type where
  image : NativeFunctionImage
    (store.lookup (typedPathReferent typing)).slot.behavior.argument
  domainPlan_eq :
    closedPlan scope environment spine.baseDomainWf = image.domainPlan

namespace NativeFunctionImage

@[simp] theorem castBehavior_domainPlan
    {first second : Exp []} (equal : first = second)
    (image : NativeFunctionImage first) :
    (equal ▸ image).domainPlan = image.domainPlan := by
  cases equal
  rfl

end NativeFunctionImage

namespace LexicalFunctionCompatibility

/-- Every direct lexical/native compatibility witness induces the
wrapper-aware form.  The transport is harmless here precisely because the
direct witness proves that the two endpoints are equal. -/
noncomputable def ofDirect
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    {store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope environment}
    {functionPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken)}
    {spine : FunctionPathSpine typing}
    {native : NativeFunctionImage
      (store.lookup
        (typedPathReferent typing)).compiled.slot.behavior.argument}
    (direct : DirectNativeCompatibility store spine native) :
    LexicalFunctionCompatibility store spine :=
  let image : NativeFunctionImage
      (store.lookup (typedPathReferent typing)).slot.behavior.argument :=
    direct.lexicalBehavior_eq.symm ▸ native
  { image := image
    domainPlan_eq := direct.domainPlan_eq.trans
      (NativeFunctionImage.castBehavior_domainPlan
        direct.lexicalBehavior_eq.symm native).symm }

/-- The wrapper-aware canonical function is exactly the base lexical path
endpoint. -/
theorem base_eq
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    {store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope environment}
    {functionPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken)}
    {spine : FunctionPathSpine typing}
    (compatibility : LexicalFunctionCompatibility store spine)
    (coherent : StorePathCoherence store) :
    compatibility.image.value.expression =
      spine.baseExpression scope environment := by
  calc
    compatibility.image.value.expression =
        (store.lookup
          (typedPathReferent typing)).slot.behavior.argument :=
      compatibility.image.behavior_eq
    _ = spine.baseExpression scope environment :=
      (spine.baseExpression_eq_slot store coherent).symm

/-- Normalize all function coercions retained by the current operator path
around its lexical base image.  The resulting image is indexed by the final
typed-path endpoint, so it can be installed as the behavior of an
arrow-typed alias without equating that wrapper with the physical slot. -/
noncomputable def endpointImage
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    {store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope environment}
    {functionPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken)}
    {spine : FunctionPathSpine typing}
    (compatibility : LexicalFunctionCompatibility store spine)
    (coherent : StorePathCoherence store)
    (pathImage : ClosedPathView scope typing environment) :
    NativeFunctionImage pathImage.view.argument where
  plan := compatibility.image.plan
  result := compatibility.image.result
  body := compatibility.image.body
  value :=
    (spine.closedView scope environment compatibility.image.value).normalize.value
  domainPlan := closedPlan scope environment spine.domainWf
  argumentEvidence := fun outer outerPlan_eq =>
    spine.argumentEvidence scope environment compatibility.image.value
      (fun inner innerPlan_eq =>
        compatibility.image.argumentEvidence inner
          (innerPlan_eq.trans compatibility.domainPlan_eq))
      outer outerPlan_eq
  behavior_eq :=
    spine.canonical_eq_pathArgument scope environment
      compatibility.image.value (compatibility.base_eq coherent) pathImage

/-- Reindex the lexical image's argument interface to the precise domain of
the base source path. -/
noncomputable def baseEvidence
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    {store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope environment}
    {functionPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken)}
    {spine : FunctionPathSpine typing}
    (compatibility : LexicalFunctionCompatibility store spine) :
    {outerPlan : Interface.BinderPlan []} ->
    (outer : EliminationView outerPlan) ->
    outerPlan = closedPlan scope environment spine.baseDomainWf ->
    ArgumentEvidence compatibility.image.value outer :=
  fun outer outerPlan_eq =>
    compatibility.image.argumentEvidence outer
      (outerPlan_eq.trans compatibility.domainPlan_eq)

/-- Apply the ready adapted lexical function endpoint to a closed typed
argument.  Structural arrow casts in the lexical image remain explicit and
contribute their argument and result contexts. -/
noncomputable def endpointApplication
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    {store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope environment}
    {functionPath argumentPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    {functionTyping : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken)}
    {spine : FunctionPathSpine functionTyping}
    {argumentTyping : Fragment.HasType sourceContext (.path argumentPath)
      domain}
    (compatibility : LexicalFunctionCompatibility store spine)
    (coherent : StorePathCoherence store)
    (functionImage : ClosedPathView scope functionTyping environment)
    (argumentImage : ClosedPathView scope argumentTyping environment) :
    ApplicationView compatibility.image.body functionImage.view.argument
      argumentImage.view.argument :=
  spine.endpointApplication scope environment compatibility.image.value
    (compatibility.base_eq coherent) compatibility.baseEvidence functionImage
    argumentImage

/-- Complete target reduction for a closed source application at an adapted
lexical function endpoint. -/
theorem closedApplication_steps
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    {store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope environment}
    {functionPath argumentPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    {functionTyping : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken)}
    {spine : FunctionPathSpine functionTyping}
    {argumentTyping : Fragment.HasType sourceContext (.path argumentPath)
      domain}
    (resultWf : Fragment.Wf sourceContext codomain)
    (compatibility : LexicalFunctionCompatibility store spine)
    (coherent : StorePathCoherence store)
    (functionImage : ClosedPathView scope functionTyping environment)
    (argumentImage : ClosedPathView scope argumentTyping environment) :
    let application := compatibility.endpointApplication coherent
      functionImage argumentImage
    Exp.Steps
      (environment.closeExp
        (TermTranslation.elaborate scope
          (.app functionTyping argumentTyping resultWf)))
      (application.context.plug
        (compatibility.image.body.subst
          application.elimination.substitution)) := by
  simpa only [endpointApplication] using
    spine.closedApplication_steps resultWf scope environment
      compatibility.image.value (compatibility.base_eq coherent)
      compatibility.baseEvidence functionImage argumentImage

end LexicalFunctionCompatibility

end OperationalLexicalFunctionCompatibility
end LambdaPToFCo
