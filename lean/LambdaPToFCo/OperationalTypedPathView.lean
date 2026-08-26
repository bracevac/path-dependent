import LambdaPToFCo.OperationalPathCoherence
import LambdaPToFCo.OperationalAdmissibility
import LambdaPToFCo.OperationalResultContext

/-!
# Closed views of admissible typed paths

A source CK path step replaces a typed path by its resolved store location.
The target does not take a corresponding lookup step: closing the translated
path already exposes the target argument stored for its static referent.

This module packages that fact as a target value normalization.  Recursive
path-only subsumption is interpreted by the compiled closed coercion and the
total ordinary `AdaptedArgument` constructor.  The endpoint is also exposed
as an `EliminationView` at the binder plan selected by the outer typing
derivation, together with the plan equality needed by application.
-/

namespace LambdaPToFCo
namespace OperationalTypedPathView

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalBindingView
open OperationalEnvironment
open OperationalApplication
open OperationalApplicationTranslation
open OperationalStoreEnvironment
open OperationalApplicationSpine
open OperationalAdmissibility
open OperationalFunctionPathSpine
open OperationalPathCoherence
open OperationalResultContext

/-! ## Path-only admissibility inversion -/

/-- Every admitted typing of a source path ends in an ordinary binder shape.
Generic subsumption records a noncanonical result, while the dedicated
function-path constructor records the only admitted arrow case. -/
def OperationallyAdmissible.pathResultShape
    {typing : Fragment.HasType sourceContext (.path path) sourceType} :
    OperationallyAdmissible typing -> OrdinaryShape sourceType
  | .path _ => .singleton
  | .functionPath _ => .arrow
  | .neutralSub .path _ _ targetShape => targetShape.ordinary

/-! ## Closed target image -/

/-- A closed typed path reaches a target value and exposes that same value as
the argument of the outer source type's compiled binder interface. -/
structure ClosedPathView
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (typing : Fragment.HasType sourceContext (.path path) sourceType)
    (environment : ClosingEnv sig []) : Type where
  normalization : ValueNormalization
    (environment.closeExp (TermTranslation.elaborate scope typing))
  view : EliminationView
    ((TermTranslation.compileBinder scope typing.typeWf).plan.subst
      environment.substitution)
  argument_eq : view.argument = normalization.result

namespace ClosedPathView

/-- The view argument is ready because it is the normalization endpoint. -/
theorem view_ready
    (image : ClosedPathView scope typing environment) :
    Exp.IsValue image.view.argument := by
  rw [image.argument_eq]
  exact image.normalization.ready

/-- The view's indexed plan agrees with the closed binder plan selected by
any other well-formedness proof for the same ordinary source type.  This is
the equality consumed by `ApplicationSpine.argumentEvidence`. -/
theorem applicationPlan_eq
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {typing : Fragment.HasType sourceContext (.path path) sourceType}
    {environment : ClosingEnv sig []}
    (expectedWf : Fragment.Wf sourceContext sourceType)
    (shape : OrdinaryShape sourceType) :
    (TermTranslation.compileBinder scope typing.typeWf).plan.subst
        environment.substitution =
      closedPlan scope environment expectedWf :=
  by
    exact closedPlan_irrel_of_ordinary scope environment typing.typeWf
      expectedWf shape

/-- Turn any value normalization at an ordinary result type into the direct
behavioral binder interface for that result. -/
noncomputable def ofNormalization
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {typing : Fragment.HasType sourceContext (.path path) sourceType}
    {environment : ClosingEnv sig []}
    (shape : OrdinaryShape sourceType)
    (normalization : ValueNormalization
      (environment.closeExp (TermTranslation.elaborate scope typing))) :
    ClosedPathView scope typing environment := by
  let closedType := environment.closeTy
    (translateType scope typing.typeWf)
  let actual : Instantiation (.ordinary closedType) :=
    .ordinary normalization.result
  let direct := BindingView.ofInstantiation actual normalization.ready
  have planEq :
      (Interface.BinderPlan.ordinary closedType) =
        (TermTranslation.compileBinder scope typing.typeWf).plan.subst
          environment.substitution := by
    rw [OperationalValueEvidence.compileBinder_plan_ordinary scope
      typing.typeWf shape]
    rfl
  let view := EliminationView.castPlan planEq
    (EliminationView.ofDirect direct)
  exact
    { normalization := normalization
      view := view
      argument_eq := by
        exact EliminationView.castPlan_argument planEq
          (EliminationView.ofDirect direct) }

end ClosedPathView

/-! ## Base lookup and recursive cast adaptation -/

/-- The untranslated target lookup for a base fragment path is already the
ready argument advertised by its static referent slot. -/
noncomputable def baseNormalization
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {pathType : LambdaPFC.Ty n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope environment)
    (coherent : StorePathCoherence store)
    (pathTyping : Fragment.PathTy sourceContext path pathType) :
    ValueNormalization
      (environment.closeExp
        (TermTranslation.elaborate scope
          (Fragment.HasType.path pathTyping))) := by
  let located := store.lookup (pathReferentIndex pathTyping)
  refine
    { result := located.slot.behavior.argument
      ready := located.slot.behavior.ready
      reductions := ?_ }
  rw [TermTranslation.elaborate, coherent pathTyping]
  exact .refl

/-- Add one closed source-subtyping cast around an already compiled path
view.  This target-only helper is shared by generic noncanonical path
subsumption and the restricted arrow spine. -/
noncomputable def ClosedPathView.adapt
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {source target : LambdaPFC.Ty n}
    {innerTyping : Fragment.HasType sourceContext (.path path) source}
    (subtype : Fragment.Sub sourceContext source target)
    (targetShape : OrdinaryShape target)
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    (innerImage : ClosedPathView scope innerTyping environment) :
    ClosedPathView scope (.sub innerTyping subtype) environment := by
  let coercion := environment.closeCo
    (CoercionTranslation.elaborateSub scope subtype)
  let closedTarget := environment.closeTy
    (translateType scope subtype.targetWf)
  let adapted := AdaptedArgument.ordinary innerImage.view coercion
    closedTarget
  let normalization : ValueNormalization
      (environment.closeExp
        (TermTranslation.elaborate scope (.sub innerTyping subtype))) :=
    { result := adapted.view.argument
      ready := adapted.view.ready
      reductions := by
        change Exp.Steps
          (.cast
            (environment.closeExp
              (TermTranslation.elaborate scope innerTyping)) coercion)
          adapted.view.argument
        exact
          (OperationalApplication.Steps.castExpression
            innerImage.normalization.reductions).trans
            (by
              simpa only [innerImage.argument_eq] using adapted.reductions) }
  exact ClosedPathView.ofNormalization targetShape normalization

/-- Compile the exact-core function-path spine.  Its base is the direct
singleton widening to the referent's precise arrow, and every outer layer is
one of the retained function-compatible coercions. -/
noncomputable def buildFunctionPath
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {domain codomain : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path path)
      (.Fun domain codomain.weaken)}
    (spine : FunctionPathSpine typing)
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope environment)
    (coherent : StorePathCoherence store) :
    ClosedPathView scope typing environment :=
  match spine with
  | .widen pathTyping domainWf codomainWf _ =>
      ClosedPathView.adapt
        (.widen pathTyping (.arrow domainWf codomainWf)) .arrow
        (ClosedPathView.ofNormalization .singleton
          (baseNormalization store coherent pathTyping))
  | @FunctionPathSpine.sub _ _ _ _ _ _ _ _ subtype _ inner _ =>
      ClosedPathView.adapt subtype .arrow
        (buildFunctionPath inner store coherent)

/-- Compile the complete path-only admissibility spine to a closed value view.
Every source subtype constructor is supported here: after closing, its target
coercion has signature `[]`, and `AdaptedArgument.ordinary` normalizes every
such cast to a ready ordinary view. -/
noncomputable def build
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path path) sourceType}
    (admissible : OperationallyAdmissible typing)
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope environment)
    (coherent : StorePathCoherence store) :
    ClosedPathView scope typing environment :=
  match admissible with
  | .path pathTyping =>
      ClosedPathView.ofNormalization .singleton
        (baseNormalization store coherent pathTyping)
  | .functionPath spine => buildFunctionPath spine store coherent
  | @OperationallyAdmissible.neutralSub _ _ _ _ _ innerTyping .path inner
      subtype targetShape => by
      let innerImage := build inner store coherent
      exact ClosedPathView.adapt subtype targetShape.ordinary innerImage

end OperationalTypedPathView
end LambdaPToFCo
