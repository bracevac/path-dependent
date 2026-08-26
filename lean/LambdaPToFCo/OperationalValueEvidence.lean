import LambdaPToFCo.OperationalApplicationTranslation
import LambdaPToFCo.OperationalPackageBehavior

/-!
# Source value spines and their closed target behavior

This module sits below the store environment in the operational dependency
graph.  It records exactly the two source value shapes admitted by the first
simulation core:

* abstractions surrounded only by reflexive/transitive/arrow coercion shapes;
* literal exact type packages surrounded only by canonical reflexivity.

Keeping this proof-relevant evidence with a physical heap cell lets function
lookup recover `ClosedFunctionEvidence` without reconstructing a typing spine
from `FunctionCell`.  The module contains no source store interpretation and
does not import `OperationalStoreEnvironment`.
-/

namespace LambdaPToFCo
namespace OperationalValueEvidence

open SystemFCo
open StaticTranslation
open OperationalBindingView
open OperationalEnvironment
open OperationalApplication
open OperationalApplicationTranslation

/-! ## Abstraction provenance -/

/-- Source-only provenance of a typed abstraction. -/
inductive FunctionSpine
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {domain : LambdaPFC.Ty n} {sourceBody : LambdaPFC.Tm (n + 1)} :
    {sourceType : LambdaPFC.Ty n} ->
    (typing : Fragment.HasType sourceContext (.abs domain sourceBody)
      sourceType) -> Type where
  | abs
      {codomain : LambdaPFC.Ty n}
      (bodyTyping : Fragment.HasType (sourceContext.snoc domain) sourceBody
        codomain.weaken)
      (domainWf : Fragment.Wf sourceContext domain)
      (codomainWf : Fragment.Wf sourceContext codomain) :
      FunctionSpine (.abs bodyTyping domainWf codomainWf)
  | sub
      {source target : LambdaPFC.Ty n}
      {innerTyping : Fragment.HasType sourceContext
        (.abs domain sourceBody) source}
      {subtype : Fragment.Sub sourceContext source target}
      (inner : FunctionSpine innerTyping)
      (shape : FragmentFunctionCo subtype) :
      FunctionSpine (.sub innerTyping subtype)

namespace FunctionSpine

def bodyTyping
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {domain : LambdaPFC.Ty n} {sourceBody : LambdaPFC.Tm (n + 1)}
    {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.abs domain sourceBody)
      sourceType} :
    FunctionSpine typing ->
      Sigma fun codomain : LambdaPFC.Ty n =>
        Fragment.HasType (sourceContext.snoc domain) sourceBody
          codomain.weaken
  | .abs body _ _ => ⟨_, body⟩
  | .sub inner _ => inner.bodyTyping

noncomputable def close
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {domain : LambdaPFC.Ty n} {sourceBody : LambdaPFC.Tm (n + 1)}
    {sourceType : LambdaPFC.Ty n}
    {sig : Sig} {targetContext : Ctx sig}
    {typing : Fragment.HasType sourceContext (.abs domain sourceBody)
      sourceType}
    (spine : FunctionSpine typing)
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig []) :
    ClosedFunctionEvidence scope environment typing :=
  match spine with
  | .abs body domainWf codomainWf => .abs body domainWf codomainWf
  | .sub inner shape =>
      .sub (inner.close scope environment) (ClosedFunctionCo.ofFragment shape)

end FunctionSpine

def functionCoTargetShape :
    {source target : LambdaPFC.Ty n} ->
    {subtype : Fragment.Sub sourceContext source target} ->
    FragmentFunctionCo subtype -> OrdinaryShape source -> OrdinaryShape target
  | _, _, _, .refl _ => fun sourceShape => sourceShape
  | _, _, _, .trans first second => fun sourceShape =>
      functionCoTargetShape second
        (functionCoTargetShape first sourceShape)
  | _, _, _, .arrow _ _ => fun _ => .arrow

namespace FunctionSpine

def targetShape
    {typing : Fragment.HasType sourceContext
      (.abs domain sourceBody) sourceType} :
    FunctionSpine typing -> OrdinaryShape sourceType
  | .abs _ _ _ => .arrow
  | .sub inner shape => functionCoTargetShape shape inner.targetShape

end FunctionSpine

/-! ## Exact-package provenance -/

inductive ExactPackageSpine
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness : LambdaPFC.Ty n} :
    {sourceType : LambdaPFC.Ty n} ->
    (typing : Fragment.HasType sourceContext
      (.pair first label (.type witness)) sourceType) -> Type where
  | package (witnessWf : Fragment.Wf sourceContext witness) :
      ExactPackageSpine
        (Fragment.HasType.typePackage (first := first) (label := label)
          witnessWf)
  | refl
      {sourceType : LambdaPFC.Ty n}
      {innerTyping : Fragment.HasType sourceContext
        (.pair first label (.type witness)) sourceType}
      (inner : ExactPackageSpine innerTyping) :
      ExactPackageSpine (.sub innerTyping (.refl innerTyping.typeWf))

namespace ExactPackageSpine

theorem sourceType_eq
    {typing : Fragment.HasType sourceContext
      (.pair first label (.type witness)) sourceType}
    (spine : ExactPackageSpine typing) :
    sourceType = Fragment.exactPackageTy first label witness := by
  induction spine with
  | package => rfl
  | refl _ ih => exact ih

noncomputable def closedView
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness sourceType : LambdaPFC.Ty n}
    {sig : Sig} {targetContext : Ctx sig}
    {typing : Fragment.HasType sourceContext
      (.pair first label (.type witness)) sourceType}
    (spine : ExactPackageSpine typing)
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (payloadReady : Exp.IsValue
      (environment.closeExp
        (translatePath scope
          (Fragment.PathTy.var
            (Γ := sourceContext) (x := first))).expression)) :
    OperationalPackageBehavior.ClosedView scope typing environment :=
  match spine with
  | .package witnessWf =>
      OperationalPackageBehavior.exact scope first label witnessWf
        environment payloadReady
  | .refl inner => by
      let innerView := inner.closedView scope environment payloadReady
      refine { view := innerView.view, normalizes := ?_ }
      change Exp.Steps
        (((TermTranslation.elaborate scope _).cast
          (CoercionTranslation.elaborateSub scope (.refl _))).subst
            environment.substitution)
        innerView.view.argument
      simp only [Exp.subst, CoercionTranslation.elaborateSub, Co.subst]
      exact
        (OperationalApplication.Steps.castExpression
          innerView.normalizes).trans
            (.single (.castRefl innerView.view.ready))

end ExactPackageSpine

/-! ## Unified physical-value evidence -/

inductive ValueEvidence :
    {n : Nat} -> {sourceContext : LambdaPFC.Ctx n} ->
    {term : LambdaPFC.Tm n} -> {sourceType : LambdaPFC.Ty n} ->
    (typing : Fragment.HasType sourceContext term sourceType) -> Type where
  | function
      {typing : Fragment.HasType sourceContext
        (.abs domain body) sourceType}
      (spine : FunctionSpine typing) : ValueEvidence typing
  | package
      {typing : Fragment.HasType sourceContext
        (.pair first label (.type witness)) sourceType}
      (spine : ExactPackageSpine typing) : ValueEvidence typing

namespace ValueEvidence

/-- Renaming cannot turn a source computation constructor into a value
constructor. -/
theorem isValue_of_rename
    (term : LambdaPFC.Tm n) (rename : LambdaPFC.FinFun n m)
    (ready : (term.rename rename).IsValue) : term.IsValue := by
  cases term with
  | path => cases ready
  | abs => exact .abs
  | pair => exact .pair
  | app => cases ready
  | «let» => cases ready

def isValue
    {typing : Fragment.HasType sourceContext term sourceType}
    (evidence : ValueEvidence typing) : LambdaPFC.Tm.IsValue term :=
  match evidence with
  | .function _ => .abs
  | .package _ => .pair

def ClosedReady
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext term sourceType}
    (evidence : ValueEvidence typing)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig []) : Prop :=
  match evidence with
  | .function _ => True
  | @ValueEvidence.package _ _ first _ _ _ _ _ =>
      Exp.IsValue
        (environment.closeExp
          (translatePath scope
            (Fragment.PathTy.var
              (Γ := sourceContext) (x := first))).expression)

end ValueEvidence

theorem compileBinder_plan_ordinary
    (scope : Scope sourceContext targetContext)
    (wf : Fragment.Wf sourceContext sourceType)
    (shape : OrdinaryShape sourceType) :
    (TermTranslation.compileBinder scope wf).plan =
      .ordinary (translateType scope wf) := by
  cases shape <;> cases wf <;> rfl

noncomputable def FunctionSpine.closedView
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {domain : LambdaPFC.Ty n} {sourceBody : LambdaPFC.Tm (n + 1)}
    {sourceType : LambdaPFC.Ty n}
    {sig : Sig} {targetContext : Ctx sig}
    {typing : Fragment.HasType sourceContext (.abs domain sourceBody)
      sourceType}
    (spine : FunctionSpine typing)
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig []) :
    OperationalPackageBehavior.ClosedView scope typing environment := by
  let functionEvidence := spine.close scope environment
  let image := functionEvidence.image
  let normalization := image.view.normalize
  let closedType :=
    (translateType scope typing.typeWf).subst environment.substitution
  let actual : Instantiation (.ordinary closedType) :=
    .ordinary normalization.value.expression
  let direct := BindingView.ofInstantiation actual normalization.value.ready
  have planEq :
      (Interface.BinderPlan.ordinary closedType) =
        (TermTranslation.compileBinder scope typing.typeWf).plan.subst
          environment.substitution := by
    rw [compileBinder_plan_ordinary scope typing.typeWf spine.targetShape]
    rfl
  let storedView :=
    EliminationView.castPlan planEq (EliminationView.ofDirect direct)
  refine { view := storedView, normalizes := ?_ }
  change Exp.Steps
    (environment.closeExp (TermTranslation.elaborate scope typing))
    storedView.argument
  rw [EliminationView.castPlan_argument]
  rw [← image.expression_eq]
  exact normalization.reductions

namespace ValueEvidence

noncomputable def closedView
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {sig : Sig} {targetContext : Ctx sig}
    {typing : Fragment.HasType sourceContext term sourceType}
    (evidence : ValueEvidence typing)
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (ready : evidence.ClosedReady scope environment) :
    OperationalPackageBehavior.ClosedView scope typing environment :=
  match evidence with
  | .function spine => spine.closedView scope environment
  | .package spine => spine.closedView scope environment ready

end ValueEvidence

end OperationalValueEvidence
end LambdaPToFCo
