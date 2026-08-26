import LambdaPToFCo.Full.ProducerPairProjection
import LambdaPToFCo.Full.ScopedPathResolution

/-!
# Action-specific opening of a proper pair member

This leaf is the second sealed stage needed by dependent right selection.  It
retains the receiver's actual first-field arguments, an exact
`openAtTargetRename` coherence result for the member, and a package at the
plan definitionally determined by that action.  The target model is never a
caller-supplied field.

The package is a required retained input.  This module does not yet derive it
from `PairInterface.Proper.View.memberInterface`; that construction requires
the separate append-scope and identity-argument equality for the Church pair
representation.  Consequently `focused` is a narrow selection finisher, not
a total `sel_r` compiler.
-/

namespace LambdaPToFCo.Full

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open ScopedPathResolution

/-- Actual target arguments, exact model-opening certificate, and a package
at the target plan determined by that same opening. -/
structure ProperMemberOpening
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx source}
    {targetTargetContext : SystemFCoExt.Ctx target}
    (scope : ScopeModel sourceContext sourceTargetContext)
    (constructed : ConstructedScope scope)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
    {path : LambdaPFC.Path n} {firstType : LambdaPFC.Ty n}
    (precise : LambdaPFC.Path.Ty sourceContext path (.ty firstType))
    {firstPlan : ValuePlan source}
    (first : ProducerPlanModel sourceContext sourceTargetContext scope.view
      firstType firstPlan)
    {memberType : LambdaPFC.Ty (n + 1)}
    {memberPlan : ValuePlan firstPlan.scope}
    (member : ProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context sourceTargetContext)
      (ScopeView.bindPlan scope.view firstPlan) memberType memberPlan) : Type where
  arguments : Telescope.Args targetTargetContext
    (firstPlan.rename mapping).telescope
  certificate : ProducerInstantiationCoherence.Result
    (ModelInstantiation.openAtTargetRename scope constructed mapping typed
      precise first arguments) member
  package : PathPackageZipper.CompiledPackage targetTargetContext
    (memberPlan.subst
      ((firstPlan.telescope.liftRename mapping).asSubst.comp
        arguments.substitution))

namespace ProperMemberOpening

def plan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx source}
    {targetTargetContext : SystemFCoExt.Ctx target}
    {scope : ScopeModel sourceContext sourceTargetContext}
    {constructed : ConstructedScope scope}
    {mapping : Rename source target}
    {typed : Rename.Typed sourceTargetContext targetTargetContext mapping}
    {path : LambdaPFC.Path n} {firstType : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext path (.ty firstType)}
    {firstPlan : ValuePlan source}
    {first : ProducerPlanModel sourceContext sourceTargetContext scope.view
      firstType firstPlan}
    {memberType : LambdaPFC.Ty (n + 1)}
    {memberPlan : ValuePlan firstPlan.scope}
    {member : ProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context sourceTargetContext)
      (ScopeView.bindPlan scope.view firstPlan) memberType memberPlan}
    (opening : ProperMemberOpening scope constructed mapping typed precise
      first member) : ValuePlan target :=
  memberPlan.subst
    ((firstPlan.telescope.liftRename mapping).asSubst.comp
      opening.arguments.substitution)

/-- The uniquely determined target model recovered from the sealed result. -/
noncomputable def modeled
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {source target : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx source}
    {targetTargetContext : SystemFCoExt.Ctx target}
    {scope : ScopeModel sourceContext sourceTargetContext}
    {constructed : ConstructedScope scope}
    {mapping : Rename source target}
    {typed : Rename.Typed sourceTargetContext targetTargetContext mapping}
    {path : LambdaPFC.Path n} {firstType : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext path (.ty firstType)}
    {firstPlan : ValuePlan source}
    {first : ProducerPlanModel sourceContext sourceTargetContext scope.view
      firstType firstPlan}
    {memberType : LambdaPFC.Ty (n + 1)}
    {memberPlan : ValuePlan firstPlan.scope}
    {member : ProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context sourceTargetContext)
      (ScopeView.bindPlan scope.view firstPlan) memberType memberPlan}
    (opening : ProperMemberOpening scope constructed mapping typed precise
      first member) :
    ProducerPlanModel sourceContext targetTargetContext
      (scope.targetRename mapping typed).view
      (memberType.subst (PathSubst.openAt path)) opening.plan :=
  ProducerInstantiationCoherence.Result.instantiated opening.certificate

/-- Finish a focused proper selection after receiver-specific code has
retained the exact zipper, arguments, package, and scope alignment. -/
noncomputable def focused
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    (rootScope : ScopeModel sourceContext rootContext)
    {source target : Sig}
    {sourceTargetContext : SystemFCoExt.Ctx source}
    {targetTargetContext : SystemFCoExt.Ctx target}
    (scope : ScopeModel sourceContext sourceTargetContext)
    (constructed : ConstructedScope scope)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceTargetContext targetTargetContext mapping)
    {receiverPath : LambdaPFC.Path n} {firstType : LambdaPFC.Ty n}
    {label : LambdaPFC.Name} {memberType : LambdaPFC.Ty (n + 1)}
    (receiverTyping : LambdaPFC.Path.Ty sourceContext receiverPath
      (.ty (.Pair firstType label (.ty memberType))))
    {firstPlan : ValuePlan source}
    (first : ProducerPlanModel sourceContext sourceTargetContext scope.view
      firstType firstPlan)
    {memberPlan : ValuePlan firstPlan.scope}
    (member : ProducerPlanModel (sourceContext.snoc firstType)
      (firstPlan.context sourceTargetContext)
      (ScopeView.bindPlan scope.view firstPlan) memberType memberPlan)
    (opening : ProperMemberOpening scope constructed mapping typed
      receiverTyping.fst first member)
    (zipper : PathPackageZipper.ResultZipper rootContext
      targetTargetContext)
    (alignment : ScopeAlignment
      (rootScope.view.rename zipper.weakening zipper.weakeningTyped)
      (scope.targetRename mapping typed).view) :
    FocusedProperPathPackage sourceContext rootContext rootScope
      receiverTyping.sel_r :=
  { currentSig := target
    currentContext := targetTargetContext
    zipper := zipper
    currentScope := scope.targetRename mapping typed
    scopeAlignment := alignment
    plan := opening.plan
    modeled := opening.modeled
    package := opening.package }

end ProperMemberOpening

end LambdaPToFCo.Full
