import LambdaPToFCo.Full.ScopedPathResolution
import LambdaPToFCo.Full.TargetModelRenaming

/-!
# Partial focused path translation core

This module implements the path rules which do not require dependent member
instantiation: variables, non-rightmost selection, and first projection from
both proper-member and interval-member pairs.  Every result stays at its
honest Church-elimination focus.

The two `fst` constructors consume an exact sealed pair-head equality.  A
future `ProducerPairProjection` capability will derive that equality through
`bound`, `underBinding`, and `targetRename`.  This module deliberately does
not expose a total resolver and makes no `sel_r` claim.
-/

namespace LambdaPToFCo.Full.FocusedPathTranslationCore

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open ScopedPathResolution

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}

/-- Kind-complete focused output for the rules implemented in this partial
core. -/
inductive Result
    (rootScope : ScopeModel sourceContext rootContext) :
    {kind : LambdaPFC.Kind} -> {path : LambdaPFC.Path n} ->
    {result : LambdaPFC.Tau n kind} ->
    LambdaPFC.Path.Ty sourceContext path result -> Type where
  | proper
      (translation : FocusedProperPathPackage sourceContext rootContext
        rootScope precise) :
      Result rootScope precise
  | interval
      (translation : FocusedIntervalPathTranslation sourceContext rootContext
        rootScope precise) :
      Result rootScope precise

/-- Variable lookup starts and remains at the root focus. -/
noncomputable def variablePath
    (rootScope : ScopeModel sourceContext rootContext) (index : Fin n) :
    Result rootScope (LambdaPFC.Path.Ty.var (x := index)) :=
  .proper
    { currentSig := rootSig
      currentContext := rootContext
      zipper := PathPackageZipper.ResultZipper.root rootContext
      currentScope := rootScope
      scopeAlignment :=
        { slot := fun slot =>
            { identity_eq := by
                simp only [PathPackageZipper.ResultZipper.root,
                  ScopeView.rename_apply, ValueInterface.rename_identity,
                  SystemFCoExt.Ty.rename_id]
              payload_eq := by
                simp only [PathPackageZipper.ResultZipper.root,
                  ScopeView.rename_apply, ValueInterface.rename_payload,
                  Exp.rename_id] } }
      plan := (rootScope.view index).plan
      modeled := rootScope.slot index
      package := rootScope.package index }

/-- Rewrap a focused result at another typing derivation of the same path and
generalized result.  No target field depends on proof identity. -/
def Result.withTyping
    (rootScope : ScopeModel sourceContext rootContext)
    {kind : LambdaPFC.Kind} {firstPath secondPath : LambdaPFC.Path n}
    {result : LambdaPFC.Tau n kind}
    {firstTyping : LambdaPFC.Path.Ty sourceContext firstPath result}
    (translated : Result rootScope firstTyping)
    (secondTyping : LambdaPFC.Path.Ty sourceContext secondPath result) :
    Result rootScope secondTyping := by
  cases translated with
  | proper translation =>
      exact .proper
        { currentSig := translation.currentSig
          currentContext := translation.currentContext
          zipper := translation.zipper
          currentScope := translation.currentScope
          scopeAlignment := translation.scopeAlignment
          plan := translation.plan
          modeled := translation.modeled
          package := translation.package }
  | interval translation =>
      exact .interval
        { currentSig := translation.currentSig
          currentContext := translation.currentContext
          zipper := translation.zipper
          currentScope := translation.currentScope
          scopeAlignment := translation.scopeAlignment
          lower := translation.lower
          upper := translation.upper
          descriptor := translation.descriptor }

/-- `sel_l` changes only the source derivation.  Its recursive tail already
denotes the exact same selected path and result. -/
def selectLeft
    (rootScope : ScopeModel sourceContext rootContext)
    {receiver : LambdaPFC.Path n} {receiverFirst : LambdaPFC.Ty n}
    {receiverLabel selectedLabel : LambdaPFC.Name}
    {receiverMember : LambdaPFC.Tau (n + 1) otherKind}
    {selectedResult : LambdaPFC.Tau n kind}
    (receiverTyping : LambdaPFC.Path.Ty sourceContext receiver
      (.ty (.Pair receiverFirst receiverLabel receiverMember)))
    (selectedTyping : LambdaPFC.Path.Ty sourceContext
      (receiver.fst.sel selectedLabel) selectedResult)
    (labelsNe : selectedLabel ≠ receiverLabel)
    (translated : Result rootScope selectedTyping) :
    Result rootScope
      (LambdaPFC.Path.Ty.sel_l receiverTyping selectedTyping labelsNe) :=
  translated.withTyping rootScope
    (LambdaPFC.Path.Ty.sel_l receiverTyping selectedTyping labelsNe)

/-! ## Focus-extension alignment -/

/-- Extending a focused zipper and target scope through the same telescope
preserves the root-to-current stable-field alignment.  Only identity and
payload fields are compared, so no equality of proof-relevant interface
argument spines is asserted. -/
noncomputable def ScopeAlignment.enter
    {currentSig : Sig}
    {currentContext : SystemFCoExt.Ctx currentSig}
    (rootScope : ScopeModel sourceContext rootContext)
    (zipper : PathPackageZipper.ResultZipper rootContext currentContext)
    (currentScope : ScopeModel sourceContext currentContext)
    (alignment : ScopeAlignment
      (rootScope.view.rename zipper.weakening zipper.weakeningTyped)
      currentScope.view)
    (telescope : Telescope currentSig) :
    ScopeAlignment
      (rootScope.view.rename
        (zipper.weakening.comp telescope.weaken)
        (zipper.weakeningTyped.comp
          (telescope.weaken_typed currentContext)))
      (currentScope.view.rename telescope.weaken
        (telescope.weaken_typed currentContext)) where
  slot index :=
    { identity_eq := by
        simp only [ScopeView.rename_apply,
          ValueInterface.rename_identity]
        calc
          (rootScope.view index).identity.rename
              (zipper.weakening.comp telescope.weaken) =
              ((rootScope.view index).identity.rename
                zipper.weakening).rename telescope.weaken :=
            (Ty.rename_comp _ _ _).symm
          _ = (currentScope.view index).identity.rename
                telescope.weaken :=
            congrArg (fun identity => identity.rename telescope.weaken)
              (alignment.identity_eq index)
      payload_eq := by
        simp only [ScopeView.rename_apply,
          ValueInterface.rename_payload]
        calc
          (rootScope.view index).payload.rename
              (zipper.weakening.comp telescope.weaken) =
              ((rootScope.view index).payload.rename
                zipper.weakening).rename telescope.weaken :=
            (Exp.rename_comp _ _ _).symm
          _ = (currentScope.view index).payload.rename
                telescope.weaken :=
            congrArg (fun payload => payload.rename telescope.weaken)
              (alignment.payload_eq index) }

/-! ## Proper-member first projection -/

/-- Project the first field once a sealed pair-head capability exposes the
exact proper pair model at the receiver focus. -/
noncomputable def projectProperFirst
    (rootScope : ScopeModel sourceContext rootContext)
    {path : LambdaPFC.Path n} {first : LambdaPFC.Ty n}
    {label : LambdaPFC.Name} {member : LambdaPFC.Ty (n + 1)}
    (receiverTyping : LambdaPFC.Path.Ty sourceContext path
      (.ty (.Pair first label (.ty member))))
    (receiver : FocusedProperPathPackage sourceContext rootContext rootScope
      receiverTyping)
    {firstPlan : ValuePlan receiver.currentSig}
    {memberPlan : ValuePlan firstPlan.scope}
    (firstModel : ProducerPlanModel sourceContext receiver.currentContext
      receiver.currentScope.view first firstPlan)
    (memberModel : ProducerPlanModel (sourceContext.snoc first)
      (firstPlan.context receiver.currentContext)
      (ScopeView.bindPlan receiver.currentScope.view firstPlan)
      member memberPlan)
    (model_eq :
      (⟨receiver.plan, receiver.modeled⟩ :
        Sigma fun plan => ProducerPlanModel sourceContext
          receiver.currentContext receiver.currentScope.view
          (.Pair first label (.ty member)) plan) =
      ⟨Pair.Proper.plan firstPlan memberPlan,
        .properPair (label := label) firstModel memberModel⟩) :
    FocusedProperPathPackage sourceContext rootContext rootScope
      receiverTyping.fst := by
  let outerPlan := Pair.Proper.plan firstPlan memberPlan
  have plan_eq : receiver.plan = outerPlan := congrArg Sigma.fst model_eq
  have package : PathPackageZipper.CompiledPackage receiver.currentContext
      outerPlan := plan_eq ▸ receiver.package
  have pairPackage : PathPackageZipper.ProperPairPackage
      receiver.currentContext firstPlan memberPlan :=
    { package := package }
  let projected := PathPackageZipper.ProperPairPackage.projectFirst
    receiver.zipper pairPackage
  let currentScope := receiver.currentScope.targetRename
    outerPlan.telescope.weaken
    (outerPlan.telescope.weaken_typed receiver.currentContext)
  exact
    { currentSig := outerPlan.scope
      currentContext := outerPlan.context receiver.currentContext
      zipper := receiver.zipper.enterPackage pairPackage.package
      currentScope := currentScope
      scopeAlignment := ScopeAlignment.enter rootScope receiver.zipper
        receiver.currentScope receiver.scopeAlignment outerPlan.telescope
      plan := firstPlan.rename outerPlan.telescope.weaken
      modeled := TargetModelRenaming.producer firstModel
        outerPlan.telescope.weaken
        (outerPlan.telescope.weaken_typed receiver.currentContext)
      package := projected.package }

/-! ## Interval-member first projection -/

private abbrev IntervalOuterPlan {sig : Sig} (first : ValuePlan sig)
    (lower upper : Ty first.scope) : ValuePlan sig :=
  Pair.Interval.plan first lower upper

private abbrev IntervalOpenFirst {sig : Sig} (first : ValuePlan sig)
    (lower upper : Ty first.scope) :
    ValuePlan (IntervalOuterPlan first lower upper).scope :=
  first.rename (IntervalOuterPlan first lower upper).telescope.weaken

private abbrev IntervalOpenLower {sig : Sig} (first : ValuePlan sig)
    (lower upper : Ty first.scope) :
    Ty (IntervalOpenFirst first lower upper).scope :=
  lower.rename
    (first.telescope.liftRename
      (IntervalOuterPlan first lower upper).telescope.weaken)

private abbrev IntervalOpenUpper {sig : Sig} (first : ValuePlan sig)
    (lower upper : Ty first.scope) :
    Ty (IntervalOpenFirst first lower upper).scope :=
  upper.rename
    (first.telescope.liftRename
      (IntervalOuterPlan first lower upper).telescope.weaken)

private noncomputable def intervalOpenedView
    {sig : Sig} {context : Ctx sig}
    {first : ValuePlan sig} {lower upper : Ty first.scope}
    (_package : PathPackageZipper.CompiledPackage context
      (Pair.Interval.plan first lower upper)) :
    PairInterface.Interval.View
      ((Pair.Interval.plan first lower upper).context context)
      (IntervalOpenFirst first lower upper)
      (IntervalOpenLower first lower upper)
      (IntervalOpenUpper first lower upper) where
  interface := PathPackageZipper.openedInterface context
    (Pair.Interval.plan first lower upper)
  plan_eq := by
    rw [PathPackageZipper.openedInterface_plan,
      Pair.Interval.plan_rename]
    rfl

/-- Low interval-pair `fst`: preserve the hidden witness under the pair
continuation while returning a first-component package at the opened outer
focus. -/
private noncomputable def projectIntervalFirstPackage
    {currentSig : Sig}
    {currentContext : SystemFCoExt.Ctx currentSig}
    (zipper : PathPackageZipper.ResultZipper rootContext currentContext)
    {first : ValuePlan currentSig} {lower upper : Ty first.scope}
    (package : PathPackageZipper.CompiledPackage currentContext
      (Pair.Interval.plan first lower upper)) :
    PathPackageZipper.PathResult rootContext := by
  let outer := IntervalOuterPlan first lower upper
  let openFirst := IntervalOpenFirst first lower upper
  let openLower := IntervalOpenLower first lower upper
  let openUpper := IntervalOpenUpper first lower upper
  let member := Pair.Interval.memberTelescope openLower openUpper
  let outerZipper := zipper.enterPackage package
  let view := intervalOpenedView package
  let firstPackage : Exp outer.scope :=
    view.consume openFirst.inputTy view.firstPackage
  have firstInterfacePlan :
      view.firstInterface.plan =
        (openFirst.rename openFirst.telescope.weaken).rename member.weaken := by
    change
      ((ValueInterface.ofArguments
          (openFirst.rename openFirst.telescope.weaken)
          (Telescope.Args.identity openFirst.telescope
            (outer.context currentContext))).rename member.weaken
        (member.weaken_typed
          (openFirst.context (outer.context currentContext)))).plan = _
    change
      (ValueInterface.ofArguments
        (openFirst.rename openFirst.telescope.weaken)
        (Telescope.Args.identity openFirst.telescope
          (outer.context currentContext))).plan.rename member.weaken = _
    rw [TranslationInterfaces.ValueInterface.ofArguments_plan]
  have firstBodyTyping :
      Exp.HasType
        (member.context (openFirst.context (outer.context currentContext)))
        view.firstPackage
        ((openFirst.inputTy.rename openFirst.telescope.weaken).rename
          member.weaken) := by
    have body := view.firstPackage_hasType
    rw [firstInterfacePlan] at body
    have type_eq :
        ((openFirst.rename openFirst.telescope.weaken).rename
            member.weaken).inputTy =
          (openFirst.inputTy.rename openFirst.telescope.weaken).rename
            member.weaken := by
      calc
        ((openFirst.rename openFirst.telescope.weaken).rename
            member.weaken).inputTy =
            (openFirst.rename openFirst.telescope.weaken).inputTy.rename
              member.weaken :=
          (ValuePlan.inputTy_rename
            (openFirst.rename openFirst.telescope.weaken)
            member.weaken).symm
        _ = _ := congrArg (fun type => type.rename member.weaken)
          (ValuePlan.inputTy_rename openFirst
            openFirst.telescope.weaken).symm
    exact type_eq ▸ body
  have firstTyping : Exp.HasType (outer.context currentContext)
      firstPackage openFirst.inputTy :=
    view.consume_hasType openFirst.inputTy view.firstPackage firstBodyTyping
  exact
    { currentSig := outer.scope
      currentContext := outer.context currentContext
      zipper := outerZipper
      plan := openFirst
      package :=
        { expression := firstPackage
          typing := firstTyping } }

/-- Project the first field once a sealed pair-head capability exposes the
exact interval pair model at the receiver focus. -/
noncomputable def projectIntervalFirst
    (rootScope : ScopeModel sourceContext rootContext)
    {path : LambdaPFC.Path n} {first : LambdaPFC.Ty n}
    {label : LambdaPFC.Name} {lower upper : LambdaPFC.Ty (n + 1)}
    (receiverTyping : LambdaPFC.Path.Ty sourceContext path
      (.ty (.Pair first label (.intv lower upper))))
    (receiver : FocusedProperPathPackage sourceContext rootContext rootScope
      receiverTyping)
    {firstPlan : ValuePlan receiver.currentSig}
    {lowerPlan upperPlan : ValuePlan firstPlan.scope}
    (firstModel : ProducerPlanModel sourceContext receiver.currentContext
      receiver.currentScope.view first firstPlan)
    (memberModel : IntervalProducerPlanModel (sourceContext.snoc first)
      (firstPlan.context receiver.currentContext)
      (ScopeView.bindPlan receiver.currentScope.view firstPlan)
      lower upper lowerPlan upperPlan)
    (model_eq :
      (⟨receiver.plan, receiver.modeled⟩ :
        Sigma fun plan => ProducerPlanModel sourceContext
          receiver.currentContext receiver.currentScope.view
          (.Pair first label (.intv lower upper)) plan) =
      ⟨Pair.Interval.plan firstPlan lowerPlan.inputTy upperPlan.inputTy,
        .intervalPair (label := label) firstModel memberModel⟩) :
    FocusedProperPathPackage sourceContext rootContext rootScope
      receiverTyping.fst := by
  let outerPlan := Pair.Interval.plan firstPlan lowerPlan.inputTy
    upperPlan.inputTy
  have plan_eq : receiver.plan = outerPlan := congrArg Sigma.fst model_eq
  have package : PathPackageZipper.CompiledPackage receiver.currentContext
      outerPlan := plan_eq ▸ receiver.package
  let projected := projectIntervalFirstPackage receiver.zipper package
  let currentScope := receiver.currentScope.targetRename
    outerPlan.telescope.weaken
    (outerPlan.telescope.weaken_typed receiver.currentContext)
  exact
    { currentSig := outerPlan.scope
      currentContext := outerPlan.context receiver.currentContext
      zipper := receiver.zipper.enterPackage package
      currentScope := currentScope
      scopeAlignment := ScopeAlignment.enter rootScope receiver.zipper
        receiver.currentScope receiver.scopeAlignment outerPlan.telescope
      plan := firstPlan.rename outerPlan.telescope.weaken
      modeled := TargetModelRenaming.producer firstModel
        outerPlan.telescope.weaken
        (outerPlan.telescope.weaken_typed receiver.currentContext)
      package := projected.package }

end LambdaPToFCo.Full.FocusedPathTranslationCore
