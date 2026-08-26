import LambdaPToFCo.Full.ProperSelectionConstruction
import LambdaPToFCo.Full.FocusedPathTranslationCore

/-!
# Construction-certified focused proper paths

This module packages the focused path translation together with the exact
`ConstructedScope` history and action-specific selection certificates that
created it.  It deliberately has no constructor for certifying an arbitrary
pre-existing `FocusedProperPathPackage`.

The recursive certificate is constructor-complete for paths whose final
result has proper kind: variables, `fst` through either proper or interval
pairs, proper-member `sel_r`, and `sel_l`.  The root scope must expose an
exact `CurrentPairCapability` for each variable, and every recursive step
retains the exact capability of its computed result.  Interval-member
`sel_r` is a distinct interval-kind operation and remains outside this leaf;
it requires a sealed rank-2 capability for the Church-hidden witness.
-/

namespace LambdaPToFCo.Full.CertifiedFocusedPathTranslation

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open ScopedPathResolution
open ProperSelectionConstruction

inductive NonPair : LambdaPFC.Ty n -> Prop where
  | top : NonPair .Top
  | bottom : NonPair .Bot
  | function : NonPair (.Fun domain codomain)
  | singleton : NonPair (.Single path)
  | selection : NonPair (.TSel path label)

private abbrev ProperOuterPlan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {view : ScopeView n base}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base view sourceType plan}
    (capability : ProperSelectionCapability model) : ValuePlan sig :=
  Pair.Proper.plan capability.firstPlan capability.memberPlan

private abbrev ProperOuterMapping
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {view : ScopeView n base}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base view sourceType plan}
    (capability : ProperSelectionCapability model) :
    Rename sig (ProperOuterPlan capability).scope :=
  (ProperOuterPlan capability).telescope.weaken

noncomputable def properFirstFocused
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    (rootScope : ScopeModel sourceContext rootContext)
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (receiverTyping : LambdaPFC.Path.Ty sourceContext path (.ty sourceType))
    (receiver : FocusedProperPathPackage sourceContext rootContext rootScope
      receiverTyping)
    (capability : ProperSelectionCapability receiver.modeled) :
    FocusedProperPathPackage sourceContext rootContext rootScope
      (capability.typing receiverTyping).fst := by
  let outer := ProperOuterPlan capability
  let mapping := ProperOuterMapping capability
  let package := capability.package receiver.package
  let pairPackage : PathPackageZipper.ProperPairPackage
      receiver.currentContext capability.firstPlan capability.memberPlan :=
    { package := package }
  let projected := PathPackageZipper.ProperPairPackage.projectFirst
    receiver.zipper pairPackage
  exact
    { currentSig := outer.scope
      currentContext := outer.context receiver.currentContext
      zipper := receiver.zipper.enterPackage package
      currentScope := receiver.currentScope.targetRename mapping
        (outer.telescope.weaken_typed receiver.currentContext)
      scopeAlignment := FocusedPathTranslationCore.ScopeAlignment.enter
        rootScope receiver.zipper receiver.currentScope
        receiver.scopeAlignment outer.telescope
      plan := capability.firstPlan.rename mapping
      modeled := TargetModelRenaming.producer capability.first mapping
        (outer.telescope.weaken_typed receiver.currentContext)
      package := projected.package }

noncomputable def properFirstConstructed
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext base}
    (constructed : ConstructedScope scope)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base scope.view sourceType plan}
    (capability : ProperSelectionCapability model) :
    ConstructedScope
      (scope.targetRename (ProperOuterMapping capability)
        ((ProperOuterPlan capability).telescope.weaken_typed base)) :=
  .targetRename constructed (ProperOuterMapping capability)
    ((ProperOuterPlan capability).telescope.weaken_typed base)

noncomputable def properSelectedConstructed
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext base}
    (constructed : ConstructedScope scope)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base scope.view sourceType plan}
    (capability : ProperSelectionCapability model) :=
  let opened := outerConstructed constructed capability.firstPlan
    capability.memberPlan
  let representation := Pair.Proper.representation
    (OuterFirst capability.firstPlan capability.memberPlan)
    (OuterMember capability.firstPlan capability.memberPlan)
  ConstructedScope.targetRename opened representation.weaken
    (representation.weaken_typed
      ((OuterPlan capability.firstPlan capability.memberPlan).context base))

private abbrev IntervalOuterPlan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {view : ScopeView n base}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base view sourceType plan}
    (capability : IntervalPairCapability model) : ValuePlan sig :=
  Pair.Interval.plan capability.firstPlan capability.lowerPlan.inputTy
    capability.upperPlan.inputTy

private abbrev IntervalOpenFirst
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {view : ScopeView n base}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base view sourceType plan}
    (capability : IntervalPairCapability model) :
    ValuePlan (IntervalOuterPlan capability).scope :=
  capability.firstPlan.rename
    (IntervalOuterPlan capability).telescope.weaken

private abbrev IntervalOpenLower
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {view : ScopeView n base}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base view sourceType plan}
    (capability : IntervalPairCapability model) :
    Ty (IntervalOpenFirst capability).scope :=
  capability.lowerPlan.inputTy.rename
    (capability.firstPlan.telescope.liftRename
      (IntervalOuterPlan capability).telescope.weaken)

private abbrev IntervalOpenUpper
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {view : ScopeView n base}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base view sourceType plan}
    (capability : IntervalPairCapability model) :
    Ty (IntervalOpenFirst capability).scope :=
  capability.upperPlan.inputTy.rename
    (capability.firstPlan.telescope.liftRename
      (IntervalOuterPlan capability).telescope.weaken)

private noncomputable def intervalOpenedView
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {view : ScopeView n base}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base view sourceType plan}
    (capability : IntervalPairCapability model)
    (_package : PathPackageZipper.CompiledPackage base
      (IntervalOuterPlan capability)) :
    PairInterface.Interval.View
      ((IntervalOuterPlan capability).context base)
      (IntervalOpenFirst capability)
      (IntervalOpenLower capability)
      (IntervalOpenUpper capability) where
  interface := PathPackageZipper.openedInterface base
    (IntervalOuterPlan capability)
  plan_eq := by
    rw [PathPackageZipper.openedInterface_plan,
      Pair.Interval.plan_rename]
    rfl

private noncomputable def intervalFirstPackage
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (zipper : PathPackageZipper.ResultZipper rootContext base)
    {view : ScopeView n base}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base view sourceType plan}
    (capability : IntervalPairCapability model)
    (package : PathPackageZipper.CompiledPackage base
      (IntervalOuterPlan capability)) :
    PathPackageZipper.PathResult rootContext := by
  let outer := IntervalOuterPlan capability
  let openFirst := IntervalOpenFirst capability
  let openLower := IntervalOpenLower capability
  let openUpper := IntervalOpenUpper capability
  let member := Pair.Interval.memberTelescope openLower openUpper
  let outerZipper := zipper.enterPackage package
  let opened := intervalOpenedView capability package
  let firstPackage : Exp outer.scope :=
    opened.consume openFirst.inputTy opened.firstPackage
  have firstInterfacePlan :
      opened.firstInterface.plan =
        (openFirst.rename openFirst.telescope.weaken).rename member.weaken := by
    change
      ((ValueInterface.ofArguments
          (openFirst.rename openFirst.telescope.weaken)
          (Telescope.Args.identity openFirst.telescope
            (outer.context base))).rename member.weaken
        (member.weaken_typed
          (openFirst.context (outer.context base)))).plan = _
    change
      (ValueInterface.ofArguments
        (openFirst.rename openFirst.telescope.weaken)
        (Telescope.Args.identity openFirst.telescope
          (outer.context base))).plan.rename member.weaken = _
    rw [TranslationInterfaces.ValueInterface.ofArguments_plan]
  have firstBodyTyping :
      Exp.HasType
        (member.context (openFirst.context (outer.context base)))
        opened.firstPackage
        ((openFirst.inputTy.rename openFirst.telescope.weaken).rename
          member.weaken) := by
    have body := opened.firstPackage_hasType
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
  have firstTyping : Exp.HasType (outer.context base)
      firstPackage openFirst.inputTy :=
    opened.consume_hasType openFirst.inputTy opened.firstPackage
      firstBodyTyping
  exact
    { currentSig := outer.scope
      currentContext := outer.context base
      zipper := outerZipper
      plan := openFirst
      package :=
        { expression := firstPackage
          typing := firstTyping } }

noncomputable def intervalFirstFocused
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    (rootScope : ScopeModel sourceContext rootContext)
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (receiverTyping : LambdaPFC.Path.Ty sourceContext path (.ty sourceType))
    (receiver : FocusedProperPathPackage sourceContext rootContext rootScope
      receiverTyping)
    (capability : IntervalPairCapability receiver.modeled) :
    FocusedProperPathPackage sourceContext rootContext rootScope
      (capability.source_eq ▸ receiverTyping).fst := by
  have package : PathPackageZipper.CompiledPackage receiver.currentContext
      (Pair.Interval.plan capability.firstPlan capability.lowerPlan.inputTy
        capability.upperPlan.inputTy) :=
    capability.plan_eq ▸ receiver.package
  let outer := IntervalOuterPlan capability
  let projected := intervalFirstPackage receiver.zipper capability package
  exact
    { currentSig := outer.scope
      currentContext := outer.context receiver.currentContext
      zipper := receiver.zipper.enterPackage package
      currentScope := receiver.currentScope.targetRename
        outer.telescope.weaken
        (outer.telescope.weaken_typed receiver.currentContext)
      scopeAlignment := FocusedPathTranslationCore.ScopeAlignment.enter
        rootScope receiver.zipper receiver.currentScope
        receiver.scopeAlignment outer.telescope
      plan := capability.firstPlan.rename outer.telescope.weaken
      modeled := TargetModelRenaming.producer capability.firstModel
        outer.telescope.weaken
        (outer.telescope.weaken_typed receiver.currentContext)
      package := projected.package }

noncomputable def intervalFirstConstructed
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext base}
    (constructed : ConstructedScope scope)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {model : ProducerPlanModel sourceContext base scope.view sourceType plan}
    (capability : IntervalPairCapability model) :
    ConstructedScope
      (scope.targetRename (IntervalOuterPlan capability).telescope.weaken
        ((IntervalOuterPlan capability).telescope.weaken_typed base)) :=
  .targetRename constructed (IntervalOuterPlan capability).telescope.weaken
    ((IntervalOuterPlan capability).telescope.weaken_typed base)

/-! ## Closed derivation-indexed proper path result -/

/-- A focused proper package paired with the exact constructed history of its
current scope.  The source typing is stored as data rather than used as a
proof index, so `sel_l` can install its new precise alias without pretending
the old and new derivations are equal. -/
structure BuiltProper
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    (rootScope : ScopeModel sourceContext rootContext)
    (path : LambdaPFC.Path n) (referent : LambdaPFC.Ty n) : Type where
  typing : LambdaPFC.Path.Ty sourceContext path (.ty referent)
  focused : FocusedProperPathPackage sourceContext rootContext rootScope typing
  constructed : ConstructedScope focused.currentScope

namespace BuiltProper

noncomputable def withTyping
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    {rootScope : ScopeModel sourceContext rootContext}
    {firstPath secondPath : LambdaPFC.Path n}
    {referent : LambdaPFC.Ty n}
    (built : BuiltProper rootScope firstPath referent)
    (typing : LambdaPFC.Path.Ty sourceContext secondPath (.ty referent)) :
    BuiltProper rootScope secondPath referent :=
  { typing := typing
    focused :=
      { currentSig := built.focused.currentSig
        currentContext := built.focused.currentContext
        zipper := built.focused.zipper
        currentScope := built.focused.currentScope
        scopeAlignment := built.focused.scopeAlignment
        plan := built.focused.plan
        modeled := built.focused.modeled
        package := built.focused.package }
    constructed := built.constructed }

noncomputable def ofVariable
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    (rootScope : ScopeModel sourceContext rootContext)
    (constructed : ConstructedScope rootScope) (index : Fin n) :
    BuiltProper rootScope (.var index) (sourceContext.lookup index) where
  typing := .var
  focused := by
    cases FocusedPathTranslationCore.variablePath rootScope index with
    | proper result => exact result
  constructed := constructed

noncomputable def properFirst
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    {rootScope : ScopeModel sourceContext rootContext}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (receiver : BuiltProper rootScope path sourceType)
    (capability : ProperSelectionCapability receiver.focused.modeled) :
    BuiltProper rootScope path.fst capability.firstType where
  typing := (capability.typing receiver.typing).fst
  focused := properFirstFocused rootScope receiver.typing receiver.focused
    capability
  constructed := properFirstConstructed receiver.constructed capability

noncomputable def intervalFirst
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    {rootScope : ScopeModel sourceContext rootContext}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (receiver : BuiltProper rootScope path sourceType)
    (capability : IntervalPairCapability receiver.focused.modeled) :
    BuiltProper rootScope path.fst capability.firstType where
  typing := (capability.source_eq ▸ receiver.typing).fst
  focused := intervalFirstFocused rootScope receiver.typing receiver.focused
    capability
  constructed := intervalFirstConstructed receiver.constructed capability

noncomputable def properSelected
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    {rootScope : ScopeModel sourceContext rootContext}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (receiver : BuiltProper rootScope path sourceType)
    (capability : ProperSelectionCapability receiver.focused.modeled)
    (outerCertificate : OuterMemberCertificate receiver.focused.currentScope
      receiver.constructed capability)
    (openingCertificate : RepresentationOpeningCertificate
      receiver.focused.currentScope receiver.constructed capability
      receiver.typing outerCertificate) :
    BuiltProper rootScope (path.sel capability.label)
      (capability.memberType.open path.fst) where
  typing := (capability.typing receiver.typing).sel_r
  focused := ProperSelectionConstruction.selectRightFocused rootScope
    receiver.typing receiver.focused receiver.constructed capability
    outerCertificate openingCertificate
  constructed := properSelectedConstructed receiver.constructed capability

end BuiltProper

/-- Exact current pair shape retained by the high path result. -/
inductive CurrentPairCapability
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : ProducerPlanModel sourceContext targetContext scope.view
      sourceType plan) : Type where
  | nonPair (notPair : NonPair sourceType) : CurrentPairCapability model
  | proper (capability : ProperSelectionCapability model) :
      CurrentPairCapability model
  | interval (capability : IntervalPairCapability model) :
      CurrentPairCapability model

/-- Closed construction provenance for a `BuiltProper`.  Every constructor
computes its output package and scope from its recursive predecessor.  There
is no constructor which certifies an arbitrary pre-existing focused package.

This family is total for proper-kind path derivations: variables, both pair
forms of `fst`, proper-member `sel_r`, and `sel_l`.  Interval-member `sel_r`
has a distinct result kind and is intentionally absent until its hidden
descriptor has an analogous sealed opening constructor. -/
inductive Certificate
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    (rootScope : ScopeModel sourceContext rootContext)
    (rootConstructed : ConstructedScope rootScope) :
    {path : LambdaPFC.Path n} -> {referent : LambdaPFC.Ty n} ->
    BuiltProper rootScope path referent -> Type where
  | var (index : Fin n)
      (current : CurrentPairCapability (rootScope.slot index)) :
      Certificate rootScope rootConstructed
        (BuiltProper.ofVariable rootScope rootConstructed index)
  | properFirst
      (receiver : BuiltProper rootScope path sourceType)
      (previous : Certificate rootScope rootConstructed receiver)
      (capability : ProperSelectionCapability receiver.focused.modeled)
      (current : CurrentPairCapability
        (BuiltProper.properFirst receiver capability).focused.modeled) :
      Certificate rootScope rootConstructed
        (BuiltProper.properFirst receiver capability)
  | intervalFirst
      (receiver : BuiltProper rootScope path sourceType)
      (previous : Certificate rootScope rootConstructed receiver)
      (capability : IntervalPairCapability receiver.focused.modeled)
      (current : CurrentPairCapability
        (BuiltProper.intervalFirst receiver capability).focused.modeled) :
      Certificate rootScope rootConstructed
        (BuiltProper.intervalFirst receiver capability)
  | properSelected
      (receiver : BuiltProper rootScope path sourceType)
      (previous : Certificate rootScope rootConstructed receiver)
      (capability : ProperSelectionCapability receiver.focused.modeled)
      (outerCertificate : OuterMemberCertificate
        receiver.focused.currentScope receiver.constructed capability)
      (openingCertificate : RepresentationOpeningCertificate
        receiver.focused.currentScope receiver.constructed capability
        receiver.typing outerCertificate)
      (current : CurrentPairCapability
        (BuiltProper.properSelected receiver capability outerCertificate
          openingCertificate).focused.modeled) :
      Certificate rootScope rootConstructed
        (BuiltProper.properSelected receiver capability outerCertificate
          openingCertificate)
  | selectLeft
      (receiverTyping : LambdaPFC.Path.Ty sourceContext receiver
        (.ty (.Pair receiverFirst receiverLabel receiverMember)))
      (selected : BuiltProper rootScope
        (receiver.fst.sel selectedLabel) referent)
      (previous : Certificate rootScope rootConstructed selected)
      (labelsNe : selectedLabel ≠ receiverLabel)
      (current : CurrentPairCapability selected.focused.modeled) :
      Certificate rootScope rootConstructed
        (selected.withTyping
          (.sel_l receiverTyping selected.typing labelsNe))

namespace Certificate

def current
    {built : BuiltProper rootScope path referent}
    (certificate : Certificate rootScope rootConstructed built) :
    CurrentPairCapability built.focused.modeled :=
  match certificate with
  | .var _ current => current
  | .properFirst _ _ _ current => current
  | .intervalFirst _ _ _ current => current
  | .properSelected _ _ _ _ _ current => current
  | .selectLeft _ _ _ _ current => current

end Certificate

/-- Existentially package the computed focus together with its closed
constructor history. -/
structure Result
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    (rootScope : ScopeModel sourceContext rootContext)
    (rootConstructed : ConstructedScope rootScope)
    (path : LambdaPFC.Path n) (referent : LambdaPFC.Ty n) : Type where
  built : BuiltProper rootScope path referent
  certificate : Certificate rootScope rootConstructed built

namespace Result

noncomputable def ofVariable
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    (rootScope : ScopeModel sourceContext rootContext)
    (rootConstructed : ConstructedScope rootScope) (index : Fin n)
    (current : CurrentPairCapability (rootScope.slot index)) :
    Result rootScope rootConstructed (.var index)
      (sourceContext.lookup index) :=
  { built := BuiltProper.ofVariable rootScope rootConstructed index
    certificate := .var index current }

noncomputable def properFirst
    (receiver : Result rootScope rootConstructed path sourceType)
    (capability : ProperSelectionCapability
      receiver.built.focused.modeled)
    (current : CurrentPairCapability
      (receiver.built.properFirst capability).focused.modeled) :
    Result rootScope rootConstructed path.fst capability.firstType :=
  { built := receiver.built.properFirst capability
    certificate := .properFirst receiver.built receiver.certificate
      capability current }

noncomputable def intervalFirst
    (receiver : Result rootScope rootConstructed path sourceType)
    (capability : IntervalPairCapability receiver.built.focused.modeled)
    (current : CurrentPairCapability
      (receiver.built.intervalFirst capability).focused.modeled) :
    Result rootScope rootConstructed path.fst capability.firstType :=
  { built := receiver.built.intervalFirst capability
    certificate := .intervalFirst receiver.built receiver.certificate
      capability current }

noncomputable def properSelected
    (receiver : Result rootScope rootConstructed path sourceType)
    (capability : ProperSelectionCapability
      receiver.built.focused.modeled)
    (outerCertificate : OuterMemberCertificate
      receiver.built.focused.currentScope receiver.built.constructed
      capability)
    (openingCertificate : RepresentationOpeningCertificate
      receiver.built.focused.currentScope receiver.built.constructed
      capability receiver.built.typing outerCertificate)
    (current : CurrentPairCapability
      (receiver.built.properSelected capability outerCertificate
        openingCertificate).focused.modeled) :
    Result rootScope rootConstructed (path.sel capability.label)
      (capability.memberType.open path.fst) :=
  { built := receiver.built.properSelected capability outerCertificate
      openingCertificate
    certificate := .properSelected receiver.built receiver.certificate
      capability outerCertificate openingCertificate current }

noncomputable def selectLeft
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    {rootScope : ScopeModel sourceContext rootContext}
    {rootConstructed : ConstructedScope rootScope}
    {receiver : LambdaPFC.Path n} {receiverFirst : LambdaPFC.Ty n}
    {receiverLabel selectedLabel : LambdaPFC.Name}
    {receiverMember : LambdaPFC.Tau (n + 1) otherKind}
    {referent : LambdaPFC.Ty n}
    (receiverTyping : LambdaPFC.Path.Ty sourceContext receiver
      (.ty (.Pair receiverFirst receiverLabel receiverMember)))
    (selected : Result rootScope rootConstructed
      (receiver.fst.sel selectedLabel) referent)
    (labelsNe : selectedLabel ≠ receiverLabel) :
    Result rootScope rootConstructed (receiver.sel selectedLabel) referent :=
  { built := selected.built.withTyping
      (.sel_l receiverTyping selected.built.typing labelsNe)
    certificate := .selectLeft receiverTyping selected.built
      selected.certificate labelsNe selected.certificate.current }

end Result

end LambdaPToFCo.Full.CertifiedFocusedPathTranslation
