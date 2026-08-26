import LambdaPToFCo.Full.PairInterface
import LambdaPToFCo.Full.ScopeView

/-!
# Compiled path packages and open-result zippers

A path result may live in a target context obtained by opening one or more
Church packages. The zipper remembers how to eliminate all of those packages
when a root-scoped answer is eventually requested. It does not pretend that
the current package has a `ValueInterface` in the root context.
-/

namespace LambdaPToFCo.Full.PathPackageZipper

open SystemFCoExt

/-- An arbitrary compiled expression at one target type. -/
structure CompiledExpression {sig : Sig} (context : Ctx sig)
    (type : Ty sig) : Type where
  expression : Exp sig
  typing : Exp.HasType context expression type

/-- A compiled Church package for exactly one value plan. In contrast to a
`ValueInterface`, this contains no claim that the hidden identity and payload
are available in `context`. -/
structure CompiledPackage {sig : Sig} (context : Ctx sig)
    (plan : ValuePlan sig) : Type where
  expression : Exp sig
  typing : Exp.HasType context expression plan.inputTy

namespace CompiledPackage

/-- Repack an interface which really is open in the current context. -/
noncomputable def ofInterface {sig : Sig} {context : Ctx sig}
    (interface : ValueInterface context) :
    CompiledPackage context interface.plan where
  expression := interface.package
  typing := interface.package_hasType

end CompiledPackage

/-- A continuation from a current open target context back to a fixed root
context. `weakening` records how root-scoped answer types appear at the
current focus. -/
structure ResultZipper {rootSig : Sig} (rootContext : Ctx rootSig)
    {currentSig : Sig} (currentContext : Ctx currentSig) : Type where
  weakening : Rename rootSig currentSig
  weakeningTyped : Rename.Typed rootContext currentContext weakening
  plug : (answer : Ty rootSig) -> (body : Exp currentSig) ->
    Exp.HasType currentContext body (answer.rename weakening) ->
    CompiledExpression rootContext answer

namespace ResultZipper

/-- The empty zipper. -/
noncomputable def root {sig : Sig} (context : Ctx sig) :
    ResultZipper context context where
  weakening := .id
  weakeningTyped := Rename.Typed.id context
  plug answer body bodyTyping :=
    { expression := body
      typing := by
        rw [Ty.rename_id] at bodyTyping
        exact bodyTyping }

/-- Enter an arbitrary Church telescope. The package is eliminated only
when `plug` is eventually invoked, so dependencies on the freshly opened
fields remain well scoped in the meantime. -/
noncomputable def enter
    {rootSig currentSig : Sig}
    {rootContext : Ctx rootSig} {currentContext : Ctx currentSig}
    (zipper : ResultZipper rootContext currentContext)
    (telescope : Telescope currentSig)
    (package : CompiledExpression currentContext telescope.existsTy) :
    ResultZipper rootContext (telescope.context currentContext) where
  weakening := zipper.weakening.comp telescope.weaken
  weakeningTyped := zipper.weakeningTyped.comp
    (telescope.weaken_typed currentContext)
  plug answer body bodyTyping := by
    have openedBodyTyping :
        Exp.HasType (telescope.context currentContext) body
          ((answer.rename zipper.weakening).rename telescope.weaken) := by
      rw [Ty.rename_comp]
      exact bodyTyping
    let eliminated := telescope.unpack package.expression
      (answer.rename zipper.weakening) body
    have eliminatedTyping :
        Exp.HasType currentContext eliminated
          (answer.rename zipper.weakening) :=
      telescope.unpack_hasType package.typing openedBodyTyping
    exact zipper.plug answer eliminated eliminatedTyping

/-- Enter the hidden interface of a compiled value package. -/
noncomputable def enterPackage
    {rootSig currentSig : Sig}
    {rootContext : Ctx rootSig} {currentContext : Ctx currentSig}
    (zipper : ResultZipper rootContext currentContext)
    {plan : ValuePlan currentSig}
    (package : CompiledPackage currentContext plan) :
    ResultZipper rootContext (plan.context currentContext) :=
  zipper.enter plan.telescope
    { expression := package.expression
      typing := package.typing }

end ResultZipper

/-- The canonical opened interface in the body of `plan.unpack`. Its fields
are the variables introduced by that unpack, rather than fields illicitly
projected in the package's original context. -/
noncomputable def openedInterface {sig : Sig} (context : Ctx sig)
    (plan : ValuePlan sig) : ValueInterface (plan.context context) :=
  ValueInterface.ofArguments (plan.rename plan.telescope.weaken)
    (Telescope.Args.identity plan.telescope context)

private theorem ValueInterface.ofArguments_plan
    {sig : Sig} {context : Ctx sig} (plan : ValuePlan sig)
    (arguments : Telescope.Args context plan.telescope) :
    (ValueInterface.ofArguments plan arguments).plan = plan := by
  cases arguments with
  | tvar identity rest =>
      cases rest with
      | var payload payloadTyping observations => rfl

@[simp] theorem openedInterface_plan {sig : Sig} (context : Ctx sig)
    (plan : ValuePlan sig) :
    (openedInterface context plan).plan =
      plan.rename plan.telescope.weaken := by
  exact ValueInterface.ofArguments_plan _ _

/-- Existentially scoped path output. The plan and package live at the
current zipper focus. A later path projection may enter more packages; a
consumer may instead compile a root-scoped answer at the current focus and
use `zipper.plug` to discharge all retained eliminations. -/
structure PathResult {rootSig : Sig} (rootContext : Ctx rootSig) : Type where
  currentSig : Sig
  currentContext : Ctx currentSig
  zipper : ResultZipper rootContext currentContext
  plan : ValuePlan currentSig
  package : CompiledPackage currentContext plan

namespace PathResult

/-- A package already available in the root context is the base path result.
This is the shape used by `Path.Ty.var`. -/
noncomputable def rootPackage
    {sig : Sig} {context : Ctx sig} {plan : ValuePlan sig}
    (package : CompiledPackage context plan) : PathResult context where
  currentSig := sig
  currentContext := context
  zipper := ResultZipper.root context
  plan := plan
  package := package

/-- Open the stable interface of the current package. This operation is the
first half of every structural projection. -/
noncomputable def enterInterface
    {rootSig : Sig} {rootContext : Ctx rootSig}
    (result : PathResult rootContext) :
    ResultZipper rootContext (result.plan.context result.currentContext) :=
  result.zipper.enterPackage result.package

/-- The opened interface corresponding to `enterInterface`. -/
noncomputable def interface
    {rootSig : Sig} {rootContext : Ctx rootSig}
    (result : PathResult rootContext) :
    ValueInterface (result.plan.context result.currentContext) :=
  openedInterface result.currentContext result.plan

end PathResult

/-! ## Proper-pair projection

These helpers demonstrate that a compiled pair package can be opened and
observed using `PairInterface` without a base-context `ValueInterface`.
-/

structure ProperPairPackage {sig : Sig} (context : Ctx sig)
    (first : ValuePlan sig) (member : ValuePlan first.scope) : Type where
  package : CompiledPackage context (Pair.Proper.plan first member)

namespace ProperPairPackage

private abbrev OuterPlan {sig : Sig} (first : ValuePlan sig)
    (member : ValuePlan first.scope) : ValuePlan sig :=
  Pair.Proper.plan first member

private abbrev OpenFirst {sig : Sig} (first : ValuePlan sig)
    (member : ValuePlan first.scope) :
    ValuePlan (OuterPlan first member).scope :=
  first.rename (OuterPlan first member).telescope.weaken

private abbrev OpenMember {sig : Sig} (first : ValuePlan sig)
    (member : ValuePlan first.scope) :
    ValuePlan (OpenFirst first member).scope :=
  Pair.Proper.renameMember first member
    (OuterPlan first member).telescope.weaken

noncomputable def openedView {sig : Sig} {context : Ctx sig}
    {first : ValuePlan sig} {member : ValuePlan first.scope}
    (_pair : ProperPairPackage context first member) :
    PairInterface.Proper.View
      ((Pair.Proper.plan first member).context context)
      (first.rename (Pair.Proper.plan first member).telescope.weaken)
      (Pair.Proper.renameMember first member
        (Pair.Proper.plan first member).telescope.weaken) where
  interface := openedInterface context (Pair.Proper.plan first member)
  plan_eq := by
    rw [openedInterface_plan, Pair.Proper.plan_rename]
    rfl

noncomputable def representation
    {sig : Sig} {context : Ctx sig}
    {first : ValuePlan sig} {member : ValuePlan first.scope}
    (pair : ProperPairPackage context first member) :
    CompiledExpression
      ((Pair.Proper.plan first member).context context)
      (Pair.Proper.representation
        (first.rename (Pair.Proper.plan first member).telescope.weaken)
        (Pair.Proper.renameMember first member
          (Pair.Proper.plan first member).telescope.weaken)).existsTy where
  expression := pair.openedView.pair.asRepresentation
  typing := pair.openedView.pair.asRepresentation_hasType

/-- Proper `fst`: open the outer stable interface, consume the pair
representation back into a package at the renamed first plan, and retain the
outer-package elimination in the zipper. The result package is in the opened
outer-interface context, not in `context`. -/
noncomputable def projectFirst
    {rootSig currentSig : Sig}
    {rootContext : Ctx rootSig} {currentContext : Ctx currentSig}
    {first : ValuePlan currentSig} {member : ValuePlan first.scope}
    (zipper : ResultZipper rootContext currentContext)
    (pair : ProperPairPackage currentContext first member) :
    PathResult rootContext := by
  let outerZipper := zipper.enterPackage pair.package
  let view := pair.openedView
  let firstPlan : ValuePlan (OuterPlan first member).scope :=
    OpenFirst first member
  let firstPackage : Exp (OuterPlan first member).scope :=
    view.consume firstPlan.inputTy view.firstPackage
  have firstInterfacePlan :
      view.firstInterface.plan =
        (firstPlan.rename firstPlan.telescope.weaken).rename
          (OpenMember first member).telescope.weaken := by
    change
      ((ValueInterface.ofArguments
          (firstPlan.rename firstPlan.telescope.weaken)
          (Telescope.Args.identity firstPlan.telescope
            ((OuterPlan first member).context currentContext))).rename
        (OpenMember first member).telescope.weaken
        ((OpenMember first member).telescope.weaken_typed
          (firstPlan.context
            ((OuterPlan first member).context currentContext)))).plan = _
    change
      (ValueInterface.ofArguments
          (firstPlan.rename firstPlan.telescope.weaken)
          (Telescope.Args.identity firstPlan.telescope
            ((OuterPlan first member).context currentContext))).plan.rename
        (OpenMember first member).telescope.weaken = _
    rw [ValueInterface.ofArguments_plan]
  have firstBodyTyping :
      Exp.HasType
        ((OpenMember first member).context
          ((OpenFirst first member).context
            ((OuterPlan first member).context currentContext)))
        view.firstPackage
        ((firstPlan.inputTy.rename firstPlan.telescope.weaken).rename
          (OpenMember first member).telescope.weaken) := by
    have body := view.firstPackage_hasType
    rw [firstInterfacePlan] at body
    have type_eq :
        ((firstPlan.rename firstPlan.telescope.weaken).rename
            (OpenMember first member).telescope.weaken).inputTy =
          (firstPlan.inputTy.rename firstPlan.telescope.weaken).rename
            (OpenMember first member).telescope.weaken := by
      calc
        ((firstPlan.rename firstPlan.telescope.weaken).rename
            (OpenMember first member).telescope.weaken).inputTy =
            (firstPlan.rename firstPlan.telescope.weaken).inputTy.rename
              (OpenMember first member).telescope.weaken :=
          (ValuePlan.inputTy_rename
            (firstPlan.rename firstPlan.telescope.weaken)
            (OpenMember first member).telescope.weaken).symm
        _ = _ := congrArg
          (fun type => type.rename
            (OpenMember first member).telescope.weaken)
          (ValuePlan.inputTy_rename firstPlan
            firstPlan.telescope.weaken).symm
    exact type_eq ▸ body
  have firstTyping :
      Exp.HasType ((OuterPlan first member).context currentContext)
        firstPackage firstPlan.inputTy :=
    view.consume_hasType firstPlan.inputTy view.firstPackage firstBodyTyping
  exact
    { currentSig := (OuterPlan first member).scope
      currentContext := (OuterPlan first member).context currentContext
      zipper := outerZipper
      plan := firstPlan
      package :=
        { expression := firstPackage
          typing := firstTyping } }

end ProperPairPackage

end LambdaPToFCo.Full.PathPackageZipper
