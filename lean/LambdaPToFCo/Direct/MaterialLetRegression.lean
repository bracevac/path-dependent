import LambdaPToFCo.Direct.MaterialLet

/-!
# Material raw let regressions

The exact case binds an explicit, noncanonical Top payload and records its
ordinary elimination law.  The focused case performs the same operation
beneath a separate actual-package telescope and returns a root material Slot.
-/

namespace LambdaPToFCo.Direct.MaterialLetRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.Wf
open LambdaPToFCo.Direct.Internal.Introduction
open LambdaPToFCo.Direct.Internal.MaterialTermPath
open LambdaPToFCo.Direct.Internal.MaterialLet

private abbrev RootContext : Ctx [] := Ctx.empty

private def topPayload {sig : Sig} : Exp sig :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

private noncomputable def topPayload_hasType (base : Ctx sig) :
    Exp.HasType base (topPayload : Exp sig) .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

private theorem topPayload_isValue {sig : Sig} :
    Exp.IsValue (topPayload : Exp sig) :=
  .castTop .abs

private noncomputable def topInterface (base : Ctx sig) :
    Shape.Interface base (.stable (Top.plan sig)) where
  arguments := Top.arguments .top topPayload (topPayload_hasType base)

private noncomputable def topSlot (base : Ctx sig) :
    Slot base (.Top : LambdaPFC.Ty 0) where
  shape := .stable (Top.plan sig)
  interface := topInterface base
  rep := .top base

/-! ## Exact let package -/

private noncomputable def bound : Slot RootContext
    (.Top : LambdaPFC.Ty 0) :=
  topSlot RootContext

private def result : Proper RootContext (.Top : LambdaPFC.Ty 0) :=
  Proper.top RootContext

private noncomputable def bodyInterface : Shape.Interface
    (bound.shape.context RootContext)
    (result.shape.rename bound.shape.binders.weaken) := by
  simpa only [bound, result, topSlot, Proper.top, Shape.rename,
    Top.plan_rename] using
    topInterface (bound.shape.context RootContext)

private theorem bound_allValues : bound.interface.AllValues := by
  change Exp.IsValue (topPayload : Exp []) ∧ True
  exact ⟨topPayload_isValue, trivial⟩

/-- The emitted let expression eliminates the receiver's actual package and
substitutes precisely its explicit interface into the checked body package. -/
theorem actual_bound_package_eliminates :
    Exp.Steps
      (bind bound.shape bound.interface.package
        result.shape.inputTy bodyInterface.package)
      (bodyInterface.package.subst bound.interface.substitution) :=
  bind_interface_steps bound.interface bound_allValues
    result.shape.inputTy bodyInterface.package

noncomputable def exactResult :
    Slot RootContext (.Top : LambdaPFC.Ty 0) :=
  bindExact bound result bodyInterface

/-- The sealed result retains the original unweakened source index. -/
noncomputable def exactResult_rep :
    Rep RootContext (.Top : LambdaPFC.Ty 0) exactResult.shape :=
  exactResult.rep

noncomputable def exactResult_hasType :
    Exp.HasType RootContext exactResult.interface.package
      exactResult.shape.inputTy :=
  exactResult.interface.package_hasType

/-! ## A bound with no source Wf derivation -/

private abbrev BadContext : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc (.Top : LambdaPFC.Ty 0)

private abbrev BadPath : LambdaPFC.Path 1 := .fst (.var 0)

private abbrev BadSource : LambdaPFC.Ty 1 := .Single BadPath

/-- `fst` cannot project the only source variable, whose precise type is
Top, so the raw singleton bound below has no corresponding Wf premise. -/
def bad_not_wf :
    LambdaPFC.Tau.Wf BadContext (.ty BadSource) -> Empty := by
  intro wf
  cases wf with
  | path typing =>
      cases typing with
      | fst receiver => cases receiver

private noncomputable def badBound : Slot RootContext BadSource where
  shape := .stable (Single.plan .top)
  interface := {
    arguments := Single.exactArguments .top topPayload
      (topPayload_hasType RootContext)
  }
  rep := .singleton RootContext BadPath .top

private def badResult : Proper RootContext
    (.Top : LambdaPFC.Ty 1) :=
  Proper.top RootContext

private noncomputable def badBody : Shape.Interface
    (badBound.shape.context RootContext)
    (badResult.shape.rename badBound.shape.binders.weaken) := by
  simpa only [badBound, badResult, Proper.top, Shape.rename,
    Top.plan_rename] using
    topInterface (badBound.shape.context RootContext)

/-- Binding needs only the raw bound Slot; it cannot demand the impossible
Wf evidence above. -/
noncomputable def badBoundResult :
    Slot RootContext (.Top : LambdaPFC.Ty 1) :=
  bindExact badBound badResult badBody

/-! ## Reclosure through an outer focus -/

private def outerFields : Telescope [] := .var .top .nil

private noncomputable def outerArguments :
    Telescope.Args RootContext outerFields :=
  .var topPayload (topPayload_hasType RootContext) .nil

private noncomputable def outerPackage : Exp [] :=
  Telescope.pack outerArguments

private noncomputable def outerPackage_hasType :
    Exp.HasType RootContext outerPackage outerFields.existsTy :=
  Telescope.pack_hasType outerArguments

private abbrev OuterContext : Ctx outerFields.scope :=
  outerFields.context RootContext

private noncomputable def outerFocus : Focus RootContext OuterContext :=
  (Focus.root RootContext).openTelescope outerFields outerPackage
    outerPackage_hasType

private noncomputable def focusedBound :
    Slot OuterContext (.Top : LambdaPFC.Ty 0) :=
  topSlot OuterContext

private def focusedResultShape : Proper OuterContext
    (.Top : LambdaPFC.Ty 0) :=
  Proper.top OuterContext

private noncomputable def focusedBody : Shape.Interface
    (focusedBound.shape.context OuterContext)
    (focusedResultShape.shape.rename
      focusedBound.shape.binders.weaken) := by
  simpa only [focusedBound, focusedResultShape, topSlot, Proper.top,
    Shape.rename, Top.plan_rename] using
    topInterface (focusedBound.shape.context OuterContext)

noncomputable def focusedResult :
    Slot RootContext (.Top : LambdaPFC.Ty 0) :=
  bindFocused outerFocus focusedBound focusedResultShape focusedBody

theorem focusedResult_isClosed :
    match focusedResult.shape with
    | .opaque _ => True
    | .stable _ => False := by
  trivial

noncomputable def focusedResult_hasType :
    Exp.HasType RootContext focusedResult.interface.package
      focusedResult.shape.inputTy :=
  focusedResult.interface.package_hasType

end LambdaPToFCo.Direct.MaterialLetRegression
