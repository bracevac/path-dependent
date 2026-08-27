import LambdaPToFCo.Direct.MaterialApplication

/-!
# Material raw application regressions

An exact Top-to-Top function is first applied in one scope.  The focused
application then starts from the same function view beneath one actual
package focus and supplies its checked argument beneath another, so its
result must close through the composed inner and outer package histories.
-/

namespace LambdaPToFCo.Direct.MaterialApplicationRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.MaterialTermPath
open LambdaPToFCo.Direct.Internal.MaterialApplication

private abbrev RootContext : Ctx [] := Ctx.empty

private abbrev DomainSource : LambdaPFC.Ty 1 := .Top
private abbrev CodomainSource : LambdaPFC.Ty 2 := .Top
private abbrev FunctionSource : LambdaPFC.Ty 1 :=
  .Fun DomainSource CodomainSource
private abbrev ArgumentPath : LambdaPFC.Path 1 := .var 0

private def topPayload {sig : Sig} : Exp sig :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

private noncomputable def topPayload_hasType (base : Ctx sig) :
    Exp.HasType base (topPayload : Exp sig) .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

private noncomputable def topInterface (base : Ctx sig) :
    Shape.Interface base (.stable (Top.plan sig)) where
  arguments := Top.arguments .top topPayload (topPayload_hasType base)

private def domain : Shape [] := .stable (Top.plan [])

private def codomain : Shape domain.scope :=
  .stable (Top.plan domain.scope)

private noncomputable def functionBody : Exp domain.scope :=
  (topInterface (domain.context RootContext)).package

private noncomputable def functionBody_hasType :
    Exp.HasType (domain.context RootContext) functionBody
      codomain.inputTy := by
  simpa only [codomain, Top.plan_subst] using
    (topInterface (domain.context RootContext)).package_hasType

private noncomputable def functionCode : Exp [] :=
  domain.binders.lambda functionBody

private noncomputable def functionCode_hasType :
    Exp.HasType RootContext functionCode (Function.codeTy domain codomain) :=
  domain.binders.lambda_hasType functionBody_hasType

private noncomputable def functionInterface :
    Shape.Interface RootContext
      (.stable (Function.plan domain codomain)) where
  arguments := Function.exactArguments domain codomain functionCode
    functionCode_hasType

private def functionRep :
    Rep RootContext FunctionSource
      (.stable (Function.plan domain codomain)) :=
  .function (.top _) (.top _)

private noncomputable def functionSlot :
    Slot RootContext FunctionSource where
  shape := .stable (Function.plan domain codomain)
  interface := functionInterface
  rep := functionRep

private noncomputable def argumentInterface :
    Shape.Interface RootContext domain :=
  topInterface RootContext

/-! ## Exact one-scope application -/

noncomputable def exactResult :
    Slot RootContext (CodomainSource.open ArgumentPath) :=
  applyExact ArgumentPath functionInterface (.top _) argumentInterface

noncomputable def exactResult_hasType :
    Exp.HasType RootContext exactResult.interface.package
      exactResult.shape.inputTy :=
  exactResult.interface.package_hasType

/-! ## Composed focused application -/

private def outerFields : Telescope [] := .var .top .nil

private noncomputable def oneFieldArguments (base : Ctx sig) :
    Telescope.Args base (.var .top .nil : Telescope sig) :=
  .var topPayload (topPayload_hasType base) .nil

private noncomputable def oneFieldPackage (base : Ctx sig) : Exp sig :=
  Telescope.pack (oneFieldArguments base)

private noncomputable def oneFieldPackage_hasType (base : Ctx sig) :
    Exp.HasType base (oneFieldPackage base)
      ((.var .top .nil : Telescope sig).existsTy) :=
  Telescope.pack_hasType (oneFieldArguments base)

private abbrev OuterContext : Ctx outerFields.scope :=
  outerFields.context RootContext

private noncomputable def outerFocus : Focus RootContext OuterContext :=
  (Focus.root RootContext).openTelescope outerFields
    (oneFieldPackage RootContext) (oneFieldPackage_hasType RootContext)

private def innerFields : Telescope outerFields.scope := .var .top .nil

private abbrev InnerContext : Ctx innerFields.scope :=
  innerFields.context OuterContext

private noncomputable def innerFocus : Focus OuterContext InnerContext :=
  (Focus.root OuterContext).openTelescope innerFields
    (oneFieldPackage OuterContext) (oneFieldPackage_hasType OuterContext)

/-- A material application under both an already exposed function focus and
a separate telescope opened while supplying the exact checked Top argument. -/
noncomputable def focusedResult :
    Slot RootContext (CodomainSource.open ArgumentPath) :=
  let outerMapping := outerFields.weaken
  let outerTyped := outerFields.weaken_typed RootContext
  let domainAt := domain.rename outerMapping
  let codomainAt := Function.renameCodomain domain codomain outerMapping
  let functionInterfaceAt : Shape.Interface OuterContext
      (.stable (Function.plan domainAt codomainAt)) := by
    simpa only [Shape.rename, Function.plan_rename] using
      functionInterface.rename outerMapping outerTyped
  let codomainRepAt := (Rep.top (domain.context RootContext) :
    Rep (domain.context RootContext) CodomainSource codomain).targetRename
      (domain.liftRename outerMapping)
      (domain.liftRename_typed outerTyped)
  let checkedArgument := topInterface InnerContext
  applyFocused outerFocus innerFocus ArgumentPath functionInterfaceAt
    codomainRepAt (by
      simpa only [domainAt, domain, Shape.rename, Top.plan_rename] using
        checkedArgument)

/-- The result is sealed locally and then reclosed through both focus
histories; neither target scope escapes. -/
theorem focusedResult_isClosed :
    match focusedResult.shape with
    | .opaque _ => True
    | .stable _ => False := by
  trivial

noncomputable def focusedResult_hasType :
    Exp.HasType RootContext focusedResult.interface.package
      focusedResult.shape.inputTy :=
  focusedResult.interface.package_hasType

end LambdaPToFCo.Direct.MaterialApplicationRegression
