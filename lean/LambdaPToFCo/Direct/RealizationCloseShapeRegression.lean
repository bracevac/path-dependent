import LambdaPToFCo.Direct.Realization

/-!
# Exact opaque-Shape realization reclosure

An opaque owner opens one ordinary target variable, not an existential
telescope package.  This gate closes an exact realized inner value through
that owner and retains the resulting root Slot realization.
-/

namespace LambdaPToFCo.Direct.Internal.RealizationCloseShapeRegression

open SystemFCo
open Representation
open Realization

private abbrev SourceContext : LambdaPFC.Ctx 0 := .nil
private abbrev RootContext : Ctx [] := Ctx.empty

private def environment : Env SourceContext RootContext where
  lookup index := Fin.elim0 index

private def topPayload {sig : Sig} : Exp sig :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

private noncomputable def topPayload_hasType (base : Ctx sig) :
    Exp.HasType base (topPayload : Exp sig) .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

private noncomputable def topInterface (base : Ctx sig) :
    Shape.Interface base (.stable (Top.plan sig)) where
  arguments := Top.arguments .top topPayload (topPayload_hasType base)

private def owner : Shape [] := .opaque .top

private noncomputable def inner :
    Slot (owner.context RootContext) (.Top : LambdaPFC.Ty 0) where
  shape := .stable (Top.plan owner.scope)
  interface := topInterface (owner.context RootContext)
  rep := .top _

private noncomputable def openedEnvironment :
    Env SourceContext (owner.context RootContext) :=
  environment.targetRename owner.binders.weaken
    (owner.binders.weaken_typed RootContext)

private noncomputable def innerRealizes :
    Realizes openedEnvironment inner.rep (.value inner.interface) :=
  Realizes.topValue openedEnvironment inner.interface

/-- The exact root Slot produced by eliminating the opaque owner package. -/
noncomputable def closed : Slot RootContext (.Top : LambdaPFC.Ty 0) :=
  MaterialTermPath.SlotMaterializer.closeShape owner topPayload
    (topPayload_hasType RootContext) inner

/-- Positive value evidence follows the same opaque Shape elimination and
the same actual package; no telescope-package premise or equality is used. -/
noncomputable def closedRealizes :
    Realizes environment closed.rep (.value closed.interface) :=
  Realizes.closeShapeValue environment owner topPayload
    (topPayload_hasType RootContext) inner innerRealizes

/-- Reclosure hides the opened value behind the ordinary opaque carrier. -/
theorem closed_isOpaque :
    match closed.shape with
    | .opaque _ => True
    | .stable _ => False := by
  trivial

end LambdaPToFCo.Direct.Internal.RealizationCloseShapeRegression
