import LambdaPToFCo.Direct.SubtypingPath

/-!
# Formation-aware path subtyping regressions

The widening receiver is a dependent pair carrying two explicit Top
packages.  Its selected member crosses the full appended representation
telescope, so both widening endpoints are genuinely closed at the root.  The
beta check records that the conversion returns that exact materialized member
package.  A second small environment exercises literal singleton symmetry.
-/

namespace LambdaPToFCo.Direct.SubtypingPathRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal.Formation
open LambdaPToFCo.Direct.Internal.FormedPath
open LambdaPToFCo.Direct.Internal.SubtypingPath

private abbrev Label : LambdaPFC.Name := 0

private abbrev PairSource : LambdaPFC.Ty 0 :=
  .Pair .Top Label (.ty .Top)

private abbrev SourceContext : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc PairSource

private abbrev TargetContext : Ctx [] := Ctx.empty

private def topPayload {sig : Sig} : Exp sig :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

private noncomputable def topPayload_hasType
    (context : Ctx sig) :
    Exp.HasType context (topPayload : Exp sig) .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

private noncomputable def topInterface
    (context : Ctx sig) :
    Shape.Interface context (.stable (Top.plan sig)) where
  arguments := Top.arguments .top topPayload (topPayload_hasType context)

private def first : Shape [] := .stable (Top.plan [])

private def member : Shape first.scope :=
  .stable (Top.plan first.scope)

private noncomputable def memberArguments :
    Telescope.Args TargetContext
      (member.binders.subst
        (topInterface TargetContext).substitution) := by
  have equal :
      member.binders.subst (topInterface TargetContext).substitution =
        (.stable (Top.plan []) : Shape []).binders := by
    change ((Top.plan first.scope).subst
      (topInterface TargetContext).substitution).telescope =
        (Top.plan []).telescope
    exact congrArg Package.Plan.telescope
      (Top.plan_subst (topInterface TargetContext).substitution)
  exact equal.symm ▸ (topInterface TargetContext).arguments

private noncomputable def receiverInterface :
    Shape.Interface TargetContext
      (.stable (Pair.Proper.plan first member)) where
  arguments := Pair.Proper.exactArguments first member
    (topInterface TargetContext).arguments memberArguments

private noncomputable def receiverFormation :
    Formation SourceContext TargetContext (SourceContext.lookup 0)
      (.stable (Pair.Proper.plan first member)) := by
  change Formation SourceContext TargetContext
    (.Pair .Top Label (.ty .Top))
    (.stable (Pair.Proper.plan first member))
  exact .properPair .top .top

private noncomputable def receiver :
    Slot SourceContext TargetContext (SourceContext.lookup 0) where
  shape := .stable (Pair.Proper.plan first member)
  interface := receiverInterface
  formation := receiverFormation

private noncomputable def environment :
    Env SourceContext TargetContext where
  lookup index := Fin.cases receiver (fun older => Fin.elim0 older) index

private def receiverTyping :
    LambdaPFC.Path.Ty SourceContext (.var 0)
      (.ty (SourceContext.lookup 0)) :=
  .var

private def memberTyping :
    LambdaPFC.Path.Ty SourceContext (.sel (.var 0) Label) (.ty .Top) := by
  simpa only [LambdaPFC.Tau.open] using receiverTyping.sel_r

/-- Widening is compiled from the same nested formed path at both endpoints. -/
noncomputable def nestedWiden :=
  widen memberTyping environment

/-- Singleton introduction is reclosed through an opaque carrier. -/
theorem nestedWiden_source_isClosed :
    match (materializeSingleton memberTyping environment).shape with
    | .opaque _ => True
    | .stable _ => False := by
  trivial

/-- The selected target member is independently reclosed through the same
real receiver package. -/
theorem nestedWiden_target_isClosed :
    match (materialize memberTyping environment).shape with
    | .opaque _ => True
    | .stable _ => False := by
  trivial

private def betaArgument : Exp [] := .abs .top (.var .here)

private theorem betaArgument_isValue : Exp.IsValue betaArgument :=
  .abs

/-- The widening adapter reduces to the exact selected member package, not a
canonical replacement interface. -/
theorem nestedWiden_returns_exact_payload :
    Exp.Step
      (Adapter.apply nestedWiden.relation.conversion.function betaArgument)
      (materialize memberTyping environment).interface.package := by
  exact widen_beta memberTyping environment betaArgument
    betaArgument_isValue

/-! ## Literal singleton symmetry -/

private abbrev SymmetryContext : LambdaPFC.Ctx 2 :=
  (LambdaPFC.Ctx.nil.snoc .Top).snoc (.Single (.var 0))

private def referentPath : LambdaPFC.Path 2 := .var 1

private def selectedPath : LambdaPFC.Path 2 := .var 0

private noncomputable def referentSlot :
    Slot SymmetryContext TargetContext
      (SymmetryContext.lookup (1 : Fin 2)) where
  shape := .stable (Top.plan [])
  interface := topInterface TargetContext
  formation := .top

private noncomputable def selectedSlot :
    Slot SymmetryContext TargetContext
      (SymmetryContext.lookup (0 : Fin 2)) := by
  change Slot SymmetryContext TargetContext (.Single referentPath)
  exact {
    shape := .stable (Single.plan (Top.plan []).inputTy)
    interface := {
      arguments := Single.exactArguments (Top.plan []).inputTy
        referentSlot.interface.package
        referentSlot.interface.package_hasType
    }
    formation := .singleton (.var : LambdaPFC.Path.Ty SymmetryContext
      referentPath (.ty .Top)) referentSlot.interface
      referentSlot.formation
  }

private noncomputable def symmetryEnvironment :
    Env SymmetryContext TargetContext where
  lookup index := Fin.cases selectedSlot
    (fun older => Fin.cases referentSlot
      (fun impossible => Fin.elim0 impossible) older) index

private def symmetryTyping :
    LambdaPFC.Path.Ty SymmetryContext selectedPath
      (.ty (.Single referentPath)) := by
  exact .var

/-- Symmetry materializes the selected singleton and then introduces the
singleton of its selecting path. -/
noncomputable def variableSymmetry :=
  symm symmetryTyping symmetryEnvironment

theorem variableSymmetry_returns_exact_payload :
    Exp.Step
      (Adapter.apply variableSymmetry.relation.conversion.function
        betaArgument)
      (materializeSingleton symmetryTyping
        symmetryEnvironment).interface.package := by
  exact symm_beta symmetryTyping symmetryEnvironment betaArgument
    betaArgument_isValue

end LambdaPToFCo.Direct.SubtypingPathRegression
