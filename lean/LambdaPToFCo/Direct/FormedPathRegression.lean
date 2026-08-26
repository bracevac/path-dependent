import LambdaPToFCo.Direct.FormedPath

/-!
# Runtime formed-path regression

The receiver below is a proper pair whose interface is assembled from two
explicit Top payloads.  It is deliberately not the canonical interface from
an elimination scope.  Projecting either component must therefore eliminate
this exact receiver package and reclose the selected runtime Slot at the root.
-/

namespace LambdaPToFCo.Direct.FormedPathRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal.Formation
open LambdaPToFCo.Direct.Internal.FormedPath

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

/-- The exact receiver interface contains the explicit `topPayload` twice;
it is not `Shape.Interface.canonical`. -/
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

private def firstTyping :
    LambdaPFC.Path.Ty SourceContext (.fst (.var 0)) (.ty .Top) := by
  exact receiverTyping.fst

private def memberTyping :
    LambdaPFC.Path.Ty SourceContext (.sel (.var 0) Label) (.ty .Top) := by
  simpa only [LambdaPFC.Tau.open] using receiverTyping.sel_r

/-- `fst` opens the actual receiver representation and materializes a closed
root Slot rather than leaking the opened first-component scope. -/
noncomputable def projectedFirst :
    Slot SourceContext TargetContext .Top :=
  materialize firstTyping environment

/-- `sel_r` exercises the full appended pair telescope and recloses its exact
member package at the root. -/
noncomputable def projectedMember :
    Slot SourceContext TargetContext .Top :=
  materialize memberTyping environment

/-- The materialized first component is genuinely reclosed through an opaque
carrier, not replaced by the canonical Top interface. -/
theorem projectedFirst_isClosed :
    match projectedFirst.shape with
    | .opaque _ => True
    | .stable _ => False := by
  trivial

/-- The actual reclosed first package has ordinary unchanged-SystemFCo target
typing at its materialized carrier type. -/
noncomputable def projectedFirst_hasType :
    Exp.HasType TargetContext projectedFirst.interface.package
      projectedFirst.shape.inputTy :=
  projectedFirst.interface.package_hasType

/-- Singleton introduction consumes that exact selected package before the
same focus runner recloses it at the root. -/
noncomputable def projectedMemberSingleton :
    Slot SourceContext TargetContext (.Single (.sel (.var 0) Label)) :=
  materializeSingleton memberTyping environment

noncomputable def projectedMemberSingleton_hasType :
    Exp.HasType TargetContext
      projectedMemberSingleton.interface.package
      projectedMemberSingleton.shape.inputTy :=
  projectedMemberSingleton.interface.package_hasType

end LambdaPToFCo.Direct.FormedPathRegression
