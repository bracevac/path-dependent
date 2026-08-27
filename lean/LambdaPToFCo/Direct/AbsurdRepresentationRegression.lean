import LambdaPToFCo.Direct.Absurd
import LambdaPToFCo.Direct.MaterialTermPath

/-!
# Persistent unreachable-representation regressions

One actual target term of type `forall X. X` represents an unreachable value
at an arbitrary source type, including a type with no source Wf derivation.
The equations below pin its target transports, dependent instantiation, and
structural path behavior.  In particular, `fst` and interval `sel_r` reuse the
same Bottom term rather than manufacturing proper or interval packages.
-/

namespace LambdaPToFCo.Direct.AbsurdRepresentationRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation

private def Bad : LambdaPFC.Ty 0 :=
  .Fun .Top (.Single (.fst (.var 0)))

/-- The codomain asks for `fst` of a precise Top variable, so `Bad` has no
source well-formedness derivation. -/
def bad_not_wf :
    LambdaPFC.Tau.Wf LambdaPFC.Ctx.nil (.ty Bad) -> Empty := by
  intro wf
  cases wf with
  | «fun» _ codomainWf =>
      cases codomainWf with
      | path typing =>
          cases typing with
          | fst receiver => cases receiver

private abbrev TargetContext : Ctx ([] ,, .var) :=
  Ctx.empty.bindVar Adapter.bottomTy

private def bottomValue : Exp ([] ,, .var) :=
  .var .here

private noncomputable def bottomValue_hasType :
    Exp.HasType TargetContext bottomValue
      (Adapter.bottomTy : Ty ([] ,, .var)) := by
  have variableTyping : Exp.HasType TargetContext bottomValue
      ((Adapter.bottomTy : Ty []).weaken .var) :=
    .var Ctx.Lookup.here
  exact variableTyping

/-- No Wf premise is needed to put the ill-formed source type in a raw Slot. -/
noncomputable def badSlot : Slot TargetContext Bad :=
  Slot.absurd bottomValue bottomValue_hasType

theorem bad_slot_retains_bottom :
    badSlot.expression = bottomValue :=
  rfl

theorem bad_rep_is_absurd :
    match badSlot.rep with
    | .absurd retained _ => retained = bottomValue
    | _ => False := by
  rfl

noncomputable def fromAbsurdRelation :
    LambdaPToFCo.Direct.Internal.Relation TargetContext Bad
      (.Top : LambdaPFC.Ty 0) (.opaque Adapter.bottomTy)
      (.stable (Top.plan ([] ,, .var))) :=
  LambdaPToFCo.Direct.Internal.Relation.fromAbsurd
    bottomValue bottomValue_hasType (.top TargetContext)

noncomputable def toAbsurdRelation :
    LambdaPToFCo.Direct.Internal.Relation TargetContext
      (.Top : LambdaPFC.Ty 0) Bad (.stable (Top.plan ([] ,, .var)))
      (.opaque Adapter.bottomTy) :=
  LambdaPToFCo.Direct.Internal.Relation.toAbsurd
    (.top TargetContext) bottomValue bottomValue_hasType

/-- Both unreachable crossings are sealed ordinary target functions with
separate typing derivations. -/
noncomputable def fromAbsurd_function_hasType :
    Exp.HasType TargetContext fromAbsurdRelation.conversion.function
      (.arrow Adapter.bottomTy (Top.plan ([] ,, .var)).inputTy) :=
  fromAbsurdRelation.conversion.functionTyping

noncomputable def toAbsurd_function_hasType :
    Exp.HasType TargetContext toAbsurdRelation.conversion.function
      (.arrow (Top.plan ([] ,, .var)).inputTy Adapter.bottomTy) :=
  toAbsurdRelation.conversion.functionTyping

/-! ## Target transport and dependent instantiation -/

private abbrev ExtendedContext : Ctx (([] ,, .var) ,, .var) :=
  TargetContext.bindVar .top

private def targetWeakening : Rename ([] ,, .var) (([] ,, .var) ,, .var) :=
  Rename.weaken .var

private def targetWeakening_typed :
    Rename.Typed TargetContext ExtendedContext targetWeakening :=
  Rename.Typed.weaken TargetContext (.var .top)

noncomputable def renamedBadSlot : Slot ExtendedContext Bad :=
  badSlot.targetRename targetWeakening targetWeakening_typed

theorem target_rename_retains_bottom :
    match renamedBadSlot.rep with
    | .absurd retained _ => retained = bottomValue.rename targetWeakening
    | _ => False := by
  rfl

private def topPayload : Exp ([] ,, .var) :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

private noncomputable def topPayload_hasType :
    Exp.HasType TargetContext topPayload .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

private def targetOpening : Subst (([] ,, .var) ,, .var) ([] ,, .var) :=
  Subst.openVar topPayload

private noncomputable def targetOpening_typed :
    Subst.Typed ExtendedContext TargetContext targetOpening :=
  Subst.Typed.openVar topPayload_hasType

noncomputable def substitutedBadSlot : Slot TargetContext Bad := by
  simpa only [Shape.rename, Shape.subst, Bot.bottomTy_rename,
    Bot.bottomTy_subst] using
    renamedBadSlot.targetSubst targetOpening targetOpening_typed

theorem target_subst_restores_bottom :
    match substitutedBadSlot.rep with
    | .absurd retained _ => retained = bottomValue
    | _ => False := by
  rfl

private def owner : Shape ([] ,, .var) := .opaque .top

private noncomputable def ownerInterface :
    Shape.Interface TargetContext owner where
  arguments := .var topPayload topPayload_hasType .nil

private def emptySourceSubstitution : LambdaPFC.PathSubst 0 0 :=
  fun index => Fin.elim0 index

/-- `Rep.instantiate` performs the same source and target substitutions while
preserving the unreachable marker and its actual Bottom payload. -/
noncomputable def instantiatedBadRep :
    Rep TargetContext (Bad.subst emptySourceSubstitution)
      ((Shape.opaque Adapter.bottomTy).subst ownerInterface.substitution) :=
  Rep.instantiate (owner := owner) renamedBadSlot.rep ownerInterface
    emptySourceSubstitution

theorem instantiate_retains_bottom :
    match instantiatedBadRep with
    | .absurd retained _ => retained = bottomValue
    | _ => False := by
  rfl

/-! ## Structural paths through an unreachable pair -/

private abbrev Label : LambdaPFC.Name := 11

private abbrev PairSource : LambdaPFC.Ty 0 :=
  .Pair Bad Label (.intv .Bot .Top)

private abbrev SourceContext : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc PairSource

private abbrev ReceiverPath : LambdaPFC.Path 1 := .var 0

private noncomputable def receiver :
    Slot TargetContext (SourceContext.lookup 0) :=
  Slot.absurd bottomValue bottomValue_hasType

private noncomputable def environment : Env SourceContext TargetContext where
  lookup index := Fin.cases receiver (fun older => Fin.elim0 older) index

private def receiverTyping :
    LambdaPFC.Path.Ty SourceContext ReceiverPath
      (.ty (SourceContext.lookup 0)) :=
  .var

private def firstTyping :
    LambdaPFC.Path.Ty SourceContext (.fst ReceiverPath)
      (.ty Bad.weaken) :=
  receiverTyping.fst

private def intervalTyping :
    LambdaPFC.Path.Ty SourceContext (.sel ReceiverPath Label)
      (.intv .Bot .Top) := by
  simpa only [LambdaPFC.Tau.open] using receiverTyping.sel_r

/-- `fst` does not inspect a fictitious pair package.  It returns the exact
same Bottom term at the (ill-Wf) advertised first-component type. -/
noncomputable def projectedFirst : Slot TargetContext Bad.weaken :=
  LambdaPToFCo.Direct.Internal.MaterialTermPath.materialize
    firstTyping environment

theorem fst_retains_bottom :
    projectedFirst.expression = bottomValue :=
  rfl

theorem fst_rep_is_absurd :
    match projectedFirst.rep with
    | .absurd retained _ => retained = bottomValue
    | _ => False := by
  rfl

private noncomputable def projectedInterval :
    LambdaPToFCo.Direct.Internal.Wf.View TargetContext
      (.intv (.Bot : LambdaPFC.Ty 1) .Top) :=
  LambdaPToFCo.Direct.Internal.MaterialPath.materialize
    intervalTyping environment

private noncomputable def projectedBounds :
    LambdaPToFCo.Direct.Internal.Wf.Interval TargetContext
      (.Bot : LambdaPFC.Ty 1) .Top := by
  cases projectedInterval with
  | interval result => exact result

theorem interval_endpoints_are_bottom :
    projectedBounds.lower = .opaque Adapter.bottomTy ∧
      projectedBounds.upper = .opaque Adapter.bottomTy := by
  exact ⟨rfl, rfl⟩

theorem interval_endpoints_retain_bottom :
    match projectedBounds.lowerRep, projectedBounds.upperRep with
    | .absurd lower _ , .absurd upper _ =>
        lower = bottomValue ∧ upper = bottomValue
    | _, _ => False := by
  exact ⟨rfl, rfl⟩

/-- The package-aware interpreter exposes Bottom as both endpoint shapes and
the selected identity; both bound functions are ordinary identity arrows. -/
private noncomputable def intervalProbe : Prop :=
  LambdaPToFCo.Direct.Internal.MaterialTermPath.compileWith
    intervalTyping environment (fun _focus _environment view => by
      cases view with
      | interval interval =>
          exact
            (interval.lowerFunction =
                Adapter.identity Adapter.bottomTy) ∧
            (interval.upperFunction =
                Adapter.identity Adapter.bottomTy) ∧
            match interval.lowerRep, interval.upperRep with
            | .absurd _ _, .absurd _ _ => True
            | _, _ => False)

theorem interval_selection_short_circuits : intervalProbe := by
  exact ⟨rfl, rfl, trivial⟩

end LambdaPToFCo.Direct.AbsurdRepresentationRegression
