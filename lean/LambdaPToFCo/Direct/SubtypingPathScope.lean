import LambdaPToFCo.Direct.SubtypingScope
import LambdaPToFCo.Direct.AtomicSubtyping

/-!
# Bounded contextual path subtyping

Reflexivity below compares endpoint-specific formations under one sealed
`SubtypingScope.Scope`.  It never identifies independently chosen Shapes.
The single consumer is natural in every target scope, so later structural
cases may open real packages without leaking a hidden target type.

This leaf deliberately exposes only the cases justified by the current
formation interface:

* Top when the target carrier is the canonical Top plan;
* Bottom when the source carrier is the canonical Bottom plan; and
* a variable singleton whose two referents are the aligned Scope slots.

A target `Formation.closed` stores the type-side closure but no root
interface or value packer.  Consequently arbitrary target-closed contextual
reflexivity, and path rules depending on it, remain outside this bounded
layer.  No equality certificate or intermediate dispatch plan is introduced.
-/

namespace LambdaPToFCo.Direct.Internal.SubtypingPathScope

open SystemFCo
open Representation
open Formation
open SubtypingScope

namespace ContextualRefl

/-- The one scope-natural result consumer for contextual reflexivity. -/
abbrev Consumer
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base)
    (answer : Ty sig) (sourceType : LambdaPFC.Ty n)
    (source target : Shape sig) : Type :=
  forall {current : Sig} {currentContext : Ctx current},
    (mapping : Rename sig current) ->
    (typed : Rename.Typed base currentContext mapping) ->
    CutView (scope.targetRename mapping typed)
      (LambdaPFC.Tau.Sub.refl
        (Γ := side.choose sourceContext targetContext)
        (τ := .ty sourceType))
      (source.rename mapping) (target.rename mapping) ->
    Path.Body currentContext (answer.rename mapping)

private noncomputable def here
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {base : Ctx sig}
    {scope : Scope sourceContext targetContext side base}
    {sourceType : LambdaPFC.Ty n}
    {source target : Shape sig}
    (cut : CutView scope
      (LambdaPFC.Tau.Sub.refl
        (Γ := side.choose sourceContext targetContext)
        (τ := .ty sourceType)) source target)
    (answer : Ty sig)
    (consumer : Consumer scope answer sourceType source target) :
    Path.Body base answer := by
  have cutAt := cut.targetRename Rename.id (TypedRename.id base)
  simpa only [Shape.rename_id, Ty.rename_id] using
    consumer Rename.id (TypedRename.id base) cutAt

/-- Contextual Top reflexivity when the target endpoint uses canonical Top.
The source endpoint may be any faithful Top carrier, including an opaque
source closure: erasing observations to canonical Top is sufficient. -/
noncomputable def top
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base)
    {source : Shape sig}
    (sourceFormation : Formation sourceContext base .Top source)
    (targetFormation : Formation targetContext base .Top
      (.stable (Top.plan sig)))
    (answer : Ty sig)
    (consumer : Consumer scope answer .Top source
      (.stable (Top.plan sig))) :
    Path.Body base answer :=
  let relation := (AtomicSubtyping.top {
    shape := source
    rep := sourceFormation.rep
  }).relation
  here (CutView.ofRelation sourceFormation targetFormation relation)
    answer consumer

/-- Contextual Bottom reflexivity when the source endpoint uses canonical
Bottom.  Bottom elimination targets any faithful opposite carrier. -/
noncomputable def bottom
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base)
    (sourceFormation : Formation sourceContext base .Bot
      (.stable (Bot.plan sig)))
    {target : Shape sig}
    (targetFormation : Formation targetContext base .Bot target)
    (answer : Ty sig)
    (consumer : Consumer scope answer .Bot
      (.stable (Bot.plan sig)) target) :
    Path.Body base answer :=
  let relation := (AtomicSubtyping.bot {
    shape := target
    rep := targetFormation.rep
  }).relation
  here (CutView.ofRelation sourceFormation targetFormation relation)
    answer consumer

/-- Contextual reflexivity for the singleton of one aligned variable.
Unlike homogeneous reflexivity, the two singleton plans may mention
genuinely different endpoint binder carriers. -/
noncomputable def singletonVariable
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base)
    (index : Fin n)
    (sourceFormation : Formation sourceContext base
      (.Single (.var index))
      (.stable (Single.plan
        (scope.source.lookup index).shape.inputTy)))
    (targetFormation : Formation targetContext base
      (.Single (.var index))
      (.stable (Single.plan
        (scope.target.lookup index).shape.inputTy)))
    (answer : Ty sig)
    (consumer : Consumer scope answer (.Single (.var index))
      (.stable (Single.plan
        (scope.source.lookup index).shape.inputTy))
      (.stable (Single.plan
        (scope.target.lookup index).shape.inputTy))) :
    Path.Body base answer :=
  here
    (CutView.ofRelation sourceFormation targetFormation
      (scope.reflSingletonVariable index)) answer consumer

end ContextualRefl

/-! ## Exact bounded widening cases -/

/-- The intended total scope-aware widening boundary.  Current exported
constructors inhabit this exact result type only where the supplied target
carrier can be built from the frozen Formation API. -/
abbrev WidenResult
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base)
    {path : LambdaPFC.Path n} {targetType : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty
      (side.choose sourceContext targetContext) path (.ty targetType))
    (source target : Shape sig) : Type :=
  CutView scope (.widen typing) source target

/-- Scope-aware widening whose demanded result is canonical Top.  This is
the exact both-side signature specialized only by the constructible carrier;
the source singleton Formation is otherwise arbitrary. -/
noncomputable def widenTop
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base)
    {path : LambdaPFC.Path n}
    (typing : LambdaPFC.Path.Ty
      (side.choose sourceContext targetContext) path (.ty .Top))
    {source : Shape sig}
    (sourceFormation : Formation sourceContext base (.Single path) source)
    (targetFormation : Formation targetContext base .Top
      (.stable (Top.plan sig))) :
    WidenResult scope typing source (.stable (Top.plan sig)) :=
  CutView.ofRelation sourceFormation targetFormation
    (AtomicSubtyping.top {
      shape := source
      rep := sourceFormation.rep
    }).relation

/-- Target-oriented variable widening across a changed binder.  Contextual
singleton reflexivity first retargets the singleton through the sealed slot
alignment; ordinary singleton elimination then exposes the exact target
slot. -/
noncomputable def widenTargetVariable
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (scope : Scope sourceContext targetContext .target base)
    (index : Fin n)
    (typing : LambdaPFC.Path.Ty targetContext (.var index)
      (.ty (targetContext.lookup index)))
    (sourceFormation : Formation sourceContext base
      (.Single (.var index))
      (.stable (Single.plan
        (scope.source.lookup index).shape.inputTy)))
    (targetFormation : Formation targetContext base
      (targetContext.lookup index) (scope.target.lookup index).shape) :
    WidenResult scope typing
      (.stable (Single.plan
        (scope.source.lookup index).shape.inputTy))
      (scope.target.lookup index).shape := by
  let singleton := scope.reflSingletonVariable index
  let targetSlot := (scope.target.lookup index).erase
  let unwrapped := AtomicSubtyping.widenAt (.var index) targetSlot
  exact CutView.ofRelation sourceFormation targetFormation
    (singleton.trans unwrapped.relation)

end LambdaPToFCo.Direct.Internal.SubtypingPathScope
