import LambdaPToFCo.Direct.Formation
import LambdaPToFCo.Direct.Relation

/-!
# Sealed contextual alignment for direct subtyping

Dependent pair and function rules compare member types under different
source binder contexts.  This compiler-local scope retains both exact formed
environments and one exact relation for each pair of corresponding slots.
The relation is oriented from the endpoint selected by `ProofSide` to the
opposite endpoint: pair members use the source side, while function
codomains use the target side.

The scope constructor is sealed.  A scope is created only by aliasing one
root environment or by extending an existing scope with the exact two
interfaces and head relation available in a structural continuation.  This
is the contextual coherence needed by literal reflexivity and path rules; it
does not compare arbitrary independently constructed formations.
-/

namespace LambdaPToFCo.Direct.Internal.SubtypingScope

open SystemFCo
open Representation
open LambdaPToFCo.Direct.Internal.Formation

abbrev FormedEnv {n : Nat} {sig : Sig}
    (sourceContext : LambdaPFC.Ctx n) (targetContext : Ctx sig) :=
  LambdaPToFCo.Direct.Internal.Formation.Env sourceContext targetContext

abbrev FormedSlot {n : Nat} {sig : Sig}
    (sourceContext : LambdaPFC.Ctx n) (targetContext : Ctx sig)
    (sourceType : LambdaPFC.Ty n) :=
  LambdaPToFCo.Direct.Internal.Formation.Slot sourceContext targetContext
    sourceType

/-- Rename the two source-syntax indices of one relation independently.
Target programs and shapes are unchanged. -/
private noncomputable def relationSourceRename
    {base : Ctx sig}
    {sourceType targetType : LambdaPFC.Ty n}
    {source target : Shape sig}
    (relation : Relation base sourceType targetType source target)
    (sourceMapping targetMapping : LambdaPFC.FinFun n m) :
    Relation base (sourceType.rename sourceMapping)
      (targetType.rename targetMapping) source target where
  sourceRep := relation.sourceRep.sourceRename sourceMapping
  targetRep := relation.targetRep.sourceRename targetMapping
  conversion := relation.conversion
  interfaceMap := relation.interfaceMap

/-- One sealed alignment of endpoint-specific formed environments. -/
structure Scope
    (sourceContext targetContext : LambdaPFC.Ctx n)
    (side : ProofSide) (base : Ctx sig) : Type where
  private mk ::
  source : FormedEnv sourceContext base
  target : FormedEnv targetContext base
  aligned : match side with
    | .source => (index : Fin n) ->
        Relation base (sourceContext.lookup index)
          (targetContext.lookup index)
          (source.lookup index).shape (target.lookup index).shape
    | .target => (index : Fin n) ->
        Relation base (targetContext.lookup index)
          (sourceContext.lookup index)
          (target.lookup index).shape (source.lookup index).shape

namespace Scope

/-- Ignore an argument and return the package retained by the exact
proof-side interface.

This is the value-specific lower leg needed to package a distinguished
mapped binder value.  It is not an inverse to the aligned source relation and
does not assert source-level equivalence. -/
private noncomputable def valueSpecificLower
    {base : Ctx sig} {shape : Shape sig}
    (interface : Shape.Interface base shape) (source : Ty sig) :
    Conversion base source shape.inputTy :=
  let typed := Rename.Typed.weaken base (.var source)
  Conversion.ofFunction
    (Adapter.ofBody source
      (interface.package.rename (Rename.weaken .var)))
    (Adapter.ofBody_hasType (by
      simpa only [Ty.weaken, Shape.inputTy_rename] using
        interface.package_hasType.rename typed))

/-- Operational qualification for `valueSpecificLower`: applying it to a
value takes one ordinary System FCo beta step to the retained proof-side
package.  No inverse or round-trip law is claimed. -/
private theorem valueSpecificLower_beta
    {base : Ctx sig} {shape : Shape sig}
    (interface : Shape.Interface base shape) (source : Ty sig)
    (argument : Exp sig) (argumentValue : Exp.IsValue argument) :
    Exp.Step
      (Adapter.apply
        (valueSpecificLower interface source).function argument)
      interface.package := by
  change Exp.Step
    (.app (.abs source
      (interface.package.rename (Rename.weaken .var))) argument)
    interface.package
  have step := Exp.Step.beta (parameter := source)
    (body := interface.package.rename (Rename.weaken .var)) argumentValue
  have cancel := interface.package.weaken_subst_cancel
    (Subst.openVar argument) (Subst.weakenAsSubst_comp_openVar argument)
  change
    (interface.package.rename (Rename.weaken .var)).subst
      (Subst.openVar argument) = interface.package at cancel
  rw [cancel] at step
  exact step

/-- Create a contextual alignment by aliasing one exact formed root
environment at both endpoints. -/
noncomputable def root
    {sourceContext : LambdaPFC.Ctx n} {base : Ctx sig}
    (environment : FormedEnv sourceContext base)
    (side : ProofSide) : Scope sourceContext sourceContext side base := by
  cases side with
  | source =>
      exact .mk environment environment (fun index =>
        Relation.refl (environment.lookup index).formation.rep)
  | target =>
      exact .mk environment environment (fun index =>
        Relation.refl (environment.lookup index).formation.rep)

/-- Reindex both formed environments and every aligned relation through one
typed target renaming. -/
noncomputable def targetRename
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    (scope : Scope sourceContext targetContext side sourceBase)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceBase targetBase mapping) :
    Scope sourceContext targetContext side targetBase := by
  cases side with
  | source =>
      exact .mk
        (scope.source.targetRename mapping typed)
        (scope.target.targetRename mapping typed)
        (fun index => (scope.aligned index).targetRename mapping typed)
  | target =>
      exact .mk
        (scope.source.targetRename mapping typed)
        (scope.target.targetRename mapping typed)
        (fun index => (scope.aligned index).targetRename mapping typed)

/-- The exact two aligned slot interfaces determine the bridge needed to
retarget their singleton packages.  The relation supplies the forward leg in
the proof-side orientation; `valueSpecificLower` supplies only the
value-specific opposite leg. -/
private noncomputable def singletonBridge
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base)
    (index : Fin n) :
    Conversion.Bridge base (scope.source.lookup index).shape.inputTy
      (scope.target.lookup index).shape.inputTy := by
  cases side with
  | source =>
      exact {
        leftToRight := (scope.aligned index).conversion
        rightToLeft := valueSpecificLower
          (scope.source.lookup index).interface
          (scope.target.lookup index).shape.inputTy
      }
  | target =>
      exact {
        leftToRight := valueSpecificLower
          (scope.target.lookup index).interface
          (scope.source.lookup index).shape.inputTy
        rightToLeft := (scope.aligned index).conversion
      }

/-- Contextual reflexivity of a variable singleton under an aligned scope.
The endpoint binder shapes may genuinely differ. -/
noncomputable def reflSingletonVariable
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base)
    (index : Fin n) :
    Relation base (.Single (.var index)) (.Single (.var index))
      (.stable (Single.plan
        (scope.source.lookup index).shape.inputTy))
      (.stable (Single.plan
        (scope.target.lookup index).shape.inputTy)) :=
  Relation.ofConversion
    (.singleton base (.var index)
      (scope.source.lookup index).shape.inputTy)
    (.singleton base (.var index)
      (scope.target.lookup index).shape.inputTy)
    (Conversion.Singleton.retarget base
      (scope.source.lookup index).shape.inputTy
      (scope.target.lookup index).shape.inputTy
      (singletonBridge scope index))

/-- Extend a source-oriented scope in the exact common continuation of a
dependent pair's first-component interface map. -/
noncomputable def extendPair
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (scope : Scope sourceContext targetContext .source base)
    {sourceType targetType : LambdaPFC.Ty n}
    {sourceShape targetShape : Shape sig}
    (sourceInterface : Shape.Interface base sourceShape)
    (sourceFormation : Formation sourceContext base sourceType sourceShape)
    (targetInterface : Shape.Interface base targetShape)
    (targetFormation : Formation targetContext base targetType targetShape)
    (head : Relation base sourceType targetType sourceShape targetShape) :
    Scope (sourceContext.snoc sourceType)
      (targetContext.snoc targetType) .source base := by
  let sourceHead : FormedSlot (sourceContext.snoc sourceType) base
      sourceType.weaken := {
    shape := sourceShape
    interface := sourceInterface
    formation := sourceFormation.sourceWeaken sourceType
  }
  let targetHead : FormedSlot (targetContext.snoc targetType) base
      targetType.weaken := {
    shape := targetShape
    interface := targetInterface
    formation := targetFormation.sourceWeaken targetType
  }
  let sourceEnvironment : FormedEnv
      (sourceContext.snoc sourceType) base := {
    lookup := Fin.cases sourceHead (fun older =>
      { shape := (scope.source.lookup older).shape
        interface := (scope.source.lookup older).interface
        formation := (scope.source.lookup older).formation.sourceWeaken
          sourceType })
  }
  let targetEnvironment : FormedEnv
      (targetContext.snoc targetType) base := {
    lookup := Fin.cases targetHead (fun older =>
      { shape := (scope.target.lookup older).shape
        interface := (scope.target.lookup older).interface
        formation := (scope.target.lookup older).formation.sourceWeaken
          targetType })
  }
  apply Scope.mk sourceEnvironment targetEnvironment
  intro index
  refine Fin.cases ?_ (fun older => ?_) index
  · simpa only [LambdaPFC.Ctx.lookup, sourceEnvironment, targetEnvironment,
      Fin.cases_zero] using
      relationSourceRename head LambdaPFC.FinFun.weaken
        LambdaPFC.FinFun.weaken
  · simp only [LambdaPFC.Ctx.lookup, sourceEnvironment, targetEnvironment,
      Fin.cases_succ, LambdaPFC.Ty.weaken]
    change Relation base
      ((sourceContext.lookup older).rename LambdaPFC.FinFun.weaken)
      ((targetContext.lookup older).rename LambdaPFC.FinFun.weaken)
      (scope.source.lookup older).shape (scope.target.lookup older).shape
    exact relationSourceRename (scope.aligned older)
      LambdaPFC.FinFun.weaken LambdaPFC.FinFun.weaken

/-- Extend a target-oriented scope in the exact common continuation of a
dependent function's reversed-domain interface map. -/
noncomputable def extendFunction
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (scope : Scope sourceContext targetContext .target base)
    {sourceType targetType : LambdaPFC.Ty n}
    {sourceShape targetShape : Shape sig}
    (sourceInterface : Shape.Interface base sourceShape)
    (sourceFormation : Formation sourceContext base sourceType sourceShape)
    (targetInterface : Shape.Interface base targetShape)
    (targetFormation : Formation targetContext base targetType targetShape)
    (head : Relation base targetType sourceType targetShape sourceShape) :
    Scope (sourceContext.snoc sourceType)
      (targetContext.snoc targetType) .target base := by
  let sourceHead : FormedSlot (sourceContext.snoc sourceType) base
      sourceType.weaken := {
    shape := sourceShape
    interface := sourceInterface
    formation := sourceFormation.sourceWeaken sourceType
  }
  let targetHead : FormedSlot (targetContext.snoc targetType) base
      targetType.weaken := {
    shape := targetShape
    interface := targetInterface
    formation := targetFormation.sourceWeaken targetType
  }
  let sourceEnvironment : FormedEnv
      (sourceContext.snoc sourceType) base := {
    lookup := Fin.cases sourceHead (fun older =>
      { shape := (scope.source.lookup older).shape
        interface := (scope.source.lookup older).interface
        formation := (scope.source.lookup older).formation.sourceWeaken
          sourceType })
  }
  let targetEnvironment : FormedEnv
      (targetContext.snoc targetType) base := {
    lookup := Fin.cases targetHead (fun older =>
      { shape := (scope.target.lookup older).shape
        interface := (scope.target.lookup older).interface
        formation := (scope.target.lookup older).formation.sourceWeaken
          targetType })
  }
  apply Scope.mk sourceEnvironment targetEnvironment
  intro index
  refine Fin.cases ?_ (fun older => ?_) index
  · simpa only [LambdaPFC.Ctx.lookup, sourceEnvironment, targetEnvironment,
      Fin.cases_zero] using
      relationSourceRename head LambdaPFC.FinFun.weaken
        LambdaPFC.FinFun.weaken
  · simp only [LambdaPFC.Ctx.lookup, sourceEnvironment, targetEnvironment,
      Fin.cases_succ, LambdaPFC.Ty.weaken]
    change Relation base
      ((targetContext.lookup older).rename LambdaPFC.FinFun.weaken)
      ((sourceContext.lookup older).rename LambdaPFC.FinFun.weaken)
      (scope.target.lookup older).shape (scope.source.lookup older).shape
    exact relationSourceRename (scope.aligned older)
      LambdaPFC.FinFun.weaken LambdaPFC.FinFun.weaken

end Scope

/-- One exact derivation cut under a sealed contextual alignment.  Endpoint
formations retain their own source-context indices. -/
structure CutView
    {n : Nat} {sig : Sig} {base : Ctx sig}
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide}
    (scope : Scope sourceContext targetContext side base)
    {sourceType targetType : LambdaPFC.Ty n}
    (_derivation : LambdaPFC.Tau.Sub
      (side.choose sourceContext targetContext)
      (.ty sourceType) (.ty targetType))
    (source target : Shape sig) : Type where
  private mk ::
  sourceFormation : Formation sourceContext base sourceType source
  targetFormation : Formation targetContext base targetType target
  relation : Relation base sourceType targetType source target

namespace CutView

/-- Package an already-derived exact relation with its endpoint-specific
formations.  This does not derive coherence between arbitrary formations. -/
noncomputable def ofRelation
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {base : Ctx sig}
    {sourceType targetType : LambdaPFC.Ty n}
    {derivation : LambdaPFC.Tau.Sub
      (side.choose sourceContext targetContext)
      (.ty sourceType) (.ty targetType)}
    {source target : Shape sig}
    {scope : Scope sourceContext targetContext side base}
    (sourceFormation : Formation sourceContext base sourceType source)
    (targetFormation : Formation targetContext base targetType target)
    (relation : Relation base sourceType targetType source target) :
    CutView scope derivation source target :=
  .mk sourceFormation targetFormation relation

/-- Reindex an exact cut and its sealed scope through one typed target
renaming. -/
noncomputable def targetRename
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    {sourceType targetType : LambdaPFC.Ty n}
    {derivation : LambdaPFC.Tau.Sub
      (side.choose sourceContext targetContext)
      (.ty sourceType) (.ty targetType)}
    {source target : Shape sourceSig}
    {scope : Scope sourceContext targetContext side sourceBase}
    (cut : CutView scope derivation source target)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceBase targetBase mapping) :
    CutView (scope.targetRename mapping typed) derivation
      (source.rename mapping) (target.rename mapping) :=
  .mk
    (cut.sourceFormation.targetRename mapping typed)
    (cut.targetFormation.targetRename mapping typed)
    (cut.relation.targetRename mapping typed)

end CutView

end LambdaPToFCo.Direct.Internal.SubtypingScope
