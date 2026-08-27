import LambdaPToFCo.Direct.Realization
import LambdaPToFCo.Direct.PairSubtyping

/-!
# Realization regressions

`MaterialView` contains only the pre-extension environments and family
representations which are otherwise hidden by `intervalMemberScopeAt`.
`CallbackView` contains the ephemeral value/demand evidence produced while
the interface map is running.  The target structural realization is built
and consumed in that callback; neither the view nor an Action escapes.
-/

namespace LambdaPToFCo.Direct.Internal.RealizationRegression

open SystemFCo
open Representation
open Realization

/-- Exact pre-substitution data at one material callback root. -/
structure MaterialView
    {n : Nat}
    (sourceContext targetContext : LambdaPFC.Ctx n)
    (sourceFirstType targetFirstType : LambdaPFC.Ty n)
    (sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1))
    (base : Ctx sig)
    (sourceFirst targetFirst : Shape sig)
    (sourceLower sourceUpper : Shape sourceFirst.scope)
    (targetLower targetUpper : Shape targetFirst.scope) : Type where
  sourceEnvironment : Env sourceContext base
  targetEnvironment : Env targetContext base
  sourceFirstRep : Rep base sourceFirstType sourceFirst
  targetFirstRep : Rep base targetFirstType targetFirst
  sourceLowerRep : Rep (sourceFirst.context base)
    sourceLowerType sourceLower
  sourceUpperRep : Rep (sourceFirst.context base)
    sourceUpperType sourceUpper
  targetLowerRep : Rep (targetFirst.context base)
    targetLowerType targetLower
  targetUpperRep : Rep (targetFirst.context base)
    targetUpperType targetUpper

namespace MaterialView

/-- The literal member scope determined by the two actual first interfaces.
Every endpoint representation is the corresponding family representation
after that interface's exact substitution. -/
noncomputable def members
    {n : Nat}
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (view : MaterialView sourceContext targetContext sourceFirstType
      targetFirstType sourceLowerType sourceUpperType targetLowerType
      targetUpperType base sourceFirst targetFirst sourceLower sourceUpper
      targetLower targetUpper)
    (sourceFirstInterface : Shape.Interface base sourceFirst)
    (targetFirstInterface : Shape.Interface base targetFirst) :
    PairSubtyping.IntervalMemberScope sourceContext targetContext
      sourceFirstType targetFirstType sourceLowerType sourceUpperType
      targetLowerType targetUpperType base where
  environments := {
    source := extendAtInterface view.sourceEnvironment sourceFirstType
      sourceFirstInterface view.sourceFirstRep
    target := extendAtInterface view.targetEnvironment targetFirstType
      targetFirstInterface view.targetFirstRep
  }
  source := {
    lower := sourceLower.subst sourceFirstInterface.substitution
    upper := sourceUpper.subst sourceFirstInterface.substitution
    lowerRep := view.sourceLowerRep.targetSubst
      sourceFirstInterface.substitution
      sourceFirstInterface.arguments.substitution_typed
    upperRep := view.sourceUpperRep.targetSubst
      sourceFirstInterface.substitution
      sourceFirstInterface.arguments.substitution_typed
  }
  target := {
    lower := targetLower.subst targetFirstInterface.substitution
    upper := targetUpper.subst targetFirstInterface.substitution
    lowerRep := view.targetLowerRep.targetSubst
      targetFirstInterface.substitution
      targetFirstInterface.arguments.substitution_typed
    upperRep := view.targetUpperRep.targetSubst
      targetFirstInterface.substitution
      targetFirstInterface.arguments.substitution_typed
  }

end MaterialView

/-- Ephemeral evidence available while the material callback is live.
Endpoint demands are indexed by the literal computed member scope, not by
an independently renamed or substituted environment. -/
structure CallbackView
    {n : Nat}
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    (material : MaterialView sourceContext targetContext sourceFirstType
      targetFirstType sourceLowerType sourceUpperType targetLowerType
      targetUpperType base sourceFirst targetFirst sourceLower sourceUpper
      targetLower targetUpper)
    (sourceFirstInterface : Shape.Interface base sourceFirst)
    (targetFirstInterface : Shape.Interface base targetFirst) : Type where
  sourceFirstValue : Realizes material.sourceEnvironment
    material.sourceFirstRep (.value sourceFirstInterface)
  targetFirstValue : Realizes material.targetEnvironment
    material.targetFirstRep (.value targetFirstInterface)
  targetLowerDemand :
    let members := material.members sourceFirstInterface targetFirstInterface
    Realizes members.environments.target members.target.lowerRep .demand
  targetUpperDemand :
    let members := material.members sourceFirstInterface targetFirstInterface
    Realizes members.environments.target members.target.upperRep .demand

namespace CallbackView

/-- The direct Werror gate: construct the target interval pair structurally
inside the callback from the exact predata and post-substitution demands. -/
noncomputable def targetPairValue
    {n : Nat}
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {base : Ctx sig}
    {sourceFirst targetFirst : Shape sig}
    {sourceLower sourceUpper : Shape sourceFirst.scope}
    {targetLower targetUpper : Shape targetFirst.scope}
    {material : MaterialView sourceContext targetContext sourceFirstType
      targetFirstType sourceLowerType sourceUpperType targetLowerType
      targetUpperType base sourceFirst targetFirst sourceLower sourceUpper
      targetLower targetUpper}
    {sourceFirstInterface : Shape.Interface base sourceFirst}
    {targetFirstInterface : Shape.Interface base targetFirst}
    (view : CallbackView material sourceFirstInterface targetFirstInterface)
    (targetWitness : Conversion.Interval.Witness base
      (targetLower.subst targetFirstInterface.substitution)
      (targetUpper.subst targetFirstInterface.substitution)) :
    Realizes material.targetEnvironment
      (intervalPairSlot (label := label) material.targetFirstRep
        material.targetLowerRep material.targetUpperRep targetFirstInterface
        targetWitness).rep
      (.value
        (intervalPairSlot (label := label) material.targetFirstRep
          material.targetLowerRep material.targetUpperRep targetFirstInterface
          targetWitness).interface) := by
  exact Realizes.intervalPairValue material.targetEnvironment
    targetFirstInterface view.targetFirstValue view.targetLowerDemand
    view.targetUpperDemand targetWitness

end CallbackView


/-! ## Literal target transport after retained extension -/

private abbrev TransportBaseSig : Sig := ([] : Sig) ,, .var

private abbrev TransportBaseContext : Ctx TransportBaseSig :=
  Ctx.empty.bindVar Adapter.bottomTy

private abbrev TransportExtendedSig : Sig := TransportBaseSig ,, .var

private abbrev TransportExtendedContext : Ctx TransportExtendedSig :=
  TransportBaseContext.bindVar .top

private def transportTopPayload {sig : Sig} : Exp sig :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

private noncomputable def transportTopPayload_hasType (base : Ctx sig) :
    Exp.HasType base (transportTopPayload : Exp sig) .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

private noncomputable def transportTopInterface (base : Ctx sig) :
    Shape.Interface base (.stable (Top.plan sig)) where
  arguments := Top.arguments .top transportTopPayload
    (transportTopPayload_hasType base)

private noncomputable def transportBaseEnvironment :
    Env (LambdaPFC.Ctx.nil : LambdaPFC.Ctx 0) TransportBaseContext :=
  Env.empty TransportBaseContext

private def transportWeakening :
    Rename TransportBaseSig TransportExtendedSig :=
  Rename.weaken .var

private def transportWeakening_typed :
    Rename.Typed TransportBaseContext TransportExtendedContext
      transportWeakening :=
  Rename.Typed.weaken TransportBaseContext (.var .top)

private noncomputable def transportBaseEndpointDemand :
    Realizes
      (extendAtInterface transportBaseEnvironment (.Top : LambdaPFC.Ty 0)
        (transportTopInterface TransportBaseContext)
        (@Rep.top 0 TransportBaseSig TransportBaseContext))
      (@Rep.bottom 1 TransportBaseSig TransportBaseContext) .demand :=
  Realizes.bottomDemand _

/-- A genuine target weakening transports an endpoint demand through the
literal retained extension, with no environment equality or rebase. -/
noncomputable def targetRenameExtendedDemand :
    Realizes
      (extendAtInterface
        (transportBaseEnvironment.targetRename transportWeakening
          transportWeakening_typed)
        (.Top : LambdaPFC.Ty 0)
        ((transportTopInterface TransportBaseContext).rename
          transportWeakening transportWeakening_typed)
        ((@Rep.top 0 TransportBaseSig TransportBaseContext).targetRename
          transportWeakening transportWeakening_typed))
      ((@Rep.bottom 1 TransportBaseSig TransportBaseContext).targetRename
        transportWeakening transportWeakening_typed)
      .demand :=
  Realizes.targetRenameExtended transportBaseEnvironment
    (transportTopInterface TransportBaseContext)
    (@Rep.top 0 TransportBaseSig TransportBaseContext)
    transportBaseEndpointDemand transportWeakening transportWeakening_typed

private def transportOpening :
    Subst TransportExtendedSig TransportBaseSig :=
  Subst.openVar transportTopPayload

private noncomputable def transportOpening_typed :
    Subst.Typed TransportExtendedContext TransportBaseContext
      transportOpening :=
  Subst.Typed.openVar (transportTopPayload_hasType TransportBaseContext)

private noncomputable def transportExtendedEnvironment :
    Env (LambdaPFC.Ctx.nil : LambdaPFC.Ctx 0) TransportExtendedContext :=
  transportBaseEnvironment.targetRename transportWeakening
    transportWeakening_typed

private noncomputable def transportExtendedFirstInterface :
    Shape.Interface TransportExtendedContext
      ((Shape.stable (Top.plan TransportBaseSig)).rename
        transportWeakening) :=
  (transportTopInterface TransportBaseContext).rename transportWeakening
    transportWeakening_typed

private noncomputable def transportExtendedFirstRep :
    Rep TransportExtendedContext (.Top : LambdaPFC.Ty 0)
      ((Shape.stable (Top.plan TransportBaseSig)).rename
        transportWeakening) :=
  (@Rep.top 0 TransportBaseSig TransportBaseContext).targetRename
    transportWeakening transportWeakening_typed

private noncomputable def transportExtendedEndpointRep :
    Rep TransportExtendedContext (.Bot : LambdaPFC.Ty 1)
      ((Shape.stable (Bot.plan TransportBaseSig)).rename
        transportWeakening) :=
  (@Rep.bottom 1 TransportBaseSig TransportBaseContext).targetRename
    transportWeakening transportWeakening_typed

private noncomputable def transportExtendedEndpointDemand :
    Realizes
      (extendAtInterface transportExtendedEnvironment (.Top : LambdaPFC.Ty 0)
        transportExtendedFirstInterface transportExtendedFirstRep)
      transportExtendedEndpointRep .demand :=
  Realizes.bottomDemand _

/-- A genuine `openVar` target substitution transports the same endpoint
demand through the literal retained extension. -/
noncomputable def targetSubstExtendedDemand :
    Realizes
      (extendAtInterface
        (transportExtendedEnvironment.targetSubst transportOpening
          transportOpening_typed)
        (.Top : LambdaPFC.Ty 0)
        (transportExtendedFirstInterface.targetSubst transportOpening
          transportOpening_typed)
        (transportExtendedFirstRep.targetSubst transportOpening
          transportOpening_typed))
      (transportExtendedEndpointRep.targetSubst transportOpening
        transportOpening_typed)
      .demand :=
  Realizes.targetSubstExtended transportExtendedEnvironment
    transportExtendedFirstInterface transportExtendedFirstRep
    transportExtendedEndpointDemand transportOpening transportOpening_typed


/-! ## Proper-path retained-value bootstrap -/

/-- A nested non-variable proper path uses the public retained-value route;
no private `PathIdentity` constructor or path replay is needed. -/
noncomputable def nestedFirstRetained
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    {receiver : LambdaPFC.Path n}
    {selectedSource : LambdaPFC.Ty n}
    {innerLabel outerLabel : LambdaPFC.Name}
    {innerKind outerKind : LambdaPFC.Kind}
    {innerMember : LambdaPFC.Tau (n + 1) innerKind}
    {outerMember : LambdaPFC.Tau (n + 1) outerKind}
    (typing : LambdaPFC.Path.Ty sourceContext receiver
      (.ty (.Pair (.Pair selectedSource innerLabel innerMember)
        outerLabel outerMember)))
    (environment : Env sourceContext base)
    (selected : Slot base selectedSource) :
    PathIdentity environment typing.fst.fst selected.shape.inputTy :=
  PathIdentity.retained typing.fst.fst environment selected


/-! ## Ordinary application leaf gates -/

private noncomputable def retainedConstant
    {base : Ctx sig} {source target : Ty sig}
    (value : Exp sig) (typing : Exp.HasType base value target) :
    Conversion base source target :=
  Conversion.ofFunction
    (Adapter.ofBody source (value.rename (Rename.weaken .var)))
    (Adapter.ofBody_hasType (by
      simpa only [Ty.weaken] using typing.weaken (.var source)))

/-- The checked `Single q <: P2` action supplies the forward leg; the exact
`q` Slot supplies the value-specific reverse leg. -/
noncomputable def checkedPathBridge
    {n : Nat} {sig : Sig} {base : Ctx sig}
    {path : LambdaPFC.Path n} {precise demanded : LambdaPFC.Ty n}
    (exact : Slot base precise)
    {demandedShape : Shape sig}
    (checked : Relation base (.Single path) demanded
      (.stable (Single.plan exact.shape.inputTy)) demandedShape) :
    Conversion.Bridge base exact.shape.inputTy demandedShape.inputTy where
  leftToRight :=
    (Conversion.Singleton.wrap base exact.shape.inputTy).compose
      checked.conversion
  rightToLeft := retainedConstant exact.interface.package
    exact.interface.package_hasType

/-- Green P1-to-P2 application leaf.  `demandedInterface` is not fabricated:
it is exactly the Interface delivered by `Action.applyValue`'s continuation.
The result is a value-mode singleton, not a bare represented demand. -/
noncomputable def applicationSingleVariable
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base) (index : Fin n)
    {demanded : LambdaPFC.Ty n} {demandedShape : Shape sig}
    (checked : Relation base (.Single (.var index)) demanded
      (.stable (Single.plan
        (environment.lookup index).shape.inputTy)) demandedShape)
    (demandedInterface : Shape.Interface base demandedShape) :
    let selected : Slot base demanded := {
      shape := demandedShape
      interface := demandedInterface
      rep := checked.targetRep
    }
    Realizes environment (singletonSlot (.var index) selected).rep
      (.value (singletonSlot (.var index) selected).interface) := by
  let selected : Slot base demanded := {
    shape := demandedShape
    interface := demandedInterface
    rep := checked.targetRep
  }
  let bridge := checkedPathBridge (environment.lookup index) checked
  let resolution := PathIdentity.across
    (PathIdentity.lookup environment index) bridge
  exact Realizes.singletonValue environment
    (LambdaPFC.Path.Ty.var (Γ := sourceContext) (x := index))
    selected resolution

/-- Later comparison with canonical `Single q` uses the reverse half of the
same applied-action bridge. -/
noncomputable def applicationSingleBackToCanonical
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base) (index : Fin n)
    {demanded : LambdaPFC.Ty n} {demandedShape : Shape sig}
    (checked : Relation base (.Single (.var index)) demanded
      (.stable (Single.plan
        (environment.lookup index).shape.inputTy)) demandedShape) :
    Relation base (.Single (.var index)) (.Single (.var index))
      (.stable (Single.plan demandedShape.inputTy))
      (.stable (Single.plan
        (environment.lookup index).shape.inputTy)) :=
  let bridge := checkedPathBridge (environment.lookup index) checked
  Relation.ofConversion
    (.singleton base (.var index) demandedShape.inputTy)
    (.singleton base (.var index)
      (environment.lookup index).shape.inputTy)
    (Conversion.Singleton.retarget base demandedShape.inputTy
      (environment.lookup index).shape.inputTy bridge.symm)

/-- Green q.A closure gate once the structural interval child has supplied
its explicit bridge.  Unlike the rejected audit, the canonical side is tied
to a `PathIdentity`; no free-standing canonical `IntervalRep` premise is
accepted. -/
noncomputable def applicationSelection
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    {environment : Env sourceContext base}
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {canonicalSelected : Ty sig}
    (typing : LambdaPFC.Path.Ty sourceContext (.sel path label)
      (.intv lowerSource upperSource))
    (canonical : PathIdentity environment typing canonicalSelected)
    {resultLower resultUpper : Shape sig} {resultSelected : Ty sig}
    (result : IntervalRep (targetContext := base)
      lowerSource upperSource resultLower resultSelected resultUpper)
    (resultInterface : Shape.Interface base (.opaque resultSelected))
    (selectedChild : Conversion.Bridge base canonicalSelected
      resultSelected) :
    Realizes environment (result.selection path label)
      (.value resultInterface) :=
  Realizes.selectionValue environment typing
    (PathIdentity.across canonical selectedChild) resultInterface

/-- The selected child is also exactly the ordinary conversion needed to
check the acted P2 result back against the canonical P1 selection demand. -/
noncomputable def applicationSelectionBackToCanonical
    {n : Nat} {sig : Sig} {base : Ctx sig}
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lowerSource upperSource : LambdaPFC.Ty n}
    {canonicalLower canonicalUpper resultLower resultUpper : Shape sig}
    {canonicalSelected resultSelected : Ty sig}
    (canonical : IntervalRep (targetContext := base)
      lowerSource upperSource canonicalLower canonicalSelected canonicalUpper)
    (result : IntervalRep (targetContext := base)
      lowerSource upperSource resultLower resultSelected resultUpper)
    (selectedChild : Conversion.Bridge base canonicalSelected
      resultSelected) :
    Relation base (.TSel path label) (.TSel path label)
      (.opaque resultSelected) (.opaque canonicalSelected) :=
  Relation.ofConversion (result.selection path label)
    (canonical.selection path label) selectedChild.rightToLeft

/-! ## Ordinary application result bootstrap -/

/-- The exact singleton value introduced from one retained environment
lookup.  This is the raw codomain witness for `Single var0` after the adapted
argument is installed as the newest variable. -/
noncomputable def lookupSingletonValue
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base) (index : Fin n) :
    Realizes environment
      (singletonSlot (.var index) (environment.lookup index)).rep
      (.value
        (singletonSlot (.var index) (environment.lookup index)).interface) :=
  Realizes.singletonValue environment
    (LambdaPFC.Path.Ty.var (Γ := sourceContext) (x := index))
    (environment.lookup index) (PathIdentity.lookup environment index)

/-! ## Same-run nested path demand bootstrap -/

private abbrev NestedInnerLabel : LambdaPFC.Name := 3
private abbrev NestedOuterLabel : LambdaPFC.Name := 7

private abbrev NestedInnerSource (n : Nat) : LambdaPFC.Ty n :=
  .Pair .Top NestedInnerLabel (.intv .Bot .Top)

private abbrev NestedOuterSource : LambdaPFC.Ty 0 :=
  .Pair (NestedInnerSource 0) NestedOuterLabel (.ty .Top)

private abbrev NestedSourceContext : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc NestedOuterSource

private def nestedInnerFirst : Shape [] := .stable (Top.plan [])
private def nestedInnerLower : Shape nestedInnerFirst.scope :=
  .stable (Bot.plan nestedInnerFirst.scope)
private def nestedInnerUpper : Shape nestedInnerFirst.scope :=
  .stable (Top.plan nestedInnerFirst.scope)
private def nestedInnerShape : Shape [] :=
  .stable (Pair.Interval.plan nestedInnerFirst nestedInnerLower
    nestedInnerUpper)
private def nestedOuterMember : Shape nestedInnerShape.scope :=
  .stable (Top.plan nestedInnerShape.scope)
private def nestedOuterShape : Shape [] :=
  .stable (Pair.Proper.plan nestedInnerShape nestedOuterMember)

private def nestedInnerRep :
    Rep Ctx.empty (NestedInnerSource 1) nestedInnerShape :=
  .intervalPair (.top _) (.bottom _) (.top _)

private def nestedOuterRep :
    Rep Ctx.empty (NestedSourceContext.lookup 0) nestedOuterShape := by
  change Rep Ctx.empty
    (.Pair (NestedInnerSource 1) NestedOuterLabel (.ty .Top))
      nestedOuterShape
  exact .properPair nestedInnerRep (.top _)

private abbrev NestedTargetContext : Ctx nestedOuterShape.scope :=
  nestedOuterShape.context Ctx.empty

private noncomputable def nestedReceiver :
    Slot NestedTargetContext (NestedSourceContext.lookup 0) where
  shape := nestedOuterShape.rename nestedOuterShape.binders.weaken
  interface := Shape.Interface.canonical Ctx.empty nestedOuterShape
  rep := nestedOuterRep.targetRename nestedOuterShape.binders.weaken
    (nestedOuterShape.binders.weaken_typed Ctx.empty)

private noncomputable def nestedEnvironment :
    Env NestedSourceContext NestedTargetContext where
  lookup index :=
    Fin.cases nestedReceiver (fun older => Fin.elim0 older) index

private def nestedReceiverTyping :
    LambdaPFC.Path.Ty NestedSourceContext (.var 0)
      (.ty (NestedSourceContext.lookup 0)) :=
  .var

private def nestedInnerTyping :
    LambdaPFC.Path.Ty NestedSourceContext (.fst (.var 0))
      (.ty (NestedInnerSource 1)) :=
  nestedReceiverTyping.fst

private def nestedFirstTyping :
    LambdaPFC.Path.Ty NestedSourceContext (.fst (.fst (.var 0)))
      (.ty .Top) :=
  nestedInnerTyping.fst

private def nestedSelectionTyping :
    LambdaPFC.Path.Ty NestedSourceContext
      (.sel (.fst (.var 0)) NestedInnerLabel) (.intv .Bot .Top) := by
  simpa only [LambdaPFC.Tau.open] using nestedInnerTyping.sel_r

private def nestedSelectionWf :
    LambdaPFC.Tau.Wf NestedSourceContext
      (.ty (.TSel (.fst (.var 0)) NestedInnerLabel)) :=
  .sel nestedSelectionTyping .bot

private noncomputable def compileNestedSelectionDemand
    (typing : LambdaPFC.Tau.Wf NestedSourceContext
      (.ty (.TSel (.fst (.var 0)) NestedInnerLabel))) : PUnit := by
  cases typing with
  | sel pathTyping _nonempty =>
      exact Realizes.withSelectionDemand pathTyping nestedEnvironment
        (fun {_current} {_currentContext} _focus _currentEnvironment
          {_lower} {_upper} {_selected} _interval
          (_demand : Realizes _currentEnvironment
            (_interval.selection (.fst (.var 0)) NestedInnerLabel) .demand) =>
            PUnit.unit)

/-- The literal `Wf.sel` branch follows nested `fst ; sel_r`, opens its hidden
interval once, and constructs its first selected demand in that callback. -/
noncomputable def nestedSelectionDemandCps : PUnit :=
  compileNestedSelectionDemand nestedSelectionWf

/-- The same enriched runner handles a nested proper path and supplies its
exact singleton identity without changing consumer result type. -/
noncomputable def nestedProperDemandCps : PUnit :=
  PathIdentity.resolveWith nestedFirstTyping nestedEnvironment
    (fun _focus currentEnvironment view resolution => by
      cases view with
      | proper slot =>
          let _demand : Realizes currentEnvironment
              (.singleton _ (.fst (.fst (.var 0))) slot.shape.inputTy)
              .demand :=
            Realizes.singletonDemand currentEnvironment nestedFirstTyping
              resolution
          exact PUnit.unit)


end LambdaPToFCo.Direct.Internal.RealizationRegression
