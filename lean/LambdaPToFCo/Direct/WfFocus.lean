import LambdaPToFCo.Direct.WfCompiler

/-!
# Focus-retaining well-formedness results

`WfCompiler` materializes every proper result at the target root.  Path and
selection formation sometimes need one additional, smaller invariant: retain
the exact `FormedPath.Focus` until an actual interface for the focused type is
available.  `FocusedProper` is precisely that existential refinement.  It is
not a plan or a second calculus; its only target evidence is an ordinary
System FCo formation and the executable path focus which closes it.

This bounded layer is a top-level packer, not the final recursively executable
Wf result.  Structural cases retain their exact `Formation`, but a distinct
focus runner belonging to a closed function domain/codomain or pair member is
not recoverable from that Formation alone.  A recursive consumer which checks
inside those children therefore needs a constructor-indexed refinement above
this leaf.
-/

namespace LambdaPToFCo.Direct.Internal.WfFocus

open SystemFCo
open LambdaPToFCo.Direct.Internal.Formation
open LambdaPToFCo.Direct.Internal.FormedPath

/-- A proper Wf result before its exact target focus is discarded.  Formation
can be closed without an inhabitant, while an eventual exact interface is
repacked through this very same focus. -/
structure FocusedProper
    (sourceContext : LambdaPFC.Ctx n)
    {root : Sig} (rootContext : Ctx root)
    (sourceType : LambdaPFC.Ty n) : Type where
  current : Sig
  currentContext : Ctx current
  shape : Shape current
  focus : Focus sourceContext rootContext currentContext
  formation : Formation sourceContext currentContext sourceType shape

namespace FocusedProper

/-- Close the retained formation to its material root Shape. -/
noncomputable def proper
    {sourceContext : LambdaPFC.Ctx n}
    {root : Sig} {rootContext : Ctx root}
    {sourceType : LambdaPFC.Ty n}
    (result : FocusedProper sourceContext rootContext sourceType) :
    Proper sourceContext rootContext sourceType :=
  result.focus.closeFormation result.formation

/-- Repack an exact focused interface at the Shape selected by `proper`.
The result index is definitional; no Shape equality is requested or stored. -/
noncomputable def closeInterface
    {sourceContext : LambdaPFC.Ctx n}
    {root : Sig} {rootContext : Ctx root}
    {sourceType : LambdaPFC.Ty n}
    (result : FocusedProper sourceContext rootContext sourceType)
    (interface : Shape.Interface result.currentContext result.shape) :
    Shape.Interface rootContext result.proper.shape :=
  result.focus.closeInterface result.formation interface

/-- Repack one exact focused value as a full formed root Slot. -/
noncomputable def closeSlot
    {sourceContext : LambdaPFC.Ctx n}
    {root : Sig} {rootContext : Ctx root}
    {sourceType : LambdaPFC.Ty n}
    (result : FocusedProper sourceContext rootContext sourceType)
    (interface : Shape.Interface result.currentContext result.shape) :
    Slot sourceContext rootContext sourceType where
  shape := result.proper.shape
  interface := result.closeInterface interface
  formation := result.proper.formation

/-- The full value closer uses exactly the Shape selected by formation
closure. -/
theorem closeSlot_shape
    {sourceContext : LambdaPFC.Ctx n}
    {root : Sig} {rootContext : Ctx root}
    {sourceType : LambdaPFC.Ty n}
    (result : FocusedProper sourceContext rootContext sourceType)
    (interface : Shape.Interface result.currentContext result.shape) :
    (result.closeSlot interface).shape = result.proper.shape := by
  rfl

/-- Regard an already material result as focused at the root. -/
noncomputable def root
    {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (result : Proper sourceContext targetContext sourceType) :
    FocusedProper sourceContext targetContext sourceType where
  current := sig
  currentContext := targetContext
  shape := result.shape
  focus := Focus.root sourceContext targetContext
  formation := result.formation

end FocusedProper

/-- Kind-complete Wf result.  Only proper types need the retained focus;
interval Wf already returns its two exact material endpoint formations. -/
inductive Result {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : Ctx sig) :
    {kind : LambdaPFC.Kind} -> LambdaPFC.Tau n kind -> Type where
| proper
    (result : FocusedProper sourceContext targetContext sourceType) :
    Result sourceContext targetContext (.ty sourceType)
| interval
    (result : Interval sourceContext targetContext lowerSource upperSource) :
    Result sourceContext targetContext (.intv lowerSource upperSource)

private noncomputable def atRoot
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {source : LambdaPFC.Tau n kind}
    {sig : Sig} {targetContext : Ctx sig} :
    WfCompiler.Result sourceContext targetContext source ->
    Result sourceContext targetContext source
| .proper result => .proper (FocusedProper.root result)
| .interval result => .interval result

/-- Compile one literal Wf derivation while retaining the real focus for the
two constructors whose result is formed at a precise path.  Every other case
uses the already total material compiler and the identity root focus.  Thus
this operation is exact for closing a value at the outer result, but does not
claim to retain independently executable focus runners for structural
children. -/
noncomputable def compile
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {source : LambdaPFC.Tau n kind}
    {sig : Sig} {targetContext : Ctx sig} :
    LambdaPFC.Tau.Wf sourceContext source ->
    Env sourceContext targetContext ->
    Result sourceContext targetContext source
| @LambdaPFC.Tau.Wf.path _ _ path referent typing, environment =>
    FormedPath.compileWith typing environment
      (fun focus _ view => by
        cases view with
        | proper interface formation =>
            exact .proper {
              current := _
              currentContext := _
              shape := .stable (Single.plan _)
              focus := focus
              formation := .singleton typing interface formation
            })
| @LambdaPFC.Tau.Wf.sel _ _ lowerSource upperSource path label typing
    _nonempty, environment =>
    FormedPath.compileWith typing environment
      (fun focus _ view => by
        cases view with
        | interval lowerFormation upperFormation lowerFunction lowerTyping
            upperFunction upperTyping =>
            exact .proper {
              current := _
              currentContext := _
              shape := .opaque _
              focus := focus
              formation := .selection typing lowerFormation upperFormation
                lowerFunction lowerTyping upperFunction upperTyping
            })
| .bot, environment =>
    atRoot (WfCompiler.compile .bot environment)
| .top, environment =>
    atRoot (WfCompiler.compile .top environment)
| @LambdaPFC.Tau.Wf.fun _ _ domainSource codomainSource domainWf codomainWf,
    environment =>
    atRoot (WfCompiler.compile (.fun domainWf codomainWf) environment)
| @LambdaPFC.Tau.Wf.pair _ _ firstSource dependentKind dependent label
    firstWf memberWf, environment =>
    atRoot (WfCompiler.compile (.pair firstWf memberWf) environment)
| @LambdaPFC.Tau.Wf.bounds_wf _ _ lowerSource upperSource lowerWf upperWf
    nonempty, environment =>
    atRoot (WfCompiler.compile
      (.bounds_wf lowerWf upperWf nonempty) environment)

end LambdaPToFCo.Direct.Internal.WfFocus
