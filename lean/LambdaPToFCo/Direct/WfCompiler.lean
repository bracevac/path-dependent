import LambdaPToFCo.Direct.FormedPath

/-!
# Total formation-preserving well-formedness compilation

This is the direct derivation interpreter for all seven `LambdaPFC.Tau.Wf`
constructors.  Its public result is only an exact material `Formation.Proper`
or `Formation.Interval`.  Focused path and selection cases retain their exact
interfaces and endpoint formations until `FormedPath` faithfully closes them
back to the root.

Every target object is ordinary unchanged System FCo syntax.  The source Wf
derivation is used solely as the recursion index; it is not translated to an
intermediate calculus.
-/

namespace LambdaPToFCo.Direct.Internal.WfCompiler

open SystemFCo
open LambdaPToFCo.Direct.Internal.Formation
open LambdaPToFCo.Direct.Internal.FormedPath

/-- Kind-complete exact result of direct Wf compilation. -/
inductive Result {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : Ctx sig) :
    {kind : LambdaPFC.Kind} -> LambdaPFC.Tau n kind -> Type where
| proper (result : Proper sourceContext targetContext sourceType) :
    Result sourceContext targetContext (.ty sourceType)
| interval
    (result : Interval sourceContext targetContext lowerSource upperSource) :
    Result sourceContext targetContext (.intv lowerSource upperSource)

private def function
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    (domain : Proper sourceContext targetContext domainSource)
    (codomain : Proper (sourceContext.snoc domainSource)
      (domain.shape.context targetContext) codomainSource) :
    Proper sourceContext targetContext
      (.Fun domainSource codomainSource) where
  shape := .stable (Function.plan domain.shape codomain.shape)
  formation := .function domain.formation codomain.formation

private def properPair
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {memberSource : LambdaPFC.Ty (n + 1)}
    (label : LambdaPFC.Name)
    (first : Proper sourceContext targetContext firstSource)
    (member : Proper (sourceContext.snoc firstSource)
      (first.shape.context targetContext) memberSource) :
    Proper sourceContext targetContext
      (.Pair firstSource label (.ty memberSource)) where
  shape := .stable (Pair.Proper.plan first.shape member.shape)
  formation := .properPair first.formation member.formation

private def intervalPair
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {lowerSource upperSource : LambdaPFC.Ty (n + 1)}
    (label : LambdaPFC.Name)
    (first : Proper sourceContext targetContext firstSource)
    (member : Interval (sourceContext.snoc firstSource)
      (first.shape.context targetContext) lowerSource upperSource) :
    Proper sourceContext targetContext
      (.Pair firstSource label (.intv lowerSource upperSource)) where
  shape := .stable
    (Pair.Interval.plan first.shape member.lower member.upper)
  formation := .intervalPair first.formation member.lowerFormation
    member.upperFormation

/-- Interpret one literal `Tau.Wf` derivation.  No callback, demanded Shape,
or caller-provided equality is needed. -/
noncomputable def compile
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {source : LambdaPFC.Tau n kind}
    {sig : Sig} {targetContext : Ctx sig} :
    LambdaPFC.Tau.Wf sourceContext source ->
    Env sourceContext targetContext ->
    Result sourceContext targetContext source
| .bot, _environment =>
    .proper (.bottom sourceContext targetContext)
| .top, _environment =>
    .proper (.top sourceContext targetContext)
| @LambdaPFC.Tau.Wf.path _ _ path referent typing, environment =>
    let singleton := FormedPath.materializeSingleton typing environment
    .proper {
      shape := singleton.shape
      formation := singleton.formation
    }
| @LambdaPFC.Tau.Wf.sel _ _ lowerSource upperSource path label typing
    _nonempty, environment =>
    .proper (FormedPath.compile typing environment
      (fun focus _ view => by
        cases view with
        | interval lowerFormation upperFormation lowerFunction lowerTyping
            upperFunction upperTyping =>
            exact focus.closeFormation
              (.selection typing lowerFormation upperFormation lowerFunction
                lowerTyping upperFunction upperTyping)))
| @LambdaPFC.Tau.Wf.fun _ _ domainSource codomainSource domainWf
    codomainWf, environment => by
    cases compile domainWf environment with
    | proper domain =>
        let nextEnvironment := environment.enter domainSource domain.formation
        cases compile codomainWf nextEnvironment with
        | proper codomain =>
            exact .proper (function domain codomain)
| @LambdaPFC.Tau.Wf.pair _ _ firstSource kind dependent label firstWf
    memberWf, environment => by
    cases compile firstWf environment with
    | proper first =>
        let nextEnvironment := environment.enter firstSource first.formation
        cases compile memberWf nextEnvironment with
        | proper member =>
            exact .proper (properPair label first member)
        | interval member =>
            exact .proper (intervalPair label first member)
| @LambdaPFC.Tau.Wf.bounds_wf _ _ lowerSource upperSource lowerWf upperWf
    _nonempty, environment => by
    cases compile lowerWf environment with
    | proper lower =>
        cases compile upperWf environment with
        | proper upper =>
            exact .interval (.bounds lower upper)

/-- Path Wf formation and term-level path introduction share one exact
material singleton.  Their Shapes therefore agree without any caller-supplied
equality or reconstructed selected identity. -/
theorem path_shape_coherent
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty referent))
    {sig : Sig} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext) :
    match compile (LambdaPFC.Tau.Wf.path typing) environment with
    | .proper result =>
        result.shape =
          (FormedPath.materializeSingleton typing environment).shape := by
  rfl

end LambdaPToFCo.Direct.Internal.WfCompiler
