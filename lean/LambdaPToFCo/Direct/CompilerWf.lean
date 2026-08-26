import LambdaPToFCo.Direct.MaterialPath

/-!
# Total material raw well-formedness compiler

Every literal `LambdaPFC.Tau.Wf` constructor is interpreted over the raw
representation environment.  Path and selection leaves use the type-only
material focus, so their referents/endpoints need no extra Wf evidence and no
hidden target type escapes.  The public result is the existing exact
`Wf.View`: one material proper `Shape`/`Rep`, or two material interval
endpoint `Shape`/`Rep`s.
-/

namespace LambdaPToFCo.Direct.Internal.CompilerWf

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.Wf
open LambdaPToFCo.Direct.Internal.MaterialPath

/-- Interpret all seven literal `Tau.Wf` constructors over a raw exact
environment. -/
noncomputable def compile
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {source : LambdaPFC.Tau n kind}
    {sig : Sig} {targetContext : Ctx sig} :
    LambdaPFC.Tau.Wf sourceContext source ->
    Env sourceContext targetContext ->
    Wf.View targetContext source
| .bot, _environment => .proper (.bottom targetContext)
| .top, _environment => .proper (.top targetContext)
| @LambdaPFC.Tau.Wf.path _ _ path referent typing, environment =>
    MaterialPath.compileWith typing environment (fun focus _ view => by
      cases view with
      | proper result =>
          exact .proper (focus.close
            (.singleton _ path result.shape.inputTy)))
| @LambdaPFC.Tau.Wf.sel _ _ lowerSource upperSource path label typing
    _nonempty, environment =>
    MaterialPath.compileWith typing environment (fun focus _ view => by
      cases view with
      | interval interval =>
          exact .proper (focus.close (interval.selection path label)))
| @LambdaPFC.Tau.Wf.fun _ _ domainSource codomainSource domainWf
    codomainWf, environment => by
    cases compile domainWf environment with
    | proper domain =>
        let nextEnvironment :=
          environment.enter domainSource domain.shape domain.rep
        cases compile codomainWf nextEnvironment with
        | proper codomain =>
            exact .proper (.function domain codomain)
| @LambdaPFC.Tau.Wf.pair _ _ firstSource kind dependent label firstWf
    memberWf, environment => by
    cases compile firstWf environment with
    | proper first =>
        let nextEnvironment :=
          environment.enter firstSource first.shape first.rep
        cases compile memberWf nextEnvironment with
        | proper member =>
            exact .proper (.properPair label first member)
        | interval member =>
            exact .proper (.intervalPair label first member)
| @LambdaPFC.Tau.Wf.bounds_wf _ _ lowerSource upperSource lowerWf upperWf
    _nonempty, environment => by
    cases compile lowerWf environment with
    | proper lower =>
        cases compile upperWf environment with
        | proper upper => exact .interval (.bounds lower upper)

end LambdaPToFCo.Direct.Internal.CompilerWf
