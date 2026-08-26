import LambdaPToFCo.Direct.TermIntroduction

/-!
# Direct dependent application

Application consumes a function slot at its literal `Rep.function` view.  Its
ordinary retained code is instantiated by the function interface and applied
to the exact domain interface arguments.  The resulting codomain package is
then eliminated around the value continuation, so its hidden interface never
escapes the scope in which it is available.

The recursive argument premise is represented by `ArgumentCompiler`.  It is
indexed by the literal source typing derivation and must compile against the
exact domain representation exposed by the function slot.  This rank-2 CPS
boundary is the current totality boundary: an arbitrary independently
compiled slot of the same source type need not have the same target shape.
-/

namespace LambdaPToFCo.Direct.Internal.Application

open SystemFCo
open Representation
open TermIntroduction

/-! ## Applying one exact function view -/

private noncomputable def appliedPackage
    {base : Ctx sig} {domain : Shape sig}
    {codomain : Shape domain.scope}
    (functionInterface : Shape.Interface base
      (.stable (Function.plan domain codomain)))
    (argumentInterface : Shape.Interface base domain) : Exp sig :=
  argumentInterface.arguments.apply
    ((Function.asCode domain codomain).subst
      functionInterface.substitution)

private noncomputable def appliedPackage_hasType
    {base : Ctx sig} {domain : Shape sig}
    {codomain : Shape domain.scope}
    (functionInterface : Shape.Interface base
      (.stable (Function.plan domain codomain)))
    (argumentInterface : Shape.Interface base domain) :
    Exp.HasType base (appliedPackage functionInterface argumentInterface)
      (codomain.subst argumentInterface.substitution).inputTy := by
  have codeTyping :=
    (Function.asCode_hasType base domain codomain).subst
      functionInterface.arguments.substitution_typed
  have codeType :
      (Function.finalCodeTy domain codomain).subst
          functionInterface.arguments.substitution =
        Function.codeTy domain codomain := by
    calc
      _ = functionInterface.arguments.instantiate
          ((Function.codeTy domain codomain).rename
            (Function.plan domain codomain).telescope.weaken) :=
        (functionInterface.arguments.instantiate_eq_subst _).symm
      _ = Function.codeTy domain codomain :=
        functionInterface.arguments.instantiate_weaken _
  rw [codeType] at codeTyping
  have applied := argumentInterface.arguments.apply_hasType codeTyping
  rw [Telescope.Args.instantiate_eq_subst] at applied
  change Exp.HasType base (appliedPackage functionInterface argumentInterface)
    (codomain.inputTy.subst argumentInterface.substitution) at applied
  simpa only [Shape.inputTy_subst] using applied

/-- Apply a function whose exact `Rep.function` view and exact-domain
interface are already present in one target scope.

The codomain result is instantiated by both the source path `q` and the
target domain interface.  It is supplied as a `Slot` only under elimination
of the result package, which keeps all hidden result binders inside CPS. -/
noncomputable def applyExact
    {sourceContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    (environment : Env sourceContext base)
    (argumentPath : LambdaPFC.Path n)
    {domain : Shape sig} {codomain : Shape domain.scope}
    (functionInterface : Shape.Interface base
      (.stable (Function.plan domain codomain)))
    (domainRep : Rep base domainSource domain)
    (codomainRep : Rep (domain.context base) codomainSource codomain)
    (argumentInterface : Shape.Interface base domain) :
    ValueComputation sourceContext base
      (codomainSource.open argumentPath) :=
  fun answer consumer => by
    let _functionRep : Rep base (.Fun domainSource codomainSource)
        (.stable (Function.plan domain codomain)) :=
      .function domainRep codomainRep
    let resultShape := codomain.subst argumentInterface.substitution
    let resultPackage := appliedPackage functionInterface argumentInterface
    have resultPackageTyping : Exp.HasType base resultPackage
        resultShape.inputTy := by
      exact appliedPackage_hasType functionInterface argumentInterface
    let resultRep := codomainRep.instantiate argumentInterface
      (LambdaPFC.PathSubst.openAt argumentPath)
    let opening := resultShape.binders.weaken
    let openingTyped := resultShape.binders.weaken_typed base
    let openedEnvironment := environment.targetRename opening openingTyped
    let openedSlot : Slot (resultShape.context base)
        (codomainSource.open argumentPath) :=
      { shape := resultShape.rename opening
        interface := Shape.Interface.canonical base resultShape
        rep := resultRep.targetRename opening openingTyped }
    let body := consumer opening openingTyped openedEnvironment openedSlot
    exact {
      expression := resultShape.eliminate resultPackage answer body.expression
      typing := resultShape.eliminate_hasType resultPackageTyping body.typing
    }

/-! ## Derivation-directed recursive boundary -/

/-- A consumer for an argument compiled against one exact function-domain
shape.  The recursive compiler may open further target scopes, but it must
return an interface for precisely the renamed demanded domain. -/
abbrev ArgumentConsumer
    {n : Nat} {root : Sig} (sourceContext : LambdaPFC.Ctx n)
    (rootContext : Ctx root) (answer : Ty root)
    (domain : Shape root) : Type :=
  forall {current : Sig} {currentContext : Ctx current},
    (mapping : Rename root current) ->
    Rename.Typed rootContext currentContext mapping ->
    Env sourceContext currentContext ->
    Shape.Interface currentContext (domain.rename mapping) ->
    Path.Body currentContext (answer.rename mapping)

/-- Recursive compilation of the full argument typing premise against the
exact domain representation demanded by the function being applied.

This is indexed by the source `Tm.Ty` derivation; it is not a raw callback or
an emitted equality witness.  In particular, subsumption in the argument
premise is compiled here before the exact interface is delivered. -/
structure ArgumentCompiler
    {sourceContext : LambdaPFC.Ctx n}
    {argumentPath : LambdaPFC.Path n}
    {domainSource : LambdaPFC.Ty n}
    (_derivation : LambdaPFC.Tm.Ty sourceContext
      (.path argumentPath) domainSource) : Type where
  compile : {sig : Sig} -> {base : Ctx sig} ->
    (environment : Env sourceContext base) ->
    {domain : Shape sig} ->
    Rep base domainSource domain ->
    (answer : Ty sig) ->
    ArgumentConsumer sourceContext base answer domain ->
    Path.Body base answer

/-- A full function-premise computation, indexed by its literal source
typing derivation.  The recursive term dispatcher supplies this computation;
application only consumes its exact resulting slot. -/
abbrev FunctionComputation
    {sourceContext : LambdaPFC.Ctx n}
    {functionPath : LambdaPFC.Path n}
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    (_derivation : LambdaPFC.Tm.Ty sourceContext (.path functionPath)
      (.Fun domainSource codomainSource))
    {sig : Sig} (base : Ctx sig) : Type :=
  ValueComputation sourceContext base (.Fun domainSource codomainSource)

/-- Compile the literal source application rule from its two recursively
compiled premises.

The function computation may itself focus paths or perform subsumption.  Once
it exposes `Rep.function`, the argument compiler is run against that exact
domain demand; `applyExact` then performs only ordinary System FCo
substitution, telescope application, and result-package elimination. -/
noncomputable def compile
    {sourceContext : LambdaPFC.Ctx n}
    {functionPath argumentPath : LambdaPFC.Path n}
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    {functionDerivation : LambdaPFC.Tm.Ty sourceContext
      (.path functionPath) (.Fun domainSource codomainSource)}
    {argumentDerivation : LambdaPFC.Tm.Ty sourceContext
      (.path argumentPath) domainSource}
    {base : Ctx sig}
    (function : FunctionComputation functionDerivation base)
    (argument : ArgumentCompiler argumentDerivation) :
    ValueComputation sourceContext base
      (codomainSource.open argumentPath) :=
  fun answer consumer =>
    function answer (fun {current} {currentContext} mapping typed
        environment functionSlot => by
      cases functionSlot with
      | mk functionShape functionInterface functionRep =>
          cases functionRep with
          | @function _ _ _ _ _ domain codomain domainRep codomainRep =>
              exact argument.compile environment domainRep
                (answer.rename mapping)
                (fun {final} {finalContext} next nextTyped finalEnvironment
                    argumentInterface => by
                  let combined := mapping.comp next
                  let combinedTyped := TypedRename.comp typed nextTyped
                  let domainAt := domain.rename next
                  let codomainAt :=
                    Function.renameCodomain domain codomain next
                  let functionInterfaceAt : Shape.Interface finalContext
                      (.stable (Function.plan domainAt codomainAt)) := by
                    simpa only [Shape.rename, Function.plan_rename] using
                      functionInterface.rename next nextTyped
                  let domainRepAt := domainRep.targetRename next nextTyped
                  let codomainRepAt := codomainRep.targetRename
                    (domain.liftRename next)
                    (domain.liftRename_typed nextTyped)
                  let localConsumer : ValueConsumer sourceContext finalContext
                      (answer.rename combined)
                      (codomainSource.open argumentPath) :=
                    fun {opened} {openedContext} opening openingTyped
                        openedEnvironment resultSlot => by
                      let total := combined.comp opening
                      let totalTyped := TypedRename.comp combinedTyped
                        openingTyped
                      simpa only [Ty.rename_comp, Rename.comp_assoc] using
                        consumer total totalTyped openedEnvironment resultSlot
                  have applied := applyExact finalEnvironment argumentPath
                    functionInterfaceAt domainRepAt codomainRepAt
                    argumentInterface
                    (answer.rename combined) localConsumer
                  simpa only [Ty.rename_comp] using applied))

end LambdaPToFCo.Direct.Internal.Application
