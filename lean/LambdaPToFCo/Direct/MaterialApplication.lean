import LambdaPToFCo.Direct.MaterialTermPath

/-!
# Material raw dependent application

This leaf applies one already exposed raw function view to one exact checked
domain interface.  The ordinary System FCo code produces the instantiated
codomain package, which is immediately sealed as a raw Slot and then reclosed
through the composed package-aware focus histories.

There is no source dispatcher or checking callback here.  Callers expose the
function and check its argument before invoking these plain target functions.
-/

namespace LambdaPToFCo.Direct.Internal.MaterialApplication

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.MaterialTermPath

/-! ## Exact application in one target scope -/

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
  change Exp.HasType base
    (appliedPackage functionInterface argumentInterface)
    (codomain.inputTy.subst argumentInterface.substitution) at applied
  simpa only [Shape.inputTy_subst] using applied

/-- Apply one closure-free `Rep.function` view in its current target scope.

The codomain representation is instantiated by both the source argument
path and the exact target domain interface.  Its ordinary result package is
sealed immediately, so no result Shape or hidden target type escapes.

The caller invokes this function in the lexical `.function domainRep
codomainRep` match which supplied the domain demand.  The checked domain
interface and the codomain's dependent target index are all this target-only
step uses, so the already-consumed `domainRep` is not repeated here. -/
noncomputable def applyExact
    {base : Ctx sig}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    (argumentPath : LambdaPFC.Path n)
    {domain : Shape sig} {codomain : Shape domain.scope}
    (functionInterface : Shape.Interface base
      (.stable (Function.plan domain codomain)))
    (codomainRep : Rep (domain.context base) codomainSource codomain)
    (argumentInterface : Shape.Interface base domain) :
    Slot base (codomainSource.open argumentPath) :=
  let resultRep := codomainRep.instantiate argumentInterface
    (LambdaPFC.PathSubst.openAt argumentPath)
  Slot.sealPackage resultRep
    (appliedPackage functionInterface argumentInterface)
    (appliedPackage_hasType functionInterface argumentInterface)

/-! ## Reclosure through function and argument focus histories -/

/-- Apply after function exposure and argument checking opened independent
package scopes.

`outerFocus` retains the function Slot's route to the caller root;
`innerFocus` retains scopes opened while checking the exact domain.  Function
data are renamed to the argument scope, application is performed there, and
the material result is reclosed in inner-then-outer runtime order by
`Focus.comp outerFocus innerFocus`.  As with `applyExact`, this is called from
the same lexical `.function` match after its domain representation has driven
argument checking. -/
noncomputable def applyFocused
    {root functionSig argumentSig : Sig}
    {rootContext : Ctx root}
    {functionContext : Ctx functionSig}
    {argumentContext : Ctx argumentSig}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    (outerFocus : Focus rootContext functionContext)
    (innerFocus : Focus functionContext argumentContext)
    (argumentPath : LambdaPFC.Path n)
    {domain : Shape functionSig} {codomain : Shape domain.scope}
    (functionInterface : Shape.Interface functionContext
      (.stable (Function.plan domain codomain)))
    (codomainRep : Rep (domain.context functionContext)
      codomainSource codomain)
    (argumentInterface : Shape.Interface argumentContext
      (domain.rename innerFocus.mapping)) :
    Slot rootContext (codomainSource.open argumentPath) := by
  let mapping := innerFocus.mapping
  let typed := innerFocus.typed
  let domainAt := domain.rename mapping
  let codomainAt := Function.renameCodomain domain codomain mapping
  let functionInterfaceAt : Shape.Interface argumentContext
      (.stable (Function.plan domainAt codomainAt)) := by
    simpa only [Shape.rename, Function.plan_rename] using
      functionInterface.rename mapping typed
  let codomainRepAt := codomainRep.targetRename
    (domain.liftRename mapping) (domain.liftRename_typed typed)
  let result := applyExact argumentPath functionInterfaceAt codomainRepAt
    argumentInterface
  exact (outerFocus.comp innerFocus).closeSlot result

end LambdaPToFCo.Direct.Internal.MaterialApplication
