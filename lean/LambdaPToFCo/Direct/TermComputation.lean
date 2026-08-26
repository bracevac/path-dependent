import LambdaPToFCo.Direct.Introduction
import LambdaPToFCo.Direct.ArgumentCancellation
import LambdaPToFCo.Direct.WfCompiler

/-!
# Formation-aware direct term computations

This leaf contains the one executable CPS carrier needed while direct term
compilation opens target packages.  Its invariant is an exact formed source
environment plus an exact formed source-indexed Slot; erased Representation
environments never become the recursion boundary.

The literal introduction kernels are intentionally separate from the future
total dispatcher.  Application and subsumption will call their own
derivation-indexed modules.  Checking-mode recursion is represented by the
single generic `AgainstCompiler`, not by a separate planning layer.
-/

namespace LambdaPToFCo.Direct.Internal.TermComputation

open SystemFCo
open LambdaPToFCo.Direct.Internal.Formation
open LambdaPToFCo.Direct.Internal.FormedPath
open LambdaPToFCo.Direct.Internal.WfCompiler

/-! ## The executable value carrier -/

/-- Consume one exact formed value in every target scope reached during
compilation. -/
abbrev ValueConsumer
    {n : Nat} {root : Sig} (sourceContext : LambdaPFC.Ctx n)
    (rootContext : Ctx root) (answer : Ty root)
    (sourceType : LambdaPFC.Ty n) : Type :=
  forall {current : Sig} {currentContext : Ctx current},
    (mapping : Rename root current) ->
    Rename.Typed rootContext currentContext mapping ->
    Env sourceContext currentContext ->
    Slot sourceContext currentContext sourceType ->
    Path.Body currentContext (answer.rename mapping)

/-- A scope-closing computation which supplies one exact formed Slot. -/
abbrev Computation
    {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {root : Sig} (rootContext : Ctx root)
    (sourceType : LambdaPFC.Ty n) : Type :=
  (answer : Ty root) ->
  ValueConsumer sourceContext rootContext answer sourceType ->
  Path.Body rootContext answer

/-- Checking-mode consumer for one demanded Formation.  The interface index
is the exact renamed demanded Shape, so no shape equality can be supplied or
fabricated by a caller. -/
abbrev AgainstConsumer
    {n : Nat} {root : Sig} (sourceContext : LambdaPFC.Ctx n)
    (rootContext : Ctx root) (answer : Ty root)
    (sourceType : LambdaPFC.Ty n)
    (demand : Proper sourceContext rootContext sourceType) : Type :=
  forall {current : Sig} {currentContext : Ctx current},
    (mapping : Rename root current) ->
    Rename.Typed rootContext currentContext mapping ->
    Env sourceContext currentContext ->
    Shape.Interface currentContext (demand.shape.rename mapping) ->
    Path.Body currentContext (answer.rename mapping)

/-- The single derivation-indexed checking boundary.  The eventual total term
interpreter implements this function directly for every `Tm.Ty` constructor.
-/
abbrev AgainstCompiler
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    (_typing : LambdaPFC.Tm.Ty sourceContext term sourceType) : Type :=
  forall {sig : Sig} {targetContext : Ctx sig},
    Env sourceContext targetContext ->
    (demand : Proper sourceContext targetContext sourceType) ->
    (answer : Ty sig) ->
    AgainstConsumer sourceContext targetContext answer sourceType demand ->
    Path.Body targetContext answer

private noncomputable def consumeHere
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n} {answer : Ty sig}
    (environment : Env sourceContext targetContext)
    (slot : Slot sourceContext targetContext sourceType)
    (consumer : ValueConsumer sourceContext targetContext answer sourceType) :
    Path.Body targetContext answer := by
  simpa only [Ty.rename_id] using
    consumer Rename.id (TypedRename.id targetContext) environment slot

/-- Lift an already-materialized formed Slot into the executable carrier. -/
noncomputable def material
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (environment : Env sourceContext targetContext)
    (slot : Slot sourceContext targetContext sourceType) :
    Computation sourceContext targetContext sourceType :=
  fun _answer consumer => consumeHere environment slot consumer

/-- Seal any ordinary package at an exact demanded Formation behind the
one-field opaque carrier produced by `Proper.close .nil`.  This is the generic
material result boundary for let, application, and subsumption synthesis. -/
noncomputable def sealResult
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (demand : Proper sourceContext targetContext sourceType)
    (package : Exp sig)
    (packageTyping : Exp.HasType targetContext package
      demand.shape.inputTy) :
    Slot sourceContext targetContext sourceType := by
  let fields : Telescope sig := .var demand.shape.inputTy .nil
  let arguments : Telescope.Args targetContext fields :=
    .var package packageTyping .nil
  let carrier := Telescope.pack arguments
  have carrierTyping : Exp.HasType targetContext carrier fields.existsTy :=
    Telescope.pack_hasType arguments
  let result := Proper.close (.nil : Telescope sig) demand.formation
  exact {
    shape := result.shape
    interface := {
      arguments := .var carrier carrierTyping .nil
    }
    formation := result.formation
  }

/-! ## Literal material introductions -/

/-- Exact singleton Slot for a literal path term, including non-variable and
closed-carrier paths. -/
noncomputable def pathSlot
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty referent))
    {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext) :
    Slot sourceContext targetContext (.Single path) :=
  FormedPath.materializeSingleton typing environment

noncomputable def compilePath
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty referent))
    {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext) :
    Computation sourceContext targetContext (.Single path) :=
  material environment (pathSlot typing environment)

/-- Exact function package from a material Wf domain and recursively
materialized body in that domain's precise opened scope. -/
noncomputable def abstractSlot
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    (domain : Proper sourceContext targetContext domainSource)
    (body : Slot (sourceContext.snoc domainSource)
      (domain.shape.context targetContext) codomainSource) :
    Slot sourceContext targetContext
      (.Fun domainSource codomainSource) where
  shape := .stable (Function.plan domain.shape body.shape)
  interface := {
    arguments := Function.exactArguments domain.shape body.shape
      (domain.shape.binders.lambda body.interface.package)
      (domain.shape.binders.lambda_hasType
        body.interface.package_hasType)
  }
  formation := .function domain.formation body.formation

theorem abstractSlot_expression
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    (domain : Proper sourceContext targetContext domainSource)
    (body : Slot (sourceContext.snoc domainSource)
      (domain.shape.context targetContext) codomainSource) :
    (abstractSlot domain body).interface.package =
      Introduction.function domain.shape body.shape
        body.interface.package body.interface.package_hasType := by
  rfl

/-- Constructor kernel for `Tm.Ty.abs`.  Recursive compilation supplies a
material body at the exact domain root; no focused target type escapes. -/
noncomputable def compileAbstract
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {domainSource : LambdaPFC.Ty n}
    {term : LambdaPFC.Tm (n + 1)}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    (_bodyTyping : LambdaPFC.Tm.Ty (sourceContext.snoc domainSource)
      term codomainSource)
    (domainWf : LambdaPFC.Tau.Wf sourceContext (.ty domainSource))
    (environment : Env sourceContext targetContext)
    (body : forall
      (domain : Proper sourceContext targetContext domainSource),
      Slot (sourceContext.snoc domainSource)
        (domain.shape.context targetContext) codomainSource) :
    Computation sourceContext targetContext
      (.Fun domainSource codomainSource) := by
  cases WfCompiler.compile domainWf environment with
  | proper domain =>
      exact material environment (abstractSlot domain (body domain))

/-! ## Exact value-member pairs -/

private def pairMemberShape
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {firstSource memberSource : LambdaPFC.Ty n}
    (first : Slot sourceContext targetContext firstSource)
    (member : Slot sourceContext targetContext memberSource) :
    Shape first.shape.scope :=
  member.shape.rename first.shape.binders.weaken

private theorem pairMemberShape_subst
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {firstSource memberSource : LambdaPFC.Ty n}
    (first : Slot sourceContext targetContext firstSource)
    (member : Slot sourceContext targetContext memberSource) :
    (pairMemberShape first member).subst first.interface.substitution =
      member.shape := by
  exact Shape.rename_subst_cancel member.shape first.shape.binders.weaken
    first.interface.substitution
    first.interface.arguments.weaken_comp_substitution

private theorem pairMemberBinders_subst
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {firstSource memberSource : LambdaPFC.Ty n}
    (first : Slot sourceContext targetContext firstSource)
    (member : Slot sourceContext targetContext memberSource) :
    (pairMemberShape first member).binders.subst
        first.interface.substitution = member.shape.binders := by
  rw [Shape.binders_subst, pairMemberShape_subst]

private noncomputable def pairMemberArguments
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {firstSource memberSource : LambdaPFC.Ty n}
    (first : Slot sourceContext targetContext firstSource)
    (member : Slot sourceContext targetContext memberSource) :
    Telescope.Args targetContext
      ((pairMemberShape first member).binders.subst
        first.interface.substitution) :=
  (pairMemberBinders_subst first member).symm ▸
    member.interface.arguments

private noncomputable def weakenedMemberFormation
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {firstSource memberSource : LambdaPFC.Ty n}
    (first : Slot sourceContext targetContext firstSource)
    (member : Slot sourceContext targetContext memberSource) :
    Formation (sourceContext.snoc firstSource)
      (first.shape.context targetContext) memberSource.weaken
      (pairMemberShape first member) := by
  let weakened := member.formation.sourceWeaken firstSource
  let opened := weakened.targetRename first.shape.binders.weaken
    (first.shape.binders.weaken_typed targetContext)
  exact opened

/-- Exact formed Slot for the literal value-pair constructor. -/
noncomputable def valuePairSlot
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext)
    (firstIndex memberIndex : Fin n) (label : LambdaPFC.Name) :
    Slot sourceContext targetContext
      (.Pair (.Single (.var firstIndex)) label
        (.ty (.Single ((LambdaPFC.Path.var memberIndex).weaken)))) :=
  let firstTyping : LambdaPFC.Path.Ty sourceContext (.var firstIndex)
      (.ty (sourceContext.lookup firstIndex)) := .var
  let memberTyping : LambdaPFC.Path.Ty sourceContext (.var memberIndex)
      (.ty (sourceContext.lookup memberIndex)) := .var
  let first := pathSlot firstTyping environment
  let member := pathSlot memberTyping environment
  let dependentMember := pairMemberShape first member
  {
    shape := .stable (Pair.Proper.plan first.shape dependentMember)
    interface := {
      arguments := Pair.Proper.exactArguments first.shape dependentMember
        first.interface.arguments (pairMemberArguments first member)
    }
    formation := .properPair first.formation
      (weakenedMemberFormation first member)
  }

noncomputable def compileValuePair
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext)
    (firstIndex memberIndex : Fin n) (label : LambdaPFC.Name) :
    Computation sourceContext targetContext
      (.Pair (.Single (.var firstIndex)) label
        (.ty (.Single ((LambdaPFC.Path.var memberIndex).weaken)))) :=
  material environment
    (valuePairSlot environment firstIndex memberIndex label)

/-! ## Exact type-member pairs -/

private noncomputable def liftEndpoint
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {firstSource endpointSource : LambdaPFC.Ty n}
    (first : Slot sourceContext targetContext firstSource)
    (endpoint : Proper sourceContext targetContext endpointSource) :
    Proper (sourceContext.snoc firstSource)
      (first.shape.context targetContext) endpointSource.weaken where
  shape := endpoint.shape.rename first.shape.binders.weaken
  formation := (endpoint.formation.sourceWeaken firstSource).targetRename
    first.shape.binders.weaken
    (first.shape.binders.weaken_typed targetContext)

private noncomputable def typePairInterface
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {endpointSource : LambdaPFC.Ty (n + 1)}
    (first : Slot sourceContext targetContext firstSource)
    (endpoint : Proper (sourceContext.snoc firstSource)
      (first.shape.context targetContext) endpointSource) :
    Shape.Interface targetContext
      (.stable
        (Pair.Interval.plan first.shape endpoint.shape endpoint.shape)) :=
  let opened := endpoint.shape.subst first.interface.substitution
  {
    arguments := Pair.Interval.exactArguments first.shape endpoint.shape
      endpoint.shape first.interface opened
      (Adapter.identity opened.inputTy)
      (Adapter.identity_hasType targetContext opened.inputTy)
      (Adapter.identity opened.inputTy)
      (Adapter.identity_hasType targetContext opened.inputTy)
  }

theorem typePairInterface_expression
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {endpointSource : LambdaPFC.Ty (n + 1)}
    (first : Slot sourceContext targetContext firstSource)
    (endpoint : Proper (sourceContext.snoc firstSource)
      (first.shape.context targetContext) endpointSource) :
    (typePairInterface first endpoint).package =
      Introduction.typePair first.erase {
        shape := endpoint.shape
        rep := endpoint.formation.rep
      } := by
  rfl

/-- Exact formed Slot for a literal equal-endpoint type pair. -/
noncomputable def typePairSlot
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext)
    (index : Fin n) (label : LambdaPFC.Name)
    {endpointSource : LambdaPFC.Ty n}
    (endpointWf : LambdaPFC.Tau.Wf sourceContext (.ty endpointSource)) :
    Slot sourceContext targetContext
      (.Pair (.Single (.var index)) label
        (LambdaPFC.Tau.intv endpointSource endpointSource).weaken) := by
  let firstTyping : LambdaPFC.Path.Ty sourceContext (.var index)
      (.ty (sourceContext.lookup index)) := .var
  let first := pathSlot firstTyping environment
  cases WfCompiler.compile endpointWf environment with
  | proper endpoint =>
      let lifted := liftEndpoint first endpoint
      exact {
        shape := .stable
          (Pair.Interval.plan first.shape lifted.shape lifted.shape)
        interface := typePairInterface first lifted
        formation := .intervalPair first.formation lifted.formation
          lifted.formation
      }

noncomputable def compileTypePair
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext)
    (index : Fin n) (label : LambdaPFC.Name)
    {endpointSource : LambdaPFC.Ty n}
    (endpointWf : LambdaPFC.Tau.Wf sourceContext (.ty endpointSource)) :
    Computation sourceContext targetContext
      (.Pair (.Single (.var index)) label
        (LambdaPFC.Tau.intv endpointSource endpointSource).weaken) :=
  material environment
    (typePairSlot environment index label endpointWf)

/-! ## Exact let checking and closure -/

/-- Shared let core whose consumer is indexed by the exact unweakened Wf
result. -/
private noncomputable def compileLetExact
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {boundSource resultSource : LambdaPFC.Ty n}
    {bodyTerm : LambdaPFC.Tm (n + 1)}
    (bound : Computation sourceContext targetContext boundSource)
    (bodyTyping : LambdaPFC.Tm.Ty (sourceContext.snoc boundSource)
      bodyTerm resultSource.weaken)
    (bodyCompiler : AgainstCompiler bodyTyping)
    (result : Proper sourceContext targetContext resultSource)
    (answer : Ty sig)
    (consumer : AgainstConsumer sourceContext targetContext answer
      resultSource result) :
    Path.Body targetContext answer :=
  bound answer (fun {current} {currentContext} mapping typed
      currentEnvironment boundSlot => by
    let opening := boundSlot.shape.binders.weaken
    let openingTyped :=
      boundSlot.shape.binders.weaken_typed currentContext
    let combined := mapping.comp opening
    let combinedTyped := TypedRename.comp typed openingTyped
    let openedEnvironment := currentEnvironment.enter boundSource
      boundSlot.formation
    let resultAt := result.targetRename combined combinedTyped
    let expected : Proper (sourceContext.snoc boundSource)
        (boundSlot.shape.context currentContext) resultSource.weaken := {
      shape := resultAt.shape
      formation := resultAt.formation.sourceWeaken boundSource
    }
    let openedBody := bodyCompiler openedEnvironment expected
      (answer.rename combined)
      (fun {current} {currentContext} bodyMapping bodyTyped
          _bodyEnvironment bodyInterface => by
        let totalMapping := combined.comp bodyMapping
        let totalTyped := TypedRename.comp combinedTyped bodyTyped
        let outerEnvironment := currentEnvironment.targetRename
          (opening.comp bodyMapping)
          (TypedRename.comp openingTyped bodyTyped)
        let normalizedInterface : Shape.Interface currentContext
            (result.shape.rename totalMapping) := by
          have normalized := bodyInterface
          change Shape.Interface currentContext
            ((result.shape.rename combined).rename bodyMapping) at normalized
          rw [Shape.rename_comp] at normalized
          exact normalized
        simpa only [totalMapping, Ty.rename_comp] using
          consumer totalMapping totalTyped outerEnvironment
            normalizedInterface)
    exact {
      expression := Introduction.bind boundSlot.shape
        boundSlot.interface.package (answer.rename mapping)
        openedBody.expression
      typing := by
        apply Introduction.bind_hasType boundSlot.interface.package_hasType
        simpa only [combined, Ty.rename_comp] using openedBody.typing
    })

/-- Compile a let body against the exact weakened Formation obtained from its
Wf premise.  The runtime Interface is reused with the independently renamed
original Formation when the outer source binding is discharged; source
indices are never cast. -/
noncomputable def compileLet
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {boundTerm : LambdaPFC.Tm n} {boundSource : LambdaPFC.Ty n}
    {resultSource : LambdaPFC.Ty n}
    {bodyTerm : LambdaPFC.Tm (n + 1)}
    (_boundTyping : LambdaPFC.Tm.Ty sourceContext boundTerm boundSource)
    (bound : Computation sourceContext targetContext boundSource)
    (resultWf : LambdaPFC.Tau.Wf sourceContext (.ty resultSource))
    (bodyTyping : LambdaPFC.Tm.Ty (sourceContext.snoc boundSource)
      bodyTerm resultSource.weaken)
    (bodyCompiler : AgainstCompiler bodyTyping)
    (environment : Env sourceContext targetContext) :
    Computation sourceContext targetContext resultSource := by
  cases WfCompiler.compile resultWf environment with
  | proper result =>
      exact fun answer consumer =>
        compileLetExact bound bodyTyping bodyCompiler result answer
          (fun mapping typed currentEnvironment interface =>
            let slot : Slot sourceContext _ resultSource := {
              shape := result.shape.rename mapping
              interface := interface
              formation := result.formation.targetRename mapping typed
            }
            consumer mapping typed currentEnvironment slot)

/-- Material let result for the future total synthesizer.  The let expression
is first checked at the exact Wf package type, then sealed behind the generic
one-field carrier; no argument spine is extracted from the expression. -/
noncomputable def compileLetSealed
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {boundTerm : LambdaPFC.Tm n} {boundSource : LambdaPFC.Ty n}
    {resultSource : LambdaPFC.Ty n}
    {bodyTerm : LambdaPFC.Tm (n + 1)}
    (_boundTyping : LambdaPFC.Tm.Ty sourceContext boundTerm boundSource)
    (bound : Computation sourceContext targetContext boundSource)
    (resultWf : LambdaPFC.Tau.Wf sourceContext (.ty resultSource))
    (bodyTyping : LambdaPFC.Tm.Ty (sourceContext.snoc boundSource)
      bodyTerm resultSource.weaken)
    (bodyCompiler : AgainstCompiler bodyTyping)
    (environment : Env sourceContext targetContext) :
    Slot sourceContext targetContext resultSource := by
  cases WfCompiler.compile resultWf environment with
  | proper result =>
      let package := compileLetExact bound bodyTyping bodyCompiler result
        result.shape.inputTy
        (fun mapping _typed _currentEnvironment interface => {
          expression := interface.package
          typing := by
            simpa only [Shape.inputTy_rename] using
              interface.package_hasType
        })
      exact sealResult result package.expression package.typing

end LambdaPToFCo.Direct.Internal.TermComputation
