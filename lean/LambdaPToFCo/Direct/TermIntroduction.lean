import LambdaPToFCo.Direct.Introduction

/-!
# Direct term-introduction compiler kernel

This leaf provides the source-indexed value handoff used by derivation-directed
term compilation.  A `ValueConsumer` receives the exact current source
environment and one compiled `Representation.Slot`; target types opened while
following a path or eliminating a let-bound package therefore stay inside the
consumer body.

Path terms and exact type pairs construct their exact target interfaces.
Function abstraction is intentionally material: its recursively compiled body
must already be a slot in the domain's precise opened scope.  Pulling a body
slot back after an additional focused existential would require scope evidence
that the current representation API does not provide, so this file does not
claim a total term dispatcher.
-/

namespace LambdaPToFCo.Direct.Internal.TermIntroduction

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation

/-- A value consumer natural in every target scope opened during compilation. -/
abbrev ValueConsumer
    {n : Nat} {root : Sig} (sourceContext : LambdaPFC.Ctx n)
    (rootContext : SystemFCo.Ctx root) (answer : SystemFCo.Ty root)
    (sourceType : LambdaPFC.Ty n) : Type :=
  forall {current : Sig} {currentContext : SystemFCo.Ctx current},
    (mapping : SystemFCo.Rename root current) ->
    SystemFCo.Rename.Typed rootContext currentContext mapping ->
    Env sourceContext currentContext ->
    Slot currentContext sourceType ->
    Path.Body currentContext (answer.rename mapping)

/-- A scope-closing computation that eventually supplies one exact source
value slot to its consumer. -/
abbrev ValueComputation
    {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {root : Sig} (rootContext : SystemFCo.Ctx root)
    (sourceType : LambdaPFC.Ty n) : Type :=
  (answer : SystemFCo.Ty root) ->
  ValueConsumer sourceContext rootContext answer sourceType ->
  Path.Body rootContext answer

/-- Invoke a value consumer in its root scope. -/
private noncomputable def consumeHere
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    {answer : SystemFCo.Ty sig}
    {sourceType : LambdaPFC.Ty n}
    (environment : Env sourceContext targetContext)
    (slot : Slot targetContext sourceType)
    (consumer : ValueConsumer sourceContext targetContext answer sourceType) :
    Path.Body targetContext answer := by
  simpa only [SystemFCo.Ty.rename_id] using
    consumer SystemFCo.Rename.id (TypedRename.id targetContext)
      environment slot

/-! ## Exact material slots -/

/-- Package the singleton of an exact path referent as a source-indexed Slot. -/
noncomputable def singletonSlot
    {targetContext : SystemFCo.Ctx sig}
    {referentSource : LambdaPFC.Ty n}
    (path : LambdaPFC.Path n)
    (referent : Slot targetContext referentSource) :
    Slot targetContext (.Single path) where
  shape := .stable (Single.plan referent.shape.inputTy)
  interface := {
    arguments := Single.exactArguments referent.shape.inputTy
      referent.interface.package referent.interface.package_hasType }
  rep := .singleton targetContext path referent.shape.inputTy

/-- The package reclosed from `singletonSlot` is the direct singleton
introduction term. -/
theorem singletonSlot_expression
    {targetContext : SystemFCo.Ctx sig}
    {referentSource : LambdaPFC.Ty n}
    (path : LambdaPFC.Path n)
    (referent : Slot targetContext referentSource) :
    (singletonSlot path referent).expression =
      Introduction.singleton referent := by
  rfl

/-- A variable path is already resolved by the current environment. -/
noncomputable def variableSlot
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    (environment : Env sourceContext targetContext)
    (index : Fin n) :
    Slot targetContext (.Single (.var index)) :=
  singletonSlot (.var index) (environment.lookup index)

/-- Assemble an exact function Slot from a domain Wf representation and a
recursively compiled body Slot in the domain's precise opened scope. -/
noncomputable def abstractSlot
    {targetContext : SystemFCo.Ctx sig}
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    (domain : Wf.Proper targetContext domainSource)
    (body : Slot (domain.shape.context targetContext) codomainSource) :
    Slot targetContext (.Fun domainSource codomainSource) where
  shape := .stable (Function.plan domain.shape body.shape)
  interface := {
    arguments := Function.exactArguments domain.shape body.shape
      (domain.shape.binders.lambda body.interface.package)
      (domain.shape.binders.lambda_hasType
        body.interface.package_hasType) }
  rep := .function domain.rep body.rep

/-- The exact function Slot recloses to `Introduction.function`. -/
theorem abstractSlot_expression
    {targetContext : SystemFCo.Ctx sig}
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    (domain : Wf.Proper targetContext domainSource)
    (body : Slot (domain.shape.context targetContext) codomainSource) :
    (abstractSlot domain body).expression =
      Introduction.function domain.shape body.shape body.interface.package
        body.interface.package_hasType := by
  rfl

/-- Lift a material endpoint beneath the exact first-component interface. -/
noncomputable def liftEndpoint
    {targetContext : SystemFCo.Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {endpointSource : LambdaPFC.Ty n}
    (first : Slot targetContext firstSource)
    (endpoint : Wf.Proper targetContext endpointSource) :
    Wf.Proper (first.shape.context targetContext) endpointSource.weaken where
  shape := endpoint.shape.rename first.shape.binders.weaken
  rep := (endpoint.rep.sourceRename LambdaPFC.FinFun.weaken).targetRename
    first.shape.binders.weaken
    (first.shape.binders.weaken_typed targetContext)

/-- Exact interface of a type pair with equal endpoints. -/
noncomputable def typePairInterface
    {targetContext : SystemFCo.Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {endpointSource : LambdaPFC.Ty (n + 1)}
    (first : Slot targetContext firstSource)
    (endpoint : Wf.Proper (first.shape.context targetContext)
      endpointSource) :
    Shape.Interface targetContext
      (.stable
        (Pair.Interval.plan first.shape endpoint.shape endpoint.shape)) :=
  let opened := endpoint.shape.subst first.interface.substitution
  { arguments := Pair.Interval.exactArguments first.shape endpoint.shape
      endpoint.shape first.interface opened
      (Adapter.identity opened.inputTy)
      (Adapter.identity_hasType targetContext opened.inputTy)
      (Adapter.identity opened.inputTy)
      (Adapter.identity_hasType targetContext opened.inputTy) }

/-- Compile an exact source type-pair introduction to a source-indexed Slot. -/
noncomputable def typePairSlot
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    (environment : Env sourceContext targetContext)
    (index : Fin n) (label : LambdaPFC.Name)
    {endpointSource : LambdaPFC.Ty n}
    (endpoint : Wf.Proper targetContext endpointSource) :
    Slot targetContext
      (.Pair (.Single (.var index)) label
        (LambdaPFC.Tau.intv endpointSource endpointSource).weaken) :=
  let first := variableSlot environment index
  let lifted := liftEndpoint first endpoint
  { shape := .stable
      (Pair.Interval.plan first.shape lifted.shape lifted.shape)
    interface := typePairInterface first lifted
    rep := .intervalPair first.rep lifted.rep lifted.rep }

/-- The exact type-pair Slot recloses to `Introduction.typePair`. -/
theorem typePairSlot_expression
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    (environment : Env sourceContext targetContext)
    (index : Fin n) (label : LambdaPFC.Name)
    {endpointSource : LambdaPFC.Ty n}
    (endpoint : Wf.Proper targetContext endpointSource) :
    (typePairSlot environment index label endpoint).expression =
      Introduction.typePair (variableSlot environment index)
        (liftEndpoint (variableSlot environment index) endpoint) := by
  rfl

/-! ## Constructor-specific compilation kernels -/

/-- Compile `Tm.Ty.path`: focus the precise referent, introduce its singleton,
and expose the resulting exact Slot only inside the focused scope. -/
noncomputable def compilePath
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty referent))
    {targetContext : SystemFCo.Ctx sig}
    (environment : Env sourceContext targetContext) :
    ValueComputation sourceContext targetContext (.Single path) :=
  fun answer consumer =>
    Path.compile typing environment answer (fun mapping typed nextEnvironment
        view => by
      cases view with
      | proper referentSlot =>
          exact consumer mapping typed nextEnvironment
            (singletonSlot path referentSlot))

/-- Expose an already-materialized compiled Slot. -/
noncomputable def compileMaterial
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (environment : Env sourceContext targetContext)
    (slot : Slot targetContext sourceType) :
    ValueComputation sourceContext targetContext sourceType :=
  fun _answer consumer => consumeHere environment slot consumer

/-- Constructor-specific exact abstraction.  The body argument is the result
of recursive compilation materialized in exactly the domain scope. -/
noncomputable def compileAbstract
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    {domainSource : LambdaPFC.Ty n}
    {codomainSource : LambdaPFC.Ty (n + 1)}
    (environment : Env sourceContext targetContext)
    (domain : Wf.Proper targetContext domainSource)
    (body : Slot (domain.shape.context targetContext) codomainSource) :
    ValueComputation sourceContext targetContext
      (.Fun domainSource codomainSource) :=
  compileMaterial environment (abstractSlot domain body)

/-- Constructor-specific exact type-pair introduction. -/
noncomputable def compileTypePair
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    (environment : Env sourceContext targetContext)
    (index : Fin n) (label : LambdaPFC.Name)
    {endpointSource : LambdaPFC.Ty n}
    (endpoint : Wf.Proper targetContext endpointSource) :
    ValueComputation sourceContext targetContext
      (.Pair (.Single (.var index)) label
        (LambdaPFC.Tau.intv endpointSource endpointSource).weaken) :=
  compileMaterial environment
    (typePairSlot environment index label endpoint)

/-! ## Scope-safe let binding -/

/-- Body compiler expected by the let kernel.

The material result fixes the exact target shape for the source result type at
the current scope.  Recursive compilation of the source body (whose type is
the weakening of that result) supplies an interface at precisely this shape;
the callback never asks for or fabricates a shape equality. -/
abbrev LetBodyCompiler
    {n : Nat} {root : Sig} (sourceContext : LambdaPFC.Ctx n)
    (rootContext : SystemFCo.Ctx root) (answer : SystemFCo.Ty root)
    (boundSource resultSource : LambdaPFC.Ty n) : Type :=
  forall {current : Sig} {currentContext : SystemFCo.Ctx current},
    (mapping : SystemFCo.Rename root current) ->
    (typed : SystemFCo.Rename.Typed rootContext currentContext mapping) ->
    Env (sourceContext.snoc boundSource) currentContext ->
    (result : Wf.Proper currentContext resultSource) ->
    (consume : Shape.Interface currentContext result.shape ->
      Path.Body currentContext (answer.rename mapping)) ->
    Path.Body currentContext (answer.rename mapping)

/-- Compile a let by compiling its bound, reopening that exact package around
the body, and extending the source environment with the canonical interface
available in the elimination scope. -/
noncomputable def compileLet
    {sourceContext : LambdaPFC.Ctx n}
    {targetContext : SystemFCo.Ctx sig}
    {boundSource resultSource : LambdaPFC.Ty n}
    (bound : ValueComputation sourceContext targetContext boundSource)
    (result : Wf.Proper targetContext resultSource)
    (answer : SystemFCo.Ty sig)
    (body : LetBodyCompiler sourceContext targetContext answer
      boundSource resultSource)
    (consumer : ValueConsumer sourceContext targetContext answer
      resultSource) :
    Path.Body targetContext answer :=
  bound answer (fun {current} {currentContext} mapping typed
      currentEnvironment boundSlot => by
    let opening := boundSlot.shape.binders.weaken
    let openingTyped :=
      boundSlot.shape.binders.weaken_typed currentContext
    let combined := mapping.comp opening
    let combinedTyped := TypedRename.comp typed openingTyped
    let openedRep :=
      (boundSlot.rep.sourceRename LambdaPFC.FinFun.weaken).targetRename
        opening openingTyped
    let openedEnvironment := currentEnvironment.extend opening openingTyped
      boundSource (Shape.Interface.canonical currentContext boundSlot.shape)
      openedRep
    let resultAt := result.targetRename combined combinedTyped
    let openedBody := body combined combinedTyped openedEnvironment resultAt
      (fun resultInterface =>
        consumer combined combinedTyped
          (currentEnvironment.targetRename opening openingTyped)
          { shape := resultAt.shape
            interface := resultInterface
            rep := resultAt.rep })
    exact {
      expression := Introduction.bind boundSlot.shape
        boundSlot.interface.package (answer.rename mapping)
        openedBody.expression
      typing := by
        apply Introduction.bind_hasType boundSlot.interface.package_hasType
        simpa only [SystemFCo.Ty.rename_comp] using openedBody.typing })

end LambdaPToFCo.Direct.Internal.TermIntroduction
