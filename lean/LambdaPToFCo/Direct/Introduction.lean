import LambdaPToFCo.Direct.Wf

/-!
# Direct target-term introductions

These helpers construct the ordinary `SystemFCo.Exp` terms needed by the
first end-to-end direct compiler regression.  They consume exact shapes,
interfaces, and representations already established by focused path or Wf
compilation.  No helper infers a source proof, reifies a hidden identity, or
adds target syntax.
-/

namespace LambdaPToFCo.Direct.Internal.Introduction

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation

/-- Introduce the singleton of an exact path slot.

The referent is the complete package type accepted by the slot's shape, and
the singleton payload is that slot's exact reclosed package.  Consequently a
later widen can recover the package and inspect it using the retained `Rep`. -/
noncomputable def singleton
    {targetContext : SystemFCo.Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (slot : Slot targetContext sourceType) : SystemFCo.Exp sig :=
  Single.exactPackage slot.shape.inputTy slot.interface.package
    slot.interface.package_hasType

/-- Exact singleton introduction typing in unchanged System FCo. -/
noncomputable def singleton_hasType
    {targetContext : SystemFCo.Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (slot : Slot targetContext sourceType) :
    SystemFCo.Exp.HasType targetContext (singleton slot)
      (Single.plan slot.shape.inputTy).inputTy :=
  Single.exactPackage_hasType slot.shape.inputTy slot.interface.package
    slot.interface.package_hasType

/-- Source-indexed singleton representation corresponding to `singleton`. -/
noncomputable def singletonRepresentation
    {targetContext : SystemFCo.Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (path : LambdaPFC.Path n)
    (slot : Slot targetContext sourceType) :
    Wf.Proper targetContext (.Single path) :=
  Wf.Proper.singletonFromSlot path slot

noncomputable def singleton_hasRepresentationType
    {targetContext : SystemFCo.Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (path : LambdaPFC.Path n)
    (slot : Slot targetContext sourceType) :
    SystemFCo.Exp.HasType targetContext (singleton slot)
      (singletonRepresentation path slot).shape.inputTy :=
  singleton_hasType slot

/-- Introduce an exact function package from a body typed under the complete
domain interface telescope.

The telescope lambda is the executable function code.  `Function.exactPackage`
uses that code type itself as the hidden function identity and retains an
ordinary identity observation from the payload to the code. -/
noncomputable def function
    {targetContext : SystemFCo.Ctx sig}
    (domain : Shape sig) (codomain : Shape domain.scope)
    (body : SystemFCo.Exp domain.scope)
    (bodyTyping : SystemFCo.Exp.HasType (domain.context targetContext)
      body codomain.inputTy) : SystemFCo.Exp sig :=
  Function.exactPackage domain codomain
    (domain.binders.lambda body)
    (by
      change SystemFCo.Exp.HasType targetContext
        (domain.binders.lambda body)
        (domain.binders.forallTy codomain.inputTy)
      exact domain.binders.lambda_hasType bodyTyping)

/-- Exact function introduction typing in unchanged System FCo. -/
noncomputable def function_hasType
    {targetContext : SystemFCo.Ctx sig}
    (domain : Shape sig) (codomain : Shape domain.scope)
    (body : SystemFCo.Exp domain.scope)
    (bodyTyping : SystemFCo.Exp.HasType (domain.context targetContext)
      body codomain.inputTy) :
    SystemFCo.Exp.HasType targetContext
      (function domain codomain body bodyTyping)
      (Function.plan domain codomain).inputTy := by
  apply Function.exactPackage_hasType

/-- Introduce an exact interval type pair whose two endpoints are the same
well-formed proper type under the first component's exact opened scope. -/
noncomputable def typePair
    {targetContext : SystemFCo.Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {endpointSource : LambdaPFC.Ty (n + 1)}
    (first : Slot targetContext firstSource)
    (endpoint : Wf.Proper (first.shape.context targetContext)
      endpointSource) : SystemFCo.Exp sig :=
  Pair.Interval.exactTypePair first.shape endpoint.shape first.interface

/-- Exact interval type-pair introduction typing in unchanged System FCo. -/
noncomputable def typePair_hasType
    {targetContext : SystemFCo.Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {endpointSource : LambdaPFC.Ty (n + 1)}
    (first : Slot targetContext firstSource)
    (endpoint : Wf.Proper (first.shape.context targetContext)
      endpointSource) :
    SystemFCo.Exp.HasType targetContext (typePair first endpoint)
      (Pair.Interval.plan first.shape endpoint.shape endpoint.shape).inputTy :=
  Pair.Interval.exactTypePair_hasType first.shape endpoint.shape
    first.interface

/-- The exact source-indexed representation introduced by `typePair`. -/
def typePairRepresentation
    {targetContext : SystemFCo.Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {endpointSource : LambdaPFC.Ty (n + 1)}
    (label : LambdaPFC.Name)
    (first : Slot targetContext firstSource)
    (endpoint : Wf.Proper (first.shape.context targetContext)
      endpointSource) :
    Wf.Proper targetContext
      (.Pair firstSource label (.intv endpointSource endpointSource)) :=
  Wf.Proper.intervalPair label
    { shape := first.shape, rep := first.rep }
    (Wf.Interval.bounds endpoint endpoint)

noncomputable def typePair_hasRepresentationType
    {targetContext : SystemFCo.Ctx sig}
    {firstSource : LambdaPFC.Ty n}
    {endpointSource : LambdaPFC.Ty (n + 1)}
    (label : LambdaPFC.Name)
    (first : Slot targetContext firstSource)
    (endpoint : Wf.Proper (first.shape.context targetContext)
      endpointSource) :
    SystemFCo.Exp.HasType targetContext (typePair first endpoint)
      (typePairRepresentation label first endpoint).shape.inputTy :=
  typePair_hasType first endpoint

/-- Eliminate a compiled bound package and close one typed body around every
shape binder.  Stable shapes use Church elimination; opaque shapes use an
ordinary lambda/application. -/
def bind (shape : Shape sig) (bound : SystemFCo.Exp sig)
    (answer : SystemFCo.Ty sig)
    (body : SystemFCo.Exp shape.scope) : SystemFCo.Exp sig :=
  shape.eliminate bound answer body

/-- Extrinsic typing for shape-eliminating direct lets. -/
noncomputable def bind_hasType
    {targetContext : SystemFCo.Ctx sig}
    {shape : Shape sig} {bound : SystemFCo.Exp sig}
    {answer : SystemFCo.Ty sig} {body : SystemFCo.Exp shape.scope}
    (boundTyping : SystemFCo.Exp.HasType targetContext bound shape.inputTy)
    (bodyTyping : SystemFCo.Exp.HasType (shape.context targetContext) body
      (answer.rename shape.binders.weaken)) :
    SystemFCo.Exp.HasType targetContext (bind shape bound answer body) answer :=
  shape.eliminate_hasType boundTyping bodyTyping

/-- Eliminating a reclosed exact interface executes the body with precisely
that interface substitution. -/
theorem bind_interface_steps
    {targetContext : SystemFCo.Ctx sig}
    {shape : Shape sig}
    (interface : Shape.Interface targetContext shape)
    (argumentsValue : interface.AllValues)
    (answer : SystemFCo.Ty sig) (body : SystemFCo.Exp shape.scope) :
    SystemFCo.Exp.Steps
      (bind shape interface.package answer body)
      (body.subst interface.substitution) :=
  shape.eliminate_interface_steps interface argumentsValue answer body

end LambdaPToFCo.Direct.Internal.Introduction
