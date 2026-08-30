import Coercions.DOT.Captures.BinderOnly.Context

/-!
# Proof-relevant static inclusion for the binder-only source

The judgment in this file is source-owned and sort indexed.  Interval lower
and upper endpoints are exposed by separate certificates: neither lookup rule
requires the other endpoint, and neither asks that the endpoints be mutually
consistent.  This is the source-level bad-bounds discipline that a later
elaboration translates into explicit target evidence.
-/

namespace DOTCapture.BinderOnly

namespace StaticRef

/-- Embed a sorted static reference into the corresponding source expression
sort. -/
def expression {scope : Sig} {sort : StaticSort}
    (reference : StaticRef sort scope) : StaticExpr sort scope :=
  reference.asExpression

@[simp]
theorem expression_eq_asExpression {scope : Sig} {sort : StaticSort}
    (reference : StaticRef sort scope) :
    reference.expression = reference.asExpression := rfl

end StaticRef

/-- Proof that a reference's interval supplies this lower endpoint.

The unused upper endpoint remains arbitrary, so lower-bound lookup is
independent of upper-bound lookup.  This separate certificate also leaves
room for future path-selected members to add their own lookup provenance. -/
inductive HasLower {scope : Sig} (context : Ctx scope) :
    {sort : StaticSort} -> StaticRef sort scope ->
      StaticExpr sort scope -> Type where
  | bound {sort : StaticSort} {index : BVar scope (.static sort)}
      {lower : StaticExpr sort scope} {upper : Endpoint sort scope}
      (found : context.lookupStatic index =
        .bounds (.some lower) upper) :
      HasLower context (.bound index) lower

/-- Proof that a reference's interval supplies this upper endpoint.

The unused lower endpoint remains arbitrary, so upper-bound lookup is
independent of lower-bound lookup. -/
inductive HasUpper {scope : Sig} (context : Ctx scope) :
    {sort : StaticSort} -> StaticRef sort scope ->
      StaticExpr sort scope -> Type where
  | bound {sort : StaticSort} {index : BVar scope (.static sort)}
      {lower : Endpoint sort scope} {upper : StaticExpr sort scope}
      (found : context.lookupStatic index =
        .bounds lower (.some upper)) :
      HasUpper context (.bound index) upper

/-- Proof-relevant directed inclusion, intrinsically requiring both endpoints
to have the same static sort and scope. -/
inductive Includes {scope : Sig} (context : Ctx scope) :
    {sort : StaticSort} -> StaticExpr sort scope ->
      StaticExpr sort scope -> Type where
  | refl {sort : StaticSort} {expression : StaticExpr sort scope} :
      Includes context expression expression
  | trans {sort : StaticSort} {source middle target : StaticExpr sort scope}
      (first : Includes context source middle)
      (second : Includes context middle target) :
      Includes context source target
  | lower {sort : StaticSort} {reference : StaticRef sort scope}
      {endpoint : StaticExpr sort scope}
      (bound : HasLower context reference endpoint) :
      Includes context endpoint reference.expression
  | upper {sort : StaticSort} {reference : StaticRef sort scope}
      {endpoint : StaticExpr sort scope}
      (bound : HasUpper context reference endpoint) :
      Includes context reference.expression endpoint
  | typeTop {type : Ty scope} :
      Includes context (.type type) (.type .top)
  | typeBottom {type : Ty scope} :
      Includes context (.type .bot) (.type type)
  | typeArrow {sourceDomain targetDomain sourceCodomain targetCodomain :
        Ty scope}
      (domain : Includes context (.type targetDomain)
        (.type sourceDomain))
      (codomain : Includes context (.type sourceCodomain)
        (.type targetCodomain)) :
      Includes context (.type (.arr sourceDomain sourceCodomain))
        (.type (.arr targetDomain targetCodomain))
  | typeCapturing {sourceCaptures targetCaptures : Capture scope}
      {sourceShape targetShape : Ty scope}
      (captures : Includes context (.capture sourceCaptures)
        (.capture targetCaptures))
      (shape : Includes context (.type sourceShape) (.type targetShape)) :
      Includes context (.type (.capturing sourceCaptures sourceShape))
        (.type (.capturing targetCaptures targetShape))
  | captureEmpty {captures : Capture scope} :
      Includes context (.capture .empty) (.capture captures)
  | captureUnionLeft {left right : Capture scope} :
      Includes context (.capture left) (.capture (.union left right))
  | captureUnionRight {left right : Capture scope} :
      Includes context (.capture right) (.capture (.union left right))
  | captureUnionElim {left right target : Capture scope}
      (fromLeft : Includes context (.capture left) (.capture target))
      (fromRight : Includes context (.capture right) (.capture target)) :
      Includes context (.capture (.union left right)) (.capture target)

/-- The type-specialized view of sorted inclusion. -/
abbrev TypeIncludes {scope : Sig} (context : Ctx scope)
    (source target : Ty scope) : Type :=
  Includes context (.type source) (.type target)

/-- The capture-specialized view of sorted inclusion. -/
abbrev CaptureIncludes {scope : Sig} (context : Ctx scope)
    (source target : Capture scope) : Type :=
  Includes context (.capture source) (.capture target)

namespace BadBoundsExamples

/-- A syntactically valid type interval whose endpoints are `Top` and
`Bottom`.  Formation carries no consistency field. -/
def typeContext : Ctx ([] ▹ .static .type) :=
  Ctx.nil.extendStatic
    (.bounds (.some (.type .top)) (.some (.type .bot)))

/-- The type reference introduced by `typeContext`. -/
def typeReference : StaticRef .type ([] ▹ .static .type) :=
  .bound .here

/-- Independent interval assumptions compose to derive `Top <= Bottom` in the
hypothetical bad-bounds context. -/
def topIncludesBottom :
    TypeIncludes typeContext .top .bot :=
  Includes.trans
    (Includes.lower (HasLower.bound (context := typeContext)
      (index := (.here : BVar ([] ▹ .static .type) (.static .type))) rfl))
    (Includes.upper (HasUpper.bound (context := typeContext)
      (index := (.here : BVar ([] ▹ .static .type) (.static .type))) rfl))

/-- A term capability followed by an abstract capture variable whose lower
endpoint is that capability and whose upper endpoint is empty. -/
def captureContext : Ctx ([] ▹ .term ▹ .static .capture) :=
  (Ctx.nil.extendTerm .one).extendStatic
    (.bounds
      (.some (.capture (.singleton (.var .here))))
      (.some (.capture .empty)))

/-- The capability remains the older term variable after adding the capture
binder. -/
def capability : Path ([] ▹ .term ▹ .static .capture) :=
  .var (.there .here)

/-- Independent capture interval assumptions compose to derive
`{capability} <= {}` in the hypothetical bad-bounds context. -/
def singletonIncludesEmpty :
    CaptureIncludes captureContext (.singleton capability) .empty :=
  Includes.trans
    (Includes.lower (HasLower.bound (context := captureContext)
      (index := (.here : BVar
        ([] ▹ .term ▹ .static .capture) (.static .capture))) rfl))
    (Includes.upper (HasUpper.bound (context := captureContext)
      (index := (.here : BVar
        ([] ▹ .term ▹ .static .capture) (.static .capture))) rfl))

end BadBoundsExamples

end DOTCapture.BinderOnly
