import Coercions.DOT.Captures.BinderOnly.Term
import Coercions.DOT.Captures.BinderOnly.Substitution
import Coercions.DOT.Captures.BinderOnly.Subtyping

/-!
# Typing for the binder-only DOT-with-captures source

The mutually defined judgments follow the source's ANF split: value
eliminations consume `Value`s, computations are sequenced only by `let'`, and
implicit adaptation is available only for values.  This keeps structural
function adaptation from duplicating or delaying arbitrary computation.

Static introduction and elimination also expose the no-self-discharge
boundary.  A concrete witness realizes its interval in the ambient context;
hypothetical interval assumptions enter the context only inside a static
abstraction or existential open body.
-/

namespace DOTCapture.BinderOnly

mutual

/-- Declarative typing of source values. -/
inductive Value.HasType : {scope : Sig} -> Ctx scope ->
    Value scope -> Ty scope -> Type where
  | var {scope : Sig} {context : Ctx scope}
      {name : BVar scope .term} :
      Value.HasType context (.var name) (context.lookupTerm name)
  | unit {scope : Sig} {context : Ctx scope} :
      Value.HasType context .unit .one
  | lam {scope : Sig} {context : Ctx scope} {domain codomain : Ty scope}
      {body : Term (scope ▹ .term)}
      (bodyTyping : Term.HasType (context.extendTerm domain) body
        (codomain.weaken (kind := .term))) :
      Value.HasType context (.lam domain codomain body)
        (.arr domain codomain)
  | staticLam {scope : Sig} {context : Ctx scope} {sort : StaticSort}
      {interval : Interval sort scope}
      {body : Value (scope ▹ .static sort)}
      {bodyType : Ty (scope ▹ .static sort)}
      (bodyTyping : Value.HasType (context.extendStatic interval)
        body bodyType) :
      Value.HasType context (.staticLam interval body)
        (.forallI interval bodyType)
  | pack {scope : Sig} {context : Ctx scope} {sort : StaticSort}
      {interval : Interval sort scope}
      {payloadType : Ty (scope ▹ .static sort)}
      {witness : StaticExpr sort scope} {payload : Value scope}
      (satisfaction : Interval.SatisfiedBy context witness interval)
      (payloadTyping : Value.HasType context payload
        (payloadType.instantiateStatic witness)) :
      Value.HasType context
        (.pack interval payloadType witness payload)
        (.existsI interval payloadType)
  | adapt {scope : Sig} {context : Ctx scope} {value : Value scope}
      {source target : Ty scope}
      (valueTyping : Value.HasType context value source)
      (adapter : Adapts context source target) :
      Value.HasType context value target

/-- Declarative typing of source ANF computations. -/
inductive Term.HasType : {scope : Sig} -> Ctx scope ->
    Term scope -> Ty scope -> Type where
  | ret {scope : Sig} {context : Ctx scope} {value : Value scope}
      {type : Ty scope} (valueTyping : Value.HasType context value type) :
      Term.HasType context (.ret value) type
  | app {scope : Sig} {context : Ctx scope}
      {function argument : Value scope} {domain codomain : Ty scope}
      (functionTyping : Value.HasType context function
        (.arr domain codomain))
      (argumentTyping : Value.HasType context argument domain) :
      Term.HasType context (.app function argument) codomain
  | let' {scope : Sig} {context : Ctx scope} {result bound : Ty scope}
      {rhs : Term scope} {body : Term (scope ▹ .term)}
      (rhsTyping : Term.HasType context rhs bound)
      (bodyTyping : Term.HasType (context.extendTerm bound) body
        (result.weaken (kind := .term))) :
      Term.HasType context (.let' result rhs body) result
  | staticApp {scope : Sig} {context : Ctx scope} {sort : StaticSort}
      {interval : Interval sort scope} {function : Value scope}
      {argument : StaticExpr sort scope}
      {bodyType : Ty (scope ▹ .static sort)}
      (functionTyping : Value.HasType context function
        (.forallI interval bodyType))
      (satisfaction : Interval.SatisfiedBy context argument interval) :
      Term.HasType context (.staticApp interval function argument)
        (bodyType.instantiateStatic argument)
  | «open» {scope : Sig} {context : Ctx scope} {sort : StaticSort}
      {interval : Interval sort scope}
      {payloadType : Ty (scope ▹ .static sort)} {result : Ty scope}
      {package : Value scope} {body : Term (PayloadScope scope sort)}
      (packageTyping : Value.HasType context package
        (.existsI interval payloadType))
      (bodyTyping : Term.HasType
        ((context.extendStatic interval).extendTerm payloadType) body
        ((result.weaken (kind := .static sort)).weaken (kind := .term))) :
      Term.HasType context
        (.«open» interval payloadType result package body) result

end

namespace TypingExamples

def exactOneInterval : Interval .type [] :=
  Interval.exact (.type .one)

/-- The abstract type selected by the newest static binder. -/
def abstractOneBodyType : Ty ([] ▹ .static .type) :=
  .ref (.bound .here)

/-- The exact interval's lower assumption converts `One` to its abstract
name inside a hypothetical static body. -/
def oneAdaptsToAbstract :
    Adapts (Ctx.nil.extendStatic exactOneInterval)
      .one abstractOneBodyType :=
  .cast (by
    unfold abstractOneBodyType
    change Includes (Ctx.nil.extendStatic exactOneInterval)
      (.type .one) (StaticRef.bound .here).expression
    exact .lower (.bound rfl))

/-- Its independent upper assumption converts the abstract name back to
`One`. -/
def abstractAdaptsToOne :
    Adapts (Ctx.nil.extendStatic exactOneInterval)
      abstractOneBodyType .one :=
  .cast (by
    unfold abstractOneBodyType
    change Includes (Ctx.nil.extendStatic exactOneInterval)
      (StaticRef.bound .here).expression (.type .one)
    exact .upper (.bound rfl))

/-- A closed ANF identity value. -/
def identity : Value [] :=
  .lam .one .one (.ret (.var .here))

/-- The identity body observes the exact type of its newest term binder. -/
def identityTyping :
    Value.HasType Ctx.nil identity (.arr .one .one) :=
  .lam (.ret .var)

/-- A closed static value whose interval is exact `One`. -/
def staticOne : Value [] :=
  .staticLam exactOneInterval .unit

/-- Static abstraction checks its value body under the hypothetical interval;
it does not construct a model at introduction time. -/
def staticOneTyping :
    Value.HasType Ctx.nil staticOne
      (.forallI exactOneInterval .one) :=
  .staticLam .unit

/-- Applying the closed static value requires ambient realization of its exact
interval and instantiates the result type with the supplied witness. -/
def applyStaticOneTyping :
    Term.HasType Ctx.nil
      (.staticApp exactOneInterval staticOne (.type .one))
      .one :=
  .staticApp staticOneTyping Interval.Examples.exactOne

/-- A non-vacuous static abstraction: its result type is the bound abstract
type, and the body uses the lower endpoint to inhabit it. -/
def staticAbstractOne : Value [] :=
  .staticLam exactOneInterval .unit

def staticAbstractOneTyping :
    Value.HasType Ctx.nil staticAbstractOne
      (.forallI exactOneInterval abstractOneBodyType) :=
  .staticLam (.adapt .unit oneAdaptsToAbstract)

/-- Static application really substitutes its witness in the result type;
the abstract reference becomes `One`. -/
def applyStaticAbstractOneTyping :
    Term.HasType Ctx.nil
      (.staticApp exactOneInterval staticAbstractOne (.type .one)) .one :=
  .staticApp staticAbstractOneTyping Interval.Examples.exactOne

/-- A closed existential package. -/
def packedOne : Value [] :=
  .pack exactOneInterval
    (.one : Ty ([] ▹ .static .type)) (.type .one) .unit

/-- Package formation realizes the interval in the empty outer context and
checks the payload at the instantiated payload type. -/
def packedOneTyping :
    Value.HasType Ctx.nil packedOne
      (.existsI exactOneInterval .one) :=
  .pack Interval.Examples.exactOne .unit

/-- A package whose payload type genuinely mentions its hidden type witness. -/
def packedAbstractOne : Value [] :=
  .pack exactOneInterval abstractOneBodyType (.type .one) .unit

def packedAbstractOneTyping :
    Value.HasType Ctx.nil packedAbstractOne
      (.existsI exactOneInterval abstractOneBodyType) :=
  .pack Interval.Examples.exactOne .unit

/-- Opening the package exposes the hidden exact interval and its payload.
The upper endpoint converts the abstract payload back to the nonescaping
ambient result `One`. -/
def openPackedAbstractOne : Term [] :=
  .«open» exactOneInterval abstractOneBodyType .one packedAbstractOne
    (.ret (.var .here))

def openPackedAbstractOneTyping :
    Term.HasType Ctx.nil openPackedAbstractOne .one :=
  .«open» packedAbstractOneTyping
    (.ret (.adapt .var (.cast (by
      change Includes
        ((Ctx.nil.extendStatic exactOneInterval).extendTerm
          abstractOneBodyType)
        (StaticRef.bound (.there .here)).expression (.type .one)
      exact .upper (.bound rfl)))))

/-- An unbounded abstract capture appears non-vacuously in a capturing
function type.  This is the binder-only capture-polymorphic identity. -/
def captureIdentityBodyType : Ty ([] ▹ .static .capture) :=
  .capturing (.ref (.bound .here)) .one

def captureIdentity : Value [] :=
  .staticLam (Interval.unbounded (sort := .capture))
    (.lam captureIdentityBodyType captureIdentityBodyType
      (.ret (.var .here)))

def captureIdentityTyping :
    Value.HasType Ctx.nil captureIdentity
      (.forallI (Interval.unbounded (sort := .capture))
        (.arr captureIdentityBodyType captureIdentityBodyType)) :=
  .staticLam (.lam (.ret .var))

/-- Instantiating the capture-polymorphic identity with the empty capture
substitutes through both capturing annotations. -/
def applyCaptureIdentityTyping :
    Term.HasType Ctx.nil
      (.staticApp (Interval.unbounded (sort := .capture)) captureIdentity
        (.capture .empty))
      (.arr (.capturing .empty .one) (.capturing .empty .one)) :=
  .staticApp captureIdentityTyping (.unbounded)

end TypingExamples

end DOTCapture.BinderOnly
