import Coercions.DOT.Captures.BinderOnly.Term
import Coercions.DOT.Captures.BinderOnly.Substitution
import Coercions.DOT.Captures.BinderOnly.Subtyping

/-!
# Typing for the binder-only DOT-with-captures source

The mutually defined judgments follow the source's capture-predictive ANF
split.  Values retain capabilities in the outer annotation of their type;
computations separately report the capabilities used immediately when they
run.  Value return is therefore pure, while application charges the outer
captures of both typed operands.

Computations are sequenced only by `let'`, and implicit type adaptation is
available only for values.  Immediate-use widening has its own constructor,
so capture subsumption cannot be confused with a type-changing adapter.
Lambda checking may discharge body use to the newest parameter singleton;
that singleton is not retained in the function closure.  Existential opening
likewise discharges the newest payload singleton, whose capabilities are
already covered by the package closure.

Static introduction and elimination also expose the no-self-discharge
boundary.  A concrete witness realizes its interval in the ambient context;
hypothetical interval assumptions enter the context only inside a static
abstraction or existential open body.  Since static abstraction and package
markers erase at runtime, their value rules carry an explicit ambient closure
capture together with inclusion evidence covering the erased body or payload.
-/

namespace DOTCapture.BinderOnly

mutual

/-- Declarative typing of source values. -/
inductive Value.HasType : {scope : Sig} -> Ctx scope ->
    Value scope -> Ty scope -> Type where
  | var {scope : Sig} {context : Ctx scope}
      {name : BVar scope .term} :
      Value.HasType context (.var name)
        ((context.lookupTerm name).precise (.var name))
  | unit {scope : Sig} {context : Ctx scope} :
      Value.HasType context .unit .one
  | lam {scope : Sig} {context : Ctx scope} {domain codomain : Ty scope}
      {body : Term (scope ▹ .term)} {bodyUse : Capture (scope ▹ .term)}
      {closure : Capture scope}
      (bodyTyping : Term.HasType (context.extendTerm domain) body
        bodyUse (codomain.weaken (kind := .term)))
      (captures : CaptureIncludes (context.extendTerm domain) bodyUse
        (.union (closure.weaken (kind := .term))
          (.singleton (.var .here)))) :
      Value.HasType context (.lam domain codomain body)
        (.capturing closure (.arr domain codomain))
  | staticLam {scope : Sig} {context : Ctx scope} {sort : StaticSort}
      {interval : Interval sort scope}
      {body : Value (scope ▹ .static sort)}
      {bodyType : Ty (scope ▹ .static sort)}
      {closure : Capture scope}
      (bodyTyping : Value.HasType (context.extendStatic interval)
        body bodyType)
      (captures : CaptureIncludes (context.extendStatic interval)
        bodyType.outerCapture (closure.weaken (kind := .static sort))) :
      Value.HasType context (.staticLam interval body)
        (.capturing closure (.forallI interval bodyType))
  | pack {scope : Sig} {context : Ctx scope} {sort : StaticSort}
      {interval : Interval sort scope}
      {payloadType : Ty (scope ▹ .static sort)}
      {witness : StaticExpr sort scope} {payload : Value scope}
      {closure : Capture scope}
      (satisfaction : Interval.SatisfiedBy context witness interval)
      (payloadTyping : Value.HasType context payload
        (payloadType.instantiateStatic witness))
      (captures : CaptureIncludes context
        (payloadType.instantiateStatic witness).outerCapture closure) :
      Value.HasType context
        (.pack interval payloadType witness payload)
        (.capturing closure (.existsI interval payloadType))
  | adapt {scope : Sig} {context : Ctx scope} {value : Value scope}
      {source target : Ty scope}
      (valueTyping : Value.HasType context value source)
      (adapter : Adapts context source target) :
      Value.HasType context value target

/-- Declarative typing of source ANF computations.

The capture index is an upper bound on capabilities used immediately by the
computation.  It is deliberately distinct from the outer capture on the
result type, which describes capabilities retained by the returned value. -/
inductive Term.HasType : {scope : Sig} -> Ctx scope ->
    Term scope -> Capture scope -> Ty scope -> Type where
  | ret {scope : Sig} {context : Ctx scope} {value : Value scope}
      {type : Ty scope} (valueTyping : Value.HasType context value type) :
      Term.HasType context (.ret value) .empty type
  | app {scope : Sig} {context : Ctx scope}
      {function argument : Value scope}
      {functionType domain codomain : Ty scope}
      (functionTyping : Value.HasType context function functionType)
      (functionShape : functionType.stripCapture = .arr domain codomain)
      (argumentTyping : Value.HasType context argument domain) :
      Term.HasType context (.app function argument)
        (.union functionType.outerCapture domain.outerCapture) codomain
  | let' {scope : Sig} {context : Ctx scope} {result bound : Ty scope}
      {rhs : Term scope} {body : Term (scope ▹ .term)}
      {rhsUse : Capture scope} {bodyUse : Capture (scope ▹ .term)}
      {bodyOuterUse : Capture scope}
      (rhsTyping : Term.HasType context rhs rhsUse bound)
      (bodyTyping : Term.HasType (context.extendTerm bound) body
        bodyUse (result.weaken (kind := .term)))
      (discharge : CaptureIncludes (context.extendTerm bound) bodyUse
        (bodyOuterUse.weaken (kind := .term))) :
      Term.HasType context (.let' result rhs body)
        (.union rhsUse bodyOuterUse) result
  | staticApp {scope : Sig} {context : Ctx scope} {sort : StaticSort}
      {interval : Interval sort scope} {function : Value scope}
      {argument : StaticExpr sort scope}
      {functionType : Ty scope} {bodyType : Ty (scope ▹ .static sort)}
      (functionTyping : Value.HasType context function functionType)
      (functionShape : functionType.stripCapture =
        .forallI interval bodyType)
      (satisfaction : Interval.SatisfiedBy context argument interval) :
      Term.HasType context (.staticApp interval function argument)
        functionType.outerCapture (bodyType.instantiateStatic argument)
  | «open» {scope : Sig} {context : Ctx scope} {sort : StaticSort}
      {interval : Interval sort scope}
      {payloadType : Ty (scope ▹ .static sort)} {result : Ty scope}
      {package : Value scope} {body : Term (PayloadScope scope sort)}
      {packageType : Ty scope}
      {bodyUse : Capture (PayloadScope scope sort)}
      {bodyOuterUse : Capture scope}
      (packageTyping : Value.HasType context package packageType)
      (packageShape : packageType.stripCapture =
        .existsI interval payloadType)
      (bodyTyping : Term.HasType
        ((context.extendStatic interval).extendTerm payloadType) body bodyUse
        ((result.weaken (kind := .static sort)).weaken (kind := .term)))
      (discharge : CaptureIncludes
        ((context.extendStatic interval).extendTerm payloadType) bodyUse
        (.union
          ((bodyOuterUse.weaken (kind := .static sort)).weaken
            (kind := .term))
          (.singleton (.var .here)))) :
      Term.HasType context
        (.«open» interval payloadType result package body)
        (.union packageType.outerCapture bodyOuterUse) result
  | use {scope : Sig} {context : Ctx scope} {term : Term scope}
      {sourceUse targetUse : Capture scope} {type : Ty scope}
      (termTyping : Term.HasType context term sourceUse type)
      (inclusion : CaptureIncludes context sourceUse targetUse) :
      Term.HasType context term targetUse type

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

/-- Returning the argument has no immediate use, so the closed identity
retains the empty closure capture. -/
def identityTyping :
    Value.HasType Ctx.nil identity
      (.capturing .empty (.arr .one .one)) :=
  .lam (.ret .var) .captureEmpty

/-- The type of a closed unary function used as a free variable below. -/
def closedUnaryType : Ty [] :=
  .capturing .empty (.arr .one .one)

/-- A lambda in a context containing a free function `f`; its body invokes
`f` and ignores its own argument. -/
def callsFreeFunction : Value ([] ▹ .term) :=
  .lam .one .one
    (.app (.var (.there .here)) .unit)

/-- Variable precision turns `f`'s declared empty capture into `{f}` at its
occurrence.  Application charges `{f} ∪ {}`, and the lambda's inclusion
premise contracts that syntactic union to the exact `{f}` closure capture. -/
def callsFreeFunctionTyping :
    Value.HasType (Ctx.nil.extendTerm closedUnaryType) callsFreeFunction
      (.capturing (.singleton (.var .here)) (.arr .one .one)) :=
  .lam
    (.app .var rfl .unit)
    (.captureUnionElim .captureUnionLeft .captureEmpty)

/-! The parameter singleton is a discharge boundary, not a retained closure. -/

/-- A bare outer variable supplies the capability name `a`.  Its bare type is
pure/untracked for capture prediction, and exports no singleton-contraction
rule; it may nevertheless occur explicitly in another value's capture. -/
def outerCapabilityContext : Ctx ([] ▹ .term) :=
  Ctx.nil.extendTerm .one

/-- The function parameter may retain the outer capability `a`. -/
def parameterCallableType : Ty ([] ▹ .term) :=
  .capturing (.singleton (.var .here)) (.arr .one .one)

/-- `λ(f : {a}(One → One)). f unit` in the outer `a` context. -/
def callsParameter : Value ([] ▹ .term) :=
  .lam parameterCallableType .one
    (.app (.var .here) .unit)

/-- The call predicts `{f} ∪ ∅`; both parts fit beneath `∅ ∪ {f}`.
Consequently the parameter invocation does not become a retained closure. -/
def callsParameterTyping :
    Value.HasType outerCapabilityContext callsParameter
      (.capturing .empty (.arr parameterCallableType .one)) :=
  .lam
    (.app .var rfl .unit)
    (.captureUnionElim .captureUnionRight .captureEmpty)

/-- A closed identity can be widened to the parameter type, retaining `a` in
its declared outer capture. -/
def parameterArgument : Value ([] ▹ .term) :=
  .lam .one .one (.ret (.var .here))

def parameterArgumentTyping :
    Value.HasType outerCapabilityContext parameterArgument
      parameterCallableType :=
  .adapt
    (.lam (.ret .var) .captureEmpty)
    (.cast (.typeCapturing .captureEmpty .refl))

/-- Applying the closure-empty function still charges the capture retained by
its domain.  The direct application index exposes that charge structurally. -/
def callsParameterApplication : Term ([] ▹ .term) :=
  .app callsParameter parameterArgument

def callsParameterApplicationTyping :
    Term.HasType outerCapabilityContext callsParameterApplication
      (.union .empty (.singleton (.var .here))) .one :=
  .app callsParameterTyping rfl parameterArgumentTyping

/-- Capture subsumption normalizes `∅ ∪ {a}` to the exact observable
prediction `{a}`. -/
def callsParameterApplicationChargesDomain :
    Term.HasType outerCapabilityContext callsParameterApplication
      (.singleton (.var .here)) .one :=
  .use callsParameterApplicationTyping
    (.captureUnionElim .captureEmpty .refl)

/-- Bind the free function to a local name and invoke that local name. -/
def letBoundCall : Term ([] ▹ .term) :=
  .let' .one (.ret (.var .here))
    (.app (.var .here) .unit)

/-- The body's immediate `{local}` use is discharged to the retained `{f}`
capture of the local binding via `captureVariable`. -/
def letBoundCallTyping :
    Term.HasType (Ctx.nil.extendTerm closedUnaryType) letBoundCall
      (.singleton (.var .here)) .one :=
  .use
    (.let' (.ret .var)
      (.app .var rfl .unit)
      (.captureUnionElim (.captureVariable rfl) .captureEmpty))
    (.captureUnionElim .captureEmpty .refl)

/-- A closed static value whose interval is exact `One`. -/
def staticOne : Value [] :=
  .staticLam exactOneInterval .unit

/-- Static abstraction checks its value body under the hypothetical interval;
it does not construct a model at introduction time. -/
def staticOneTyping :
    Value.HasType Ctx.nil staticOne
      (.capturing .empty (.forallI exactOneInterval .one)) :=
  .staticLam .unit .refl

/-- Applying the closed static value requires ambient realization of its exact
interval and instantiates the result type with the supplied witness. -/
def applyStaticOneTyping :
    Term.HasType Ctx.nil
      (.staticApp exactOneInterval staticOne (.type .one))
      .empty .one :=
  .staticApp staticOneTyping rfl Interval.Examples.exactOne

/-- A non-vacuous static abstraction: its result type is the bound abstract
type, and the body uses the lower endpoint to inhabit it. -/
def staticAbstractOne : Value [] :=
  .staticLam exactOneInterval .unit

def staticAbstractOneTyping :
    Value.HasType Ctx.nil staticAbstractOne
      (.capturing .empty
        (.forallI exactOneInterval abstractOneBodyType)) :=
  .staticLam (.adapt .unit oneAdaptsToAbstract) .refl

/-- Static application really substitutes its witness in the result type;
the abstract reference becomes `One`. -/
def applyStaticAbstractOneTyping :
    Term.HasType Ctx.nil
      (.staticApp exactOneInterval staticAbstractOne (.type .one))
      .empty .one :=
  .staticApp staticAbstractOneTyping rfl Interval.Examples.exactOne

/-- A closed existential package. -/
def packedOne : Value [] :=
  .pack exactOneInterval
    (.one : Ty ([] ▹ .static .type)) (.type .one) .unit

/-- Package formation realizes the interval in the empty outer context and
checks the payload at the instantiated payload type. -/
def packedOneTyping :
    Value.HasType Ctx.nil packedOne
      (.capturing .empty (.existsI exactOneInterval .one)) :=
  .pack Interval.Examples.exactOne .unit .refl

/-- A package whose payload type genuinely mentions its hidden type witness. -/
def packedAbstractOne : Value [] :=
  .pack exactOneInterval abstractOneBodyType (.type .one) .unit

def packedAbstractOneTyping :
    Value.HasType Ctx.nil packedAbstractOne
      (.capturing .empty
        (.existsI exactOneInterval abstractOneBodyType)) :=
  .pack Interval.Examples.exactOne .unit .refl

/-- Opening the package exposes the hidden exact interval and its payload.
The upper endpoint converts the abstract payload back to the nonescaping
ambient result `One`. -/
def openPackedAbstractOne : Term [] :=
  .«open» exactOneInterval abstractOneBodyType .one packedAbstractOne
    (.ret (.var .here))

def openPackedAbstractOneTyping :
    Term.HasType Ctx.nil openPackedAbstractOne .empty .one :=
  .use
    (.«open» packedAbstractOneTyping rfl
      (.ret (.adapt .var (.cast (by
        change Includes
          ((Ctx.nil.extendStatic exactOneInterval).extendTerm
            abstractOneBodyType)
          (StaticRef.bound (.there .here)).expression (.type .one)
        exact .upper (.bound rfl)))))
      .captureEmpty)
    (.captureUnionElim .refl .refl)

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
      (.capturing .empty
        (.forallI (Interval.unbounded (sort := .capture))
          (.capturing .empty
            (.arr captureIdentityBodyType captureIdentityBodyType)))) :=
  .staticLam
    (.lam
      (.ret (.adapt .var
        (.cast (.typeCapturing (.captureVariable rfl) .refl))))
      .captureEmpty)
    .refl

/-- Instantiating the capture-polymorphic identity with the empty capture
substitutes through both capturing annotations. -/
def applyCaptureIdentityTyping :
    Term.HasType Ctx.nil
      (.staticApp (Interval.unbounded (sort := .capture)) captureIdentity
        (.capture .empty))
      .empty
      (.capturing .empty
        (.arr (.capturing .empty .one) (.capturing .empty .one))) :=
  .staticApp captureIdentityTyping rfl (.unbounded)

end TypingExamples

end DOTCapture.BinderOnly
