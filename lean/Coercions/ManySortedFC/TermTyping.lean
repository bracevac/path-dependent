import Coercions.ManySortedFC.Term

/-!
# Capture-predictive typing for annotated many-sorted FC terms

The judgment follows the explicit term syntax without performing subtyping,
subcapturing, or adapter synthesis.  Besides the returned type it predicts an
upper bound on capabilities used immediately when the computation runs.
Capabilities retained by a returned value live separately in the outer
capture annotation of its type.  Thus variables and other values have empty
immediate use, while a variable occurrence at an explicitly captured binding
receives a precise singleton outer capture.

Logical models supplied to static application and package formation are
checked in the ambient context.  Only static abstraction and existential
opening extend the context with a theory, preserving the no-self-discharge
boundary of `Theory.SatisfiedBy`.

Function codomains and elimination results are nondependent.  Under a term or
static binder they are therefore weakened from their recorded ambient scope.
-/

namespace ManySortedFC

namespace Tm

/-- Syntax-directed typing with an immediate-use capture and returned type. -/
inductive HasType : {scope : Sig} -> Ctx scope -> Tm scope ->
    Capture scope -> Ty scope -> Type where
  /-- Values do not use capabilities merely by being returned.  A variable at
  an explicitly captured type does, however, retain its own precise root. -/
  | var {scope : Sig} {context : Ctx scope}
      (index : BVar scope .term) :
      HasType context (.var index) .empty
        (Ty.precise index (context.lookup index).termType)

  | unit {scope : Sig} {context : Ctx scope} :
      HasType context (.unit : Tm scope) .empty .one

  /-- The recorded codomain is ambient and is weakened below the parameter.
  The explicit certificate bounds the body's immediate use by the retained
  closure capture together with the parameter singleton.  Uses discharged to
  that singleton therefore do not leak into the function's closure. -/
  | lam {scope : Sig} {context : Ctx scope}
      {domain codomain : Ty scope} {closure : Capture scope}
      {body : Tm (scope ▹ .term)}
      {captures : Evidence (.inclusion .capture) (scope ▹ .term)}
      {bodyUse : Capture (scope ▹ .term)}
      (bodyTyping : HasType (context.extendTerm domain) body
        bodyUse codomain.weaken)
      (capturesTyping : Evidence.Proves (context.extendTerm domain)
        captures (.inclusion (.capture bodyUse)
          (.capture (.union closure.weaken (.singleton .here))))) :
      HasType context (.lam domain codomain closure body captures) .empty
        (.capturing closure (.arr domain codomain))

  /-- General call-by-value application.  The two operands may themselves be
  computations.  Their immediate-use predictions are sequenced before the
  retained captures of the function and argument are charged by invocation. -/
  | app {scope : Sig} {context : Ctx scope}
      {function argument : Tm scope} {functionType domain codomain : Ty scope}
      {functionUse argumentUse : Capture scope}
      (functionTyping : HasType context function functionUse functionType)
      (functionShape : functionType.stripCapture = .arr domain codomain)
      (argumentTyping : HasType context argument argumentUse domain) :
      HasType context (.app function argument)
        (functionUse.sequence
          (argumentUse.sequence
            (.union functionType.outerCapture domain.outerCapture))) codomain

  /-- The explicit result annotation prevents the body type from escaping its
  ordinary binder.  The discharge certificate removes the local binder from
  the body's use prediction before sequencing it after the right-hand side. -/
  | let' {scope : Sig} {context : Ctx scope}
      {result boundType : Ty scope} {bodyOuterUse : Capture scope}
      {rhsUse : Capture scope} {rhs : Tm scope}
      {body : Tm (scope ▹ .term)}
      {bodyUse : Capture (scope ▹ .term)}
      {discharge : Evidence (.inclusion .capture) (scope ▹ .term)}
      (rhsTyping : HasType context rhs rhsUse boundType)
      (bodyTyping : HasType (context.extendTerm boundType) body
        bodyUse result.weaken)
      (dischargeTyping : Evidence.Proves (context.extendTerm boundType)
        discharge (.inclusion (.capture bodyUse)
          (.capture bodyOuterUse.weaken))) :
      HasType context
        (.let' result bodyOuterUse rhs body discharge)
        (.union rhsUse bodyOuterUse) result

  /-- Structural adaptation is explicit, consumes a value, and must have
  the same source type as its argument.  The value premise prevents a function
  eta-adapter from delaying an unevaluated call-by-value computation.  Type
  transport does not change the immediate-use prediction. -/
  | adapt {scope : Sig} {context : Ctx scope}
      {term : Tm scope} {adapter : Adapter scope}
      {use : Capture scope} {source target : Ty scope}
      (termValue : IsValue term)
      (termTyping : HasType context term use source)
      (adapterTyping : Adapter.HasType context adapter source target) :
      HasType context (.adapt term adapter) use target

  /-- A static abstraction may use all symbols and assumptions exported by its
  theory.  Since the abstraction marker erases, the outer captures retained by
  its value body must be covered by the abstraction's ambient closure. -/
  | slam {scope : Sig} {context : Ctx scope}
      {symbols : List StaticSort} {relations : List Relation}
      {theory : Theory scope symbols relations}
      {closure : Capture scope}
      {body : Tm (StaticScope scope symbols relations)}
      {bodyType : Ty (StaticScope scope symbols relations)}
      {captures : Evidence (.inclusion .capture)
        (StaticScope scope symbols relations)}
      (bodyValue : IsValue body)
      (bodyTyping : HasType (context.extendTheory theory) body .empty bodyType)
      (capturesTyping : Evidence.Proves (context.extendTheory theory)
        captures (.inclusion (.capture bodyType.outerCapture)
          (.capture (closure.rename
            (Rename.weakenStatic symbols relations))))) :
      HasType context (.slam theory closure body captures) .empty
        (.capturing closure (.forallT theory bodyType))

  /-- Static arguments and their evidence form a model in the ambient context;
  the instantiated body type is the application result.  Invoking the value
  charges its retained outer capture. -/
  | sapp {scope : Sig} {context : Ctx scope}
      {symbols : List StaticSort} {relations : List Relation}
      {theory : Theory scope symbols relations}
      {function : Tm scope}
      {functionType : Ty scope}
      {bodyType : Ty (StaticScope scope symbols relations)}
      {symbolArguments : SymbolArgs scope symbols}
      {evidenceArguments : EvidenceArgs scope relations}
      (functionValue : IsValue function)
      (functionTyping : HasType context function .empty functionType)
      (functionShape : functionType.stripCapture =
        .forallT theory bodyType)
      (satisfaction : Theory.SatisfiedBy context symbolArguments theory
        evidenceArguments) :
      HasType context
        (.sapp theory function symbolArguments evidenceArguments)
        functionType.outerCapture
        (bodyType.instantiateStatic symbolArguments)

  /-- Package witnesses, certificates, and payload are all formed in the
  ambient context.  In particular the supplied evidence cannot use the
  theory's own assumptions.  The explicit capture certificate covers the
  payload capabilities retained after the package marker erases. -/
  | pack {scope : Sig} {context : Ctx scope}
      {symbols : List StaticSort} {relations : List Relation}
      {theory : Theory scope symbols relations}
      {payloadType : Ty (StaticScope scope symbols relations)}
      {closure : Capture scope}
      {symbolArguments : SymbolArgs scope symbols}
      {evidenceArguments : EvidenceArgs scope relations}
      {payload : Tm scope}
      {captures : Evidence (.inclusion .capture) scope}
      (satisfaction : Theory.SatisfiedBy context symbolArguments theory
        evidenceArguments)
      (payloadValue : IsValue payload)
      (payloadTyping : HasType context payload .empty
        (payloadType.instantiateStatic symbolArguments))
      (capturesTyping : Evidence.Proves context captures
        (.inclusion
          (.capture
            (payloadType.instantiateStatic symbolArguments).outerCapture)
          (.capture closure))) :
      HasType context
        (.pack theory payloadType closure symbolArguments evidenceArguments
          payload captures)
        .empty (.capturing closure (.existsT theory payloadType))

  /-- Opening exposes the complete local theory and then the package payload.
  The recorded ambient result is weakened through both scopes.  The package
  may itself be a computation: its immediate use is sequenced before opening
  charges the package's retained outer capture and the exported body
  prediction.  The newest payload singleton is available only to the
  discharge certificate and is covered by the package closure. -/
  | «open» {scope : Sig} {context : Ctx scope}
      {symbols : List StaticSort} {relations : List Relation}
      {theory : Theory scope symbols relations}
      {payloadType : Ty (StaticScope scope symbols relations)}
      {result : Ty scope} {bodyOuterUse : Capture scope}
      {packageUse : Capture scope} {packageType : Ty scope}
      {package : Tm scope}
      {body : Tm (PayloadScope scope symbols relations)}
      {bodyUse : Capture (PayloadScope scope symbols relations)}
      {discharge : Evidence (.inclusion .capture)
        (PayloadScope scope symbols relations)}
      (packageTyping : HasType context package packageUse packageType)
      (packageShape : packageType.stripCapture =
        .existsT theory payloadType)
      (bodyTyping : HasType
        ((context.extendTheory theory).extendTerm payloadType) body
        bodyUse
        ((result.rename (Rename.weakenStatic symbols relations)).weaken))
      (dischargeTyping : Evidence.Proves
        ((context.extendTheory theory).extendTerm payloadType)
        discharge (.inclusion (.capture bodyUse)
          (.capture (.union
            ((bodyOuterUse.rename
              (Rename.weakenStatic symbols relations)).weaken)
            (.singleton .here))))) :
      HasType context
        (.«open» theory payloadType result bodyOuterUse package body
          discharge)
        (packageUse.sequence
          (.union packageType.outerCapture bodyOuterUse)) result

  /-- Explicit immediate-use widening.  Unlike `adapt`, this node does not
  change the returned type and has no runtime behavior. -/
  | use {scope : Sig} {context : Ctx scope} {term : Tm scope}
      {inclusion : Evidence (.inclusion .capture) scope}
      {sourceUse targetUse : Capture scope} {type : Ty scope}
      (termTyping : HasType context term sourceUse type)
      (inclusionTyping : Evidence.Proves context inclusion
        (.inclusion (.capture sourceUse) (.capture targetUse))) :
      HasType context (.use term inclusion) targetUse type

/-- Inverting package typing exposes the ambient model obligation.  The
returned judgment is against `context`, not `context.extendTheory theory`, so
the package cannot discharge its certificates with assumptions it introduces. -/
def pack_satisfaction {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    {theory : Theory scope symbols relations}
    {payloadType : Ty (StaticScope scope symbols relations)}
    {symbolArguments : SymbolArgs scope symbols}
    {evidenceArguments : EvidenceArgs scope relations}
    {closure use : Capture scope}
    {captures : Evidence (.inclusion .capture) scope}
    {payload : Tm scope} {result : Ty scope}
    (typing : HasType context
      (.pack theory payloadType closure symbolArguments evidenceArguments
        payload captures)
      use result) :
    Theory.SatisfiedBy context symbolArguments theory evidenceArguments := by
  cases typing with
  | pack satisfaction _ _ _ => exact satisfaction

end Tm

end ManySortedFC
