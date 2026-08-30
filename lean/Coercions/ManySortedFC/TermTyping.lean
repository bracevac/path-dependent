import Coercions.ManySortedFC.Term

/-!
# Declarative typing for annotated many-sorted FC terms

The judgment follows the explicit term syntax without performing subtyping or
adapter synthesis.  Logical models supplied to static application and package
formation are checked in the ambient context.  Only static abstraction and
existential opening extend the context with a theory, preserving the
no-self-discharge boundary of `Theory.SatisfiedBy`.

Function codomains and elimination results are nondependent.  Under a term or
static binder they are therefore weakened from their recorded ambient scope.
-/

namespace ManySortedFC

namespace Tm

/-- Syntax-directed declarative typing for explicitly annotated terms. -/
inductive HasType : {scope : Sig} -> Ctx scope -> Tm scope -> Ty scope ->
    Type where
  /-- A variable has exactly the type stored by heterogeneous context lookup. -/
  | var {scope : Sig} {context : Ctx scope}
      (index : BVar scope .term) :
      HasType context (.var index) (context.lookup index).termType

  | unit {scope : Sig} {context : Ctx scope} :
      HasType context (.unit : Tm scope) .one

  /-- The recorded codomain is ambient and is weakened below the parameter. -/
  | lam {scope : Sig} {context : Ctx scope}
      {domain codomain : Ty scope} {body : Tm (scope ▹ .term)}
      (bodyTyping : HasType (context.extendTerm domain) body
        codomain.weaken) :
      HasType context (.lam domain codomain body) (.arr domain codomain)

  | app {scope : Sig} {context : Ctx scope}
      {function argument : Tm scope} {domain codomain : Ty scope}
      (functionTyping : HasType context function (.arr domain codomain))
      (argumentTyping : HasType context argument domain) :
      HasType context (.app function argument) codomain

  /-- The explicit result annotation prevents the body type from escaping its
  ordinary binder. -/
  | let' {scope : Sig} {context : Ctx scope}
      {result boundType : Ty scope} {rhs : Tm scope}
      {body : Tm (scope ▹ .term)}
      (rhsTyping : HasType context rhs boundType)
      (bodyTyping : HasType (context.extendTerm boundType) body
        result.weaken) :
      HasType context (.let' result rhs body) result

  /-- Structural adaptation is explicit, consumes an ANF value, and must have
  the same source type as its argument.  The value premise prevents a function
  eta-adapter from delaying an unevaluated call-by-value computation. -/
  | adapt {scope : Sig} {context : Ctx scope}
      {term : Tm scope} {adapter : Adapter scope} {source target : Ty scope}
      (termValue : IsValue term)
      (termTyping : HasType context term source)
      (adapterTyping : Adapter.HasType context adapter source target) :
      HasType context (.adapt term adapter) target

  /-- A static abstraction may use all symbols and assumptions exported by its
  theory. -/
  | slam {scope : Sig} {context : Ctx scope}
      {symbols : List StaticSort} {relations : List Relation}
      {theory : Theory scope symbols relations}
      {body : Tm (StaticScope scope symbols relations)}
      {bodyType : Ty (StaticScope scope symbols relations)}
      (bodyValue : IsValue body)
      (bodyTyping : HasType (context.extendTheory theory) body bodyType) :
      HasType context (.slam theory body) (.forallT theory bodyType)

  /-- Static arguments and their evidence form a model in the ambient context;
  the instantiated body type is the application result. -/
  | sapp {scope : Sig} {context : Ctx scope}
      {symbols : List StaticSort} {relations : List Relation}
      {theory : Theory scope symbols relations}
      {function : Tm scope}
      {bodyType : Ty (StaticScope scope symbols relations)}
      {symbolArguments : SymbolArgs scope symbols}
      {evidenceArguments : EvidenceArgs scope relations}
      (functionTyping : HasType context function
        (.forallT theory bodyType))
      (satisfaction : Theory.SatisfiedBy context symbolArguments theory
        evidenceArguments) :
      HasType context
        (.sapp theory function symbolArguments evidenceArguments)
        (bodyType.instantiateStatic symbolArguments)

  /-- Package witnesses, certificates, and payload are all formed in the
  ambient context.  In particular the supplied evidence cannot use the
  theory's own assumptions. -/
  | pack {scope : Sig} {context : Ctx scope}
      {symbols : List StaticSort} {relations : List Relation}
      {theory : Theory scope symbols relations}
      {payloadType : Ty (StaticScope scope symbols relations)}
      {symbolArguments : SymbolArgs scope symbols}
      {evidenceArguments : EvidenceArgs scope relations}
      {payload : Tm scope}
      (satisfaction : Theory.SatisfiedBy context symbolArguments theory
        evidenceArguments)
      (payloadTyping : HasType context payload
        (payloadType.instantiateStatic symbolArguments)) :
      HasType context
        (.pack theory payloadType symbolArguments evidenceArguments payload)
        (.existsT theory payloadType)

  /-- Opening exposes the complete local theory and then the package payload.
  The recorded ambient result is weakened through both scopes. -/
  | «open» {scope : Sig} {context : Ctx scope}
      {symbols : List StaticSort} {relations : List Relation}
      {theory : Theory scope symbols relations}
      {payloadType : Ty (StaticScope scope symbols relations)}
      {result : Ty scope} {package : Tm scope}
      {body : Tm (PayloadScope scope symbols relations)}
      (packageTyping : HasType context package
        (.existsT theory payloadType))
      (bodyTyping : HasType
        ((context.extendTheory theory).extendTerm payloadType) body
        ((result.rename (Rename.weakenStatic symbols relations)).weaken)) :
      HasType context
        (.«open» theory payloadType result package body) result

/-- Inverting package typing exposes the ambient model obligation.  The
returned judgment is against `context`, not `context.extendTheory theory`, so
the package cannot discharge its certificates with assumptions it introduces. -/
def pack_satisfaction {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    {theory : Theory scope symbols relations}
    {payloadType : Ty (StaticScope scope symbols relations)}
    {symbolArguments : SymbolArgs scope symbols}
    {evidenceArguments : EvidenceArgs scope relations}
    {payload : Tm scope} {result : Ty scope}
    (typing : HasType context
      (.pack theory payloadType symbolArguments evidenceArguments payload)
      result) :
    Theory.SatisfiedBy context symbolArguments theory evidenceArguments := by
  cases typing with
  | pack satisfaction _ => exact satisfaction

end Tm

end ManySortedFC
