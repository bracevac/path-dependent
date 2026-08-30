import Coercions.DOT.Captures.BinderOnly.IntervalModel

/-!
# Derivation-directed source adapters

`Adapts` records how an implicit source conversion must be elaborated.  A
logical cast is backed by source `Includes` evidence, while function and
quantifier constructors are explicitly structural.  Keeping the function
case distinct prevents a later elaborator from treating eta-expansion as an
ordinary erased cast.
-/

namespace DOTCapture.BinderOnly

/-- A proof-relevant, directed adaptation between source types.  The context
is an index rather than a fixed parameter so structural quantifier rules may
recurse under their shared interval binder. -/
inductive Adapts : {scope : Sig} -> Ctx scope ->
    Ty scope -> Ty scope -> Type where
  | identity {scope : Sig} {context : Ctx scope} {type : Ty scope} :
      Adapts context type type
  | cast {scope : Sig} {context : Ctx scope} {source target : Ty scope}
      (inclusion : Includes context (.type source) (.type target)) :
      Adapts context source target
  | compose {scope : Sig} {context : Ctx scope}
      {source middle target : Ty scope}
      (first : Adapts context source middle)
      (second : Adapts context middle target) :
      Adapts context source target
  | function {scope : Sig} {context : Ctx scope}
      {sourceDomain targetDomain sourceCodomain targetCodomain : Ty scope}
      (domain : Adapts context targetDomain sourceDomain)
      (codomain : Adapts context sourceCodomain targetCodomain) :
      Adapts context (.arr sourceDomain sourceCodomain)
        (.arr targetDomain targetCodomain)
  | forallI {scope : Sig} {context : Ctx scope} {sort : StaticSort}
      {interval : Interval sort scope}
      {sourceBody targetBody : Ty (scope ▹ .static sort)}
      (body : Adapts (context.extendStatic interval) sourceBody targetBody) :
      Adapts context (.forallI interval sourceBody)
        (.forallI interval targetBody)
  | existsI {scope : Sig} {context : Ctx scope} {sort : StaticSort}
      {interval : Interval sort scope}
      {sourceBody targetBody : Ty (scope ▹ .static sort)}
      (body : Adapts (context.extendStatic interval) sourceBody targetBody) :
      Adapts context (.existsI interval sourceBody)
        (.existsI interval targetBody)

namespace Adapts

/-- Lift a logical type inclusion into the adaptation layer. -/
def ofIncludes {scope : Sig} {context : Ctx scope} {source target : Ty scope}
    (inclusion : TypeIncludes context source target) :
    Adapts context source target :=
  .cast inclusion

/-- Function adaptation remains structural even when both component
adaptations happen to be logical casts. -/
def arrow {scope : Sig} {context : Ctx scope}
    {sourceDomain targetDomain sourceCodomain targetCodomain : Ty scope}
    (domain : Adapts context targetDomain sourceDomain)
    (codomain : Adapts context sourceCodomain targetCodomain) :
    Adapts context (.arr sourceDomain sourceCodomain)
      (.arr targetDomain targetCodomain) :=
  .function domain codomain

end Adapts

end DOTCapture.BinderOnly
