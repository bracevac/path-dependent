import LambdaPToFCo.OperationalApplicationSpine

/-!
# Source-only exact-core function paths

This module is intentionally below `OperationalAdmissibility` in the import
graph.  It records the operator-path provenance needed by application without
depending on stores, closed target paths, or machine images.
-/

namespace LambdaPToFCo
namespace OperationalFunctionPathSpine

open OperationalApplicationTranslation
open OperationalApplicationSpine

/-- A fragment path which synthesizes an arrow is necessarily a variable;
the exact-first rule always synthesizes a singleton. -/
def pathIsVarOfArrow
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (typing : Fragment.PathTy sourceContext path sourceType)
    {domain codomain : LambdaPFC.Ty n}
    (typeEq : sourceType = .Fun domain codomain.weaken) : path.IsVar := by
  cases typing with
  | var => exact .var
  | exactFst => cases typeEq

/-- The exact operator-path fragment used by the first application theorem.

The base rule is literally singleton introduction followed by singleton
widening to the path referent's precise arrow.  The recursive rule accepts
only the strengthened function-coercion shapes with ordinary domains.  In
particular, arbitrary selection and package detours have no constructor. -/
inductive FunctionPathSpine
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} :
    {domain codomain : LambdaPFC.Ty n} ->
    (typing : Fragment.HasType sourceContext (.path path)
      (.Fun domain codomain.weaken)) -> Type where
  | widen
      (pathTyping : Fragment.PathTy sourceContext path
        (.Fun domain codomain.weaken))
      (domainWf : Fragment.Wf sourceContext domain)
      (codomainWf : Fragment.Wf sourceContext codomain)
      (domainShape : StaticTranslation.OrdinaryShape domain) :
      FunctionPathSpine
        (.sub (.path pathTyping)
          (.widen pathTyping (.arrow domainWf codomainWf)))
  | sub
      {sourceDomain sourceCodomain targetDomain targetCodomain :
        LambdaPFC.Ty n}
      {innerTyping : Fragment.HasType sourceContext (.path path)
        (.Fun sourceDomain sourceCodomain.weaken)}
      {subtype : Fragment.Sub sourceContext
        (.Fun sourceDomain sourceCodomain.weaken)
        (.Fun targetDomain targetCodomain.weaken)}
      {shape : FragmentFunctionCo subtype}
      (inner : FunctionPathSpine innerTyping)
      (coercion : ApplicationFunctionCo shape) :
      FunctionPathSpine (.sub innerTyping subtype)

namespace FunctionPathSpine

/-- The precise-arrow base of an admitted function path can only be a
variable.  Outer function coercions do not change that source path. -/
def pathIsVar
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {domain codomain : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path path)
      (.Fun domain codomain.weaken)} :
    FunctionPathSpine typing -> path.IsVar
  | .widen pathTyping _ _ _ => by
      exact pathIsVarOfArrow pathTyping rfl
  | .sub inner _ => inner.pathIsVar

end FunctionPathSpine

end OperationalFunctionPathSpine
end LambdaPToFCo
