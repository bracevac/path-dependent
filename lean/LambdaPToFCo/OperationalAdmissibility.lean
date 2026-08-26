import LambdaPToFCo.OperationalAdmissibilityCore
import LambdaPToFCo.OperationalStoreEnvironment

/-!
# Operationally admissible source derivations

Static preservation remains available for the whole `Fragment`.  The first
source/target simulation deliberately uses a smaller, proof-relevant
operational fragment so every canonical-value assumption is visible:

* a source abstraction starts at `HasType.abs` and may be surrounded by the
  reflexive/transitive/arrow shapes recognized by `FragmentFunctionCo`;
* an exact member value starts at literal `typePackage` and may be surrounded
  only by canonical reflexive casts;
* paths may use arbitrary source subsumption when their final binder
  representation is ordinary.  This includes lower/upper selection evidence
  after closing, but never asks such an arbitrary value to behave as a member
  package;
* applications and lets must end in their direct typing constructors.  This
  makes the first executable simulation's CK inversion total; the static
  `Fragment` translation remains unrestricted.

The closed value compiler below turns the two syntactic source values into
the `EliminationView` expected by the store environment.  Package payload
readiness is required only after the older store environment has closed the
compiled path.
-/

namespace LambdaPToFCo
namespace OperationalAdmissibility

open SystemFCo
open StaticTranslation
open OperationalBindingView
open OperationalEnvironment
open OperationalApplication
open OperationalApplicationTranslation
open OperationalStoreEnvironment
open OperationalValueEvidence
open OperationalApplicationSpine

namespace FunctionSpine

/-- Allocating an admissible abstraction cannot create a member-package
cell, because every supported outer function coercion still ends at an
ordinary arrow representation. -/
theorem allocateMemberCell
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {domain sourceType : LambdaPFC.Ty lexical}
    {sourceBody : LambdaPFC.Tm (lexical + 1)}
    {typing : Fragment.HasType sourceContext
      (.abs domain sourceBody) sourceType}
    (spine : FunctionSpine typing)
    (sourceStore : LambdaPFC.Store current)
    (valuation : OperationalCode.SourceValuation lexical current)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    MemberCell (lexical := lexical) (current := current + 1) sourceType
      (.val sourceStore runtimeValue runtimeReady) valuation.weaken 0 :=
  MemberCell.ofNotMember spine.targetShape.notMember

/-- The native value installed for an admissible abstraction has an
abstraction head, independently of the outer function-coercion spine used
for its lexical type. -/
theorem allocateFunctionCell
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {domain sourceType : LambdaPFC.Ty lexical}
    {sourceBody : LambdaPFC.Tm (lexical + 1)}
    {typing : Fragment.HasType sourceContext
      (.abs domain sourceBody) sourceType}
    (_spine : FunctionSpine typing)
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation lexical current}
    {runtimeValue : LambdaPFC.Tm current}
    (runtimeReady : runtimeValue.IsValue)
    (runtime_eq : runtimeValue =
      (LambdaPFC.Tm.abs domain sourceBody).rename valuation) :
    FunctionCell (lexical := lexical) (current := current + 1) sourceType
      (.val sourceStore runtimeValue runtimeReady) valuation.weaken 0 := by
  cases runtime_eq
  intro _ _ _
  exact ⟨(domain.rename valuation).weaken,
    (sourceBody.rename valuation.ext).rename
      LambdaPFC.FinFun.weaken.ext,
    .here⟩

end FunctionSpine

namespace ExactPackageSpine

/-- Literal exact-package allocation supplies the required member head;
reflexive typing administration does not alter that native cell. -/
theorem allocateMemberCell
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {first : Fin lexical} {label : LambdaPFC.Name}
    {witness sourceType : LambdaPFC.Ty lexical}
    {typing : Fragment.HasType sourceContext
      (.pair first label (.type witness)) sourceType}
    (spine : ExactPackageSpine typing)
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation lexical current}
    {runtimeValue : LambdaPFC.Tm current}
    (runtimeReady : runtimeValue.IsValue)
    (runtime_eq : runtimeValue =
      (LambdaPFC.Tm.pair first label (.type witness)).rename valuation) :
    MemberCell (lexical := lexical) (current := current + 1) sourceType
      (.val sourceStore runtimeValue runtimeReady) valuation.weaken 0 := by
  rw [spine.sourceType_eq]
  exact MemberCell.allocateTypePackage runtimeReady runtime_eq

/-- An exact-package spine cannot advertise its freshly allocated pair as a
function cell. -/
theorem allocateFunctionCell
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {first : Fin lexical} {label : LambdaPFC.Name}
    {witness sourceType : LambdaPFC.Ty lexical}
    {typing : Fragment.HasType sourceContext
      (.pair first label (.type witness)) sourceType}
    (spine : ExactPackageSpine typing)
    (sourceStore : LambdaPFC.Store current)
    (valuation : OperationalCode.SourceValuation lexical current)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    FunctionCell (lexical := lexical) (current := current + 1) sourceType
      (.val sourceStore runtimeValue runtimeReady) valuation.weaken 0 := by
  intro domain codomain typeEq
  rw [spine.sourceType_eq] at typeEq
  cases typeEq

end ExactPackageSpine

namespace ApplicationValueEvidence

/-- Member-head provenance generated uniformly from either admitted source
value shape. -/
theorem allocateMemberCell
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {term : LambdaPFC.Tm lexical}
    {sourceType : LambdaPFC.Ty lexical}
    {typing : Fragment.HasType sourceContext term sourceType}
    (evidence : ApplicationValueEvidence typing)
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation lexical current}
    {runtimeValue : LambdaPFC.Tm current}
    (runtimeReady : runtimeValue.IsValue)
    (runtime_eq : runtimeValue = term.rename valuation) :
    MemberCell (lexical := lexical) (current := current + 1) sourceType
      (.val sourceStore runtimeValue runtimeReady) valuation.weaken 0 := by
  cases evidence with
  | function spine =>
      exact
        OperationalAdmissibility.FunctionSpine.allocateMemberCell
          spine.functionSpine sourceStore valuation runtimeValue runtimeReady
  | package spine =>
      exact
        OperationalAdmissibility.ExactPackageSpine.allocateMemberCell spine
          runtimeReady runtime_eq

/-- Function-head provenance generated uniformly from either admitted source
value shape. -/
theorem allocateFunctionCell
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {term : LambdaPFC.Tm lexical}
    {sourceType : LambdaPFC.Ty lexical}
    {typing : Fragment.HasType sourceContext term sourceType}
    (evidence : ApplicationValueEvidence typing)
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation lexical current}
    {runtimeValue : LambdaPFC.Tm current}
    (runtimeReady : runtimeValue.IsValue)
    (runtime_eq : runtimeValue = term.rename valuation) :
    FunctionCell (lexical := lexical) (current := current + 1) sourceType
      (.val sourceStore runtimeValue runtimeReady) valuation.weaken 0 := by
  cases evidence with
  | function spine =>
      exact
        OperationalAdmissibility.FunctionSpine.allocateFunctionCell
          spine.functionSpine runtimeReady runtime_eq
  | package spine =>
      exact
        OperationalAdmissibility.ExactPackageSpine.allocateFunctionCell spine
          sourceStore valuation runtimeValue runtimeReady

end ApplicationValueEvidence

namespace OperationallyAdmissible

/-- Closed value-view compiler exposed directly from the whole-program
admissibility predicate and native source value evidence. -/
noncomputable def closedValueView
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext term sourceType}
    (admissible : OperationallyAdmissible typing)
    (value : LambdaPFC.Tm.IsValue term)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (ready : (admissible.valueEvidence value).ClosedReady scope environment) :
    OperationalPackageBehavior.ClosedView scope typing environment :=
  (admissible.valueEvidence value).closedView scope environment ready

end OperationallyAdmissible

end OperationalAdmissibility
end LambdaPToFCo
