import LambdaPToFCo.OperationalApplicationSpine
import LambdaPToFCo.OperationalFunctionPathCore

/-!
# Source-only executable-fragment evidence

This module contains the proof-relevant operational fragment independently of
the compiled store environment.  Keeping it below the store layer lets every
physical cell retain the admissibility evidence of its native code, including
the `ApplicationSpine` needed when that cell is later used as a function.

Static preservation remains available for the complete `Fragment`.  The
first executable core is intentionally narrower:

* functions carry an application spine and recursively admissible body;
* packages are literal exact packages with reflexive administration;
* applications and lets end in their direct typing constructors;
* arbitrary subsumption remains available only on paths whose result cannot
  demand a canonical source head;
* arrow-typed paths retain an explicit exact-core function spine.
-/

namespace LambdaPToFCo
namespace OperationalAdmissibility

open StaticTranslation
open OperationalValueEvidence
open OperationalApplicationSpine
open OperationalFunctionPathSpine

/-- Paths are the only non-value computations around which the executable
core admits arbitrary subsumption. -/
inductive Neutral : LambdaPFC.Tm n -> Type where
  | path : Neutral (.path path)

namespace Neutral

/-- Generic path subsumption may not create a result which demands a
canonical abstraction or package head.  Arrow results use the dedicated
`functionPath` constructor below. -/
def ResultShape {term : LambdaPFC.Tm n} :
    Neutral term -> LambdaPFC.Ty n -> Type
  | .path, target => NonCanonicalResultShape target

end Neutral

/-- Executable lets either bind a source value directly, retaining its
application-value provenance, or bind a result whose type cannot demand a
canonical source head.  In particular, an arrow-typed path result cannot be
used as a let bound in the first executable core. -/
inductive LetBoundPolicy
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {bound : LambdaPFC.Tm n} {boundType : LambdaPFC.Ty n}
    (typing : Fragment.HasType sourceContext bound boundType) : Type where
  | directValue (evidence : ApplicationValueEvidence typing) :
      LetBoundPolicy typing
  | nonCanonical (shape : NonCanonicalResultShape boundType) :
      LetBoundPolicy typing

/-- Proof-relevant source fragment used by the first executable simulation.
The predicate stores all canonical-value and application-shape evidence; it
does not depend on a source store or target runtime invariant. -/
inductive OperationallyAdmissible :
    {n : Nat} -> {sourceContext : LambdaPFC.Ctx n} ->
    {term : LambdaPFC.Tm n} -> {sourceType : LambdaPFC.Ty n} ->
    (typing : Fragment.HasType sourceContext term sourceType) -> Type where
  | path
      (pathTyping : Fragment.PathTy sourceContext path sourceType) :
      OperationallyAdmissible (.path pathTyping)
  | functionPath
      {n : Nat} {sourceContext : LambdaPFC.Ctx n}
      {path : LambdaPFC.Path n} {domain codomain : LambdaPFC.Ty n}
      {typing : Fragment.HasType sourceContext (.path path)
        (.Fun domain codomain.weaken)}
      (spine : FunctionPathSpine typing) :
      OperationallyAdmissible typing
  | function
      {n : Nat} {sourceContext : LambdaPFC.Ctx n}
      {nativeDomain domain codomain : LambdaPFC.Ty n}
      {body : LambdaPFC.Tm (n + 1)}
      {typing : Fragment.HasType sourceContext
        (.abs nativeDomain body) (.Fun domain codomain.weaken)}
      (spine : ApplicationSpine typing)
      (bodyAdmissible :
        OperationallyAdmissible spine.functionSpine.bodyTyping.2) :
      OperationallyAdmissible typing
  | package
      {typing : Fragment.HasType sourceContext
        (.pair first label (.type witness)) sourceType}
      (spine : ExactPackageSpine typing) :
      OperationallyAdmissible typing
  | app
      {n : Nat} {sourceContext : LambdaPFC.Ctx n}
      {function argument : LambdaPFC.Path n}
      {domain resultType : LambdaPFC.Ty n}
      {functionTyping : Fragment.HasType sourceContext (.path function)
        (.Fun domain resultType.weaken)}
      {argumentTyping : Fragment.HasType sourceContext (.path argument) domain}
      {resultWf : Fragment.Wf sourceContext resultType}
      (function : OperationallyAdmissible functionTyping)
      (functionSpine : FunctionPathSpine functionTyping)
      (argument : OperationallyAdmissible argumentTyping)
      (resultShape : NonCanonicalResultShape resultType) :
      OperationallyAdmissible
        (.app functionTyping argumentTyping resultWf)
  | «let»
      {n : Nat} {sourceContext : LambdaPFC.Ctx n}
      {bound : LambdaPFC.Tm n} {boundType resultType : LambdaPFC.Ty n}
      {body : LambdaPFC.Tm (n + 1)}
      {boundTyping : Fragment.HasType sourceContext bound boundType}
      {resultWf : Fragment.Wf sourceContext resultType}
      {bodyTyping : Fragment.HasType (sourceContext.snoc boundType) body
        resultType.weaken}
      (bound : OperationallyAdmissible boundTyping)
      (boundPolicy : LetBoundPolicy boundTyping)
      (body : OperationallyAdmissible bodyTyping)
      (resultShape : NonCanonicalResultShape resultType) :
      OperationallyAdmissible
        (.let boundTyping resultWf bodyTyping)
  | neutralSub
      {typing : Fragment.HasType sourceContext term source}
      (neutral : Neutral term)
      (inner : OperationallyAdmissible typing)
      (subtype : Fragment.Sub sourceContext source target)
      (targetShape : neutral.ResultShape target) :
      OperationallyAdmissible (.sub typing subtype)

namespace OperationallyAdmissible

/-- Propositional inversion of an admitted source value. -/
theorem valueEvidence_nonempty
    {typing : Fragment.HasType sourceContext term sourceType}
    (admissible : OperationallyAdmissible typing)
    (value : LambdaPFC.Tm.IsValue term) :
    Nonempty (ApplicationValueEvidence typing) := by
  cases admissible with
  | path => cases value
  | functionPath => cases value
  | function spine _ => exact ⟨.function spine⟩
  | package spine => exact ⟨.package spine⟩
  | app => cases value
  | «let» => cases value
  | neutralSub neutral => cases neutral <;> cases value

/-- Type-valued value evidence extracted across Lean's `Prop`/`Type`
boundary.  Later consumers use the retained spine only for proofs and closed
target syntax. -/
noncomputable def valueEvidence
    {typing : Fragment.HasType sourceContext term sourceType}
    (admissible : OperationallyAdmissible typing)
    (value : LambdaPFC.Tm.IsValue term) : ApplicationValueEvidence typing :=
  match admissible with
  | .function spine _ => .function spine
  | .package spine => .package spine
  | other => Classical.choice (valueEvidence_nonempty other value)

end OperationallyAdmissible

end OperationalAdmissibility

end LambdaPToFCo
