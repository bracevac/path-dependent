import LambdaPToFCo.TermTranslationNaturality
import LambdaPToFCo.StaticCoherence

/-!
# Type preservation for the restricted LambdaP compiler

Coherent scopes provide the endpoint equalities needed by explicit coercions
and remain coherent after either ordinary or member-package compilation. These
facts instantiate the finite law tree consumed by the term-typing induction.
-/

namespace LambdaPToFCo
namespace TermTranslation

open StaticTranslation

/-- Compiling any supported source binder preserves scope coherence. -/
noncomputable def compiledBinder_coherent
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : SystemFCo.Sig} {targetContext : SystemFCo.Ctx sig}
    {scope : Scope sourceContext targetContext}
    (coherent : scope.Coherent)
    {sourceType : LambdaPFC.Ty n}
    (wf : Fragment.Wf sourceContext sourceType) :
    (compileBinder scope wf).extended.Coherent := by
  cases wf with
  | top => exact coherent.bindOrdinary .top .top
  | singleton pathTyping =>
      exact coherent.bindOrdinary (.singleton pathTyping) .singleton
  | selection member nonempty =>
      exact coherent.bindOrdinary (.selection member nonempty) .selection
  | @memberPackage first label lower upper lowerWf upperWf nonempty =>
      exact coherent.bindMember first label lowerWf upperWf nonempty
  | arrow domainWf codomainWf =>
      exact coherent.bindOrdinary (.arrow domainWf codomainWf) .arrow

/-- A coherent scope supplies every local endpoint and binder-naturality fact
used by term elaboration. -/
def TermEndpointLaws.ofCoherent
    {scope : Scope sourceContext targetContext}
    (coherent : scope.Coherent) : TermEndpointLaws scope where
  subtyping := CoercionTranslation.SubtypingEndpointLaws.ofCoherent coherent
  binderNaturality := compileBinder_naturality scope

/-- Build the finite static-law tree for one source typing derivation. -/
noncomputable def ElaborationLaws.ofCoherent
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : SystemFCo.Sig} {targetContext : SystemFCo.Ctx sig}
    {scope : Scope sourceContext targetContext}
    (coherent : scope.Coherent) :
    {term : LambdaPFC.Tm n} -> {sourceType : LambdaPFC.Ty n} ->
    (typing : Fragment.HasType sourceContext term sourceType) ->
      ElaborationLaws scope typing
  | _, _, .path _ => TermEndpointLaws.ofCoherent coherent
  | _, _, .abs bodyTyping domainWf _ =>
      ⟨TermEndpointLaws.ofCoherent coherent,
        ElaborationLaws.ofCoherent
          (compiledBinder_coherent coherent domainWf) bodyTyping⟩
  | _, _, .app functionTyping argumentTyping _ =>
      ⟨TermEndpointLaws.ofCoherent coherent,
        ElaborationLaws.ofCoherent coherent functionTyping,
        ElaborationLaws.ofCoherent coherent argumentTyping⟩
  | _, _, .typePackage _ => TermEndpointLaws.ofCoherent coherent
  | _, _, .let boundTyping _ bodyTyping =>
      ⟨TermEndpointLaws.ofCoherent coherent,
        ElaborationLaws.ofCoherent coherent boundTyping,
        ElaborationLaws.ofCoherent
          (compiledBinder_coherent coherent boundTyping.typeWf)
          bodyTyping⟩
  | _, _, .sub termTyping _ =>
      ⟨TermEndpointLaws.ofCoherent coherent,
        ElaborationLaws.ofCoherent coherent termTyping⟩

/-- The derivation-directed compiler is type preserving. Source subsumption
is checked in the target solely through the generated object-language casts. -/
noncomputable def elaborate_hasType
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : SystemFCo.Sig} {targetContext : SystemFCo.Ctx sig}
    {scope : Scope sourceContext targetContext}
    (coherent : scope.Coherent)
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    (typing : Fragment.HasType sourceContext term sourceType) :
    SystemFCo.Exp.HasType targetContext (elaborate scope typing)
      (translateType scope typing.typeWf) :=
  elaborate_hasType_of_laws scope typing
    (ElaborationLaws.ofCoherent coherent typing)

end TermTranslation
end LambdaPToFCo
