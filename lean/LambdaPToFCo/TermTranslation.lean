import LambdaPToFCo.Binder
import LambdaPToFCo.CoercionTranslation
import LambdaPToFCo.StaticTranslation

/-!
# Term translation for the restricted LambdaP fragment

The compiler follows source typing derivations. Ordinary source binders add
one target term variable. Abstract-member package binders add one raw variable
and use the target Church eliminator exactly once to expose its hidden type,
bound coercions, and payload as lexical slots.
-/

namespace LambdaPToFCo
namespace TermTranslation

open SystemFCo
open StaticTranslation

/-- The target binder plan selected by a supported source type, together with
the corresponding extension of the single source/target scope relation. -/
structure CompiledBinder
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (wf : Fragment.Wf sourceContext sourceType) where
  plan : Interface.BinderPlan sig
  extended : Scope (sourceContext.snoc sourceType)
    (plan.context targetContext)
  inputType_eq : plan.inputType = translateType scope wf

/-- Select the lexical representation of one source binder. -/
noncomputable def compileBinder
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (wf : Fragment.Wf sourceContext sourceType) :
    CompiledBinder scope wf :=
  match wf with
  | .top =>
      { plan := .ordinary (translateType scope .top)
        extended := scope.bindOrdinary .top .top
        inputType_eq := rfl }
  | .singleton pathTyping =>
      { plan := .ordinary (translateType scope (.singleton pathTyping))
        extended := scope.bindOrdinary (.singleton pathTyping) .singleton
        inputType_eq := rfl }
  | .selection member nonempty =>
      { plan := .ordinary
          (translateType scope (.selection member nonempty))
        extended := scope.bindOrdinary
          (.selection member nonempty) .selection
        inputType_eq := rfl }
  | @Fragment.Wf.memberPackage _ _ first label lower upper lowerWf upperWf
      nonempty =>
      { plan := .exact
          (translateType scope lowerWf)
          (translateType scope upperWf)
          (payloadFamily (scope.lookup first).path.targetType)
        extended := scope.bindMember first label lowerWf upperWf nonempty
        inputType_eq := rfl }
  | .arrow domainWf codomainWf =>
      { plan := .ordinary
          (translateType scope (.arrow domainWf codomainWf))
        extended := scope.bindOrdinary
          (.arrow domainWf codomainWf) .arrow
        inputType_eq := rfl }

/-- Compile a source typing derivation to target expression syntax.

Source subsumption becomes an explicit `cast`. Package introduction is exact
and uses `packMember`; abstract-member abstraction and let binding use the one-unpack
helpers in `BinderPlan.lambda` and `BinderPlan.close`. -/
noncomputable def elaborate
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n} :
    Fragment.HasType sourceContext term sourceType -> Exp sig
  | .path pathTyping =>
      (translatePath scope pathTyping).expression
  | .abs bodyTyping domainWf codomainWf =>
      let binder := compileBinder scope domainWf
      binder.plan.lambda (translateType scope codomainWf)
        (elaborate binder.extended bodyTyping)
  | .app functionTyping argumentTyping _ =>
      .app (elaborate scope functionTyping)
        (elaborate scope argumentTyping)
  | @Fragment.HasType.typePackage _ _ first label witness witnessWf =>
      let targetWitness := translateType scope witnessWf
      let firstTranslation := translatePath scope
        (Fragment.PathTy.var
          (Γ := sourceContext) (x := first))
      .packMember targetWitness targetWitness targetWitness
        (payloadFamily firstTranslation.targetType)
        (.refl targetWitness) (.refl targetWitness)
        firstTranslation.expression
  | .let boundTyping resultWf bodyTyping =>
      let binder := compileBinder scope boundTyping.typeWf
      binder.plan.close (elaborate scope boundTyping)
        (translateType scope resultWf)
        (elaborate binder.extended bodyTyping)
  | .sub termTyping subtype =>
      .cast (elaborate scope termTyping)
        (CoercionTranslation.elaborateSub scope subtype)

/-! ## Conditional type preservation

The proof below isolates the static facts required from coherent scopes. This
keeps the term induction independent of the representation of the coherence
invariant: it needs the subtyping endpoint laws and naturality of type
translation through the binder selected by `compileBinder`.
-/

structure TermEndpointLaws
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext) : Type where
  subtyping : CoercionTranslation.SubtypingEndpointLaws scope
  binderNaturality : forall
      {sourceType resultType : LambdaPFC.Ty n}
      (binderWf : Fragment.Wf sourceContext sourceType)
      (resultWf : Fragment.Wf sourceContext resultType),
    let binder := compileBinder scope binderWf
    translateType binder.extended (resultWf.weaken sourceType) =
      (translateType scope resultWf).rename binder.plan.weaken

/-- The finite tree of endpoint facts used by one typing derivation. Body
nodes carry laws for their concretely extended lexical scope. -/
noncomputable def ElaborationLaws
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n} :
    Fragment.HasType sourceContext term sourceType -> Type
  | .path _ => TermEndpointLaws scope
  | .abs bodyTyping domainWf _ =>
      let binder := compileBinder scope domainWf
      TermEndpointLaws scope × ElaborationLaws binder.extended bodyTyping
  | .app functionTyping argumentTyping _ =>
      TermEndpointLaws scope × ElaborationLaws scope functionTyping ×
        ElaborationLaws scope argumentTyping
  | .typePackage _ => TermEndpointLaws scope
  | .let boundTyping _ bodyTyping =>
      let binder := compileBinder scope boundTyping.typeWf
      TermEndpointLaws scope × ElaborationLaws scope boundTyping ×
        ElaborationLaws binder.extended bodyTyping
  | .sub termTyping _ =>
      TermEndpointLaws scope × ElaborationLaws scope termTyping

noncomputable def ElaborationLaws.endpoint
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext term sourceType} :
    ElaborationLaws scope typing -> TermEndpointLaws scope := by
  cases typing <;> intro laws
  · exact laws
  · exact laws.1
  · exact laws.1
  · exact laws
  · exact laws.1
  · exact laws.1

/-- Type preservation from exactly the endpoint/naturality facts consumed by
the derivation-directed compiler. -/
noncomputable def elaborate_hasType_of_laws
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    (typing : Fragment.HasType sourceContext term sourceType)
    (laws : ElaborationLaws scope typing) :
    Exp.HasType targetContext (elaborate scope typing)
      (translateType scope typing.typeWf) := by
  induction typing generalizing sig targetContext with
  | path pathTyping =>
      exact (translatePath scope pathTyping).typing
  | abs bodyTyping domainWf codomainWf bodyIH =>
      let binder := compileBinder scope domainWf
      have bodyLaws : ElaborationLaws binder.extended bodyTyping := laws.2
      have bodyTyped := bodyIH binder.extended bodyLaws
      have bodyEq := bodyLaws.endpoint.subtyping.typeIrrel
        bodyTyping.typeWf (codomainWf.weaken _)
      have bodyTyped' : Exp.HasType (binder.plan.context targetContext)
          (elaborate binder.extended bodyTyping)
          (translateType binder.extended (codomainWf.weaken _)) :=
        bodyEq ▸ bodyTyped
      have natural := laws.1.binderNaturality domainWf codomainWf
      rw [natural] at bodyTyped'
      have result := binder.plan.lambda_hasType bodyTyped'
      rw [binder.inputType_eq] at result
      exact result
  | app functionTyping argumentTyping resultWf functionIH argumentIH =>
      have functionTyped := functionIH scope laws.2.1
      have argumentTyped := argumentIH scope laws.2.2
      have functionEq := laws.1.subtyping.typeIrrel
        functionTyping.typeWf
        (Fragment.Wf.arrow argumentTyping.typeWf resultWf)
      have functionTyped' : Exp.HasType targetContext
          (elaborate scope functionTyping)
          (.arrow (translateType scope argumentTyping.typeWf)
            (translateType scope resultWf)) := by
        rw [← translateType_arrow]
        exact functionEq ▸ functionTyped
      exact .app functionTyped' argumentTyped
  | @typePackage _ sourceContext first label witness witnessWf =>
      let targetWitness := translateType scope witnessWf
      let firstTranslation := translatePath scope
        (Fragment.PathTy.var (Γ := sourceContext) (x := first))
      change Exp.HasType targetContext
        (Exp.packMember targetWitness targetWitness targetWitness
          (payloadFamily firstTranslation.targetType)
          (.refl targetWitness) (.refl targetWitness)
          firstTranslation.expression)
        (Ty.member targetWitness targetWitness
          (payloadFamily firstTranslation.targetType))
      apply Exp.HasType.packMember (.refl) (.refl)
      simpa only [payloadFamily, Ty.weaken_openTVar] using
        firstTranslation.typing
  | «let» boundTyping resultWf bodyTyping boundIH bodyIH =>
      let binder := compileBinder scope boundTyping.typeWf
      have boundTyped := boundIH scope laws.2.1
      have boundTyped' : Exp.HasType targetContext
          (elaborate scope boundTyping) binder.plan.inputType := by
        rw [binder.inputType_eq]
        exact boundTyped
      have bodyLaws : ElaborationLaws binder.extended bodyTyping := laws.2.2
      have bodyTyped := bodyIH binder.extended bodyLaws
      have bodyEq := bodyLaws.endpoint.subtyping.typeIrrel
        bodyTyping.typeWf (resultWf.weaken _)
      have bodyTyped' : Exp.HasType (binder.plan.context targetContext)
          (elaborate binder.extended bodyTyping)
          (translateType binder.extended (resultWf.weaken _)) :=
        bodyEq ▸ bodyTyped
      have natural := laws.1.binderNaturality
        boundTyping.typeWf resultWf
      rw [natural] at bodyTyped'
      exact binder.plan.close_hasType boundTyped' bodyTyped'
  | sub termTyping subtype termIH =>
      have termTyped := termIH scope laws.2
      have sourceEq := laws.1.subtyping.typeIrrel
        termTyping.typeWf subtype.sourceWf
      have termTyped' : Exp.HasType targetContext
          (elaborate scope termTyping)
          (translateType scope subtype.sourceWf) :=
        sourceEq ▸ termTyped
      exact .cast termTyped'
        (CoercionTranslation.elaborateSub_hasType_of_laws
          laws.1.subtyping subtype)

end TermTranslation
end LambdaPToFCo
