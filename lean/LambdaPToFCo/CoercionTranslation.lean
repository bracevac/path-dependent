import LambdaPToFCo.StaticCoherence
import SystemFCo.ChurchPackageCovariance

/-!
# Explicit coercions for restricted LambdaP subtyping

Every source `Fragment.Sub` constructor is compiled to object-language
`SystemFCo.Co` syntax. Member selection uses the lower and upper coercion
variables exposed by the package's lexical interface. Fixed-first package
covariance uses `Co.member`; its payload conversion is reflexivity because
the source rule does not change the first path or label.
-/

namespace LambdaPToFCo
namespace CoercionTranslation

open SystemFCo
open StaticTranslation

/-- Compile a source subtyping derivation to an explicit target coercion. -/
noncomputable def elaborateSub
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {source target : LambdaPFC.Ty n}
    (scope : Scope sourceContext targetContext) :
    Fragment.Sub sourceContext source target -> Co sig
| .refl wf => .refl (translateType scope wf)
| .trans first second =>
    .trans (elaborateSub scope first) (elaborateSub scope second)
| .top wf => .top (translateType scope wf)
| .widen _ targetWf => .refl (translateType scope targetWf)
| .selectLower member _ => (scope.lookupMember member).interface.lower
| .selectUpper member _ => (scope.lookupMember member).interface.upper
| .arrow domain codomain =>
    .arrow (elaborateSub scope domain) (elaborateSub scope codomain)
| @Fragment.Sub.package _ _ first _ _ _ _ _ lower upper _ =>
    .member (elaborateSub scope lower) (elaborateSub scope upper)
      (.refl (payloadFamily (scope.lookup first).path.targetType))

structure SubtypingEndpointLaws
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext) : Type where
  typeIrrel : forall {sourceType : LambdaPFC.Ty n}
      (left right : Fragment.Wf sourceContext sourceType),
    translateType scope left = translateType scope right
  singletonEq : forall {path : LambdaPFC.Path n}
      {sourceType : LambdaPFC.Ty n}
      (pathTyping : Fragment.PathTy sourceContext path sourceType)
      (targetWf : Fragment.Wf sourceContext sourceType),
    translateType scope (.singleton pathTyping) =
      translateType scope targetWf
  lowerEq : forall {package first : Fin n} {label : LambdaPFC.Name}
      {lower upper : LambdaPFC.Ty n}
      (member : Fragment.BoundMember sourceContext package label lower upper
        first)
      (lowerWf : Fragment.Wf sourceContext lower),
    translateType scope lowerWf = (scope.lookupMember member).lowerBound
  upperEq : forall {package first : Fin n} {label : LambdaPFC.Name}
      {lower upper : LambdaPFC.Ty n}
      (member : Fragment.BoundMember sourceContext package label lower upper
        first)
      (upperWf : Fragment.Wf sourceContext upper),
    translateType scope upperWf = (scope.lookupMember member).upperBound

def SubtypingEndpointLaws.ofCoherent
    {scope : Scope sourceContext targetContext}
    (coherent : scope.Coherent) : SubtypingEndpointLaws scope where
  typeIrrel := coherent.typeIrrel
  singletonEq := coherent.widen_eq
  lowerEq := coherent.lower_eq
  upperEq := coherent.upper_eq

/-- Type preservation from precisely the endpoint equalities used by the
subtyping compiler. -/
noncomputable def elaborateSub_hasType_of_laws
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {source target : LambdaPFC.Ty n}
    {scope : Scope sourceContext targetContext}
    (laws : SubtypingEndpointLaws scope) :
    (subtype : Fragment.Sub sourceContext source target) ->
    Co.HasType targetContext (elaborateSub scope subtype)
      (translateType scope subtype.sourceWf)
      (translateType scope subtype.targetWf)
  | .refl wf => .refl
  | .trans first second => by
      have firstTyped := elaborateSub_hasType_of_laws laws first
      have secondTyped := elaborateSub_hasType_of_laws laws second
      have middleEq := laws.typeIrrel first.targetWf second.sourceWf
      exact .trans firstTyped (middleEq.symm ▸ secondTyped)
  | .top wf => .top
  | .widen pathTyping targetWf => by
      change Co.HasType targetContext
        (.refl (translateType scope targetWf))
        (translateType scope (.singleton pathTyping))
        (translateType scope targetWf)
      rw [laws.singletonEq pathTyping targetWf]
      exact .refl
  | .selectLower member nonempty => by
      change Co.HasType targetContext
        (scope.lookupMember member).interface.lower
        (translateType scope nonempty.sourceWf)
        (translateType scope (.selection member nonempty))
      rw [laws.lowerEq member nonempty.sourceWf, translateType_selection]
      exact (scope.lookupMember member).lowerTyping
  | .selectUpper member nonempty => by
      change Co.HasType targetContext
        (scope.lookupMember member).interface.upper
        (translateType scope (.selection member nonempty))
        (translateType scope nonempty.targetWf)
      rw [translateType_selection, laws.upperEq member nonempty.targetWf]
      exact (scope.lookupMember member).upperTyping
  | .arrow domain codomain =>
      .arrow (elaborateSub_hasType_of_laws laws domain)
        (elaborateSub_hasType_of_laws laws codomain)
  | @Fragment.Sub.package _ _ first label lower1 upper1 lower2 upper2
      lower upper nonempty => by
      let payload := payloadFamily (scope.lookup first).path.targetType
      have lowerTyped := elaborateSub_hasType_of_laws laws lower
      have upperTyped := elaborateSub_hasType_of_laws laws upper
      have payloadTyped :
          Co.HasType targetContext.bindTVar (.refl payload) payload payload :=
        .refl
      change Co.HasType targetContext
        (Co.member (elaborateSub scope lower) (elaborateSub scope upper)
          (.refl payload))
        (Ty.member (translateType scope lower.targetWf)
          (translateType scope upper.sourceWf) payload)
        (Ty.member (translateType scope lower.sourceWf)
          (translateType scope upper.targetWf) payload)
      exact Co.HasType.member lowerTyped upperTyped payloadTyped
termination_by subtype => subtype.depth
decreasing_by
  all_goals simp only [Fragment.Sub.depth]
  · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  · exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
  · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  · exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
  · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  · exact Nat.lt_succ_of_le
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))

/-- Every coherent source subtyping derivation compiles to a target coercion
checked at the translations of its actual source and target endpoints. -/
noncomputable def elaborateSub_hasType
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {source target : LambdaPFC.Ty n}
    {scope : Scope sourceContext targetContext}
    (coherent : scope.Coherent)
    (subtype : Fragment.Sub sourceContext source target) :
    Co.HasType targetContext (elaborateSub scope subtype)
      (translateType scope subtype.sourceWf)
      (translateType scope subtype.targetWf) :=
  elaborateSub_hasType_of_laws
    (SubtypingEndpointLaws.ofCoherent coherent) subtype

end CoercionTranslation
end LambdaPToFCo
