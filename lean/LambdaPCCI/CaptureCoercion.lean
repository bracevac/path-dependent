import LambdaPCCI.CaptureStatic
import LambdaPCCI.StoreStratification

/-!
Action of capture-aware coercions on semantic inhabitants. Every change
to a type's capture set is justified by a `Cap.Relation`; recursive shape
coercions preserve the capture set assigned at introduction and recorded by
the world.
-/

namespace LambdaPCCI
namespace Cap

noncomputable section

/-! ## Instantiating dependent members -/

noncomputable def MemberClosure.instantiate
    {n : Nat} {k : Kind} {sigma : Store n} {world : World sigma}
    {S : Ty n} {d e : Tau (n + 1) k} {x : Fin n} :
    MemberClosure world S d e ->
    LocationEvidence world x S ->
    Coercion world (d.open (.var x)) (e.open (.var x))
| .source environment code, argument => by
    have extended := environment.snoc argument
    have compiled := Cap.Tau.Sub.compile extended code
    simpa only [← Tau.rename_openAt_eq_open_var,
      Tau.rename_ext_openAt] using compiled

/-! ## Coercion sizes -/

mutual

def TyCoercion.treeSize : TyCoercion world T U -> Nat
| .refl => 1
| .trans first second => first.treeSize + second.treeSize + 1
| .runtime _ => 1
| .capt _ shape => shape.treeSize + 1

def ShapeCoercion.treeSize : ShapeCoercion world S T -> Nat
| .refl => 1
| .trans first second => first.treeSize + second.treeSize + 2
| .runtime _ => 1
| .bot => 1
| .top => 1
| .inter left right => left.treeSize + right.treeSize + 1
| .interLeft => 1
| .interRight => 1
| .unionLeft => 1
| .unionRight => 1
| .union left right => left.treeSize + right.treeSize + 1
| .pairInter => 1
| .pairTypeInter => 1
| .pairTypeUnionInter => 1
| .widen _ _ => 1
| .alias _ _ => 1
| .selectLower _ lower => lower.treeSize + 2
| .selectUpper _ upper => upper.treeSize + 2
| .fun domain _ => domain.treeSize + 1
| .pair first _ => first.treeSize + 1

def Coercion.treeSize : Coercion world d e -> Nat
| .refl => 1
| .trans first second => first.treeSize + second.treeSize + 1
| .runtime _ => 1
| .term types => types.treeSize + 1
| .type lower upper => lower.treeSize + upper.treeSize + 1
| .capture _ _ => 1

end

/-! ## Coercion action -/

/-- Apply a capture-aware coercion to a realized runtime referent. -/
noncomputable def Coercion.action
    {n : Nat} {k : Kind} {sigma : Store n} {world : World sigma}
    {d e : Tau n k} {referent : Path.Referent n} :
    Coercion world d e ->
    Realizes world referent d ->
    Realizes world referent e
| .refl, realizes => realizes
| .trans first second, realizes => second.action (first.action realizes)
| .runtime conversion, realizes => realizes.convert conversion
| .type lower upper, .type sourceLower sourceUpper =>
    .type (.trans lower sourceLower) (.trans sourceUpper upper)
| .capture lower upper, .capture sourceLower sourceUpper =>
    .capture (.trans lower sourceLower) (.trans sourceUpper upper)
| .term .refl, .loc possible => .loc possible
| .term (.trans first second), .loc possible =>
    (Coercion.term second).action
      ((Coercion.term first).action (.loc possible))
| .term (.runtime conversion), .loc possible =>
    .loc (possible.convert conversion)
| .term (.capt captures .refl), .loc possible =>
    .loc (possible.widenCaptureSet captures)
| .term (.capt captures (.trans first second)), .loc possible => by
    have firstResult :=
      (Coercion.term (TyCoercion.capt .refl first)).action (.loc possible)
    have secondResult :=
      (Coercion.term (TyCoercion.capt .refl second)).action firstResult
    cases secondResult with
    | loc result => exact .loc (result.widenCaptureSet captures)
| .term (.capt captures (.runtime conversion)), .loc possible =>
    .loc ((possible.convertCongruent
      (.capt
        (CaptureSet.RuntimeCongruent.refl
          (Path.RuntimeEq.eqCongruence sigma) _)
        (conversion.runtimeCongruent
          (Path.RuntimeEq.eqCongruence sigma)))).widenCaptureSet captures)
| .term (.capt captures .bot), .loc possible => by
    cases possible
| .term (.capt captures .top), .loc possible =>
    .loc (possible.toTop.widenCaptureSet captures)
| .term (.capt captures (.inter left right)), .loc possible => by
    have leftResult :=
      (Coercion.term (TyCoercion.capt .refl left)).action (.loc possible)
    have rightResult :=
      (Coercion.term (TyCoercion.capt .refl right)).action (.loc possible)
    cases leftResult with
    | loc leftPossible =>
        cases rightResult with
        | loc rightPossible =>
            have paired := LocationEvidence.inter leftPossible rightPossible
            exact .loc (paired.widenCaptureSet captures)
| .term (.capt captures .interLeft), .loc (.inter left _) =>
    .loc (left.widenCaptureSet captures)
| .term (.capt captures .interRight), .loc (.inter _ right) =>
    .loc (right.widenCaptureSet captures)
| .term (.capt captures .unionLeft), .loc possible =>
    .loc (.unionLeft (possible.widenCaptureSet captures))
| .term (.capt captures .unionRight), .loc possible =>
    .loc (.unionRight (possible.widenCaptureSet captures))
| .term (.capt captures (.union left right)),
    .loc (.unionLeft possible) => by
    have result :=
      (Coercion.term (TyCoercion.capt .refl left)).action (.loc possible)
    cases result with
    | loc mapped => exact .loc (mapped.widenCaptureSet captures)
| .term (.capt captures (.union left right)),
    .loc (.unionRight possible) => by
    have result :=
      (Coercion.term (TyCoercion.capt .refl right)).action (.loc possible)
    cases result with
    | loc mapped => exact .loc (mapped.widenCaptureSet captures)
| .term (.capt captures .pairInter), .loc (.inter left right) => by
    cases left with
    | @pair _ _ _ _ _ _ _ _ _ leftDefinition _ _
        leftLookup leftFirst leftMember leftCoverage =>
        cases leftDefinition with
        | val _ =>
        cases right with
        | @pair _ _ _ _ _ _ _ _ _ rightDefinition _ _
            rightLookup _ rightMember _ =>
            cases rightDefinition with
            | val _ =>
            obtain ⟨valueEq, captureEq⟩ :=
              leftLookup.unique rightLookup
            cases valueEq
            cases captureEq
            cases leftMember with
            | loc leftPossible =>
                cases rightMember with
                | loc rightPossible =>
                    exact .loc (.pair leftLookup leftFirst
                      (.loc (.inter leftPossible rightPossible))
                      (leftCoverage.comp captures))
| .term (.capt captures .pairTypeInter), .loc (.inter left right) => by
    cases left with
    | @pair _ _ _ _ _ _ _ _ _ leftDefinition _ _
        leftLookup leftFirst leftMember leftCoverage =>
        cases leftDefinition with
        | type _ =>
        cases right with
        | @pair _ _ _ _ _ _ _ _ _ rightDefinition _ _
            rightLookup _ rightMember _ =>
            cases rightDefinition with
            | type _ =>
            obtain ⟨valueEq, captureEq⟩ :=
              leftLookup.unique rightLookup
            cases valueEq
            cases captureEq
            cases leftMember with
            | type leftLower leftUpper =>
                cases rightMember with
                | type _ rightUpper =>
                    exact .loc (.pair leftLookup leftFirst
                      (.type leftLower (.inter leftUpper rightUpper))
                      (leftCoverage.comp captures))
| .term (.capt captures .pairTypeUnionInter),
    .loc (.inter left right) => by
    cases left with
    | @pair _ _ _ _ _ _ _ _ _ leftDefinition _ _
        leftLookup leftFirst leftMember leftCoverage =>
        cases leftDefinition with
        | type _ =>
        cases right with
        | @pair _ _ _ _ _ _ _ _ _ rightDefinition _ _
            rightLookup _ rightMember _ =>
            cases rightDefinition with
            | type _ =>
            obtain ⟨valueEq, captureEq⟩ :=
              leftLookup.unique rightLookup
            cases valueEq
            cases captureEq
            cases leftMember with
            | type leftLower leftUpper =>
                cases rightMember with
                | type rightLower rightUpper =>
                    exact .loc (.pair leftLookup leftFirst
                      (.type (.union leftLower rightLower)
                        (.inter leftUpper rightUpper))
                      (leftCoverage.comp captures))
| .term (.capt captures (.widen targetResolution target)),
    .loc (.single lookup sourceResolution sourceCoverage) => by
    cases sourceResolution.deterministic targetResolution
    exact .loc (target.replaceLookup lookup (sourceCoverage.comp captures))
| .term (.capt captures (.alias targetResolution sourceResolution)),
    .loc (.single lookup resolution sourceCoverage) => by
    cases resolution.deterministic sourceResolution
    exact .loc (.single lookup targetResolution
      (sourceCoverage.comp captures))
| .term (.capt captures (.selectLower resolution lower)),
    .loc possible => by
    let view := possible.captureSetView
    have witness :=
      (Coercion.term (TyCoercion.capt .refl lower)).action (.loc possible)
    cases witness with
    | loc possibleWitness =>
        exact .loc (.selection view.lookup resolution possibleWitness
          (view.captures.comp captures))
| .term (.capt captures (.selectUpper resolution upper)),
    .loc (.selection lookup sourceResolution witness sourceCoverage) => by
    cases sourceResolution.deterministic resolution
    have result :=
      (Coercion.term (TyCoercion.capt .refl upper)).action (.loc witness)
    cases result with
    | loc possibleResult =>
        exact .loc (possibleResult.replaceLookup lookup
          (sourceCoverage.comp captures))
| .term (.capt captures (.fun domain codomain)),
    .loc (.fun lookup body input output sourceCoverage) =>
    .loc (.fun lookup body
      (.trans domain input)
      (.trans (.narrow domain output) codomain)
      (sourceCoverage.comp captures))
| .term (.capt captures (.pair firstCode memberClosure)),
    .loc (@LocationEvidence.pair _ _ _ _ _ _ _ _ _ _ _ _
      lookup first member sourceCoverage) => by
    have binding := lookup.binds
    have firstStratum := binding.pair_first_stratum_lt
    have memberStratum := binding.pair_referent_stratum_lt
    have mapped := (Coercion.term firstCode).action (.loc first)
    cases mapped with
    | loc mappedFirst =>
        have mappedMember :=
          (memberClosure.instantiate first).action member
        exact .loc (.pair lookup mappedFirst mappedMember
          (sourceCoverage.comp captures))
termination_by coercion _ => (referent.stratum, coercion.treeSize)
decreasing_by
  all_goals simp_wf
  all_goals simp only [Coercion.treeSize, TyCoercion.treeSize,
    ShapeCoercion.treeSize]
  all_goals omega

noncomputable def Coercion.actionLocation
    (coercion : Coercion world (.term T) (.term U))
    (possible : LocationEvidence world x T) : LocationEvidence world x U := by
  have mapped := coercion.action (.loc possible)
  cases mapped with
  | loc result => exact result

noncomputable def TyCoercion.actionLocation
    (coercion : TyCoercion world T U)
    (possible : LocationEvidence world x T) : LocationEvidence world x U :=
  (Coercion.term coercion).actionLocation possible

/-! ## Instantiating function codomains -/

noncomputable def DeferredCoercion.instantiate
    {n : Nat} {sigma : Store n} {world : World sigma}
    {S : Ty n} {T U : Ty (n + 1)} {x : Fin n} :
    DeferredCoercion world S T U ->
    LocationEvidence world x S ->
    TyCoercion world (T.open (.var x)) (U.open (.var x))
| .refl, _ => .refl
| .trans first second, argument =>
    .trans (first.instantiate argument) (second.instantiate argument)
| .runtime conversion, _ =>
    .runtime (conversion.openSame
      (Path.RuntimeEq.eqCongruence sigma) (.var x))
| .narrow domain deferred, argument =>
    deferred.instantiate (domain.actionLocation argument)
| .source environment code, argument => by
    have extended := environment.snoc argument
    have compiled := Cap.Ty.Sub.compile extended code
    simpa only [← Ty.rename_openAt_eq_open_var,
      Ty.rename_ext_openAt] using compiled

end
end Cap
end LambdaPCCI
