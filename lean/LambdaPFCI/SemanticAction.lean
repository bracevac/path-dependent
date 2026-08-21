import LambdaPFCI.SemanticEvidence
import LambdaPFCI.StoreStratification

/-!
Execution and elaboration of finite semantic evidence.  Runtime conversion is
first normalized to structural congruence.  Source subtyping is compiled
eagerly under a semantic environment.  Function codomains and dependent-pair
members are suspended until execution supplies their bound locations.
-/

namespace LambdaPFCI

noncomputable section

/-! ## Runtime conversion -/

mutual

/-- Structural runtime conversion preserves possible inhabitants. -/
noncomputable def Store.Possible.convertCongruent
    {m : Nat} {sigma : Store m} {x : Fin m} {S T : Ty m} :
    Store.Possible sigma x S ->
      Tau.RuntimeCongruent (Path.RuntimeEq sigma) (.ty S) (.ty T) ->
      Store.Possible sigma x T
| .top, .top => .top
| .inter left right, .inter leftConversion rightConversion =>
    .inter
      (Store.Possible.convertCongruent left leftConversion)
      (Store.Possible.convertCongruent right rightConversion)
| .unionLeft left, .union leftConversion _ =>
    .unionLeft (Store.Possible.convertCongruent left leftConversion)
| .unionRight right, .union _ rightConversion =>
    .unionRight (Store.Possible.convertCongruent right rightConversion)
| .fun binding body input output, .fun domain codomain =>
    let operations := Path.RuntimeEq.eqCongruence sigma
    let backwards : Coercion sigma _ _ :=
      .runtime ((domain.symm operations).toRuntimeConv)
    .fun binding body
      (.trans backwards input)
      (.trans (.narrow backwards output)
        (.runtime codomain.toRuntimeConv))
| @Store.Possible.pair m sigma x y a k _ S d
      binding first member, .pair firstConversion memberConversion =>
    let operations := Path.RuntimeEq.eqCongruence sigma
    let opened :=
      memberConversion.toRuntimeConv.openSame operations (Path.var y)
    .pair binding
      (Store.Possible.convertCongruent first firstConversion)
      (Path.Referent.Realizes.convertCongruent member
        (opened.runtimeCongruent operations))
| .single resolution, .single paths =>
    .single ((paths.resolve_iff _).mp resolution)
| .selection resolution witness, .selection paths =>
    .selection (((paths.sel _).resolve_iff _).mp resolution) witness

/-- Structural runtime conversion preserves generalized referent
realization. -/
noncomputable def Path.Referent.Realizes.convertCongruent
    {m : Nat} {k : Kind} {sigma : Store m}
    {referent : Path.Referent m} {d1 d2 : Tau m k}
    (realizes : Path.Referent.Realizes sigma referent d1)
    (congruent : Tau.RuntimeCongruent (Path.RuntimeEq sigma) d1 d2) :
    Path.Referent.Realizes sigma referent d2 :=
  match d2, realizes, congruent with
  | .ty _, .loc possible, types =>
      .loc (Store.Possible.convertCongruent possible types)
  | .intv _ _, .type lower upper, .interval lowerConversion upperConversion =>
      let operations := Path.RuntimeEq.eqCongruence sigma
      .type
        (.trans
          (.runtime ((lowerConversion.symm operations).toRuntimeConv))
          lower)
        (.trans upper (.runtime upperConversion.toRuntimeConv))

end

/-- Direct action of arbitrary runtime conversion on generalized referent
realization. -/
noncomputable def Path.Referent.Realizes.convert
    (realizes : Path.Referent.Realizes sigma referent d1)
    (conversion : Tau.RuntimeConv (Path.RuntimeEq sigma) d1 d2) :
    Path.Referent.Realizes sigma referent d2 :=
  realizes.convertCongruent
    (conversion.runtimeCongruent (Path.RuntimeEq.eqCongruence sigma))

/-! ## Resolving source path derivations -/

/-- The semantic result of a source path-typing derivation under a
valuation. -/
structure Path.Ty.Resolution
    {n m : Nat} {k : Kind} (sigma : Store m)
    (rho : Valuation n m) (p : Path n) (d : Tau n k) : Type 1 where
  referent : Path.Referent m
  resolution : Path.Resolve (p.rename rho) sigma referent
  realizes : Path.Referent.Realizes sigma referent (d.rename rho)

/-- Resolve a typed source path and retain realization of its precise type. -/
noncomputable def Path.Ty.resolve
    {n m : Nat} {Gamma : Ctx n} {rho : Valuation n m}
    {sigma : Store m} {k : Kind} {p : Path n} {d : Tau n k}
    (environment : Environment Gamma rho sigma)
    (code : Path.Ty Gamma p d) :
    Path.Ty.Resolution sigma rho p d := by
  induction code with
  | @var _ x =>
      refine ⟨.loc (rho x), ?_, ?_⟩
      · exact .var
      · apply Path.Referent.Realizes.loc
        exact Environment.lookup environment x
  | fst receiver ih =>
      obtain ⟨referent, resolution, realizes⟩ := ih environment
      cases realizes with
      | loc possible =>
          cases possible with
          | pair binding first member =>
              exact ⟨.loc _, .fst resolution binding, .loc first⟩
  | @sel_r _ _ receiverPath S a dependent receiver ih =>
      obtain ⟨referent, resolution, realizes⟩ := ih environment
      cases realizes with
      | loc possible =>
          cases possible with
          | @pair _ _ _ y _ _ delta _ _
              binding first member =>
              have firstResolution :
                  Path.Resolve ((receiverPath.rename rho).fst)
                    sigma (.loc y) :=
                .fst resolution binding
              have paths :
                  Path.RuntimeEq sigma (.var y)
                    ((receiverPath.rename rho).fst) :=
                .coresolve .var firstResolution
              have converted := member.convert
                (Tau.RuntimeConv.replace (dependent.rename rho.ext) paths)
              have converted' :
                  Path.Referent.Realizes sigma delta.referent
                    ((dependent.open receiverPath.fst).rename rho) := by
                simpa [Tau.open_rename, Path.rename] using converted
              exact ⟨delta.referent, .sel resolution binding, converted'⟩
  | @sel_l _ _ receiverPath S b receiverKind dependent a d
      receiver member distinct ihReceiver ihMember =>
      obtain ⟨receiverReferent, receiverResolution, receiverRealizes⟩ :=
        ihReceiver environment
      obtain ⟨memberReferent, memberResolution, memberRealizes⟩ :=
        ihMember environment
      cases receiverRealizes with
      | loc possible =>
          cases possible with
          | @pair _ _ _ y _ _ delta _ _ binding first storedMember =>
              have firstResolution :
                  Path.Resolve ((receiverPath.rename rho).fst)
                    sigma (.loc y) :=
                .fst receiverResolution binding
              have tailResolution := Path.Resolve.sel_congr
                memberResolution firstResolution Path.Resolve.var
              exact ⟨memberReferent,
                .sel_miss receiverResolution binding distinct tailResolution,
                memberRealizes⟩

/-! ## Eager compilation of source subtyping -/

/-- Compile source subtyping under a semantic environment to a finite
target-store coercion, retaining function codomains and dependent-pair
members until their binder locations are known. -/
noncomputable def Tau.Sub.compile
    {n m : Nat} {Gamma : Ctx n} {rho : Valuation n m}
    {sigma : Store m} {k : Kind} {d1 d2 : Tau n k}
    (environment : Environment Gamma rho sigma) :
    Tau.Sub Gamma d1 d2 ->
      Coercion sigma (d1.rename rho) (d2.rename rho)
| .refl => .refl
| .trans first second =>
    .trans (first.compile environment) (second.compile environment)
| .bot => .bot
| .top => .top
| .inter left right =>
    .inter (left.compile environment) (right.compile environment)
| .inter_left => .interLeft
| .inter_right => .interRight
| .union_left => .unionLeft
| .union_right => .unionRight
| .union left right =>
    .union (left.compile environment) (right.compile environment)
| .merge plan => .merge environment plan
| .widen path => by
    obtain ⟨referent, resolution, realizes⟩ := path.resolve environment
    cases realizes with
    | loc possible =>
        exact .widen resolution possible
| .symm path => by
    obtain ⟨referent, resolution, realizes⟩ := path.resolve environment
    cases realizes with
    | loc possible =>
        cases possible with
        | single targetResolution =>
            exact .alias resolution targetResolution
| .sel_hi path _bounds => by
    obtain ⟨referent, resolution, realizes⟩ := path.resolve environment
    cases realizes with
    | type lower upper =>
        exact .selHi resolution upper
| .sel_lo path _bounds => by
    obtain ⟨referent, resolution, realizes⟩ := path.resolve environment
    cases realizes with
    | type lower upper =>
        exact .selLo resolution lower
| .fun domain codomain =>
    .fun (domain.compile environment) (.source environment codomain)
| .pair first member =>
    .pair (first.compile environment) (.source environment member)
| .bounds lower upper _nonempty =>
    .bounds (lower.compile environment) (upper.compile environment)

/-! ## Executing aligned merge plans -/

/-- Combine the two lower-bound coercions prescribed by an interval merge. -/
noncomputable def Ty.Join.action
    {n m : Nat} {Gamma : Ctx n} {rho : Valuation n m}
    {sigma : Store m} {L1 L2 L : Ty n} {W : Ty m}
    (plan : Ty.Join Gamma L1 L2 L)
    (left : Coercion sigma (.ty (L1.rename rho)) (.ty W))
    (right : Coercion sigma (.ty (L2.rename rho)) (.ty W)) :
    Coercion sigma (.ty (L.rename rho)) (.ty W) :=
  match plan with
  | .same => left
  | .union => .union left right

/-- Merge generalized member certificates.  Proper members recurse on their
types.  Pair recursion first merges the stored predecessor and then
interprets the member plan under that concrete merged predecessor.  Interval
members join their lower bounds and recursively merge their upper bounds. -/
noncomputable def Tau.Merge.action
    {n m : Nat} {Gamma : Ctx n} {rho : Valuation n m}
    {sigma : Store m} {k : Kind} {d1 d2 d : Tau n k}
    {referent : Path.Referent m} :
    (plan : Tau.Merge Gamma d1 d2 d) ->
    (environment : Environment Gamma rho sigma) ->
    Path.Referent.Realizes sigma referent (d1.rename rho) ->
    Path.Referent.Realizes sigma referent (d2.rename rho) ->
    Path.Referent.Realizes sigma referent (d.rename rho)
  | .same, _, left, _ => left
  | .inter, _, left, right => by
      change Path.Referent.Realizes sigma referent (.ty _) at left right ⊢
      cases left with
      | loc left =>
        cases right with
        | loc right =>
          exact .loc (.inter left right)
  | .pair firstPlan memberPlan, environment, left, right => by
      change Path.Referent.Realizes sigma referent (.ty (.Pair _ _ _))
        at left right ⊢
      cases left with
      | loc left =>
        cases right with
        | loc right =>
          cases left with
          | @pair _ _ _ _ _ _ leftDefinition _ _
              leftBinding leftFirst leftMember =>
            cases right with
            | @pair _ _ _ _ _ _ rightDefinition _ _
                rightBinding rightFirst rightMember =>
              cases Store.Binds.unique leftBinding rightBinding
              have mergedFirstRealizes :=
                firstPlan.action environment (.loc leftFirst) (.loc rightFirst)
              cases mergedFirstRealizes with
              | loc mergedFirst =>
                have extended := Environment.snoc environment mergedFirst
                have normalizedLeft := by
                  simpa only [← Tau.rename_openAt_eq_open_var,
                    Tau.rename_ext_openAt] using leftMember
                have normalizedRight := by
                  simpa only [← Tau.rename_openAt_eq_open_var,
                    Tau.rename_ext_openAt] using rightMember
                have mergedMember :=
                  memberPlan.action extended normalizedLeft normalizedRight
                refine .loc (.pair leftBinding mergedFirst ?_)
                simpa only [← Tau.rename_openAt_eq_open_var,
                  Tau.rename_ext_openAt] using mergedMember
  | .intv lowerPlan upperPlan, environment, left, right => by
      change Path.Referent.Realizes sigma referent (.intv _ _) at left right ⊢
      cases left with
      | type leftLower leftUpper =>
        cases right with
        | type rightLower rightUpper =>
          exact .type
            (lowerPlan.action leftLower rightLower)
            (.trans (.inter leftUpper rightUpper)
              (.merge environment upperPlan))

/-! ## Instantiating dependent-pair members -/

/-- Compile a delayed member comparison after the stored pair exposes its
concrete first-component location. -/
noncomputable def MemberClosure.instantiate
    {m : Nat} {sigma : Store m} {S : Ty m} {k : Kind}
    {d d' : Tau (m + 1) k} {x : Fin m} :
    MemberClosure sigma S d d' ->
    Store.Possible sigma x S ->
    Coercion sigma (d.open (.var x)) (d'.open (.var x))
| .source environment code, argument => by
    have extended := Environment.snoc environment argument
    have compiled := Tau.Sub.compile extended code
    simpa only [← Tau.rename_openAt_eq_open_var,
      Tau.rename_ext_openAt] using compiled

/-! ## Coercion size -/

/-- Structural size used as the secondary component of coercion action's
well-founded measure. -/
def Coercion.treeSize : Coercion sigma d1 d2 -> Nat
| .refl => 1
| .trans first second => first.treeSize + second.treeSize + 1
| .runtime _ => 1
| .bot => 1
| .top => 1
| .inter left right => left.treeSize + right.treeSize + 1
| .interLeft => 1
| .interRight => 1
| .unionLeft => 1
| .unionRight => 1
| .union left right => left.treeSize + right.treeSize + 1
| .merge _ _ => 1
| .widen _ _ => 1
| .alias _ _ => 1
| .selLo _ lower => lower.treeSize + 1
| .selHi _ upper => upper.treeSize + 1
| .fun domain _ => domain.treeSize + 1
| .pair first _ => first.treeSize + 1
| .bounds lower upper =>
    lower.treeSize + upper.treeSize + 1

/-! ## Coercion action -/

/-- Execute a finite coercion on generalized referent realization.  Ordinary
recursive calls consume a proper subcoercion.  Acting on a pair descends to
the older first-component and member referents recorded by its store
binding, which is the primary component of the well-founded measure. -/
noncomputable def Coercion.action
    {m : Nat} {sigma : Store m} {k : Kind} {d1 d2 : Tau m k}
    {referent : Path.Referent m} :
    Coercion sigma d1 d2 ->
    Path.Referent.Realizes sigma referent d1 ->
    Path.Referent.Realizes sigma referent d2
| .refl, realizes => realizes
| .trans first second, realizes =>
    second.action (first.action realizes)
| .runtime conversion, realizes => realizes.convert conversion
| .bot, realizes => by
    cases realizes with
    | loc possible => cases possible
| .top, realizes => by
    cases realizes with
    | loc possible => exact .loc .top
| .inter left right, .loc possible => by
    have leftResult := left.action (.loc possible)
    have rightResult := right.action (.loc possible)
    cases leftResult with
    | loc leftPossible =>
        cases rightResult with
        | loc rightPossible =>
            exact .loc (.inter leftPossible rightPossible)
| .interLeft, .loc (.inter left _) => .loc left
| .interRight, .loc (.inter _ right) => .loc right
| .unionLeft, .loc possible => .loc (.unionLeft possible)
| .unionRight, .loc possible => .loc (.unionRight possible)
| .union left _, .loc (.unionLeft possible) =>
    left.action (.loc possible)
| .union _ right, .loc (.unionRight possible) =>
    right.action (.loc possible)
| .merge environment plan, .loc (.inter left right) =>
    plan.action environment (.loc left) (.loc right)
| .widen resolution target, realizes => by
    cases realizes with
    | loc possible =>
        cases possible with
        | single sourceResolution =>
            cases sourceResolution.deterministic resolution
            exact .loc target
| .alias targetResolution sourceResolution, realizes => by
    cases realizes with
    | loc possible =>
        cases possible with
        | single resolution =>
            cases resolution.deterministic sourceResolution
            exact .loc (.single targetResolution)
| .selLo resolution lower, .loc possible => by
    have witness := lower.action (.loc possible)
    cases witness with
    | loc possibleWitness =>
        exact .loc (.selection resolution possibleWitness)
| .selHi resolution upper, .loc (.selection sourceResolution witness) => by
    cases sourceResolution.deterministic resolution
    exact upper.action (.loc witness)
| .fun domain codomain, realizes => by
    cases realizes with
    | loc possible =>
        cases possible with
        | «fun» binding body input output =>
            exact .loc (.fun binding body
              (.trans domain input)
              (.trans (.narrow domain output) codomain))
| .pair firstCode memberClosure,
    .loc (@Store.Possible.pair _ _ _ _ _ _ _ _ _
      binding first member) => by
    have firstStratum := binding.pair_first_stratum_lt
    have memberStratum := binding.pair_referent_stratum_lt
    have mapped := firstCode.action (.loc first)
    cases mapped with
    | loc mappedFirst =>
        have mappedMember :=
          (memberClosure.instantiate first).action member
        exact .loc (.pair binding mappedFirst mappedMember)
| .bounds lower upper, realizes => by
    cases realizes with
    | type sourceLower sourceUpper =>
        exact .type (.trans lower sourceLower) (.trans sourceUpper upper)
termination_by coercion _ =>
  (referent.stratum, coercion.treeSize)
decreasing_by
  all_goals simp_wf
  all_goals simp only [Coercion.treeSize]
  all_goals omega

/-- Proper-type specialization of coercion action. -/
noncomputable def Coercion.actionPossible
    (coercion : Coercion sigma (.ty S) (.ty T))
    (possible : Store.Possible sigma x S) :
    Store.Possible sigma x T := by
  have mapped := coercion.action (.loc possible)
  cases mapped with
  | loc result => exact result

/-! ## Instantiating deferred codomains -/

/-- Supply the concrete argument of a deferred function-codomain coercion.
The source case extends its saved environment before compiling the body of
the subtyping derivation. -/
noncomputable def DeferredCoercion.instantiate
    {m : Nat} {sigma : Store m} {S : Ty m} {T U : Ty (m + 1)}
    {x : Fin m} :
    DeferredCoercion sigma S T U ->
    Store.Possible sigma x S ->
    Coercion sigma (.ty (T.open (.var x))) (.ty (U.open (.var x)))
| .refl, argument => .refl
| .trans first second, argument =>
    .trans (first.instantiate argument) (second.instantiate argument)
| .runtime conversion, argument =>
    .runtime (conversion.openSame
      (Path.RuntimeEq.eqCongruence sigma) (.var x))
| .narrow domain deferred, argument =>
    deferred.instantiate (domain.actionPossible argument)
| .source environment code, argument =>
    (MemberClosure.source environment code).instantiate argument

end
end LambdaPFCI
