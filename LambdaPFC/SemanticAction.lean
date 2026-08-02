import LambdaPFC.SemanticEvidence
import LambdaPFC.CodeMetatheory

/-!
Execution and elaboration of finite semantic evidence.  Runtime conversion is
first normalized to structural congruence.  Source subtyping is compiled
eagerly under a semantic environment; the sole suspended source derivations
are function codomains, which are compiled after application supplies their
bound argument.
-/

namespace LambdaPFC

noncomputable section

/-! ## Runtime conversion -/

mutual

/-- Structural runtime conversion preserves possible inhabitants. -/
noncomputable def Store.Possible.convertCongruent
    {m : Nat} {sigma : Store m} {x : Fin m} {S T : Ty m} :
    Store.Possible sigma x S ->
      Ty.RuntimeCongruent (Path.RuntimeEq sigma) S T ->
      Store.Possible sigma x T
| .top, .top => .top
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
      (Path.Endpoint.Realizes.convertCongruent member
        (opened.runtimeCongruent operations))
| .single resolution, .single paths =>
    .single ((paths.resolve_iff _).mp resolution)
| .selection resolution witness, .selection paths =>
    .selection (((paths.sel _).resolve_iff _).mp resolution) witness

/-- Structural runtime conversion preserves generalized endpoint
realization. -/
noncomputable def Path.Endpoint.Realizes.convertCongruent
    {m : Nat} {k : Kind} {sigma : Store m}
    {endpoint : Path.Endpoint m} {d1 d2 : Tau m k} :
    Path.Endpoint.Realizes sigma endpoint d1 ->
      Tau.RuntimeCongruent (Path.RuntimeEq sigma) d1 d2 ->
      Path.Endpoint.Realizes sigma endpoint d2
| .val possible, .proper types =>
    .val (Store.Possible.convertCongruent possible types)
| .type lower upper, .interval lowerConversion upperConversion =>
    let operations := Path.RuntimeEq.eqCongruence sigma
    .type
      (.trans
        (.runtime ((lowerConversion.symm operations).toRuntimeConv))
        lower)
      (.trans upper (.runtime upperConversion.toRuntimeConv))

end

/-- Direct action of arbitrary runtime conversion on possible inhabitants. -/
noncomputable def Store.Possible.convert
    (possible : Store.Possible sigma x S)
    (conversion : Tau.RuntimeConv (Path.RuntimeEq sigma)
      (.ty S) (.ty T)) :
    Store.Possible sigma x T :=
  possible.convertCongruent
    (conversion.runtimeCongruent
      (Path.RuntimeEq.eqCongruence sigma)).properTypes

/-- Direct action of arbitrary runtime conversion on generalized endpoint
realization. -/
noncomputable def Path.Endpoint.Realizes.convert
    (realizes : Path.Endpoint.Realizes sigma endpoint d1)
    (conversion : Tau.RuntimeConv (Path.RuntimeEq sigma) d1 d2) :
    Path.Endpoint.Realizes sigma endpoint d2 :=
  realizes.convertCongruent
    (conversion.runtimeCongruent (Path.RuntimeEq.eqCongruence sigma))

/-! ## Resolving source path derivations -/

/-- The semantic result of a source path-typing derivation under a
valuation. -/
structure PathCode.Resolution
    {n m : Nat} {k : Kind} (sigma : Store m)
    (rho : Valuation n m) (p : Path n) (d : Tau n k) : Type 1 where
  endpoint : Path.Endpoint m
  resolution : Path.Resolve (p.rename rho) sigma endpoint
  realizes : Path.Endpoint.Realizes sigma endpoint (d.rename rho)

/-- Resolve a typed source path and retain realization of its precise type. -/
noncomputable def PathCode.resolve
    {n m : Nat} {Gamma : Ctx n} {rho : Valuation n m}
    {sigma : Store m} {k : Kind} {p : Path n} {d : Tau n k}
    (environment : Environment Gamma rho sigma)
    (code : PathCode Gamma p d) :
    PathCode.Resolution sigma rho p d := by
  induction code with
  | @var x T binds =>
      refine ⟨.val (rho x), ?_, ?_⟩
      · exact .var
      · apply Path.Endpoint.Realizes.val
        simpa [binds.eq_lookup] using Environment.lookup environment _
  | fst receiver ih =>
      obtain ⟨endpoint, resolution, realizes⟩ := ih
      cases realizes with
      | val possible =>
          cases possible with
          | pair binding first member =>
              exact ⟨.val _, .fst resolution binding, .val first⟩
  | @sel_r receiverPath S a kind dependent receiver ih =>
      obtain ⟨endpoint, resolution, realizes⟩ := ih
      cases realizes with
      | val possible =>
          cases possible with
          | @pair _ _ _ y _ _ delta _ _
              binding first member =>
              have firstResolution :
                  Path.Resolve ((receiverPath.rename rho).fst)
                    sigma (.val y) :=
                .fst resolution binding
              have paths :
                  Path.RuntimeEq sigma (.var y)
                    ((receiverPath.rename rho).fst) :=
                .ofResolve .var firstResolution
              have converted := member.convert
                (Tau.RuntimeConv.replace (dependent.rename rho.ext) paths)
              have converted' :
                  Path.Endpoint.Realizes sigma delta.endpoint
                    ((dependent.open receiverPath.fst).rename rho) := by
                simpa [Tau.open_rename, Path.rename] using converted
              cases delta with
              | val z =>
                  exact ⟨.val z, .sel_val resolution binding, converted'⟩
              | «type» W =>
                  exact ⟨.type W, .sel_type resolution binding, converted'⟩
  | @sel_l receiverPath S b receiverKind dependent a memberKind d
      receiver member distinct ihReceiver ihMember =>
      obtain ⟨receiverEndpoint, receiverResolution, receiverRealizes⟩ :=
        ihReceiver
      obtain ⟨memberEndpoint, memberResolution, memberRealizes⟩ := ihMember
      cases receiverRealizes with
      | val possible =>
          cases possible with
          | @pair _ _ _ y _ _ delta _ _ binding first storedMember =>
              have firstResolution :
                  Path.Resolve ((receiverPath.rename rho).fst)
                    sigma (.val y) :=
                .fst receiverResolution binding
              have tailResolution := Path.Resolve.sel_congr
                memberResolution firstResolution Path.Resolve.var
              exact ⟨memberEndpoint,
                .sel_miss receiverResolution binding distinct tailResolution,
                memberRealizes⟩

/-! ## Eager compilation of source subtyping -/

/-- Compile source subtyping under a semantic environment to a finite
target-store coercion.  Function codomains are the sole deferred case. -/
noncomputable def SubCode.compile
    {n m : Nat} {Gamma : Ctx n} {rho : Valuation n m}
    {sigma : Store m} {k : Kind} {d1 d2 : Tau n k}
    (environment : Environment Gamma rho sigma) :
    SubCode Gamma d1 d2 ->
      Coercion sigma (d1.rename rho) (d2.rename rho)
| .refl => .refl
| .trans first second =>
    .trans (first.compile environment) (second.compile environment)
| .bot => .bot
| .top => .top
| .widen path => by
    obtain ⟨endpoint, resolution, realizes⟩ := path.resolve environment
    cases realizes with
    | val possible =>
        exact .widen resolution possible
| .symm path => by
    obtain ⟨endpoint, resolution, realizes⟩ := path.resolve environment
    cases realizes with
    | val possible =>
        cases possible with
        | single targetResolution =>
            exact .alias resolution targetResolution
| .sel_hi path boundCode => by
    obtain ⟨endpoint, resolution, realizes⟩ := path.resolve environment
    cases realizes with
    | type lower upper =>
        exact .selHi resolution upper
| .sel_lo path boundCode => by
    obtain ⟨endpoint, resolution, realizes⟩ := path.resolve environment
    cases realizes with
    | type lower upper =>
        exact .selLo resolution lower
| .fun domain codomain =>
    .fun (domain.compile environment) (.source environment codomain)
| .pair_fst first =>
    .pairFst (first.compile environment)
| @SubCode.pair_single_member _ _ p P kind dependent dependent'
      label path underBinder opened => by
    obtain ⟨endpoint, resolution, realizes⟩ := path.resolve environment
    cases realizes with
    | val possible =>
        have openedCode := opened.compile environment
        have openedCode' :
            Coercion sigma
              ((dependent.rename rho.ext).open (p.rename rho))
              ((dependent'.rename rho.ext).open (p.rename rho)) := by
          simpa only [Tau.open_rename] using openedCode
        simpa [Tau.rename, Ty.rename, Path.rename, Tau.open_rename] using
          Coercion.pairMember resolution openedCode'
| .bounds lower upper nonempty =>
    .bounds (lower.compile environment) (upper.compile environment)
      (nonempty.compile environment)

/-! ## Coercion action -/

/-- Execute a finite coercion on generalized endpoint realization. -/
noncomputable def Coercion.action
    {m : Nat} {sigma : Store m} {k : Kind} {d1 d2 : Tau m k}
    {endpoint : Path.Endpoint m} :
    Coercion sigma d1 d2 ->
    Path.Endpoint.Realizes sigma endpoint d1 ->
    Path.Endpoint.Realizes sigma endpoint d2
| .refl, realizes => realizes
| .trans first second, realizes =>
    second.action (first.action realizes)
| .runtime conversion, realizes => realizes.convert conversion
| .bot, realizes => by
    cases realizes with
    | val possible => cases possible
| .top, realizes => by
    cases realizes with
    | val possible => exact .val .top
| .widen resolution target, realizes => by
    cases realizes with
    | val possible =>
        cases possible with
        | single sourceResolution =>
            cases sourceResolution.deterministic resolution
            exact .val target
| .alias targetResolution sourceResolution, realizes => by
    cases realizes with
    | val possible =>
        cases possible with
        | single resolution =>
            cases resolution.deterministic sourceResolution
            exact .val (.single targetResolution)
| .selLo resolution lower, realizes => by
    cases realizes with
    | val possible =>
        have witness := lower.action (.val possible)
        cases witness with
        | val possibleWitness =>
            exact .val (.selection resolution possibleWitness)
| .selHi resolution upper, realizes => by
    cases realizes with
    | val possible =>
        cases possible with
        | selection sourceResolution witness =>
            cases sourceResolution.deterministic resolution
            exact upper.action (.val witness)
| .fun domain codomain, realizes => by
    cases realizes with
    | val possible =>
        cases possible with
        | «fun» binding body input output =>
            exact .val (.fun binding body
              (.trans domain input)
              (.trans (.narrow domain output) codomain))
| .pairFst firstCode, realizes => by
    cases realizes with
    | val possible =>
        cases possible with
        | pair binding first member =>
            have mapped := firstCode.action (.val first)
            cases mapped with
            | val mappedFirst =>
                exact .val (.pair binding mappedFirst member)
| @Coercion.pairMember m sigma p x a k dependent dependent'
      pathResolution opened, realizes => by
    cases realizes with
    | val possible =>
        cases possible with
        | @pair _ _ _ y _ _ delta _ _ binding first member =>
            cases first with
            | single firstResolution =>
                cases firstResolution.deterministic pathResolution
                let paths : Path.RuntimeEq sigma (.var x) p :=
                  .ofResolve .var pathResolution
                have atPath := member.convert
                  (Tau.RuntimeConv.replace dependent paths)
                have mapped := opened.action atPath
                have atLocation := mapped.convert
                  (Tau.RuntimeConv.replace dependent' paths.symm)
                exact .val (.pair binding (.single firstResolution) atLocation)
| .bounds lower upper nonempty, realizes => by
    cases realizes with
    | type sourceLower sourceUpper =>
        exact .type (.trans lower sourceLower) (.trans sourceUpper upper)

/-- Proper-type specialization of coercion action. -/
noncomputable def Coercion.actionPossible
    (coercion : Coercion sigma (.ty S) (.ty T))
    (possible : Store.Possible sigma x S) :
    Store.Possible sigma x T := by
  have mapped := coercion.action (.val possible)
  cases mapped with
  | val result => exact result

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
| @DeferredCoercion.source n m Gamma rho sigma A B C
      environment code, argument => by
    have extended := Environment.snoc environment argument
    have compiled := SubCode.compile extended code
    simpa only [← Ty.rename_openAt_eq_open_var,
      Ty.rename_ext_openAt] using compiled

end
end LambdaPFC
