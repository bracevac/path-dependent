import LambdaPCCI.CaptureEvidence

namespace LambdaPCCI
namespace Cap

noncomputable section

def Relation.comp
    (first : Relation world C D) (second : Relation world D E) :
    Relation world C E := .trans first second

def TyCoercion.comp
    (first : TyCoercion world T U) (second : TyCoercion world U V) :
    TyCoercion world T V := .trans first second

/-- Every coercion between capturing types contains a subcapturing
derivation between their capture sets. -/
noncomputable def TyCoercion.captureRelation
    {n : Nat} {sigma : Store n} {world : World sigma}
    {T U : Ty n} (coercion : TyCoercion world T U) :
    Relation world T.captureSet U.captureSet :=
  match coercion with
  | .refl => .refl
  | .trans first second =>
      .trans first.captureRelation second.captureRelation
  | .runtime conversion => .runtime conversion.captureConversion
  | .capt captures _ => captures

structure CaptureSetView
    {n : Nat} {sigma : Store n} (world : World sigma)
    (x : Fin n) (C : CaptureSet n) : Type 1 where
  value : Tm n
  assignedCaptureSet : CaptureSet n
  lookup : Lookup world x value assignedCaptureSet
  captures : Relation world assignedCaptureSet C

def LocationEvidence.captureSetView
    (possible : LocationEvidence world x (.capt C S)) :
    CaptureSetView world x C := by
  cases possible with
  | top lookup captures => exact ⟨_, _, lookup, captures⟩
  | inter left _ => exact left.captureSetView
  | unionLeft possible => exact possible.captureSetView
  | unionRight possible => exact possible.captureSetView
  | «fun» lookup body input output captures =>
      exact ⟨_, _, lookup, captures⟩
  | pair lookup first member captures =>
      exact ⟨_, _, lookup, captures⟩
  | single lookup resolution captures => exact ⟨_, _, lookup, captures⟩
  | selection lookup resolution witness captures =>
      exact ⟨_, _, lookup, captures⟩

def LocationEvidence.toTop
    (possible : LocationEvidence world x (.capt C S)) :
    LocationEvidence world x (.capt C .Top) :=
  let view := possible.captureSetView
  .top view.lookup view.captures

/-- World lookup entails lookup in the underlying runtime store. -/
theorem Lookup.binds {n : Nat} {sigma : Store n}
    {world : World sigma} {x : Fin n} {v : Tm n} {Q : CaptureSet n}
    (evidence : Lookup world x v Q) : Store.Binds sigma x v := by
  induction evidence with
  | here => exact .here
  | there _ ih => exact .there ih

private def World.lookupCaptureSet {n : Nat} {sigma : Store n} :
    (world : World sigma) -> Fin n -> CaptureSet n
| .empty, x => Fin.elim0 x
| @World.val n sigma v vv Q world exact, x =>
    Fin.cases Q.weaken
      (fun y => (world.lookupCaptureSet y).weaken) x

private theorem Lookup.captureSet_eq {n : Nat} {sigma : Store n}
    {world : World sigma} {x : Fin n} {v : Tm n} {Q : CaptureSet n}
    (evidence : Lookup world x v Q) :
    world.lookupCaptureSet x = Q := by
  induction evidence with
  | here => rfl
  | there old ih =>
      simpa [World.lookupCaptureSet] using congrArg CaptureSet.weaken ih

/-- World lookup is deterministic at a location. -/
theorem Lookup.unique
    {n : Nat} {sigma : Store n} {world : World sigma} {x : Fin n}
    {v u : Tm n} {Q R : CaptureSet n}
    (first : Lookup world x v Q) (second : Lookup world x u R) :
    v = u /\ Q = R :=
  ⟨Store.Binds.unique first.binds second.binds,
    first.captureSet_eq.symm.trans second.captureSet_eq⟩

/-- Widen a location's capture set using a proved subcapturing edge. -/
noncomputable def LocationEvidence.widenCaptureSet
    (possible : LocationEvidence world x (.capt C S))
    (captures : Relation world C D) :
    LocationEvidence world x (.capt D S) := by
  cases possible with
  | top lookup old => exact .top lookup (old.comp captures)
  | inter left right =>
      exact .inter (left.widenCaptureSet captures)
        (right.widenCaptureSet captures)
  | unionLeft possible =>
      exact .unionLeft (possible.widenCaptureSet captures)
  | unionRight possible =>
      exact .unionRight (possible.widenCaptureSet captures)
  | «fun» lookup body input output old =>
      exact .fun lookup body input output (old.comp captures)
  | pair lookup first member old =>
      exact .pair lookup first member (old.comp captures)
  | single lookup resolution old =>
      exact .single lookup resolution (old.comp captures)
  | selection lookup resolution witness old =>
      exact .selection lookup resolution witness (old.comp captures)

/-- Replace a lookup witness at the same world location, preserving the
stored shape evidence and using the supplied capture-set bound. -/
noncomputable def LocationEvidence.replaceLookup
    (possible : LocationEvidence world x (.capt C S))
    (lookup : Lookup world x v Q)
    (captures : Relation world Q D) :
    LocationEvidence world x (.capt D S) := by
  cases possible with
  | top oldLookup old =>
      obtain ⟨rfl, rfl⟩ := oldLookup.unique lookup
      exact .top lookup captures
  | inter left right =>
      exact .inter (left.replaceLookup lookup captures)
        (right.replaceLookup lookup captures)
  | unionLeft possible =>
      exact .unionLeft (possible.replaceLookup lookup captures)
  | unionRight possible =>
      exact .unionRight (possible.replaceLookup lookup captures)
  | «fun» oldLookup body input output old =>
      obtain ⟨rfl, rfl⟩ := oldLookup.unique lookup
      exact .fun lookup body input output captures
  | pair oldLookup first member old =>
      obtain ⟨rfl, rfl⟩ := oldLookup.unique lookup
      exact .pair lookup first member captures
  | single oldLookup resolution old =>
      obtain ⟨rfl, rfl⟩ := oldLookup.unique lookup
      exact .single lookup resolution captures
  | selection oldLookup resolution witness old =>
      obtain ⟨rfl, rfl⟩ := oldLookup.unique lookup
      exact .selection lookup resolution witness captures

mutual

/-- Structural runtime conversion preserves capture-aware inhabitants. -/
noncomputable def LocationEvidence.convertCongruent
    {n : Nat} {sigma : Store n} {world : World sigma}
    {x : Fin n} {T U : Ty n} :
    LocationEvidence world x T ->
    Ty.RuntimeCongruent (Path.RuntimeEq sigma) T U ->
    LocationEvidence world x U
| .top lookup captures, .capt captureSetConversion .top =>
    .top lookup (captures.comp (.runtime captureSetConversion.toRuntimeConv))
| .inter left right,
    .capt captureSetConversion (.inter leftConversion rightConversion) =>
    .inter
      (LocationEvidence.convertCongruent left
        (.capt captureSetConversion leftConversion))
      (LocationEvidence.convertCongruent right
        (.capt captureSetConversion rightConversion))
| .unionLeft possible,
    .capt captureSetConversion (.union leftConversion rightConversion) =>
    .unionLeft
      (LocationEvidence.convertCongruent possible
        (.capt captureSetConversion leftConversion))
| .unionRight possible,
    .capt captureSetConversion (.union leftConversion rightConversion) =>
    .unionRight
      (LocationEvidence.convertCongruent possible
        (.capt captureSetConversion rightConversion))
| .fun lookup body input output captures,
    .capt captureSetConversion (.fun domain codomain) =>
    let operations := Path.RuntimeEq.eqCongruence sigma
    let backwards : TyCoercion world _ _ :=
      .runtime ((domain.symm operations).toRuntimeConv)
    .fun lookup body
      (.trans backwards input)
      (.trans (.narrow backwards output)
        (.runtime codomain.toRuntimeConv))
      (captures.comp (.runtime captureSetConversion.toRuntimeConv))
| @LocationEvidence.pair n k sigma world x y _ C a _ S d lookup
      first member captures,
    .capt captureSetConversion (.pair firstConversion memberConversion) =>
    let operations := Path.RuntimeEq.eqCongruence sigma
    let opened := memberConversion.toRuntimeConv.openSame operations (.var y)
    .pair lookup
      (LocationEvidence.convertCongruent first firstConversion)
      (Realizes.convertCongruent member
        (opened.runtimeCongruent operations))
      (captures.comp (.runtime captureSetConversion.toRuntimeConv))
| .single lookup resolution captures,
    .capt captureSetConversion (.single paths) =>
    .single lookup ((paths.resolve_iff _).mp resolution)
      (captures.comp (.runtime captureSetConversion.toRuntimeConv))
| .selection lookup resolution witness captures,
    .capt captureSetConversion (.selection paths) =>
    .selection lookup (((paths.sel _).resolve_iff _).mp resolution)
      witness (captures.comp (.runtime captureSetConversion.toRuntimeConv))

/-- Structural runtime conversion preserves capture-aware referent
realization. -/
noncomputable def Realizes.convertCongruent
    {n : Nat} {k : Kind} {sigma : Store n} {world : World sigma}
    {referent : Path.Referent n}
    {d e : Tau n k} :
    Realizes world referent d ->
    Tau.RuntimeCongruent (Path.RuntimeEq sigma) d e ->
    Realizes world referent e
| .loc possible, .term types =>
    .loc (LocationEvidence.convertCongruent possible types)
| .type lower upper, .type lowerConversion upperConversion =>
    let operations := Path.RuntimeEq.eqCongruence sigma
    .type
      (.trans (.runtime ((lowerConversion.symm operations).toRuntimeConv)) lower)
      (.trans upper (.runtime upperConversion.toRuntimeConv))
| .capture lower upper, .capture lowerConversion upperConversion =>
    let operations := Path.RuntimeEq.eqCongruence sigma
    .capture
      (.trans (.runtime ((lowerConversion.symm operations).toRuntimeConv)) lower)
      (.trans upper (.runtime upperConversion.toRuntimeConv))

end

noncomputable def LocationEvidence.convert
    {n : Nat} {sigma : Store n}
    {world : World sigma} {x : Fin n} {T U : Ty n}
    (possible : LocationEvidence world x T)
    (conversion : Ty.RuntimeConv (Path.RuntimeEq sigma) T U) :
    LocationEvidence world x U :=
  possible.convertCongruent
    (conversion.runtimeCongruent (Path.RuntimeEq.eqCongruence sigma))

noncomputable def Realizes.convert
    {n : Nat} {k : Kind} {sigma : Store n}
    {world : World sigma} {referent : Path.Referent n}
    {d e : Tau n k}
    (realizes : Realizes world referent d)
    (conversion : Tau.RuntimeConv (Path.RuntimeEq sigma) d e) :
    Realizes world referent e :=
  realizes.convertCongruent
    (conversion.runtimeCongruent (Path.RuntimeEq.eqCongruence sigma))

end
end Cap
end LambdaPCCI
