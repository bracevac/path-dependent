import LambdaPFC.Model

/-!
The first regression for unrestricted dependent-pair covariance.

The source member is the singleton of the pair's first component.  Its first
component type is `Top`, so the derivation is outside LambdaP's current
singleton-first special case.  Applying the evidence to an inhabited pair
changes the member classification to `Top` while preserving the runtime pair
and both observations.
-/

namespace LambdaPFC.PairProbe

open LambdaP LambdaPFC

def label : Name := 0

def dependentMember : Ty 1 :=
  .Single (.var 0)

def source : Ty 0 :=
  .Pair .Top label (.ty dependentMember)

def target : Ty 0 :=
  .Pair .Top label (.ty .Top)

/--
The binder assumption gives the general conversion
`Pair S (fun x => Single x) <: Pair Top (fun _ => S)`.
-/
def assumedCovariance (S : Ty n) (a : Name) :
    Evidence (.map
      (.Pair S a (.ty (.Single (.var 0))))
      (.Pair .Top a (.ty S.weaken))) :=
  .pair .top .bound

theorem assumed_covariance_action
    (S : Ty n) (a : Name) (M : Model m) (rho : Valuation n m) :
    forall x,
      Possible M rho x (.Pair S a (.ty (.Single (.var 0)))) ->
      Possible M rho x (.Pair .Top a (.ty S.weaken)) :=
  (assumedCovariance S a).action M rho

/--
The `bound` evidence consumes the first component's `Top` realization supplied
by the pair action and identifies the singleton member with that component.
-/
def covariance : Evidence (.map source target) :=
  .pair .refl .bound

def pairLocation : Fin 2 := 0
def componentLocation : Fin 2 := 1

def model : Model 2 := fun x =>
  if x = pairLocation then
    .pair componentLocation label (.val componentLocation)
  else
    .atom

def emptyValuation : Valuation 0 2 := fun x => Fin.elim0 x

/-- The concrete pair `(y, y)` realizes the dependent source type. -/
def sourceValue : Typed model emptyValuation source where
  raw := pairLocation
  realizes := by
    apply Possible.pair (y := componentLocation) (z := componentLocation)
    · simp [model, pairLocation]
    · exact .top
    · exact .single .var

/-- Evidence classifies the same runtime pair at the target type. -/
def targetValue : Typed model emptyValuation target :=
  covariance.cast sourceValue

theorem target_realized :
    Possible model emptyValuation pairLocation target :=
  by
    simpa [targetValue, Evidence.cast, sourceValue] using targetValue.realizes

theorem runtime_pair_preserved : targetValue.erase = sourceValue.erase := rfl

theorem first_projection_preserved :
    targetValue.first? = sourceValue.first? := rfl

theorem member_projection_preserved :
    targetValue.member? = sourceValue.member? := rfl

theorem source_derivation : Sub source target :=
  covariance.erase

end LambdaPFC.PairProbe
