import Coercions.FCsub.Substitution
import Coercions.FCsub.Typing

/-!
# Annotated call-by-value dynamics for FCsub

Static constructs either stutter or expose ordinary call-by-value work after
erasure.  Packages evaluate their payloads, static abstractions retain the
typing-layer value restriction, and casts are pushed only by eliminators.
This prevents a static wrapper from becoming an accidental runtime thunk.
-/

namespace FCsub

namespace EqCo

/-- Irreducible equality assumptions.  Closed programs have no inhabitants
of either constructor; they are retained so the open operational semantics
remains well scoped. -/
inductive IsAtom : {scope : Sig} → EqCo scope → Prop where
  | var {scope : Sig} (index : BVar scope (.evidence .equality)) :
      IsAtom (.var index)
  | symmVar {scope : Sig} (index : BVar scope (.evidence .equality)) :
      IsAtom (.symm (.var index))

end EqCo

namespace LeCo

/-- A cast head that cannot take an administrative step by itself.  Arrow,
existential, and universal heads are values until the matching eliminator
pushes them. -/
inductive IsInert : {scope : Sig} → LeCo scope → Prop where
  | var {scope : Sig} (index : BVar scope (.evidence .inclusion)) :
      IsInert (.var index)
  | top {scope : Sig} (source : Ty scope) : IsInert (.top source)
  | bot {scope : Sig} (target : Ty scope) : IsInert (.bot target)
  | equality {scope : Sig} {evidence : EqCo scope}
      (atom : evidence.IsAtom) : IsInert (.eqToLe evidence)
  | arr {scope : Sig} (domain : LeCo scope)
      (codomain : LeCo (scope ▹ .term)) : IsInert (.arr domain codomain)
  | existsT {scope : Sig}
      {sourceNames sourceConstraints targetNames targetConstraints : Nat}
      (adaptation : TelMor scope sourceNames sourceConstraints
        targetNames targetConstraints)
      (sourcePayload : Ty
        (StaticScope scope sourceNames sourceConstraints))
      (targetPayload : Ty
        (StaticScope scope targetNames targetConstraints))
      (payload : LeCo (StaticScope scope sourceNames sourceConstraints)) :
      IsInert (.existsT adaptation sourcePayload targetPayload payload)
  | forallT {scope : Sig}
      {sourceNames sourceConstraints targetNames targetConstraints : Nat}
      (adaptation : TelMor scope targetNames targetConstraints
        sourceNames sourceConstraints)
      (sourceBody : Ty (StaticScope scope sourceNames sourceConstraints))
      (targetBody : Ty (StaticScope scope targetNames targetConstraints))
      (body : LeCo (StaticScope scope targetNames targetConstraints)) :
      IsInert (.forallT adaptation sourceBody targetBody body)

end LeCo

namespace Tm

/-- Operational values.  This is deliberately more precise than the
typing-layer value-restriction predicate: reflexive and composite casts take
administrative steps, while structured casts wait for an eliminator. -/
inductive IsRuntimeValue : {scope : Sig} → Tm scope → Prop where
  | unit {scope : Sig} : IsRuntimeValue (.unit : Tm scope)
  | lam {scope : Sig} {domain : Ty scope} {body : Tm (scope ▹ .term)} :
      IsRuntimeValue (.lam domain body)
  | cast {scope : Sig} {term : Tm scope} {evidence : LeCo scope}
      (termValue : IsRuntimeValue term) (inert : evidence.IsInert) :
      IsRuntimeValue (.cast term evidence)
  | pack {scope : Sig} {names constraints : Nat}
      {telescope : Telescope scope names constraints}
      {payloadType : Ty (StaticScope scope names constraints)}
      {witnesses : TypeArgs scope names} {evidence : LeArgs scope constraints}
      {payload : Tm scope} (payloadValue : IsRuntimeValue payload) :
      IsRuntimeValue
        (.pack telescope payloadType witnesses evidence payload)
  | slam {scope : Sig} {names constraints : Nat}
      {telescope : Telescope scope names constraints}
      {body : Tm (StaticScope scope names constraints)}
      (bodyValue : Tm.IsValue body) :
      IsRuntimeValue (.slam telescope body)
  | foldRec {scope : Sig} {names : Nat}
      {bodies : RecBodies scope names names} {index : Fin names}
      {term : Tm scope} (termValue : IsRuntimeValue term) :
      IsRuntimeValue (.foldRec bodies index term)

/-- Deterministic, left-to-right annotated reduction.  Proof-only cast
normalization and static beta steps stutter under erasure. -/
inductive Step : {scope : Sig} → Tm scope → Tm scope → Prop where
  | appFunction {scope : Sig} {function function' argument : Tm scope}
      (step : Step function function') :
      Step (.app function argument) (.app function' argument)
  | appArgument {scope : Sig} {function argument argument' : Tm scope}
      (functionValue : IsRuntimeValue function)
      (step : Step argument argument') :
      Step (.app function argument) (.app function argument')
  | beta {scope : Sig} {domain : Ty scope} {body : Tm (scope ▹ .term)}
      {argument : Tm scope} (argumentValue : IsRuntimeValue argument) :
      Step (.app (.lam domain body) argument)
        (body.instantiateTerm argument)
  | appCastArrow {scope : Sig} {function argument : Tm scope}
      {domain : LeCo scope} {codomain : LeCo (scope ▹ .term)}
      (functionValue : IsRuntimeValue function)
      (argumentValue : IsRuntimeValue argument) :
      Step (.app (.cast function (.arr domain codomain)) argument)
        (.cast (.app function (.cast argument domain))
          (codomain.substitute
            (Subst.id.instantiateTerm argument)))
  | letRhs {scope : Sig} {rhs rhs' : Tm scope}
      {body : Tm (scope ▹ .term)} (step : Step rhs rhs') :
      Step (.let' rhs body) (.let' rhs' body)
  | zeta {scope : Sig} {rhs : Tm scope} {body : Tm (scope ▹ .term)}
      (rhsValue : IsRuntimeValue rhs) :
      Step (.let' rhs body) (body.instantiateTerm rhs)
  | castInner {scope : Sig} {term term' : Tm scope}
      {evidence : LeCo scope} (step : Step term term') :
      Step (.cast term evidence) (.cast term' evidence)
  | castRefl {scope : Sig} {term : Tm scope} {type : Ty scope}
      (termValue : IsRuntimeValue term) :
      Step (.cast term (.refl type)) term
  | castTrans {scope : Sig} {term : Tm scope} {first second : LeCo scope}
      (termValue : IsRuntimeValue term) :
      Step (.cast term (.trans first second))
        (.cast (.cast term first) second)
  | castEqRefl {scope : Sig} {term : Tm scope} {type : Ty scope}
      (termValue : IsRuntimeValue term) :
      Step (.cast term (.eqToLe (.refl type))) term
  | castEqSymmRefl {scope : Sig} {term : Tm scope} {type : Ty scope}
      (termValue : IsRuntimeValue term) :
      Step (.cast term (.eqToLe (.symm (.refl type)))) term
  | castEqSymmSymm {scope : Sig} {term : Tm scope} {evidence : EqCo scope}
      (termValue : IsRuntimeValue term) :
      Step (.cast term (.eqToLe (.symm (.symm evidence))))
        (.cast term (.eqToLe evidence))
  | castEqSymmTrans {scope : Sig} {term : Tm scope}
      {first second : EqCo scope} (termValue : IsRuntimeValue term) :
      Step (.cast term (.eqToLe (.symm (.trans first second))))
        (.cast term
          (.trans (.eqToLe (.symm second)) (.eqToLe (.symm first))))
  | castEqTrans {scope : Sig} {term : Tm scope}
      {first second : EqCo scope} (termValue : IsRuntimeValue term) :
      Step (.cast term (.eqToLe (.trans first second)))
        (.cast term (.trans (.eqToLe first) (.eqToLe second)))
  | castEqUnfoldRec {scope : Sig} {names : Nat}
      {bodies : RecBodies scope names names} {index : Fin names}
      {term : Tm scope} (termValue : IsRuntimeValue term) :
      Step (.cast term (.eqToLe (.unfoldRec bodies index)))
        (.unfoldRec bodies index term)
  | castEqSymmUnfoldRec {scope : Sig} {names : Nat}
      {bodies : RecBodies scope names names} {index : Fin names}
      {term : Tm scope} (termValue : IsRuntimeValue term) :
      Step (.cast term (.eqToLe (.symm (.unfoldRec bodies index))))
        (.foldRec bodies index term)
  | packPayload {scope : Sig} {names constraints : Nat}
      {telescope : Telescope scope names constraints}
      {payloadType : Ty (StaticScope scope names constraints)}
      {witnesses : TypeArgs scope names} {evidence : LeArgs scope constraints}
      {payload payload' : Tm scope} (step : Step payload payload') :
      Step (.pack telescope payloadType witnesses evidence payload)
        (.pack telescope payloadType witnesses evidence payload')
  | openScrutinee {scope : Sig} {names constraints : Nat}
      {telescope : Telescope scope names constraints}
      {payloadType : Ty (StaticScope scope names constraints)}
      {scrutinee scrutinee' : Tm scope}
      {body : Tm (PayloadScope scope names constraints)}
      (step : Step scrutinee scrutinee') :
      Step (.open telescope payloadType scrutinee body)
        (.open telescope payloadType scrutinee' body)
  | openPack {scope : Sig} {names constraints : Nat}
      {telescope : Telescope scope names constraints}
      {payloadType : Ty (StaticScope scope names constraints)}
      {witnesses : TypeArgs scope names} {evidence : LeArgs scope constraints}
      {payload : Tm scope} {body : Tm (PayloadScope scope names constraints)}
      (payloadValue : IsRuntimeValue payload) :
      Step
        (.open telescope payloadType
          (.pack telescope payloadType witnesses evidence payload) body)
        (body.instantiatePayload witnesses evidence payload)
  | openCastExists {scope : Sig}
      {sourceNames sourceConstraints targetNames targetConstraints : Nat}
      {adaptation : TelMor scope sourceNames sourceConstraints
        targetNames targetConstraints}
      {sourcePayload : Ty
        (StaticScope scope sourceNames sourceConstraints)}
      {targetPayload : Ty
        (StaticScope scope targetNames targetConstraints)}
      {targetTelescope : Telescope scope targetNames targetConstraints}
      {payloadEvidence : LeCo
        (StaticScope scope sourceNames sourceConstraints)}
      {package : Tm scope}
      {body : Tm (PayloadScope scope targetNames targetConstraints)}
      (packageValue : IsRuntimeValue package) :
      Step
        (.open targetTelescope targetPayload
          (.cast package
            (.existsT adaptation sourcePayload targetPayload payloadEvidence))
          body)
        (.open adaptation.sourceTelescope sourcePayload package
          (body.substitute
            (adaptation.payloadSubstitution payloadEvidence)))
  | sappFunction {scope : Sig} {names constraints : Nat}
      {telescope : Telescope scope names constraints}
      {function function' : Tm scope} {witnesses : TypeArgs scope names}
      {evidence : LeArgs scope constraints} (step : Step function function') :
      Step (.sapp telescope function witnesses evidence)
        (.sapp telescope function' witnesses evidence)
  | sappSlam {scope : Sig} {names constraints : Nat}
      {telescope : Telescope scope names constraints}
      {body : Tm (StaticScope scope names constraints)}
      {witnesses : TypeArgs scope names} {evidence : LeArgs scope constraints}
      (bodyValue : Tm.IsValue body) :
      Step (.sapp telescope (.slam telescope body) witnesses evidence)
        (body.instantiateStatic witnesses evidence)
  | sappCastForall {scope : Sig}
      {sourceNames sourceConstraints targetNames targetConstraints : Nat}
      {adaptation : TelMor scope targetNames targetConstraints
        sourceNames sourceConstraints}
      {sourceBody : Ty (StaticScope scope sourceNames sourceConstraints)}
      {targetBody : Ty (StaticScope scope targetNames targetConstraints)}
      {targetTelescope : Telescope scope targetNames targetConstraints}
      {bodyEvidence : LeCo
        (StaticScope scope targetNames targetConstraints)}
      {function : Tm scope} {witnesses : TypeArgs scope targetNames}
      {evidence : LeArgs scope targetConstraints}
      (functionValue : IsRuntimeValue function) :
      Step
        (.sapp targetTelescope
          (.cast function
            (.forallT adaptation sourceBody targetBody bodyEvidence))
          witnesses evidence)
        (.cast
          (.sapp adaptation.targetTelescope function
            (adaptation.apply ⟨witnesses, evidence⟩).types
            (adaptation.apply ⟨witnesses, evidence⟩).evidence)
          (bodyEvidence.instantiateStatic witnesses evidence))
  | newtype {scope : Sig} {witness : Ty scope}
      {body : Tm (NewtypeScope scope)} :
      Step (.newtype witness body) (body.instantiateNewtype witness)
  | foldRecInner {scope : Sig} {names : Nat}
      {bodies : RecBodies scope names names} {index : Fin names}
      {term term' : Tm scope} (step : Step term term') :
      Step (.foldRec bodies index term) (.foldRec bodies index term')
  | unfoldRecInner {scope : Sig} {names : Nat}
      {bodies : RecBodies scope names names} {index : Fin names}
      {term term' : Tm scope} (step : Step term term') :
      Step (.unfoldRec bodies index term) (.unfoldRec bodies index term')
  | unfoldFold {scope : Sig} {names : Nat}
      {bodies : RecBodies scope names names} {index : Fin names}
      {term : Tm scope} (termValue : IsRuntimeValue term) :
      Step (.unfoldRec bodies index (.foldRec bodies index term)) term

/-- Reflexive-transitive closure of annotated reduction. -/
inductive Steps : {scope : Sig} → Tm scope → Tm scope → Prop where
  | refl {scope : Sig} {term : Tm scope} : Steps term term
  | tail {scope : Sig} {first second third : Tm scope}
      (steps : Steps first second) (step : Step second third) :
      Steps first third

namespace Steps

def single {scope : Sig} {first second : Tm scope}
    (step : Step first second) : Steps first second :=
  .tail .refl step

def trans {scope : Sig} {first second third : Tm scope}
    (firstSteps : Steps first second) (secondSteps : Steps second third) :
    Steps first third := by
  induction secondSteps with
  | refl => exact firstSteps
  | tail previous final induction => exact .tail induction final

end Steps

end Tm

end FCsub
