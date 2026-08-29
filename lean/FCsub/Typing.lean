import FCsub.Context
import FCsub.Recursion

/-!
# Declarative typing for standalone FCsub

The judgments in this module inspect only explicit FCsub certificates and
annotations.  In particular, package witnesses and constraint evidence are
checked in the ambient context; the packaged constraints are not in scope
while their own evidence is checked.
-/

namespace FCsub

/-! ## Nonescape -/

namespace Ty

/-- Remove an ordinary term binder from a type.  The current type grammar has
no term-variable constructor, so failure is impossible, but retaining the
`Option` aligns this operation with the other nonescape checks. -/
def strengthenTerm {scope : Sig} (type : Ty (scope ▹ .term)) :
    Option (Ty scope) :=
  type.rename? PartialTypeRename.dropTerm

end Ty

/-! ## Values -/

/-- Annotated values.  Static abstractions obey a value restriction because
their wrapper erases: a non-value body must be thunked with an ordinary
lambda before it can be abstracted. -/
inductive Tm.IsValue : {scope : Sig} → Tm scope → Prop where
  | unit {scope : Sig} : IsValue (.unit : Tm scope)
  | lam {scope : Sig} {domain : Ty scope} {body : Tm (scope ▹ .term)} :
      IsValue (.lam domain body)
  | cast {scope : Sig} {term : Tm scope} {evidence : LeCo scope}
      (termValue : IsValue term) : IsValue (.cast term evidence)
  | pack {scope : Sig} {names constraints : Nat}
      {telescope : Telescope scope names constraints}
      {payloadType : Ty (StaticScope scope names constraints)}
      {witnesses : TypeArgs scope names} {evidence : LeArgs scope constraints}
      {payload : Tm scope} (payloadValue : IsValue payload) :
      IsValue (.pack telescope payloadType witnesses evidence payload)
  | slam {scope : Sig} {names constraints : Nat}
      {telescope : Telescope scope names constraints}
      {body : Tm (StaticScope scope names constraints)}
      (bodyValue : IsValue body) : IsValue (.slam telescope body)
  | foldRec {scope : Sig} {names : Nat}
      {bodies : RecBodies scope names names} {index : Fin names}
      {term : Tm scope} (termValue : IsValue term) :
      IsValue (.foldRec bodies index term)

/-! ## Instantiated telescope interfaces -/

namespace Ty

/-- Instantiate a type that is scoped after the simultaneous name block but
before any telescope evidence. -/
def instantiateNames {scope : Sig} {names : Nat}
    (type : Ty (TypeScope scope names))
    (arguments : TypeArgs scope names) : Ty scope :=
  type.subst (TySubst.ofArgs Rename.id arguments)

end Ty

/-! ## Certificate endpoints -/

namespace EqCo

inductive HasType : {scope : Sig} → Ctx scope → EqCo scope →
    Ty scope → Ty scope → Type where
  | var {scope : Sig} {context : Ctx scope}
      {index : BVar scope (.evidence .equality)} {left right : Ty scope}
      (binding : context.lookup index = Binding.equality left right) :
      HasType context (.var index) left right
  | refl {scope : Sig} {context : Ctx scope} (type : Ty scope) :
      HasType context (.refl type) type type
  | symm {scope : Sig} {context : Ctx scope} {evidence : EqCo scope}
      {left right : Ty scope}
      (typing : HasType context evidence left right) :
      HasType context (.symm evidence) right left
  | trans {scope : Sig} {context : Ctx scope} {first second : EqCo scope}
      {left middle right : Ty scope}
      (firstTyping : HasType context first left middle)
      (secondTyping : HasType context second middle right) :
      HasType context (.trans first second) left right
  | unfoldRec {scope : Sig} {context : Ctx scope} {names : Nat}
      {bodies : RecBodies scope names names} {index : Fin names}
      (guarded : bodies.headGuarded = true) :
      HasType context (.unfoldRec bodies index) (.recProj bodies index)
        (bodies.unfoldAt index)

end EqCo

mutual

/-- Structural endpoints of directed inclusion evidence. -/
inductive LeCo.HasType : {scope : Sig} → Ctx scope → LeCo scope →
    Ty scope → Ty scope → Type where
  | var {scope : Sig} {context : Ctx scope}
      {index : BVar scope (.evidence .inclusion)} {source target : Ty scope}
      (binding : context.lookup index = Binding.inclusion source target) :
      LeCo.HasType context (.var index) source target
  | refl {scope : Sig} {context : Ctx scope} (type : Ty scope) :
      LeCo.HasType context (.refl type) type type
  | trans {scope : Sig} {context : Ctx scope} {first second : LeCo scope}
      {source middle target : Ty scope}
      (firstTyping : LeCo.HasType context first source middle)
      (secondTyping : LeCo.HasType context second middle target) :
      LeCo.HasType context (.trans first second) source target
  | top {scope : Sig} {context : Ctx scope} (source : Ty scope) :
      LeCo.HasType context (.top source) source .top
  | bot {scope : Sig} {context : Ctx scope} (target : Ty scope) :
      LeCo.HasType context (.bot target) .bot target
  | eqToLe {scope : Sig} {context : Ctx scope} {evidence : EqCo scope}
      {source target : Ty scope}
      (typing : EqCo.HasType context evidence source target) :
      LeCo.HasType context (.eqToLe evidence) source target
  | arr {scope : Sig} {context : Ctx scope}
      {domain : LeCo scope} {codomain : LeCo (scope ▹ .term)}
      {sourceDomain targetDomain : Ty scope}
      {sourceCodomain targetCodomain : Ty (scope ▹ .term)}
      (domainTyping : LeCo.HasType context domain targetDomain sourceDomain)
      (codomainTyping : LeCo.HasType (context.extendTerm targetDomain) codomain
        sourceCodomain targetCodomain) :
      LeCo.HasType context (.arr domain codomain)
        (.arr sourceDomain sourceCodomain)
        (.arr targetDomain targetCodomain)
  | existsT {scope : Sig} {context : Ctx scope}
      {sourceNames sourceConstraints targetNames targetConstraints : Nat}
      {adaptation : TelMor scope sourceNames sourceConstraints
        targetNames targetConstraints}
      {sourceTelescope : Telescope scope sourceNames sourceConstraints}
      {targetTelescope : Telescope scope targetNames targetConstraints}
      {sourcePayload : Ty
        (StaticScope scope sourceNames sourceConstraints)}
      {targetPayload : Ty
        (StaticScope scope targetNames targetConstraints)}
      {payload : LeCo (StaticScope scope sourceNames sourceConstraints)}
      (adaptationTyping : TelMor.HasType context adaptation
        sourceTelescope targetTelescope)
      (payloadTyping : LeCo.HasType
        (context.extendTelescope sourceTelescope) payload sourcePayload
        (adaptation.pull targetPayload)) :
      LeCo.HasType context
        (.existsT adaptation sourcePayload targetPayload payload)
        (.existsT sourceTelescope sourcePayload)
        (.existsT targetTelescope targetPayload)
  | forallT {scope : Sig} {context : Ctx scope}
      {sourceNames sourceConstraints targetNames targetConstraints : Nat}
      {adaptation : TelMor scope targetNames targetConstraints
        sourceNames sourceConstraints}
      {sourceTelescope : Telescope scope sourceNames sourceConstraints}
      {targetTelescope : Telescope scope targetNames targetConstraints}
      {sourceBody : Ty
        (StaticScope scope sourceNames sourceConstraints)}
      {targetBody : Ty
        (StaticScope scope targetNames targetConstraints)}
      {body : LeCo (StaticScope scope targetNames targetConstraints)}
      (adaptationTyping : TelMor.HasType context adaptation
        targetTelescope sourceTelescope)
      (bodyTyping : LeCo.HasType (context.extendTelescope targetTelescope) body
        (adaptation.pull sourceBody) targetBody) :
      LeCo.HasType context
        (.forallT adaptation sourceBody targetBody body)
        (.forallT sourceTelescope sourceBody)
        (.forallT targetTelescope targetBody)

/-- Evidence arguments satisfy a telescope after simultaneous name
instantiation.  Notice that `context` is unchanged in the `snoc` premise:
constraints never become assumptions for their own certificates. -/
inductive LeArgs.HasType : {scope : Sig} → Ctx scope →
    {names constraints : Nat} → Telescope scope names constraints →
    TypeArgs scope names → LeArgs scope constraints → Type where
  | nil {scope : Sig} {context : Ctx scope} {names : Nat}
      {witnesses : TypeArgs scope names} :
      LeArgs.HasType context (.nil : Telescope scope names 0) witnesses .nil
  | snoc {scope : Sig} {context : Ctx scope} {names constraints : Nat}
      {initial : Telescope scope names constraints}
      {lower upper : Ty (TypeScope scope names)}
      {witnesses : TypeArgs scope names}
      {arguments : LeArgs scope constraints} {evidence : LeCo scope}
      (initialTyping : LeArgs.HasType context initial witnesses arguments)
      (evidenceTyping : LeCo.HasType context evidence
        (lower.instantiateNames witnesses) (upper.instantiateNames witnesses)) :
      LeArgs.HasType context (.snoc initial (.inclusion lower upper)) witnesses
        (.snoc arguments evidence)

/-- A morphism is checked as an interface map.  `map` checks target
constraints under the opened source interface.  Transitivity merely matches
the intermediate telescope; it does not synthesize new evidence. -/
inductive TelMor.HasType : {scope : Sig} → Ctx scope →
    {sourceNames sourceConstraints targetNames targetConstraints : Nat} →
    TelMor scope sourceNames sourceConstraints targetNames targetConstraints →
    Telescope scope sourceNames sourceConstraints →
    Telescope scope targetNames targetConstraints → Type where
  | refl {scope : Sig} {context : Ctx scope} {names constraints : Nat}
      (telescope : Telescope scope names constraints) :
      TelMor.HasType context (.refl telescope) telescope telescope
  | map {scope : Sig} {context : Ctx scope}
      {sourceNames sourceConstraints targetNames targetConstraints : Nat}
      {source : Telescope scope sourceNames sourceConstraints}
      {target : Telescope scope targetNames targetConstraints}
      {names : TypeArgs (StaticScope scope sourceNames sourceConstraints)
        targetNames}
      {evidence : LeArgs (StaticScope scope sourceNames sourceConstraints)
        targetConstraints}
      (argumentsTyping : LeArgs.HasType
        (context.extendTelescope source)
        (target.rename (Rename.weakenStatic sourceNames sourceConstraints))
        names evidence) :
      TelMor.HasType context (.map source target names evidence) source target
  | trans {scope : Sig} {context : Ctx scope}
      {firstNames firstConstraints middleNames middleConstraints
        lastNames lastConstraints : Nat}
      {first : TelMor scope firstNames firstConstraints
        middleNames middleConstraints}
      {second : TelMor scope middleNames middleConstraints
        lastNames lastConstraints}
      {source : Telescope scope firstNames firstConstraints}
      {middle : Telescope scope middleNames middleConstraints}
      {target : Telescope scope lastNames lastConstraints}
      (firstTyping : TelMor.HasType context first source middle)
      (secondTyping : TelMor.HasType context second middle target) :
      TelMor.HasType context (.trans first second) source target

end

/-! ## Syntax-directed term typing -/

namespace Tm

inductive HasType : {scope : Sig} → Ctx scope → Tm scope →
    Ty scope → Type where
  | unit {scope : Sig} {context : Ctx scope} :
      HasType context .unit .one
  | var {scope : Sig} {context : Ctx scope}
      {index : BVar scope .term} {type : Ty scope}
      (binding : context.lookup index = Binding.term type) :
      HasType context (.var index) type
  | lam {scope : Sig} {context : Ctx scope} {domain : Ty scope}
      {body : Tm (scope ▹ .term)} {codomain : Ty (scope ▹ .term)}
      (bodyTyping : HasType (context.extendTerm domain) body codomain) :
      HasType context (.lam domain body) (.arr domain codomain)
  | app {scope : Sig} {context : Ctx scope} {function argument : Tm scope}
      {domain : Ty scope} {codomain : Ty (scope ▹ .term)}
      {result : Ty scope}
      (functionTyping : HasType context function (.arr domain codomain))
      (argumentTyping : HasType context argument domain)
      (nonescape : codomain.strengthenTerm = some result) :
      HasType context (.app function argument) result
  | let' {scope : Sig} {context : Ctx scope} {rhs : Tm scope}
      {body : Tm (scope ▹ .term)} {bound : Ty scope}
      {bodyType : Ty (scope ▹ .term)} {result : Ty scope}
      (rhsTyping : HasType context rhs bound)
      (bodyTyping : HasType (context.extendTerm bound) body bodyType)
      (nonescape : bodyType.strengthenTerm = some result) :
      HasType context (.let' rhs body) result
  | cast {scope : Sig} {context : Ctx scope} {term : Tm scope}
      {evidence : LeCo scope} {source target : Ty scope}
      (termTyping : HasType context term source)
      (evidenceTyping : LeCo.HasType context evidence source target) :
      HasType context (.cast term evidence) target
  | pack {scope : Sig} {context : Ctx scope} {names constraints : Nat}
      {telescope : Telescope scope names constraints}
      {payloadType : Ty (StaticScope scope names constraints)}
      {witnesses : TypeArgs scope names} {evidence : LeArgs scope constraints}
      {payload : Tm scope}
      (argumentsTyping : LeArgs.HasType context telescope witnesses evidence)
      (payloadTyping : HasType context payload
        (payloadType.instantiateStatic witnesses)) :
      HasType context
        (.pack telescope payloadType witnesses evidence payload)
        (.existsT telescope payloadType)
  | openT {scope : Sig} {context : Ctx scope} {names constraints : Nat}
      {telescope : Telescope scope names constraints}
      {payloadType : Ty (StaticScope scope names constraints)}
      {package : Tm scope}
      {body : Tm (PayloadScope scope names constraints)}
      {bodyType : Ty (PayloadScope scope names constraints)}
      {result : Ty scope}
      (packageTyping : HasType context package
        (.existsT telescope payloadType))
      (bodyTyping : HasType (context.extendPayload telescope payloadType)
        body bodyType)
      (nonescape : bodyType.strengthenPayload = some result) :
      HasType context (.open telescope payloadType package body) result
  | slam {scope : Sig} {context : Ctx scope} {names constraints : Nat}
      {telescope : Telescope scope names constraints}
      {body : Tm (StaticScope scope names constraints)}
      {bodyType : Ty (StaticScope scope names constraints)}
      (bodyValue : IsValue body)
      (bodyTyping : HasType (context.extendTelescope telescope) body bodyType) :
      HasType context (.slam telescope body) (.forallT telescope bodyType)
  | sapp {scope : Sig} {context : Ctx scope} {names constraints : Nat}
      {telescope : Telescope scope names constraints}
      {function : Tm scope} {witnesses : TypeArgs scope names}
      {evidence : LeArgs scope constraints}
      {bodyType : Ty (StaticScope scope names constraints)}
      (functionTyping : HasType context function (.forallT telescope bodyType))
      (argumentsTyping : LeArgs.HasType context telescope witnesses evidence) :
      HasType context (.sapp telescope function witnesses evidence)
        (bodyType.instantiateStatic witnesses)
  | newtype {scope : Sig} {context : Ctx scope} {witness : Ty scope}
      {body : Tm (NewtypeScope scope)} {bodyType : Ty (NewtypeScope scope)}
      {result : Ty scope}
      (bodyTyping : HasType (context.extendNewtype witness) body bodyType)
      (nonescape : bodyType.strengthenNewtype = some result) :
      HasType context (.newtype witness body) result
  | foldRec {scope : Sig} {context : Ctx scope} {names : Nat}
      {bodies : RecBodies scope names names} {index : Fin names}
      {term : Tm scope}
      (guarded : bodies.headGuarded = true)
      (termTyping : HasType context term (bodies.unfoldAt index)) :
      HasType context (.foldRec bodies index term) (.recProj bodies index)
  | unfoldRec {scope : Sig} {context : Ctx scope} {names : Nat}
      {bodies : RecBodies scope names names} {index : Fin names}
      {term : Tm scope}
      (guarded : bodies.headGuarded = true)
      (termTyping : HasType context term (.recProj bodies index)) :
      HasType context (.unfoldRec bodies index term) (bodies.unfoldAt index)

end Tm

/-! ## No-self-discharge shape -/

/-- Inversion for package formation.  The result deliberately mentions the
ambient `context`, not `context.extendTelescope telescope`. -/
theorem Tm.HasType.pack_arguments_outer {scope : Sig} {context : Ctx scope}
    {names constraints : Nat}
    {telescope : Telescope scope names constraints}
    {payloadType : Ty (StaticScope scope names constraints)}
    {witnesses : TypeArgs scope names} {evidence : LeArgs scope constraints}
    {payload : Tm scope} {type : Ty scope}
    (typing : Tm.HasType context
      (.pack telescope payloadType witnesses evidence payload) type) :
    Nonempty (LeArgs.HasType context telescope witnesses evidence) := by
  cases typing with
  | pack argumentsTyping _ => exact ⟨argumentsTyping⟩

end FCsub
