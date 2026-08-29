import FCsub.Context

/-!
# The single-member DOT convention in general FCsub telescopes

This module is intentionally a client of FCsub.  FCsub itself has no notion of
a DOT member, label, lower bound, or upper bound.  The bridge represents one
DOT member by one abstract type name followed by two directed constraints.  A
runtime payload is added separately, after the complete static telescope.
-/

namespace DotToFCsub.MemberEncoding

open FCsub

/-- The Milestone-3 member convention allocates one abstract type name. -/
abbrev names : Nat := 1

/-- The Milestone-3 member convention carries a lower and an upper constraint. -/
abbrev constraints : Nat := 2

/-- Static scope of one generated name and its two directed constraints. -/
abbrev Static (scope : Sig) : Sig := StaticScope scope names constraints

/-- Static member scope followed by its separate runtime payload. -/
abbrev Payload (scope : Sig) : Sig := PayloadScope scope names constraints

/-- The generated name while all names, but no constraints, are in scope. -/
def nameInTypes {scope : Sig} : BVar (TypeScope scope names) .type := .here

/-- The generated name in the complete static scope. -/
def staticName {scope : Sig} : BVar (Static scope) .type :=
  .there (.there .here)

/-- The lower-bound evidence in the complete static scope. -/
def staticLower {scope : Sig} :
    BVar (Static scope) (.evidence .inclusion) :=
  .there .here

/-- The upper-bound evidence in the complete static scope. -/
def staticUpper {scope : Sig} :
    BVar (Static scope) (.evidence .inclusion) :=
  .here

/-- The generated name after the runtime payload has also been opened. -/
def name {scope : Sig} : BVar (Payload scope) .type :=
  .there staticName

/-- The lower-bound evidence after the runtime payload has also been opened. -/
def lower {scope : Sig} :
    BVar (Payload scope) (.evidence .inclusion) :=
  .there staticLower

/-- The upper-bound evidence after the runtime payload has also been opened. -/
def upper {scope : Sig} :
    BVar (Payload scope) (.evidence .inclusion) :=
  .there staticUpper

/-- The separately bound runtime payload. -/
def payload {scope : Sig} : BVar (Payload scope) .term := .here

/-- Lift a renaming below this client-level static convention. -/
def liftStatic {source target : Sig} (rho : Rename source target) :
    Rename (Static source) (Static target) :=
  rho.liftStatic names constraints

/-- Lift a renaming below the static convention and its runtime payload. -/
def liftPayload {source target : Sig} (rho : Rename source target) :
    Rename (Payload source) (Payload target) :=
  rho.liftPayload names constraints

/-- Weaken an ambient FCsub scope below one complete opened member. -/
def weakenPayload {scope : Sig} : Rename scope (Payload scope) :=
  Rename.weakenPayload names constraints

/-- The names-first telescope chosen for a DOT interval `lower .. upper`. -/
def telescope {scope : Sig} (lowerBound upperBound : Ty scope) :
    Telescope scope names constraints :=
  let weakenNames := Rename.weakenTypes (scope := scope) names
  let alpha : Ty (TypeScope scope names) := .tvar nameInTypes
  .snoc
    (.snoc (.nil (names := names))
      (.inclusion (lowerBound.rename weakenNames) alpha))
    (.inclusion alpha (upperBound.rename weakenNames))

/-- The single simultaneous type witness expected by a member telescope. -/
def witnessArgs {scope : Sig} (witness : Ty scope) : TypeArgs scope names :=
  .snoc .nil witness

/-- Lower evidence precedes upper evidence in telescope order. -/
def evidenceArgs {scope : Sig} (lowerEvidence upperEvidence : LeCo scope) :
    LeArgs scope constraints :=
  .snoc (.snoc .nil lowerEvidence) upperEvidence

/-- A telescope map that preserves the one generated identity and supplies two
derived target constraints from the source static scope. -/
def morphism {scope : Sig}
    {sourceLower sourceUpper targetLower targetUpper : Ty scope}
    (lowerEvidence upperEvidence : LeCo (Static scope)) :
    TelMor scope names constraints names constraints :=
  .map (telescope sourceLower sourceUpper)
    (telescope targetLower targetUpper)
    (witnessArgs (.tvar staticName))
    (evidenceArgs lowerEvidence upperEvidence)

/-- Variance-correct member adaptation.  The first certificate proves
`targetLower <= sourceLower`; the second proves
`sourceUpper <= targetUpper`. -/
def varianceMorphism {scope : Sig}
    {sourceLower sourceUpper targetLower targetUpper : Ty scope}
    (lowerEvidence upperEvidence : LeCo scope) :
    TelMor scope names constraints names constraints :=
  let weaken := Rename.weakenStatic (scope := scope) names constraints
  morphism (sourceLower := sourceLower) (sourceUpper := sourceUpper)
    (targetLower := targetLower) (targetUpper := targetUpper)
    (.trans (lowerEvidence.rename weaken) (.var staticLower))
    (.trans (.var staticUpper) (upperEvidence.rename weaken))

/-- Existential member package with a unit runtime representation. -/
def existsType {scope : Sig} (lowerBound upperBound : Ty scope) : Ty scope :=
  .existsT (telescope lowerBound upperBound) .one

/-- A constrained member function is a static universal followed by its
ordinary runtime payload arrow. -/
def forallType {scope : Sig} (lowerBound upperBound : Ty scope)
    (result : Ty (Payload scope)) : Ty scope :=
  .forallT (telescope lowerBound upperBound) (.arr .one result)

/-- Package a unit representation behind the one-name/two-constraint view. -/
def pack {scope : Sig} (lowerBound upperBound witness : Ty scope)
    (lowerEvidence upperEvidence : LeCo scope) (representation : Tm scope) :
    Tm scope :=
  .pack (telescope lowerBound upperBound) .one (witnessArgs witness)
    (evidenceArgs lowerEvidence upperEvidence) representation

/-- Open exactly one member telescope and its separate runtime payload. -/
def «open» {scope : Sig} (lowerBound upperBound : Ty scope)
    (package : Tm scope) (body : Tm (Payload scope)) : Tm scope :=
  .open (telescope lowerBound upperBound) .one package body

/-- Abstract the static member telescope, then the runtime payload. -/
def lam {scope : Sig} (lowerBound upperBound : Ty scope)
    (body : Tm (Payload scope)) : Tm scope :=
  .slam (telescope lowerBound upperBound) (.lam .one body)

/-- Instantiate the static member telescope and then apply its runtime
payload argument. -/
def app {scope : Sig} (lowerBound upperBound : Ty scope)
    (function : Tm scope) (witness : Ty scope)
    (lowerEvidence upperEvidence : LeCo scope) (argument : Tm scope) :
    Tm scope :=
  .app
    (.sapp (telescope lowerBound upperBound) function (witnessArgs witness)
      (evidenceArgs lowerEvidence upperEvidence))
    argument

/-- Structural evidence between existential member packages. -/
def existsEvidence {scope : Sig}
    (adaptation : TelMor scope names constraints names constraints) :
    LeCo scope :=
  .existsT adaptation .one .one (.refl .one)

/-- Structural evidence between constrained member functions.  The supplied
telescope map is contravariant, from the target interface to the source
interface; the result certificate lives below the target telescope and its
runtime payload. -/
def forallEvidence {scope : Sig}
    (adaptation : TelMor scope names constraints names constraints)
    (sourceResult targetResult : Ty (Payload scope))
    (result : LeCo (Payload scope)) : LeCo scope :=
  .forallT adaptation (.arr .one sourceResult) (.arr .one targetResult)
    (.arr (.refl .one) result)

end DotToFCsub.MemberEncoding
