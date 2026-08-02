import LambdaPFC.Model

/-!
One-hop interpretation of an abstract type member.

A realized type member records its witness and directed evidence for both
bounds.  Selection exposes the witness internally; the two evidence terms
implement introduction at the lower bound and elimination at the upper bound.
The evidence language used here is still the structurally interpreted fragment
from `Evidence.lean`.
-/

namespace LambdaPFC

open LambdaP

/-- Regard a runtime valuation as a path substitution. -/
def Valuation.asPathSubst (rho : Valuation n m) : PathSubst n m :=
  fun x => .var (rho x)

/-- Instantiate a scoped type in the runtime location scope. -/
def instantiateTy (rho : Valuation n m) (T : Ty n) : Ty m :=
  T.subst rho.asPathSubst

/--
A package certificate for an abstract member `p.A : L..U`.  `Selected` uses
the recorded witness as the internal representation of the surface selection.
-/
structure MemberPackage {n m : Nat}
    (M : Model m) (rho : Valuation n m)
    (p : Path n) (A : Name) (L U : Ty n) where
  witness : Ty n
  resolves : Resolve M rho (p.sel A) (.type (instantiateTy rho witness))
  lower : Evidence (.map L witness)
  upper : Evidence (.map witness U)

/-- A value viewed at the abstract selection represented by a package. -/
structure Selected {n m : Nat} {M : Model m} {rho : Valuation n m}
    {p : Path n} {A : Name} {L U : Ty n}
    (P : MemberPackage M rho p A L U) where
  raw : Fin m
  realizesWitness : Possible M rho raw P.witness

/-- Introduce an abstractly selected value through its lower bound. -/
def MemberPackage.intro {n m : Nat} {M : Model m} {rho : Valuation n m}
    {p : Path n} {A : Name} {L U : Ty n}
    (P : MemberPackage M rho p A L U)
    (v : Typed M rho L) : Selected P :=
  ⟨v.raw, (P.lower.cast v).realizes⟩

/-- Eliminate an abstractly selected value through its upper bound. -/
def MemberPackage.elim {n m : Nat} {M : Model m} {rho : Valuation n m}
    {p : Path n} {A : Name} {L U : Ty n}
    (P : MemberPackage M rho p A L U)
    (v : Selected P) : Typed M rho U :=
  P.upper.cast ⟨v.raw, v.realizesWitness⟩

/-- Erasure of a selected value exposes its underlying runtime location. -/
def Selected.erase {n m : Nat} {M : Model m} {rho : Valuation n m}
    {p : Path n} {A : Name} {L U : Ty n}
    {P : MemberPackage M rho p A L U} (v : Selected P) : Fin m :=
  v.raw

@[simp] theorem MemberPackage.erase_intro
    {n m : Nat} {M : Model m} {rho : Valuation n m}
    {p : Path n} {A : Name} {L U : Ty n}
    (P : MemberPackage M rho p A L U) (v : Typed M rho L) :
    (P.intro v).erase = v.erase := rfl

@[simp] theorem MemberPackage.erase_elim
    {n m : Nat} {M : Model m} {rho : Valuation n m}
    {p : Path n} {A : Name} {L U : Ty n}
    (P : MemberPackage M rho p A L U) (v : Selected P) :
    (P.elim v).erase = v.erase := rfl

end LambdaPFC
