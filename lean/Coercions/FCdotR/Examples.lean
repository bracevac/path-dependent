import Coercions.FCdotR.Typing
import Coercions.Oopsla16.Examples

/-!
# The recursive-subtyping example, as target evidence

`Oopsla16.Examples.FunctionField` derives

```text
S(z) = {A : ⊥ .. z.B} ∧ ({B : ⊥ .. ⊤} ∧ {f : ∀(_ : ⊤) z.A})
T(z) =                                   {f : ∀(_ : ⊤) z.B}
μ z. S(z)  <:  μ z. T(z)
```

in the reference calculus.  Here the same statement is a closed evidence term.
Two steps carry it: `selL`, whose subject may be the self of an enclosing
`bindx` because observation evidence is scoped at that subject's prefix, and
`bindx` itself, whose hypothesis is the opened body.
-/

namespace FCdotR.Examples

open FCdot (Kind Sig BVar Rename)
open Oopsla16 (Vr Ty Ctx Store)
open Oopsla16.Examples.FunctionField (A B f Sbody Tbody)

/-- The empty store has no locations, so its literal typing is the empty
function. -/
def W0 : StoreTy [] := fun l => nomatch l

/-- The self of the `bindx`, seen from under the method's parameter. -/
abbrev z' : Vr [] ([],x,x) := .abs (.there .here)

/-! The three conjuncts of `S(z)`, named so that the projections can say which
one they keep. -/

/-- `{A : ⊥ .. z.B}`. -/
abbrev aDecl : Ty [] ([],x) := .TTyp A .TBot (.TSel (.abs .here) B)
/-- `{B : ⊥ .. ⊤}`. -/
abbrev bDecl : Ty [] ([],x) := .TTyp B .TBot .TTop
/-- `{f : ∀(_ : ⊤) z.A}`. -/
abbrev fDecl : Ty [] ([],x) := .TFun f .TTop (.TSel z' A)

example : Sbody = .TAnd aDecl (.TAnd bDecl fDecl) := rfl
example : Tbody = .TFun f .TTop (.TSel z' B) := rfl

/-- `S(z) ≤ {A : ⊥ .. z.B}`, in the prefix at the self.  `Oopsla16`'s
`sBound`. -/
def sBound : Le [] ([],x) :=
  .andE1 (.TAnd bDecl fDecl) (.dtyp A (.bot .TBot) (.refl (.TSel (.abs .here) B)))

def sBound_typed :
    LeTy (σ := []) .nil W0 (Ctx.nil.cons Sbody) sBound Sbody aDecl :=
  .andE1 (.TAnd bDecl fDecl) (.dtyp (.bot .TBot) (.refl (.TSel (.abs .here) B)))

/-- The self's `A` member, observed from under the parameter.  The subject is
one binder further out, and its prefix — hence the context the inclusion is
checked in — is unchanged by the parameter.  `Oopsla16`'s `selMember`. -/
abbrev aMember : Vc [] (scopeAt z') := .vcSub Sbody sBound .vcVar

def aMember_typed :
    VcTy (σ := []) .nil W0 ((Ctx.nil.cons Sbody).cons .TTop) z' aMember aDecl :=
  VcTy.vcSub (p := z') (Γ := (Ctx.nil.cons Sbody).cons .TTop) Sbody
    (VcTy.vcVar (x := .there .here)) sBound_typed

/-- `z.A ≤ z.B`, under the parameter.  `Oopsla16`'s `selUnder`. -/
def selUnder : Le [] ([],x,x) := .selL z' A aMember

def selUnder_typed :
    LeTy (σ := []) .nil W0 ((Ctx.nil.cons Sbody).cons .TTop) selUnder
      (.TSel z' A) (.TSel z' B) :=
  .selL aMember_typed

/-- `{f : ∀(_ : ⊤) z.A} ≤ {f : ∀(_ : ⊤) z.B}`. -/
def methodCovariant : Le [] ([],x) := .dfun f (.top .TTop) selUnder

def methodCovariant_typed :
    LeTy (σ := []) .nil W0 (Ctx.nil.cons Sbody) methodCovariant fDecl Tbody :=
  .dfun (.top .TTop) selUnder_typed

/-- The `bindx` premise, `S(z) ≤ T(z)`. -/
def premise : Le [] ([],x) := .andE2 aDecl (.andE2 bDecl methodCovariant)

def premise_typed :
    LeTy (σ := []) .nil W0 (Ctx.nil.cons Sbody) premise Sbody Tbody :=
  .andE2 aDecl (.andE2 bDecl methodCovariant_typed)

/-- `μ z. S(z) ≤ μ z. T(z)`, as a closed evidence term over the empty store. -/
def recursive : Le [] [] := .bindx Sbody Tbody premise

def recursive_typed :
    LeTy (σ := []) (s := []) .nil W0 .nil recursive (.TBind Sbody) (.TBind Tbody) :=
  .bindx Sbody Tbody premise_typed

/-- The evidence is closed: it mentions no hypothesis of an ambient context. -/
example : Le [] [] := recursive

end FCdotR.Examples
