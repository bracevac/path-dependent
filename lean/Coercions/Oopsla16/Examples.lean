import Coercions.Oopsla16.Typing

/-!
# Examples

Sanity checks that the rules compose, and the recursive-subtyping example the
rest of this development needs.

`ex0` is `dot_exs.v:173-177`.  The reference's remaining examples (`ex1`,
`ex2`, `paper_lst`) are not ported here; `ex1` and `ex2` exercise the
polymorphic identity method, and `paper_lst` is the OOPSLA'16 §2 list module.
All three are written as `Oopsla16` derivations in
`FCdotR/CheckerExamples.lean` (namespaces `FCdotR.CheckerExamples.DotExs` and
`FCdotR.CheckerExamples.PaperLst`), which elaborates and checks them; this
library's constants are kept fixed.

`FunctionField` is not in `dot_exs.v`.  It is modelled on the premise
`z : S(z) ⊢ S(z) <: T(z)` of the function-field example of the WadlerFest line.
Here the premise is an ordinary `stp_bindx` derivation, with a method in place
of the WadlerFest field of function type.
-/

namespace Oopsla16.Examples

open FCdot (Kind Sig BVar Rename)

/-! ## The empty object -/

/-- `ex0`, `dot_exs.v:173-177`: `{ z => } : ⊤`.  Even the empty object needs
subsumption, because `T_Obj` always concludes at a `TBind`. -/
def ex0 : HasType (σ := []) (s := []) .nil .nil (.tobj .dnil) .TTop :=
  .T_Sub (.T_Obj .D_Nil) .stp_top

/-- The same object at its precise type. -/
def ex0_precise :
    HasType (σ := []) (s := []) .nil .nil (.tobj .dnil) (.TBind .TTop) :=
  .T_Obj .D_Nil

/-! ## Recursive subtyping through a self-dependent method

```text
S(z) = {A : ⊥ .. z.B} ∧ ({B : ⊥ .. ⊤} ∧ {f : ∀(_ : ⊤) z.A})
T(z) =                                   {f : ∀(_ : ⊤) z.B}
```

The conclusion `μ z. S(z) <: μ z. T(z)` needs `stp_bindx`: the method's result
type mentions the self, so no amount of `Rec-I`/`Rec-E` on a *variable*
produces it.
-/

namespace FunctionField

/-- The type member whose upper bound is another member of the same self. -/
abbrev A : Lb := 2
/-- The unconstrained type member. -/
abbrev B : Lb := 1
/-- The method member. -/
abbrev f : Lb := 0

/-- `S(z)`, with `z` the innermost binder. -/
def Sbody : Ty [] ([],x) :=
  .TAnd (.TTyp A .TBot (.TSel (.abs .here) B))
    (.TAnd (.TTyp B .TBot .TTop)
      (.TFun f .TTop (.TSel (.abs (.there .here)) A)))

/-- `T(z)`. -/
def Tbody : Ty [] ([],x) :=
  .TFun f .TTop (.TSel (.abs (.there .here)) B)

/-- The context of the `stp_bindx` premise: the self at its *opened* type. -/
def Γz : Ctx [] ([],x) := Ctx.nil.cons Sbody

/-- `S(z) <: {A : ⊥ .. z.B}` in the prefix at the self, which here is the
whole context: the self is the newest binder, so `htp_sub`'s truncation is
vacuous at this variable. -/
def sBound : Stp (σ := []) .nil Γz Sbody (.TTyp A .TBot (.TSel (.abs .here) B)) :=
  .stp_and11 (.stp_typ .stp_bot .stp_selx)

/-- The self's `A` member, seen from under the method's parameter.  The
receiver is one binder further out, and its prefix — hence the context
`htp_sub` is allowed to use — is unchanged by the parameter. -/
def selMember :
    Htp (σ := []) .nil (Γz.cons .TTop) (.there .here)
      (.TTyp A .TBot (.TSel (.abs .here) B)) :=
  .htp_sub .htp_var sBound

/-- `z.A <: z.B`, under the method's parameter. -/
def selUnder :
    Stp (σ := []) .nil (Γz.cons .TTop)
      (.TSel (.abs (.there .here)) A) (.TSel (.abs (.there .here)) B) :=
  .stp_sel1 selMember

/-- `{f : ∀(_ : ⊤) z.A} <: {f : ∀(_ : ⊤) z.B}` by method covariance. -/
def methodCovariant :
    Stp (σ := []) .nil Γz
      (.TFun f .TTop (.TSel (.abs (.there .here)) A)) Tbody :=
  .stp_fun .stp_top selUnder

/-- The `stp_bindx` premise. -/
def premise : Stp (σ := []) .nil Γz Sbody Tbody :=
  .stp_and12 (.stp_and12 methodCovariant)

/-- `μ z. S(z) <: μ z. T(z)`. -/
def recursive : Stp (σ := []) .nil .nil (.TBind Sbody) (.TBind Tbody) :=
  .stp_bindx premise

end FunctionField

/-! ## `stp_bind1`: forgetting an unused self -/

/-- `μ z. (⊤ ∧ {B : ⊥ .. ⊤}) <: ⊤ ∧ {B : ⊥ .. ⊤}` when the body does not
mention its self.  The right endpoint is a weakening, which is the
reference's `z ∉ FV(T2)`. -/
def forgetSelf :
    Stp (σ := []) (s := []) .nil .nil
      (.TBind (.TAnd .TTop (.TTyp 1 .TBot .TTop)))
      (.TAnd .TTop (.TTyp 1 .TBot .TTop)) :=
  .stp_bind1 (.stp_and2 .stp_top (.stp_and12 (.stp_typ .stp_bot .stp_top)))

end Oopsla16.Examples
