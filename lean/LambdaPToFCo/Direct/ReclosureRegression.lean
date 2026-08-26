import LambdaPToFCo.Direct.Reclosure

/-! A nonempty closure transported through a genuinely non-renaming target
substitution. -/

namespace LambdaPToFCo.Direct.Internal.ReclosureRegression

open SystemFCo
open Reclosure

abbrev RootContext : Ctx [] := Ctx.empty

abbrev Prefix : Telescope [] := .var .top .nil

def topPayload {sig : Sig} : Exp sig :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

noncomputable def topPayload_hasType (base : Ctx sig) :
    Exp.HasType base (topPayload : Exp sig) .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

noncomputable def topInterface (base : Ctx sig) :
    Shape.Interface base (.opaque .top) where
  arguments := .var topPayload (topPayload_hasType base) .nil

abbrev OpenedContext : Ctx Prefix.scope := Prefix.context RootContext

/-- This substitution closes the prefix variable with a non-variable term. -/
noncomputable def opening : Subst Prefix.scope [] :=
  Subst.openVar topPayload

noncomputable def opening_typed :
    Subst.Typed OpenedContext RootContext opening :=
  Subst.Typed.openVar (topPayload_hasType RootContext)

abbrev Inner : Shape Prefix.scope := .opaque .top

noncomputable def reclosed : Shape.Interface RootContext
    ((outerShape Prefix Inner).subst
      (Prefix.weaken.asSubst.comp opening)) :=
  Reclosure.reclose RootContext Prefix Inner opening opening_typed (by
    simpa only [Inner, Shape.subst, Ty.subst] using topInterface RootContext)

/-- The reconstructed carrier is an ordinary well-typed System FCo package. -/
noncomputable def reclosed_package_hasType :
    Exp.HasType RootContext reclosed.package
      (((outerShape Prefix Inner).subst
        (Prefix.weaken.asSubst.comp opening)).inputTy) :=
  reclosed.package_hasType

end LambdaPToFCo.Direct.Internal.ReclosureRegression
