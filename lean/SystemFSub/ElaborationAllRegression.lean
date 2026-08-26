import SystemFSub.ElaborationTyping
import SystemFCo.Safety

/-!
# Full bounded-universal elaboration regression

This closed example exercises the nontrivial `all` case of F<: subtyping.
The polymorphic source value initially accepts every `X <: Top`; it is then
viewed at the narrower bound `X <: Top -> Top`.  The source body consumes its
original `X <: Top` evidence, so the qualifier coercion must adapt the new
bound evidence before invoking it.  The body subtyping derivation is written
structurally, producing an arrow coercion as well.
-/

namespace SystemFSub.ElaborationAllRegression

open SystemFSub

/-- A proper subtype of `Top`, used as the narrower universal bound. -/
def arrowTop : SystemFSub.Ty {} :=
  .arrow .top .top

def broadTypeContext : SystemFSub.Ctx ({},X) :=
  SystemFSub.Ctx.empty,X<:.top

def broadBodyContext : SystemFSub.Ctx (({},X),x) :=
  broadTypeContext,x:(.tvar .here)

def narrowTypeContext : SystemFSub.Ctx ({},X) :=
  SystemFSub.Ctx.empty,X<:arrowTop

/-- `Lambda X <: Top. lambda x : X. x`, with the result viewed at `Top`. -/
def boundedToTopBody : SystemFSub.Tm ({},X) :=
  .abs (.tvar .here) (.var .here)

def boundedToTop : SystemFSub.Tm {} :=
  .tabs .top boundedToTopBody

def topIdentity : SystemFSub.Tm {} :=
  .abs .top (.var .here)

/-- Subsumption is present only in the typing derivation, so this is the same
raw source term as an ordinary type application followed by an application. -/
def program : SystemFSub.Tm {} :=
  .app (.tapp boundedToTop arrowTop) topIdentity

def broad_body_variable_typing :
    broadBodyContext |- (.var .here) :
      (.top : SystemFSub.Ty (({},X),x)) := by
  apply SystemFSub.Tm.HasType.sub (.var .here)
  exact .bound (.there .here)

def broad_body_typing :
    broadTypeContext |- boundedToTopBody :
      .arrow (.tvar .here) (.top : SystemFSub.Ty ({},X)) :=
  .abs broad_body_variable_typing

def broad_polymorphic_typing :
    SystemFSub.Ctx.empty |- boundedToTop :
      .all .top (.arrow (.tvar .here) .top) :=
  .tabs broad_body_typing

/-- The bounded-universal body is related through an explicit arrow
derivation rather than the general reflexivity rule.  Its elaboration is
therefore an object-language `Co.arrow`. -/
def all_body_subtyping :
    narrowTypeContext |- (.arrow (.tvar .here) .top) <:
      (.arrow (.tvar .here) .top) :=
  .arrow .refl .refl

/-- Full-F<: contravariance in the bound:

`forall X <: Top. X -> Top  <:  forall X <: Top -> Top. X -> Top`.
-/
def bounded_universal_subtyping :
    SystemFSub.Ctx.empty |-
      (.all .top (.arrow (.tvar .here) .top)) <:
      (.all arrowTop (.arrow (.tvar .here) .top)) :=
  .all .top all_body_subtyping

def narrow_polymorphic_typing :
    SystemFSub.Ctx.empty |- boundedToTop :
      .all arrowTop (.arrow (.tvar .here) .top) :=
  .sub broad_polymorphic_typing bounded_universal_subtyping

def instantiated_typing :
    SystemFSub.Ctx.empty |- (.tapp boundedToTop arrowTop) :
      .arrow arrowTop .top := by
  simpa only [SystemFSub.Ty.open, SystemFSub.Ty.subst,
    SystemFSub.Subst.openTVar] using
    SystemFSub.Tm.HasType.tapp narrow_polymorphic_typing
      (SystemFSub.Ty.Sub.refl :
        SystemFSub.Ctx.empty |- arrowTop <: arrowTop)

def top_identity_typing :
    SystemFSub.Ctx.empty |- topIdentity : arrowTop :=
  .abs (.var .here)

def program_typing :
    SystemFSub.Ctx.empty |- program : (.top : SystemFSub.Ty {}) :=
  .app instantiated_typing top_identity_typing

noncomputable def elaborated_program_typing :
    SystemFCo.Ctx.empty |-e
      SystemFSub.Elaboration.elaborateTerm program_typing :
      SystemFSub.Elaboration.translateTy (.top : SystemFSub.Ty {}) :=
  SystemFSub.Elaboration.elaborateTermTyping program_typing

theorem elaborated_program_sound :
    Not (SystemFCo.Exp.GoesWrong
      (SystemFSub.Elaboration.elaborateTerm program_typing)) :=
  SystemFCo.Exp.soundness elaborated_program_typing

end SystemFSub.ElaborationAllRegression
