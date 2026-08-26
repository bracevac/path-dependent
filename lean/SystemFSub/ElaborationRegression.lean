import SystemFSub.ElaborationTyping
import SystemFCo.Safety

/-!
# A closed F<: elaboration example

The body of `boundedIdentity` uses its abstract bound `X <: Top`. Elaboration
therefore inserts an actual target cast driven by the coercion variable paired
with `X`; instantiation supplies the explicit reflexive coercion for `Top`.
-/

namespace SystemFSub.ElaborationRegression

open SystemFSub

def typeContext : SystemFSub.Ctx ({},X) :=
  SystemFSub.Ctx.empty,X<:.top

def bodyContext : SystemFSub.Ctx (({},X),x) :=
  typeContext,x:(.tvar .here)

def boundedIdentityBody : SystemFSub.Tm ({},X) :=
  .abs (.tvar .here) (.var .here)

def boundedIdentity : SystemFSub.Tm {} :=
  .tabs .top boundedIdentityBody

def topIdentity : SystemFSub.Tm {} :=
  .abs .top (.var .here)

def program : SystemFSub.Tm {} :=
  .app (.tapp boundedIdentity .top) topIdentity

def body_variable_typing :
    bodyContext |- (.var .here) : (.top : SystemFSub.Ty (({},X),x)) := by
  apply SystemFSub.Tm.HasType.sub (.var .here)
  exact .bound (.there .here)

def bounded_identity_body_typing :
    typeContext |- boundedIdentityBody :
      .arrow (.tvar .here) (.top : SystemFSub.Ty ({},X)) :=
  .abs body_variable_typing

def bounded_identity_typing :
    SystemFSub.Ctx.empty |- boundedIdentity :
      .all .top (.arrow (.tvar .here) .top) :=
  .tabs bounded_identity_body_typing

def top_identity_typing :
    SystemFSub.Ctx.empty |- topIdentity : .arrow .top .top :=
  .abs (.var .here)

def top_identity_as_top_typing :
    SystemFSub.Ctx.empty |- topIdentity : (.top : SystemFSub.Ty {}) :=
  .sub top_identity_typing .top

def instantiated_typing :
    SystemFSub.Ctx.empty |- (.tapp boundedIdentity .top) :
      .arrow .top .top := by
  simpa only [SystemFSub.Ty.open, SystemFSub.Ty.subst,
    SystemFSub.Subst.openTVar] using
    SystemFSub.Tm.HasType.tapp bounded_identity_typing
      (SystemFSub.Ty.Sub.refl :
        SystemFSub.Ctx.empty |- (.top : SystemFSub.Ty {}) <: .top)

def program_typing :
    SystemFSub.Ctx.empty |- program : (.top : SystemFSub.Ty {}) :=
  .app instantiated_typing top_identity_as_top_typing

noncomputable def elaborated_program_typing :
    SystemFCo.Ctx.empty |-e
      SystemFSub.Elaboration.elaborateTerm program_typing :
      SystemFSub.Elaboration.translateTy (.top : SystemFSub.Ty {}) :=
  SystemFSub.Elaboration.elaborateTermTyping program_typing

theorem elaborated_program_sound :
    Not (SystemFCo.Exp.GoesWrong
      (SystemFSub.Elaboration.elaborateTerm program_typing)) :=
  SystemFCo.Exp.soundness elaborated_program_typing

end SystemFSub.ElaborationRegression
