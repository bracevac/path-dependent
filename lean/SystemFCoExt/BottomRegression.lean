import SystemFCoExt.Safety
import SystemFCoExt.Operational

/-!
# Impredicative-bottom coercion regression

`Ty.bottom` is the impredicative encoding `forall X. X`. The object coercion
`Co.bottom target` eliminates that encoding into `target`; operationally, a
cast by this coercion becomes the corresponding type application.
-/

namespace SystemFCoExt.BottomRegression

open SystemFCoExt

def bottomToTop : Co {} :=
  .bottom .top

def bottomToTopTyping :
    Ctx.empty |-c bottomToTop : (Ty.bottom : Ty {}) => .top :=
  .bottom

def castBottomTyping
    {context : Ctx sig} {expression : Exp sig}
    (expressionTyping : context |-e expression : Ty.bottom)
    (target : Ty sig) :
    context |-e (.cast expression (.bottom target)) : target :=
  .cast expressionTyping .bottom

def bottomApplicationTyping
    {context : Ctx sig} {expression : Exp sig}
    (expressionTyping : context |-e expression : Ty.bottom)
    (target : Ty sig) :
    context |-e (.tapp expression target) : target :=
  .tapp expressionTyping

theorem bottomRename
    (target : Ty source) (rename : Rename source result) :
    (Co.bottom target).rename rename = .bottom (target.rename rename) :=
  rfl

theorem bottomSubst
    (target : Ty source) (substitution : Subst source result) :
    (Co.bottom target).subst substitution = .bottom (target.subst substitution) :=
  rfl

theorem castBottomStep
    {expression : Exp sig} (value : Exp.IsValue expression)
    (target : Ty sig) :
    Exp.Step (.cast expression (.bottom target)) (.tapp expression target) :=
  .castBottom value

theorem castBottomPreserved
    {context : Ctx sig} {expression : Exp sig}
    (expressionTyping : context |-e expression : Ty.bottom)
    (value : Exp.IsValue expression) (target : Ty sig) :
    Nonempty (context |-e (.tapp expression target) : target) :=
  Exp.preservation (castBottomTyping expressionTyping target)
    (.castBottom value)

theorem castBottomDeterministic
    {expression result : Exp sig} (value : Exp.IsValue expression)
    (target : Ty sig)
    (reduction : Exp.Step (.cast expression (.bottom target)) result) :
    result = .tapp expression target :=
  Exp.Step.deterministic reduction (.castBottom value)

end SystemFCoExt.BottomRegression
