import SystemFCoExt.Safety
import SystemFCoExt.Operational

/-!
# Computational-adapter regression

This closed example checks that an object coercion may compute its result from
the source value. The adapter body is scoped under exactly one term variable;
casting substitutes the ready source expression for that variable.
-/

namespace SystemFCoExt.AdapterRegression

open SystemFCoExt

def arrowTop : Ty {} :=
  .arrow .top .top

def identity : Exp {} :=
  .abs .top (.var .here)

def identityTyping :
    Ctx.empty |-e identity : arrowTop :=
  .abs (.var .here)

def identityBody : Exp ({} ,, .var) :=
  .var .here

def identityBodyTyping :
    Ctx.empty.bindVar arrowTop |-e identityBody :
      (arrowTop.weaken .var) :=
  .var .here

def identityAdapter : Co {} :=
  .adapter arrowTop identityBody

def identityAdapterTyping :
    Ctx.empty |-c identityAdapter : arrowTop => arrowTop :=
  .adapter identityBodyTyping

def program : Exp {} :=
  .cast identity identityAdapter

def programTyping :
    Ctx.empty |-e program : arrowTop :=
  .cast identityTyping identityAdapterTyping

def result : Exp {} :=
  identityBody.subst (Subst.openVar identity)

theorem adapterStep :
    Exp.Step program result :=
  .castAdapter .abs

theorem result_eq : result = identity :=
  rfl

theorem adapterPreserved :
    Nonempty (Ctx.empty |-e result : arrowTop) :=
  Exp.preservation programTyping adapterStep

theorem adapterDeterministic
    (reduction : Exp.Step program next) : next = result :=
  Exp.Step.deterministic reduction adapterStep

theorem programSound :
    Not (Exp.GoesWrong program) :=
  Exp.soundness programTyping

end SystemFCoExt.AdapterRegression
