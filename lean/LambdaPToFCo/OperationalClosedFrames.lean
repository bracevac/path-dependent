import LambdaPToFCo.OperationalCode
import LambdaPToFCo.OperationalSubstitution

/-!
# Closing heterogeneous compiled continuation frames

A native LambdaP continuation may contain bodies originating in different
lexical contexts.  It is therefore generally impossible to compile the
whole continuation under one open target signature.  This module closes
each compiled frame with the environment belonging to that frame, after
which all frames have the common target signature `[]` and can be assembled
into an ordinary target continuation.

The construction is entirely syntactic.  Its generic first half proves that
target frame filling and continuation plugging commute with heterogeneous
substitution.  The second half pairs every retained source `FrameImage` with
its own static compilation and closing substitution.  No current-store
typing invariant or semantic realization relation is used.
-/

namespace LambdaPToFCo

open SystemFCo

namespace OperationalContexts

namespace Frame

/-- Apply one heterogeneous target substitution to all syntax stored in a
compiled continuation frame, lifting it through the frame's complete binder
interface for the saved body. -/
def subst (frame : Frame source) (substitution : Subst source target) :
    Frame target where
  plan := frame.plan.subst substitution
  result := frame.result.subst substitution
  body := frame.body.subst (frame.plan.scopeSubst substitution)

/-- Filling a compiled frame is natural in its base target signature. -/
@[simp] theorem fill_subst (frame : Frame source) (current : Exp source)
    (substitution : Subst source target) :
    (frame.fill current).subst substitution =
      (frame.subst substitution).fill (current.subst substitution) := by
  exact frame.plan.close_subst current frame.result frame.body substitution

/-- A substituted target step remains a step underneath the correspondingly
substituted frame. -/
theorem fill_step_subst (frame : Frame source)
    (substitution : Subst source target)
    (step : Exp.Step current current') :
    Exp.Step
      ((frame.subst substitution).fill (current.subst substitution))
      ((frame.subst substitution).fill (current'.subst substitution)) :=
  (frame.subst substitution).fill_step (step.subst substitution)

/-- Multi-step counterpart of `fill_step_subst`. -/
theorem fill_steps_subst (frame : Frame source)
    (substitution : Subst source target)
    (steps : Exp.Steps current current') :
    Exp.Steps
      ((frame.subst substitution).fill (current.subst substitution))
      ((frame.subst substitution).fill (current'.subst substitution)) := by
  induction steps with
  | refl => exact .refl
  | tail step rest ih =>
      exact .tail (frame.fill_step_subst substitution step) ih

end Frame

namespace Cont

/-- Substitute every frame of a homogeneous target continuation. -/
def subst : Cont source -> Subst source target -> Cont target
| .halt, _ => .halt
| .push frame rest, substitution =>
    .push (frame.subst substitution) (rest.subst substitution)

/-- Plugging a target continuation is natural in its base signature. -/
@[simp] theorem plug_subst (cont : Cont source) (current : Exp source)
    (substitution : Subst source target) :
    (cont.plug current).subst substitution =
      (cont.subst substitution).plug (current.subst substitution) := by
  induction cont generalizing current with
  | halt => rfl
  | push frame rest ih =>
      rw [plug, subst, plug, ← Frame.fill_subst]
      exact ih (frame.fill current)

/-- A substituted target step remains a step underneath every frame of the
correspondingly substituted continuation. -/
theorem plug_step_subst (cont : Cont source)
    (substitution : Subst source target)
    (step : Exp.Step current current') :
    Exp.Step
      ((cont.subst substitution).plug (current.subst substitution))
      ((cont.subst substitution).plug (current'.subst substitution)) :=
  (cont.subst substitution).plug_step (step.subst substitution)

/-- Multi-step counterpart of `plug_step_subst`. -/
theorem plug_steps_subst (cont : Cont source)
    (substitution : Subst source target)
    (steps : Exp.Steps current current') :
    Exp.Steps
      ((cont.subst substitution).plug (current.subst substitution))
      ((cont.subst substitution).plug (current'.subst substitution)) :=
  (cont.subst substitution).plug_steps (steps.subst substitution)

end Cont

end OperationalContexts

namespace OperationalEnvironment
namespace ClosingEnv

/-- Close all syntax retained by one target frame. -/
def closeFrame (environment : ClosingEnv source target)
    (frame : OperationalContexts.Frame source) :
    OperationalContexts.Frame target :=
  frame.subst environment.substitution

/-- Close every frame in a homogeneous open target continuation. -/
def closeCont (environment : ClosingEnv source target)
    (cont : OperationalContexts.Cont source) :
    OperationalContexts.Cont target :=
  cont.subst environment.substitution

/-- Closing commutes with filling one target frame. -/
@[simp] theorem closeExp_fill (environment : ClosingEnv source target)
    (frame : OperationalContexts.Frame source) (current : Exp source) :
    environment.closeExp (frame.fill current) =
      (environment.closeFrame frame).fill (environment.closeExp current) :=
  frame.fill_subst current environment.substitution

/-- Closing commutes with plugging a homogeneous target continuation. -/
@[simp] theorem closeExp_plug (environment : ClosingEnv source target)
    (cont : OperationalContexts.Cont source) (current : Exp source) :
    environment.closeExp (cont.plug current) =
      (environment.closeCont cont).plug (environment.closeExp current) :=
  cont.plug_subst current environment.substitution

end ClosingEnv
end OperationalEnvironment

namespace OperationalCode

namespace FrameImage

/-- Static compilation and target closing environment owned by one retained
source frame.  Different frames in one native continuation may choose
different open target signatures and contexts; only their closed result is
shared. -/
structure Compilation
    {current : Nat} {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : FrameImage runtimeBody) : Type where
  targetSig : Sig
  targetContext : Ctx targetSig
  scope : StaticTranslation.Scope frame.context targetContext
  coherent : scope.Coherent
  environment : OperationalEnvironment.ClosingEnv targetSig []

namespace Compilation

/-- Compile the original, typed let body retained by this frame. -/
noncomputable def openFrame
    {current : Nat} {runtimeBody : LambdaPFC.Tm (current + 1)}
    {frame : FrameImage runtimeBody} (compilation : Compilation frame) :
    OperationalContexts.Frame compilation.targetSig :=
  OperationalContexts.compileFrame compilation.scope frame.holeWf
    frame.resultWf frame.bodyTyping

/-- Close an individually compiled frame to the common run-time target
signature. -/
noncomputable def closeFrame
    {current : Nat} {runtimeBody : LambdaPFC.Tm (current + 1)}
    {frame : FrameImage runtimeBody} (compilation : Compilation frame) :
    OperationalContexts.Frame [] :=
  compilation.environment.closeFrame compilation.openFrame

/-- Filling an individually closed frame is exactly closing its open fill. -/
@[simp] theorem closeExp_openFrame_fill
    {current : Nat} {runtimeBody : LambdaPFC.Tm (current + 1)}
    {frame : FrameImage runtimeBody} (compilation : Compilation frame)
    (expression : Exp compilation.targetSig) :
    compilation.environment.closeExp
        (compilation.openFrame.fill expression) =
      compilation.closeFrame.fill
        (compilation.environment.closeExp expression) :=
  compilation.environment.closeExp_fill compilation.openFrame expression

/-- Target reduction is closed under an individually closed frame. -/
theorem closeFrame_fill_step
    {current : Nat} {runtimeBody : LambdaPFC.Tm (current + 1)}
    {frame : FrameImage runtimeBody} (compilation : Compilation frame)
    (step : Exp.Step expression expression') :
    Exp.Step (compilation.closeFrame.fill expression)
      (compilation.closeFrame.fill expression') :=
  compilation.closeFrame.fill_step step

/-- Multi-step target reduction is closed under an individually closed
frame. -/
theorem closeFrame_fill_steps
    {current : Nat} {runtimeBody : LambdaPFC.Tm (current + 1)}
    {frame : FrameImage runtimeBody} (compilation : Compilation frame)
    (steps : Exp.Steps expression expression') :
    Exp.Steps (compilation.closeFrame.fill expression)
      (compilation.closeFrame.fill expression') := by
  induction steps with
  | refl => exact .refl
  | tail step rest ih =>
      exact .tail (compilation.closeFrame_fill_step step) ih

end Compilation
end FrameImage

/-! ## Heterogeneous source stacks, homogeneous closed target stacks -/

/-- A compilation choice for every frame of a retained native continuation.
Each head owns an unrelated open target signature, context, and closing
environment; the recursive spine only becomes homogeneous after closing. -/
inductive ContCompilation {current : Nat} :
    {runtime : LambdaPFC.Tm.Cont current} -> ContImage runtime -> Type where
| nil : ContCompilation .nil
| cons
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {frame : FrameImage runtimeBody} {rest : ContImage runtimeRest}
    (head : FrameImage.Compilation frame)
    (tail : ContCompilation rest) :
    ContCompilation (.cons frame rest)

namespace ContCompilation

/-- Close every independently compiled frame and assemble one ordinary
closed target continuation. -/
noncomputable def closeCont :
    {runtime : LambdaPFC.Tm.Cont current} ->
    {image : ContImage runtime} -> ContCompilation image ->
      OperationalContexts.Cont []
| _, _, .nil => .halt
| _, _, .cons head tail => .push head.closeFrame tail.closeCont

/-- A target step remains a step after plugging all independently closed
source frames around it. -/
theorem closeCont_plug_step
    {runtime : LambdaPFC.Tm.Cont current} {image : ContImage runtime}
    (compilation : ContCompilation image)
    (step : Exp.Step expression expression') :
    Exp.Step (compilation.closeCont.plug expression)
      (compilation.closeCont.plug expression') :=
  compilation.closeCont.plug_step step

/-- Multi-step target reduction remains valid after plugging all
independently closed source frames around it. -/
theorem closeCont_plug_steps
    {runtime : LambdaPFC.Tm.Cont current} {image : ContImage runtime}
    (compilation : ContCompilation image)
    (steps : Exp.Steps expression expression') :
    Exp.Steps (compilation.closeCont.plug expression)
      (compilation.closeCont.plug expression') :=
  compilation.closeCont.plug_steps steps

end ContCompilation

end OperationalCode
end LambdaPToFCo
