import LambdaPFC.Runtime
import LambdaPToFCo.OperationalMacros
import LambdaPToFCo.TermTranslation

/-!
# Syntactic target images of LambdaP CK continuations

The source CK machine stores a list of suspended `let` bodies.  The target
has no machine continuation, so the compiler represents that list by nested
applications of `BinderPlan.close`.

This file deliberately says nothing about source-store typing or semantic
realization.  It establishes the target evaluation-context algebra needed by
a later simulation.  In particular, a source `let_push` is represented by an
equality (zero target steps), while computation under the pushed frame is
closed under target reduction.
-/

namespace LambdaPToFCo
namespace OperationalContexts

open SystemFCo
open StaticTranslation

/-- One suspended compiled `let` body. -/
structure Frame (sig : Sig) where
  plan : Interface.BinderPlan sig
  result : Ty sig
  body : Exp plan.scope

namespace Frame

/-- Put the current computation into a suspended binder. -/
def fill (frame : Frame sig) (current : Exp sig) : Exp sig :=
  frame.plan.close current frame.result frame.body

/-- The target evaluates the argument of a compiled binder left-to-right. -/
theorem fill_step (frame : Frame sig)
    (step : Exp.Step current current') :
    Exp.Step (frame.fill current) (frame.fill current') := by
  cases frame with
  | mk plan result body =>
      cases plan <;> exact .appArgument .abs step

end Frame

/-- Target representation of a CK continuation.  The first pushed frame is
the innermost one, just as the head of `LambdaPFC.Tm.Cont` is the next body to
resume. -/
inductive Cont (sig : Sig) : Type where
| halt : Cont sig
| push : Frame sig -> Cont sig -> Cont sig

namespace Cont

/-- Reconstruct the single target expression represented by a target
continuation and its current computation. -/
def plug : Cont sig -> Exp sig -> Exp sig
| .halt, current => current
| .push frame rest, current => rest.plug (frame.fill current)

/-- A target step in the current computation remains a target step after all
suspended source `let` frames are plugged around it. -/
theorem plug_step (cont : Cont sig)
    (step : Exp.Step current current') :
    Exp.Step (cont.plug current) (cont.plug current') := by
  induction cont generalizing current current' with
  | halt => exact step
  | push frame rest ih => exact ih (frame.fill_step step)

/-- Multi-step version of `plug_step`. -/
theorem plug_steps (cont : Cont sig)
    (steps : Exp.Steps current current') :
    Exp.Steps (cont.plug current) (cont.plug current') := by
  induction steps with
  | refl => exact .refl
  | tail step steps ih => exact .tail (cont.plug_step step) ih

end Cont

/-- Compile one typed source continuation frame.  The bound type selects the
same one-slot or five-slot plan used by term elaboration. -/
noncomputable def compileFrame
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {boundType resultType : LambdaPFC.Ty n}
    {body : LambdaPFC.Tm (n + 1)}
    (boundWf : Fragment.Wf sourceContext boundType)
    (resultWf : Fragment.Wf sourceContext resultType)
    (bodyTyping : Fragment.HasType (sourceContext.snoc boundType) body
      resultType.weaken) : Frame sig :=
  let binder := TermTranslation.compileBinder scope boundWf
  { plan := binder.plan
    result := StaticTranslation.translateType scope resultWf
    body := TermTranslation.elaborate binder.extended bodyTyping }

/-- A proof-relevant relation between the native CK continuation and its
nested target frames.  Source continuation syntax omits the types of its
bodies, so those types and typing derivations are precisely the evidence
stored by this relation. -/
inductive ContImage
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext) :
    LambdaPFC.Ty n -> LambdaPFC.Tm.Cont n -> Cont sig -> Type where
| nil {holeType : LambdaPFC.Ty n} :
    ContImage scope holeType [] .halt
| cons
    {holeType resultType : LambdaPFC.Ty n}
    {body : LambdaPFC.Tm (n + 1)} {sourceRest : LambdaPFC.Tm.Cont n}
    {targetRest : Cont sig}
    (holeWf : Fragment.Wf sourceContext holeType)
    (resultWf : Fragment.Wf sourceContext resultType)
    (bodyTyping : Fragment.HasType (sourceContext.snoc holeType) body
      resultType.weaken)
    (rest : ContImage scope resultType sourceRest targetRest) :
    ContImage scope holeType (body :: sourceRest)
      (.push (compileFrame scope holeWf resultWf bodyTyping) targetRest)

/-! ## The first CK administrative cases -/

/-- Term elaboration already places a source `let` into exactly the target
frame used by `compileFrame`.  Thus CK `let_push` changes only the chosen
decomposition of the target expression; it takes zero target steps. -/
theorem elaborate_let_eq_fill
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {bound : LambdaPFC.Tm n} {body : LambdaPFC.Tm (n + 1)}
    {boundType resultType : LambdaPFC.Ty n}
    (boundTyping : Fragment.HasType sourceContext bound boundType)
    (resultWf : Fragment.Wf sourceContext resultType)
    (bodyTyping : Fragment.HasType (sourceContext.snoc boundType) body
      resultType.weaken) :
    TermTranslation.elaborate scope
        (.let boundTyping resultWf bodyTyping) =
      (compileFrame scope boundTyping.typeWf resultWf bodyTyping).fill
        (TermTranslation.elaborate scope boundTyping) := by
  rfl

/-- The `let_push` equality remains true underneath every already-compiled
outer continuation. -/
theorem plug_elaborate_let_eq
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext) (cont : Cont sig)
    {bound : LambdaPFC.Tm n} {body : LambdaPFC.Tm (n + 1)}
    {boundType resultType : LambdaPFC.Ty n}
    (boundTyping : Fragment.HasType sourceContext bound boundType)
    (resultWf : Fragment.Wf sourceContext resultType)
    (bodyTyping : Fragment.HasType (sourceContext.snoc boundType) body
      resultType.weaken) :
    cont.plug
        (TermTranslation.elaborate scope
          (.let boundTyping resultWf bodyTyping)) =
      (Cont.push (compileFrame scope boundTyping.typeWf resultWf bodyTyping)
          cont).plug
        (TermTranslation.elaborate scope boundTyping) := by
  rw [elaborate_let_eq_fill]
  rfl

end OperationalContexts
end LambdaPToFCo
