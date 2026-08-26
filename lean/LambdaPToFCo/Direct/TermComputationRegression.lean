import LambdaPToFCo.Direct.TermComputation

/-!
# Formation-aware term-kernel regressions

These examples exercise every literal material constructor.  The final let
kernel is parameterized only by the one generic checking-mode boundary that
will later be implemented by total derivation recursion; no separate let plan
or shape equality is supplied.
-/

namespace LambdaPToFCo.Direct.TermComputationRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal.Formation
open LambdaPToFCo.Direct.Internal.TermComputation

private abbrev TargetContext : Ctx [] := Ctx.empty

private noncomputable def emptyEnvironment :
    Env LambdaPFC.Ctx.nil TargetContext :=
  Env.empty TargetContext

/-! ## Path and abstraction -/

private def identityBodyTyping :
    LambdaPFC.Tm.Ty (LambdaPFC.Ctx.nil.snoc .Top)
      (.path (.var 0)) (.Single (.var 0)) :=
  .path .var

private def identityTyping :
    LambdaPFC.Tm.Ty LambdaPFC.Ctx.nil
      (.abs .Top (.path (.var 0)))
      (.Fun .Top (.Single (.var 0))) :=
  .abs identityBodyTyping .top

private noncomputable def topDomain :
    Proper LambdaPFC.Ctx.nil TargetContext (.Top : LambdaPFC.Ty 0) :=
  .top LambdaPFC.Ctx.nil TargetContext

private def topPayload : Exp [] :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

private noncomputable def topPayload_hasType :
    Exp.HasType TargetContext topPayload .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

private noncomputable def topInterface :
    Shape.Interface TargetContext topDomain.shape where
  arguments := Top.arguments .top topPayload topPayload_hasType

/-- An arbitrary typed package becomes a material one-field carrier without
recovering or guessing the demand's argument spine. -/
noncomputable def sealedTop :
    Slot LambdaPFC.Ctx.nil TargetContext .Top :=
  sealResult topDomain topInterface.package
    topInterface.package_hasType

theorem sealedTop_isOpaque :
    match sealedTop.shape with
    | .opaque _ => True
    | .stable _ => False := by
  trivial

private noncomputable def identityEnvironment :
    Env (LambdaPFC.Ctx.nil.snoc .Top)
      (topDomain.shape.context TargetContext) :=
  emptyEnvironment.enter .Top topDomain.formation

/-- Literal path introduction uses the formed variable interface. -/
noncomputable def identityBody :
    Slot (LambdaPFC.Ctx.nil.snoc .Top)
      (topDomain.shape.context TargetContext)
      (.Single (.var 0)) :=
  pathSlot (.var : LambdaPFC.Path.Ty
    (LambdaPFC.Ctx.nil.snoc .Top) (.var 0) (.ty .Top))
    identityEnvironment

/-- Literal abstraction retains both domain and body Formations. -/
noncomputable def identity :
    Slot LambdaPFC.Ctx.nil TargetContext
      (.Fun .Top (.Single (.var 0))) :=
  abstractSlot topDomain identityBody

noncomputable def identity_hasType :
    Exp.HasType TargetContext identity.interface.package
      identity.shape.inputTy :=
  identity.interface.package_hasType

theorem identity_expression :
    identity.interface.package =
      LambdaPToFCo.Direct.Internal.Introduction.function
        topDomain.shape identityBody.shape identityBody.interface.package
        identityBody.interface.package_hasType :=
  abstractSlot_expression topDomain identityBody

/-- CPS constructor kernel for the same literal abstraction. -/
noncomputable def identityComputation :
    Computation LambdaPFC.Ctx.nil TargetContext
      (.Fun .Top (.Single (.var 0))) :=
  compileAbstract identityBodyTyping .top emptyEnvironment
    (fun domain =>
      pathSlot (.var : LambdaPFC.Path.Ty
        (LambdaPFC.Ctx.nil.snoc .Top) (.var 0) (.ty .Top))
        (emptyEnvironment.enter .Top domain.formation))

/-! ## Value and type pairs -/

private abbrev TwoTops : LambdaPFC.Ctx 2 :=
  (LambdaPFC.Ctx.nil.snoc .Top).snoc .Top

private noncomputable def secondTop :
    Proper (LambdaPFC.Ctx.nil.snoc .Top)
      (topDomain.shape.context TargetContext) (.Top : LambdaPFC.Ty 1) :=
  .top (LambdaPFC.Ctx.nil.snoc .Top)
    (topDomain.shape.context TargetContext)

private noncomputable def twoTopEnvironment :
    Env TwoTops (secondTop.shape.context
      (topDomain.shape.context TargetContext)) :=
  identityEnvironment.enter .Top secondTop.formation

/-- Literal value pair from two exact formed variable paths. -/
noncomputable def valuePair :=
  valuePairSlot twoTopEnvironment (0 : Fin 2) (1 : Fin 2) 5

noncomputable def valuePair_hasType :
    Exp.HasType
      (secondTop.shape.context (topDomain.shape.context TargetContext))
      valuePair.interface.package valuePair.shape.inputTy :=
  valuePair.interface.package_hasType

/-- Literal type pair with a Wf-compiled equal Top endpoint. -/
noncomputable def typePair :=
  typePairSlot identityEnvironment (0 : Fin 1) 9
    (LambdaPFC.Tau.Wf.top : LambdaPFC.Tau.Wf
      (LambdaPFC.Ctx.nil.snoc .Top) (.ty .Top))

noncomputable def typePair_hasType :
    Exp.HasType (topDomain.shape.context TargetContext)
      typePair.interface.package typePair.shape.inputTy :=
  typePair.interface.package_hasType

/-! ## Let with one exact checking boundary -/

private abbrev BoundSource : LambdaPFC.Ty 0 :=
  .Fun .Top (.Single (.var 0))

private def letBodyTyping :
    LambdaPFC.Tm.Ty (LambdaPFC.Ctx.nil.snoc BoundSource)
      (.path (.var 0)) .Top :=
  .sub (.path .var) .top .top

/-- The let kernel fixes the result to Wf Top, weakens that exact Formation
under the bound function, and delegates only checking of the source body. -/
noncomputable def letKernel
    (bodyCompiler : AgainstCompiler letBodyTyping) :
    Computation LambdaPFC.Ctx.nil TargetContext .Top :=
  compileLet identityTyping identityComputation .top letBodyTyping
    bodyCompiler emptyEnvironment

/-- Material let synthesis uses the same checking boundary, then seals the
typed let package at the fixed root Formation. -/
noncomputable def sealedLet
    (bodyCompiler : AgainstCompiler letBodyTyping) :
    Slot LambdaPFC.Ctx.nil TargetContext .Top :=
  compileLetSealed identityTyping identityComputation .top letBodyTyping
    bodyCompiler emptyEnvironment

end LambdaPToFCo.Direct.TermComputationRegression
