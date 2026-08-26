import LambdaPToFCo.Direct.TermIntroduction
import LambdaPToFCo.Direct.WfRegression

/-!
# Direct term-introduction regressions

The first two values are the introduction fragments used by
`LambdaPFC.GeneralPairRegression`: the bound identity function and its exact
type-pair body before subtyping.  The final definition instantiates the
scope-safe let kernel with a material Top result, exercising bound-package
opening and the expected-shape body handoff.
-/

namespace LambdaPToFCo.Direct.TermIntroductionRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.TermIntroduction
open LambdaPToFCo.Direct.WfRegression

/-- The body of the GeneralPair bound is the singleton of its newest Top
argument, resolved without opening another target existential. -/
noncomputable def identityBody :
    Slot (first.shape.context TargetContext)
      (.Single (.var 0) : LambdaPFC.Ty 1) :=
  variableSlot memberEnvironment 0

/-- Exact direct package for `abs Top (path (var 0))`. -/
noncomputable def identityFunction :
    Slot TargetContext
      (.Fun .Top (.Single (.var 0)) : LambdaPFC.Ty 0) :=
  abstractSlot first identityBody

/-- Exact direct package for the type-pair used inside the GeneralPair let,
before the source subtyping derivations expose and hide its interval. -/
noncomputable def exactTypePair :
    Slot (first.shape.context TargetContext)
      (.Pair (.Single (.var 0)) LambdaPFC.GeneralPairRegression.label
        (LambdaPFC.Tau.intv
          (.Single (.var 0) : LambdaPFC.Ty 1)
          (.Single (.var 0) : LambdaPFC.Ty 1)).weaken) :=
  typePairSlot memberEnvironment 0
    LambdaPFC.GeneralPairRegression.label singletonEndpoint

/-! ## Let-kernel instantiation -/

abbrev BoundSource : LambdaPFC.Ty 0 :=
  .Fun .Top (.Single (.var 0))

noncomputable def boundComputation :
    ValueComputation LambdaPFC.Ctx.nil TargetContext
      BoundSource :=
  compileMaterial emptyEnvironment identityFunction

def topPayload {sig : Sig} : SystemFCo.Exp sig :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

noncomputable def topPayload_hasType
    (targetContext : SystemFCo.Ctx sig) :
    SystemFCo.Exp.HasType targetContext (topPayload : SystemFCo.Exp sig)
      .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

noncomputable def topInterface
    (targetContext : SystemFCo.Ctx sig) :
    Shape.Interface targetContext (.stable (Top.plan sig)) where
  arguments := Top.arguments .top topPayload
    (topPayload_hasType targetContext)

/-- An expected-shape body compiler for a weakened source Top.  Pattern
matching the exact `Rep.top` index determines the canonical target shape; no
shape equality is assumed. -/
noncomputable def topBody
    (answer : SystemFCo.Ty []) :
    LetBodyCompiler LambdaPFC.Ctx.nil TargetContext answer
      BoundSource .Top :=
  fun _mapping _typed _environment result consume => by
    cases result with
    | mk shape rep =>
        cases rep with
        | top => exact consume (topInterface _)

/-- A closed instantiation of the let kernel.  The caller remains free to
choose how the resulting exact Top Slot is consumed. -/
noncomputable def letKernel
    (answer : SystemFCo.Ty [])
    (consumer : ValueConsumer LambdaPFC.Ctx.nil
      TargetContext answer .Top) :
    LambdaPToFCo.Direct.Internal.Path.Body TargetContext answer :=
  compileLet boundComputation
    (LambdaPToFCo.Direct.Internal.Wf.Proper.top TargetContext)
    answer (topBody answer)
    consumer

end LambdaPToFCo.Direct.TermIntroductionRegression
