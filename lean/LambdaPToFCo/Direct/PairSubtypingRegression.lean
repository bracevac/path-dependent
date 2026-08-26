import LambdaPToFCo.Direct.PairSubtyping
import LambdaPToFCo.Direct.TermIntroductionRegression
import LambdaPToFCo.Direct.WfRegression
import LambdaPFC.GeneralPairRegression

/-!
# Direct dependent-pair subtyping regressions

These checks compile the two closed generalized-pair covariance statements
from `LambdaPFC.GeneralPairRegression`.  Both results are exact-shape
`Relation`s; no caller-supplied equation reconnects an existential result to
the source representation.
-/

namespace LambdaPToFCo.Direct.PairSubtypingRegression

noncomputable section

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.PairSubtyping

abbrev TargetContext : Ctx [] := Ctx.empty

noncomputable def firstRefl :=
  (AtomicSubtyping.refl WfRegression.first).relation

abbrev MemberContext :=
  WfRegression.first.shape.context TargetContext

noncomputable def exactFirstSlot :=
  TermIntroduction.variableSlot WfRegression.memberEnvironment 0

noncomputable def exactFirst : Wf.Proper MemberContext
    (.Single (.var 0) : LambdaPFC.Ty 1) where
  shape := exactFirstSlot.shape
  rep := exactFirstSlot.rep

noncomputable def exposedFirst : Wf.Proper MemberContext
    (.Top : LambdaPFC.Ty 1) :=
  Wf.Proper.top MemberContext

noncomputable def exposedEnvironment :=
  WfRegression.memberEnvironment.enter (.Top : LambdaPFC.Ty 1)
    exposedFirst.shape exposedFirst.rep

noncomputable def exposedEndpoint : Wf.Proper
    (exposedFirst.shape.context MemberContext)
    (.Single (.var 0) : LambdaPFC.Ty 2) :=
  Wf.Proper.singletonVariable exposedEnvironment 0

noncomputable def exposedInterval : Wf.Proper MemberContext
    (.Pair (.Top : LambdaPFC.Ty 1)
      LambdaPFC.GeneralPairRegression.label
      (.intv (.Single (.var 0)) (.Single (.var 0)))) :=
  Wf.Proper.intervalPair LambdaPFC.GeneralPairRegression.label exposedFirst
    (Wf.Interval.bounds exposedEndpoint exposedEndpoint)

noncomputable def firstTop :=
  (AtomicSubtyping.top exactFirst).relation

/-- The Slot/Wf smart constructor connects term introduction to pair
subtyping with both endpoint shapes left definitionally visible. -/
noncomputable def exactFromIntroducedSlot :=
  exactTypePair WfRegression.memberEnvironment 0
    LambdaPFC.GeneralPairRegression.label exposedFirst firstTop

/-- Exact compilation of
`.pair .top (.bounds (.widen .var) (.symm .var) .refl)`. -/
noncomputable def exactToIntervalSource : Relation MemberContext
    (.Pair (.Single (.var 0)) LambdaPFC.GeneralPairRegression.label
      (.intv
        ((.Single (.var 0) : LambdaPFC.Ty 1).weaken)
        ((.Single (.var 0) : LambdaPFC.Ty 1).weaken)))
    (.Pair (.Top : LambdaPFC.Ty 1)
      LambdaPFC.GeneralPairRegression.label
      (.intv (.Single (.var 0)) (.Single (.var 0))))
    (.stable (Pair.Interval.plan exactFirst.shape
      (liftedFirstFamily exactFirst.shape)
      (liftedFirstFamily exactFirst.shape)))
    (.stable (Pair.Interval.plan exposedFirst.shape
      (newestSingletonFamily exposedFirst.shape)
      (newestSingletonFamily exposedFirst.shape))) :=
  exactSingletonInterval (label := LambdaPFC.GeneralPairRegression.label)
    firstTop

/-- The first leg consumes the literal source Slot emitted by type-pair
introduction; no post-hoc shape equality is supplied to the compiler. -/
example : TermIntroductionRegression.exactTypePair.shape =
    (.stable (Pair.Interval.plan exactFirst.shape
      (liftedFirstFamily exactFirst.shape)
      (liftedFirstFamily exactFirst.shape))) := by
  rfl

/-- The target index is definitionally the direct Wf result for the exposed
interval source. -/
example : exposedInterval.shape =
    (.stable (Pair.Interval.plan exposedFirst.shape
      (newestSingletonFamily exposedFirst.shape)
      (newestSingletonFamily exposedFirst.shape))) := by
  rfl

/-- Exact compilation of `.pair .refl .top`. -/
noncomputable def proper : Relation TargetContext
    LambdaPFC.GeneralPairRegression.properSource
    LambdaPFC.GeneralPairRegression.properTarget
    (.stable (Pair.Proper.plan WfRegression.first.shape
      WfRegression.singletonEndpoint.shape))
    (.stable (Pair.Proper.plan WfRegression.first.shape
      (.stable (Top.plan WfRegression.first.shape.scope)))) :=
  properTop firstRefl WfRegression.singletonEndpoint.rep

/-- Exact compilation of `.pair .refl (.bounds .bot .top .refl)`.  The
selected interval witness remains the source package's actual opaque type. -/
noncomputable def interval : Relation TargetContext
    LambdaPFC.GeneralPairRegression.intervalSource
    LambdaPFC.GeneralPairRegression.intervalTarget
    (.stable (Pair.Interval.plan WfRegression.first.shape
      WfRegression.singletonEndpoint.shape
      WfRegression.singletonEndpoint.shape))
    (.stable (Pair.Interval.plan WfRegression.first.shape
      (.stable (Bot.plan WfRegression.first.shape.scope))
      (.stable (Top.plan WfRegression.first.shape.scope)))) :=
  intervalBotTop firstRefl WfRegression.singletonEndpoint.rep
    WfRegression.singletonEndpoint.rep

/-- The emitted proper-pair program is an ordinary SystemFCo function. -/
example : Exp.HasType TargetContext proper.conversion.function
    (.arrow
      (Pair.Proper.plan WfRegression.first.shape
        WfRegression.singletonEndpoint.shape).inputTy
      (Pair.Proper.plan WfRegression.first.shape
        (.stable (Top.plan WfRegression.first.shape.scope))).inputTy) :=
  proper.conversion.functionTyping

/-- The emitted interval-pair program is likewise an ordinary SystemFCo
function, with no target calculus extension. -/
example : Exp.HasType TargetContext interval.conversion.function
    (.arrow
      (Pair.Interval.plan WfRegression.first.shape
        WfRegression.singletonEndpoint.shape
        WfRegression.singletonEndpoint.shape).inputTy
      (Pair.Interval.plan WfRegression.first.shape
        (.stable (Bot.plan WfRegression.first.shape.scope))
        (.stable (Top.plan WfRegression.first.shape.scope))).inputTy) :=
  interval.conversion.functionTyping

end
end LambdaPToFCo.Direct.PairSubtypingRegression
