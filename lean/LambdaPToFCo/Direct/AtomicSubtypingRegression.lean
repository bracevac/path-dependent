import LambdaPToFCo.Direct.AtomicSubtyping
import LambdaPToFCo.Direct.WfRegression

/-!
# Atomic subtyping regressions

These checks exercise the atomic premises used by
`LambdaPFC.GeneralPairRegression`: singleton widening and symmetry at exact
environment slots, Bottom/Top endpoint adaptation, interval reflexivity, and
the `.bounds .bot .top .refl` endpoint map.
-/

namespace LambdaPToFCo.Direct.AtomicSubtypingRegression

noncomputable section

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.AtomicSubtyping

abbrev MemberContext :=
  (WfRegression.first.shape.context WfRegression.TargetContext)

/-- Literal `.widen .var` used by the exact-to-source GeneralPair coercion. -/
noncomputable def widenVariable :
    Result MemberContext
      (.Single (.var 0) : LambdaPFC.Ty 1) .Top :=
  widenAt (.var 0) (WfRegression.memberEnvironment.lookup 0)

/-- Bottom reaches the exact singleton endpoint through ordinary target
functions. -/
noncomputable def bottomToSingleton :
    Result MemberContext .Bot
      (.Single (.var 0) : LambdaPFC.Ty 1) :=
  bot WfRegression.singletonEndpoint

/-- The exact singleton endpoint forgets its observations into Top. -/
noncomputable def singletonToTop :
    Result MemberContext
      (.Single (.var 0) : LambdaPFC.Ty 1) .Top :=
  top WfRegression.singletonEndpoint

/-- The exact interval source is reflexive without reopening either
endpoint package. -/
noncomputable def exactBoundsRefl :
    IntervalResult MemberContext
      (.Single (.var 0) : LambdaPFC.Ty 1)
      (.Single (.var 0) : LambdaPFC.Ty 1)
      (.Single (.var 0) : LambdaPFC.Ty 1)
      (.Single (.var 0) : LambdaPFC.Ty 1) :=
  IntervalResult.refl WfRegression.exactMember

/-- Literal `.bounds .bot .top .refl` used by GeneralPair interval
covariance.  The nonemptiness reflexivity proof emits no target field. -/
noncomputable def abstractBounds :
    IntervalResult MemberContext
      (.Single (.var 0) : LambdaPFC.Ty 1)
      (.Single (.var 0) : LambdaPFC.Ty 1)
      .Bot .Top :=
  IntervalResult.bounds bottomToSingleton.relation
    singletonToTop.relation

/-! The GeneralPair symmetry premise is checked one binder deeper: the new
variable has the singleton of the older first-component variable. -/

noncomputable def singletonEnvironment :=
  WfRegression.memberEnvironment.enter
    (.Single (.var 0) : LambdaPFC.Ty 1)
    WfRegression.singletonEndpoint.shape
    WfRegression.singletonEndpoint.rep

/-- A closed inhabitant used only as the answer of the symmetry CPS check. -/
private def topValue {sig : Sig} : Exp sig :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

private noncomputable def topValue_hasType (base : Ctx sig) :
    Exp.HasType base (topValue : Exp sig) .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

/-- Literal `.symm .var`: the exact singleton result is consumed beneath any
faithful closure layers rather than escaping as a material relation. -/
noncomputable def symmetryVariable : Path.Body
    (WfRegression.singletonEndpoint.shape.context MemberContext) .top :=
  symmAt (.var 0) (singletonEnvironment.lookup 0) .top
    (fun _mapping _typed _result => {
      expression := topValue
      typing := topValue_hasType _
    })

end
end LambdaPToFCo.Direct.AtomicSubtypingRegression
