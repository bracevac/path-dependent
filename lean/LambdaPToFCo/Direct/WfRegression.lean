import LambdaPToFCo.Direct.Wf
import LambdaPFC.GeneralPairRegression

/-!
# Direct Wf representation regressions

These checks materialize both generalized-pair Wf shapes used by
`LambdaPFC.GeneralPairRegression`.  The singleton endpoint is resolved from
the exact already-open first-component variable; interval formation itself
does not compile or retain the nonemptiness subtyping proof.
-/

namespace LambdaPToFCo.Direct.WfRegression

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.Wf

abbrev TargetContext : SystemFCo.Ctx [] := SystemFCo.Ctx.empty

noncomputable def emptyEnvironment :
    Env LambdaPFC.Ctx.nil TargetContext :=
  Env.empty TargetContext

noncomputable def first : Proper TargetContext (.Top : LambdaPFC.Ty 0) :=
  Proper.top TargetContext

noncomputable def memberEnvironment :
    Env (LambdaPFC.Ctx.nil.snoc .Top)
      (first.shape.context TargetContext) :=
  emptyEnvironment.enter .Top first.shape first.rep

noncomputable def singletonEndpoint :
    Proper (first.shape.context TargetContext)
      (.Single (.var 0) : LambdaPFC.Ty 1) :=
  Proper.singletonVariable memberEnvironment 0

noncomputable def exactMember :
    Interval (first.shape.context TargetContext)
      (.Single (.var 0) : LambdaPFC.Ty 1)
      (.Single (.var 0) : LambdaPFC.Ty 1) :=
  Interval.bounds singletonEndpoint singletonEndpoint

/-- Material representation of the exact interval source from the
general-pair regression. -/
noncomputable def intervalSource :
    Proper TargetContext LambdaPFC.GeneralPairRegression.intervalSource :=
  Proper.intervalPair LambdaPFC.GeneralPairRegression.label first exactMember

noncomputable def bottomEndpoint :
    Proper (first.shape.context TargetContext) (.Bot : LambdaPFC.Ty 1) :=
  Proper.bottom (first.shape.context TargetContext)

noncomputable def topEndpoint :
    Proper (first.shape.context TargetContext) (.Top : LambdaPFC.Ty 1) :=
  Proper.top (first.shape.context TargetContext)

noncomputable def abstractMember :
    Interval (first.shape.context TargetContext)
      (.Bot : LambdaPFC.Ty 1) (.Top : LambdaPFC.Ty 1) :=
  Interval.bounds bottomEndpoint topEndpoint

/-- Material representation of the abstract interval target from the
general-pair regression. -/
noncomputable def intervalTarget :
    Proper TargetContext LambdaPFC.GeneralPairRegression.intervalTarget :=
  Proper.intervalPair LambdaPFC.GeneralPairRegression.label first
    abstractMember

end LambdaPToFCo.Direct.WfRegression
