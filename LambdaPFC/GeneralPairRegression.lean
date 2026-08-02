import LambdaPFC.SemanticSafety

/-!
Regressions for unrestricted dependent-pair covariance.

Both source types below use `Top` for the first component, so changing their
dependent member cannot be handled by the former singleton-first rule.  The
second regression uses an interval member and therefore checks the
kind-generic case of the rule.
-/

namespace LambdaPFC.GeneralPairRegression

noncomputable section

def label : Name := 0

/-! ## Proper members -/

def properSource : Ty 0 :=
  .Pair .Top label (.ty (.Single (.var 0)))

def properTarget : Ty 0 :=
  .Pair .Top label (.ty .Top)

def properCode :
    SubCode Ctx.nil (.ty properSource) (.ty properTarget) :=
  .pair .refl .top

theorem proper_subtyping :
    Tau.Sub Ctx.nil (.ty properSource) (.ty properTarget) :=
  properCode.erase

/-! ## Abstract members -/

def intervalSource : Ty 0 :=
  .Pair .Top label
    (.intv (.Single (.var 0)) (.Single (.var 0)))

def intervalTarget : Ty 0 :=
  .Pair .Top label (.intv .Bot .Top)

def intervalCode :
    SubCode Ctx.nil (.ty intervalSource) (.ty intervalTarget) :=
  .pair .refl (.bounds .bot .top .refl)

theorem interval_subtyping :
    Tau.Sub Ctx.nil (.ty intervalSource) (.ty intervalTarget) :=
  intervalCode.erase

/-! ## Closed end-to-end regression -/

/--
The stored type is the singleton of `y`.  The ascription first exposes it as
the exact dependent interval `{x}..{x}`; the enclosing typing derivation then
uses `intervalCode` to hide that interval behind `Bot..Top` while the first
component remains `Top`.
-/
def term : Tm 0 :=
  .let
    (.abs .Top (.path (.var 0)))
    (.typed
      (.pair 0 label (.type (.Single (.var 0))))
      intervalSource.weaken)

private def intervalSourceWf :
    WfCode Ctx.nil (.ty intervalSource) :=
  .pair .top
    (.bounds_wf
      (.path (.var .here))
      (.path (.var .here))
      .refl)

private def intervalTargetWf :
    WfCode Ctx.nil (.ty intervalTarget) :=
  .pair .top (.bounds_wf .bot .top .bot)

private def boundCode :
    TermCode Ctx.nil
      (.abs .Top (.path (.var 0))) .Top :=
  .sub
    (.abs (.path (.var .here)) .top)
    .top
    .top

private def exactToIntervalSource :
    SubCode (Ctx.nil.snoc .Top)
      (.ty (.Pair (.Single (.var 0)) label
        (Tau.intv (.Single (.var 0)) (.Single (.var 0))).weaken))
      (.ty intervalSource.weaken) :=
  .pair .top
    (.bounds
      (.widen (.var .here))
      (.symm (.var .here))
      .refl)

private def annotatedSourceCode :
    TermCode (Ctx.nil.snoc .Top)
      (.typed
        (.pair 0 label (.type (.Single (.var 0))))
        intervalSource.weaken)
      intervalSource.weaken :=
  .typed
    (.sub
      (.tpair .here (.path (.var .here)))
      exactToIntervalSource
      intervalSourceWf.weaken)
    intervalSourceWf.weaken

private def bodyCode :
    TermCode (Ctx.nil.snoc .Top)
      (.typed
        (.pair 0 label (.type (.Single (.var 0))))
        intervalSource.weaken)
      intervalTarget.weaken :=
  .sub annotatedSourceCode intervalCode.weaken intervalTargetWf.weaken

def termCode : TermCode Ctx.nil term intervalTarget := by
  unfold term
  exact .let boundCode intervalTargetWf bodyCode

theorem term_typing : Tm.Ty Ctx.nil term intervalTarget :=
  termCode.erase

theorem term_type_safety
    {n : Nat} {target : State n}
    (steps : State.Steps (State.initial term) target) :
    State.Progress target :=
  term_typing.closed_type_safety steps

end
end LambdaPFC.GeneralPairRegression
