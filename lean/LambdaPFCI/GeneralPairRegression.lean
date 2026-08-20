import LambdaPFCI.SemanticSafety

/-!
Regressions for unrestricted dependent-pair covariance.

Both source types below use `Top` for the first component, so changing their
dependent member cannot be handled by the former singleton-first rule.  The
second regression uses an interval member and therefore checks the
kind-generic case of the rule.
-/

namespace LambdaPFCI.GeneralPairRegression

noncomputable section

def label : Name := 0

/-! ## Proper members -/

def properSource : Ty 0 :=
  .Pair .Top label (.ty (.Single (.var 0)))

def properTarget : Ty 0 :=
  .Pair .Top label (.ty .Top)

def proper_subtyping :
    Tau.Sub Ctx.nil (.ty properSource) (.ty properTarget) :=
  .pair .refl .top

/-! ## Abstract members -/

def intervalSource : Ty 0 :=
  .Pair .Top label
    (.intv (.Single (.var 0)) (.Single (.var 0)))

def intervalTarget : Ty 0 :=
  .Pair .Top label (.intv .Bot .Top)

def interval_subtyping :
    Tau.Sub Ctx.nil (.ty intervalSource) (.ty intervalTarget) :=
  .pair .refl (.bounds .bot .top .refl)

/-! ## Closed end-to-end regression -/

/--
The stored type is the singleton of `y`.  Subsumption first exposes the exact
dependent interval `{x}..{x}` and then hides it behind `Bot..Top`, while the
first component remains `Top`.
-/
def term : Tm 0 :=
  .let
    (.abs .Top (.path (.var 0)))
    (.pair 0 label (.type (.Single (.var 0))))

/- The helper derivations below are context-generic: the derivations are
   identical in any context, so weakening the closed statements is a matter
   of definitional reduction rather than a renaming lemma. -/

private def intervalSourceWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (.Pair .Top label
      (.intv (.Single (.var 0)) (.Single (.var 0))))) :=
  .pair .top
    (.bounds_wf
      (.path .var)
      (.path .var)
      .refl)

private def intervalTargetWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (.Pair .Top label (.intv .Bot .Top))) :=
  .pair .top (.bounds_wf .bot .top .bot)

private def boundTyping :
    Tm.Ty Ctx.nil
      (.abs .Top (.path (.var 0))) .Top :=
  .sub
    (.abs (.path .var) .top)
    .top
    .top

private def exactToIntervalSource :
    Tau.Sub (Ctx.nil.snoc .Top)
      (.ty (.Pair (.Single (.var 0)) label
        (Tau.intv (.Single (.var 0)) (.Single (.var 0))).weaken))
      (.ty intervalSource.weaken) :=
  .pair .top
    (.bounds
      (.widen .var)
      (.symm .var)
      .refl)

private def sourceTyping :
    Tm.Ty (Ctx.nil.snoc .Top)
      (.pair 0 label (.type (.Single (.var 0))))
      intervalSource.weaken :=
  .sub
    (.tpair (.path .var))
    exactToIntervalSource
    intervalSourceWf

private def bodyTyping :
    Tm.Ty (Ctx.nil.snoc .Top)
      (.pair 0 label (.type (.Single (.var 0))))
      intervalTarget.weaken :=
  .sub sourceTyping (.pair .refl (.bounds .bot .top .refl)) intervalTargetWf

def term_typing : Tm.Ty Ctx.nil term intervalTarget :=
  .let boundTyping intervalTargetWf bodyTyping

theorem term_type_safety
    {n : Nat} {target : State n}
    (steps : State.Steps (State.initial term) target) :
    State.Progress target :=
  term_typing.closed_type_safety steps

end
end LambdaPFCI.GeneralPairRegression
