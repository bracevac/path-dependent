import LambdaPToFCo.Full.ContextWellFormed

/-!
# Well-formed results of full introduction forms

The full calculus has typed application results which are not well formed,
so result well-formedness must be recovered only from constructors that
actually justify it.  `let` stores the result proof explicitly.  Both pair
introductions synthesize canonical singleton fields; the type-member form
also stores the witness proof.
-/

namespace LambdaPToFCo.Full

open LambdaPFC

namespace LetTermTyping

/-- The advertised result of a typed `let` is well formed. -/
def resultWf :
    (typing : Tm.Ty context (.let bound body) result) ->
    Tau.Wf context (.ty result)
  | .let _ resultWf _ => resultWf
  | .sub _ _ targetWf => targetWf

end LetTermTyping

namespace PairTermTyping

/-- The advertised result of a term-member pair is well formed. -/
noncomputable def valueResultWf :
    (typing : Tm.Ty context (.pair first label (.val member)) result) ->
    Tau.Wf context (.ty result)
  | .pair => .pair (.path .var) (.path .var)
  | .sub _ _ targetWf => targetWf

/-- The advertised result of a type-member pair is well formed. -/
noncomputable def typeResultWf :
    (typing : Tm.Ty context (.pair first label (.type witness)) result) ->
    Tau.Wf context (.ty result)
  | .tpair witnessWf =>
      .pair (.path .var)
        (.bounds_wf
          (TypeWellFormed.weaken witnessWf
            (.Single (Path.var first)))
          (TypeWellFormed.weaken witnessWf
            (.Single (Path.var first)))
          .refl)
  | .sub _ _ targetWf => targetWf

end PairTermTyping

end LambdaPToFCo.Full
