import LambdaPFC.Typing

/-!
# Well-formed results for path terms

Full `LambdaPFC` does not ensure that every advertised term type is well
formed: dependent application is a genuine counterexample.  Path terms are a
smaller and important exception.  Their direct singleton result is
well-formed, and every outer subsumption constructor stores the
well-formedness of its advertised target explicitly.
-/

namespace LambdaPToFCo.Full

open LambdaPFC

namespace PathTermTyping

/-- The advertised type of a typed path term is always well formed. -/
def resultWf :
    (typing : Tm.Ty context (.path path) result) ->
    Tau.Wf context (.ty result)
  | .path precise => .path precise
  | .sub _ _ targetWf => targetWf

end PathTermTyping

end LambdaPToFCo.Full
