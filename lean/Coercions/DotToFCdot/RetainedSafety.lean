import Coercions.DotToFCdot.WadlerFest
import Coercions.DotMNF.WadlerFest.OperationalCorrespondence
import Coercions.DotMNF.WadlerFest.ReductionProgress

/-!
# Safety for the retained-let reduction relation

This is the published form of the safety statement: every term reachable
from a closed typed program is an answer or reduces. The proof transports
machine safety through the operational correspondence. The argument uses
no source type-preservation theorem or additional source inertness argument.
-/

namespace WadlerFest.Retained

/-- No retained-let execution of a closed typed program reaches a stuck term. -/
theorem not_stuck {t u : Tm []} {T : DotMNF.Ty []}
    (h : HasTy .nil t T) (run : Steps .nil t u) : ¬ Stuck .nil u := by
  intro hs
  have hb := run.behavior_back .nil h.wf .nil (hs.behavior .nil)
  obtain ⟨s, st, hr, hst⟩ := hb.stuck_run
  exact WadlerFest.dot_not_stuck h hr hst

/-- Reachable progress for the retained-let semantics, obtained through FCdot. -/
theorem safety {t u : Tm []} {T : DotMNF.Ty []}
    (h : HasTy .nil t T) (run : Steps .nil t u) :
    Answer u ∨ ∃ v, Red .nil u v := by
  rcases trichotomy Store.nil u with ha | hr | hs
  · exact .inl ha
  · exact .inr hr
  · exact False.elim (not_stuck h run hs)

end WadlerFest.Retained
